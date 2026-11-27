import LSql.Check
import LSql.Output
import Std.Time
/-! The command-line shell (shell.c's role): reads SQL from stdin, an argument or .read files, runs each statement,
prints rows in the current output mode (LSql/Output.lean), and handles the common dot commands. -/
namespace LSql.Shell

structure St where
  db : DB
  out : Output.Settings := {}
  failed : Bool := false
  quit : Bool := false
  /-- .bail on: stop at the first error -/
  bail : Bool := false
  /-- .echo on: print each command before running it -/
  echo : Bool := false

/-- Control bytes other than tab and newline as `^X`, as the shell prints them. -/
def escapeCtrl (b : ByteArray) : ByteArray :=
  if b.foldl (fun ok c => ok && (c ≥ 32 || c == 9 || c == 10)) true then b else
  b.foldl (fun acc c => if c < 32 && c != 9 && c != 10 then (acc.push 94).push (c + 64) else acc.push c) ByteArray.empty

/-- A value as list mode prints it. -/
def render (nullValue : String) : Value → ByteArray
  | .null => nullValue.toUTF8
  | .int i => (Num.int64ToText i).toUTF8
  | .real f => (Num.fmtReal f).toUTF8
  | .text s =>
    let b := textBytes s
    -- text is printed as a C string: it ends at a NUL
    let b := match b.findIdx? (· == 0) with | some k => b.extract 0 k | none => b
    escapeCtrl b
  | .blob b => escapeCtrl b

def printResult (out : IO.FS.Stream) (st : St) (r : Result) : IO Unit := do
  if r.names.isEmpty && r.rows.isEmpty then return
  -- list mode without headers, the common case, straight to bytes
  if st.out.mode == .list && st.out.titles == .off && st.out.colSep == "|" && st.out.rowSep == "\n" then
    let mut b := ByteArray.emptyWithCapacity 4096
    for row in r.rows do
      let mut first := true
      for v in row do
        unless first do b := b.push 124
        b := b ++ render st.out.nullStr v
        first := false
      b := b.push 10
      if b.size > 65536 then out.write b; b := ByteArray.emptyWithCapacity 4096
    out.write b
  else out.write (Output.render st.out r.names r.rows)

/-- An error line; standard output is flushed first, so the streams interleave as sqlite3's do. -/
def errLine (out err : IO.FS.Stream) (msg : String) : IO Unit := do
  out.flush
  err.putStrLn msg

def writeFile (db : DB) : IO DB := do
  match db.path with
  | none => return db
  | some path =>
    let p0 := db.pager
    let db := { db with pager := Pager.placeholder }
    let (bytes, p) := p0.encodeFile
    IO.FS.writeBinFile path bytes
    return { db with pager := p }

/-- Runs the statements of `sql` (which starts on line `line`); an error stops the rest of it. -/
def runSql (out err : IO.FS.Stream) (st : St) (sql : String) (line : Nat) : IO St := do
  let mut st := st
  let mut pos := 0
  for _ in [0:sql.utf8ByteSize + 1] do
    match Parse.parseNext sql pos with
    | .error e =>
      errLine out err s!"Parse error near line {line + lineOf sql e.pos}: {e.msg}"
      return { st with failed := true }
    | .ok none => break
    | .ok (some (stmt, next)) =>
      -- the database moves out of the shell's state, so the statement holds the only reference to its pages
      -- 'now' is read once per statement
      let now ← Std.Time.Timestamp.now
      let db0 := { st.db with nowMs := some (now.toMillisecondsSinceUnixEpoch.val.toInt64) }
      st := { st with db := DB.placeholder }
      let (db, r, writes) := match stmt with
        | .pragma n _ =>
          if nameEq n "integrity_check" || nameEq n "quick_check" then
            let errs := Check.run db0
            let rows := if errs.isEmpty then #[#[Value.text "ok"]] else #[#[Value.text ("*** in database main ***\n" ++ "\n".intercalate errs.toList)]]
            (db0, (Except.ok { names := #[lowerAscii n], rows } : Except Err Result), false)
          else runStmt db0 stmt
        | _ => runStmt db0 stmt
      match r with
      | .error e =>
        let stmtLine := line + lineOf sql pos
        match e.kind with
        | .parse => errLine out err s!"Parse error near line {stmtLine}: {e.msg}"
        | .runtime => errLine out err s!"Error near line {stmtLine}: {e.msg}"
        return { st with db, failed := true }
      | .ok res =>
        printResult out st res
        let db ← if writes then writeFile db else pure db
        st := { st with db }
        pos := next
  return st
where
  /-- the line of byte offset `p` within `s`, counted from 0, after leading blank lines -/
  lineOf (s : String) (p : Nat) : Nat :=
    let start := skipBlank s 0 (s.utf8ByteSize + 1)
    (List.range (p - start)).foldl (fun n k => if Lex.byteAt s (start + k) == 10 then n + 1 else n) 0
  skipBlank (s : String) (i : Nat) : Nat → Nat
    | 0 => i
    | f+1 => if Lex.byteAt s i == 10 || Lex.byteAt s i == 32 || Lex.byteAt s i == 9 || Lex.byteAt s i == 13 then skipBlank s (i+1) f else i

/-- Names laid out side by side, column by column, as the shell's split mode prints `.tables` and `.indexes`
(qrf.c's qrfSplitColumn): the most columns that fit 80 characters with 2-space gaps, then gaps of up to 5. -/
def columns (names : Array String) : String :=
  if names.isEmpty then "" else
  let n := names.size
  let widths := names.map (·.length)
  -- the widths of the columns of an nCol layout, if it fits
  let layout (nCol : Nat) : Option (Array Nat) :=
    let nr := (n + nCol - 1) / nCol
    let aw := (List.range nCol).toArray.map fun c =>
      (List.range nr).foldl (fun m r => max m (widths.getD (c * nr + r) 0)) 0
    if aw.foldl (· + ·) 0 + 2 * (nCol - 1) > 80 then none else some aw
  -- grow the column count while a layout fits (sqlite skips counts that give the same number of rows)
  let best := (List.range n).foldl (fun (acc : Nat × Array Nat × Bool) k =>
      let (nCol, aw, done) := acc
      let c := k + 2
      if done || c > n then acc
      else if (n + c - 1) / c == (n + nCol - 1) / nCol && nCol > 1 then acc
      else match layout c with
        | none => (nCol, aw, true)
        | some aw' => (c, aw', (n + c - 1) / c == 1)) (1, #[], false)
  let (nCol, aw, _) := best
  if nCol == 1 then String.join (names.toList.map (· ++ "\n")) else
  let nRow := (n + nCol - 1) / nCol
  let margin := min 5 ((80 - aw.foldl (· + ·) 0) / (nCol - 1))
  let lines := (List.range nRow).map fun r =>
    let cells := (List.range nCol).map fun c =>
      let s := names.getD (c * nRow + r) ""
      if c + 1 == nCol then s else s.pushn ' ' (aw.getD c 0 - s.length + margin)
    (String.join cells).trimAsciiEnd.toString
  String.join (lines.map (· ++ "\n"))

/-- A dot command's arguments, as shell.c's parseDotCmdArgs splits them: a trailing `;` dropped, words separated by
spaces, '...' taken literally, "..." with C escapes (\t, \n, \x41, \101, ...). -/
def dotArgs (line : String) : List String :=
  let cs := line.trimAsciiEnd.toString.toList
  let cs := match cs.reverse with
    | ';' :: r => (r.dropWhile Char.isWhitespace).reverse
    | _ => cs
  go cs [] (cs.length + 1)
where
  go (cs : List Char) (acc : List String) : Nat → List String
    | 0 => acc.reverse
    | f+1 =>
      match cs.dropWhile Char.isWhitespace with
      | [] => acc.reverse
      | q :: rest =>
        if q == '\'' || q == '"' then
          let (body, after) := quoted q rest [] (rest.length + 1)
          let s := String.ofList body
          go after ((if q == '"' then unescape s.toList [] (s.length + 1) else s) :: acc) f
        else
          let w := (q :: rest).takeWhile (!·.isWhitespace)
          go ((q :: rest).dropWhile (!·.isWhitespace)) (String.ofList w :: acc) f
  /-- the body of a quoted word (a backslash keeps the next character inside "..."), and what follows it -/
  quoted (q : Char) : List Char → List Char → Nat → List Char × List Char
    | cs, acc, 0 => (acc.reverse, cs)
    | [], acc, _ => (acc.reverse, [])
    | c :: rest, acc, f+1 =>
      if c == q then (acc.reverse, rest)
      else if c == '\\' && q == '"' then
        match rest with
        | d :: r => quoted q r (d :: c :: acc) f
        | [] => (acc.reverse, [])
      else quoted q rest (c :: acc) f
  hexVal (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none
  isOct (c : Char) : Bool := '0' ≤ c && c ≤ '7'
  /-- resolve_backslashes -/
  unescape : List Char → List Char → Nat → String
    | _, acc, 0 => String.ofList acc.reverse
    | [], acc, _ => String.ofList acc.reverse
    | '\\' :: c :: rest, acc, f+1 =>
      let simple (d : Char) := unescape rest (d :: acc) f
      match c with
      | 'a' => simple (Char.ofNat 7) | 'b' => simple (Char.ofNat 8) | 't' => simple '\t' | 'n' => simple '\n'
      | 'v' => simple (Char.ofNat 11) | 'f' => simple (Char.ofNat 12) | 'r' => simple '\r'
      | 'x' =>
        let ds := (rest.take 2).takeWhile (hexVal · |>.isSome)
        let v := ds.foldl (fun a d => a * 16 + (hexVal d).getD 0) 0
        unescape (rest.drop ds.length) (Char.ofNat v :: acc) f
      | c =>
        if isOct c then
          let ds := c :: (rest.take 2).takeWhile isOct
          let v := ds.foldl (fun a d => a * 8 + (d.toNat - '0'.toNat)) 0
          unescape (rest.drop (ds.length - 1)) (Char.ofNat (v % 256) :: acc) f
        else simple c
    | c :: rest, acc, f+1 => unescape rest (c :: acc) f

/-- A name as the shell quotes it in generated SQL (.dump): as is when a plain identifier, else in double quotes. -/
def quoteIdent (s : String) : String := quoteName s

/-- `.dump [table]`: the SQL that rebuilds the database (shell.c's dump_callback): the tables and their rows, then
sqlite_sequence, then views, triggers and indexes. -/
def dump (st : St) (pats : List String) (dataOnly : Bool) : IO ByteArray := do
  let db := st.db
  let rows := schemaRowsOf db.pager
  let mut b := if dataOnly then ByteArray.empty else "PRAGMA foreign_keys=OFF;\nBEGIN TRANSACTION;\n".toUTF8
  let mut writable := false
  -- an object is dumped when its name matches one of the LIKE patterns (ESCAPE '\')
  let wanted (name : String) : Bool := pats.isEmpty || pats.any fun p => likeMatch p.toUTF8 name.toUTF8 (some 92)
  -- tables, sqlite_sequence last
  let tables := rows.filter fun (_, vs) => (vs.getD 0 .null).toText == "table" && !(vs.getD 4 .null).isNull
  let tables := tables.filter (fun (_, vs) => (vs.getD 1 .null).toText != "sqlite_sequence")
    ++ tables.filter (fun (_, vs) => (vs.getD 1 .null).toText == "sqlite_sequence")
  for (_, vs) in tables do
    let name := (vs.getD 1 .null).toText
    let sql := (vs.getD 4 .null).toText
    if !wanted name then continue
    if name == "sqlite_sequence" then
      let n := match runStmt db (.select (.mk false [] (.select false [.expr (.fn "count" false true []) none "count(*)"]
          (some (.table name none)) [] none [] none) [] [] none none)) with
        | (_, .ok r, _) => ((r.rows[0]?).bind (·[0]?)).map Num.castToInt |>.getD 0
        | _ => 0
      if n > 0 then
        if !writable then b := b ++ "PRAGMA writable_schema=ON;\n".toUTF8; writable := true
        b := b ++ "CREATE TABLE IF NOT EXISTS sqlite_sequence(name,seq);\nDELETE FROM sqlite_sequence;\n".toUTF8
      else continue
    else if name.startsWith "sqlite_" then continue
    else
      -- a quoted table name: CREATE TABLE IF NOT EXISTS (printSchemaLine)
      let sql := if sql.startsWith "CREATE TABLE \"" || sql.startsWith "CREATE TABLE '" then
          "CREATE TABLE IF NOT EXISTS " ++ (sql.drop 13).toString else sql
      unless dataOnly do b := b ++ (sql ++ ";\n").toUTF8
    -- its rows, as INSERT statements
    match runStmt db (.select (.mk false [] (.select false [.star] (some (.table name none)) [] none [] none) [] [] none none)) with
    | (_, .ok r, _) =>
      -- insert mode as `.mode insert NAME` sets it up (it quotes the name)
      let s := (Output.setMode ({} : Output.Settings) ["insert", name]).toOption.getD {}
      b := b ++ Output.render s r.names r.rows
    | _ => pure ()
  -- views, triggers, indexes (by type, descending), with SQL
  let others := rows.filter fun (_, vs) =>
    !dataOnly && ["index", "trigger", "view"].contains (vs.getD 0 .null).toText && !(vs.getD 4 .null).isNull &&
      wanted (vs.getD 1 .null).toText
  let byType (ty : String) := others.filter fun (_, vs) => (vs.getD 0 .null).toText == ty
  for (_, vs) in byType "view" ++ byType "trigger" ++ byType "index" do
    b := b ++ ((vs.getD 4 .null).toText ++ ";\n").toUTF8
  if writable then b := b ++ "PRAGMA writable_schema=OFF;\n".toUTF8
  unless dataOnly do b := b ++ "COMMIT;\n".toUTF8
  return b

def dotCommand (out err : IO.FS.Stream) (st : St) (line : String) : IO St := do
  let words := dotArgs line
  let arg (i : Nat) : String := (words[i]?).getD ""
  let unq (s : String) : String := s
  let onOff (s : String) : Bool := Output.booleanValue s
  match words.headD "" with
  | ".headers" | ".header" =>
    return { st with out := st.out.setHeaders (if onOff (arg 1) then .on else .off) }
  | ".nullvalue" => return { st with out := st.out.setNullValue (unq (arg 1)) }
  | ".separator" =>
    if words.length < 2 then
      errLine out err "Usage: .separator COL ?ROW?"
      return { st with failed := true }
    return { st with out := st.out.setSeparator (unq (arg 1)) (if words.length > 2 then some (unq (arg 2)) else none) }
  | ".width" => return { st with out := st.out.setWidths ((words.drop 1).map Output.integerValue) }
  | ".mode" =>
    match Output.setMode st.out ((words.drop 1).map unq) with
    | .ok s => return { st with out := s }
    | .error e =>
      errLine out err e
      return { st with failed := true }
  | ".bail" => return { st with bail := onOff (arg 1) }
  | ".echo" => return { st with echo := onOff (arg 1) }
  | ".print" =>
    out.putStrLn (" ".intercalate ((words.drop 1).map unq))
    return st
  | ".quit" | ".exit" => return { st with quit := true }
  | ".tables" =>
    let names := st.db.schema.tables.map (fun t => if t.temp then "temp." ++ t.name else t.name)
      ++ st.db.schema.views.map (fun v => if v.temp then "temp." ++ v.name else v.name)
    let like (pat s : String) : Bool := likeMatch pat.toUTF8 s.toUTF8 none
    let names := names.filter fun n =>
      let bare := if n.startsWith "temp." then (n.drop 5).toString else n
      !bare.startsWith "sqlite_" && (words.length < 2 || like (arg 1) bare)
    out.putStr (columns (sortBy names fun a b => compare a b))
    return st
  | ".indexes" | ".indices" =>
    let like (pat s : String) : Bool := likeMatch pat.toUTF8 s.toUTF8 none
    let names := st.db.schema.indexes.filter (fun ix =>
        !ix.name.startsWith "sqlite_" && (words.length < 2 || like ("%" ++ arg 1 ++ "%") ix.name))
      |>.map (fun ix => if ix.temp then "temp." ++ ix.name else ix.name)
    out.putStr (columns (sortBy names fun a b => compare a b))
    return st
  | ".schema" =>
    for (_, vs) in schemaRowsOf st.db.pager do
      match vs.getD 4 .null with
      | .text s =>
        if arg 1 == "" || nameEq (vs.getD 2 .null).toText (arg 1) then out.putStrLn (s ++ ";")
      | _ => pure ()
    return st
  | ".dump" =>
    let pats := (words.drop 1).filter (!·.startsWith "-")
    let dataOnly := words.any (fun w => w == "--data-only" || w == "-data-only")
    out.write (← dump st pats dataOnly)
    return st
  | cmd =>
    errLine out err s!"Error: unknown command or invalid arguments:  \"{cmd.drop 1}\". Enter \".help\" for help"
    return { st with failed := true }

/-- The shell's input loop: lines collect until they end a statement (a dot command is a line of its own); `.read`
runs a file's lines in its place (`fuel`: how deep .read may nest). -/
def runInput (out err : IO.FS.Stream) (st : St) (input : String) : Nat → IO St
  | 0 => do errLine out err "Error: .read nested too deeply"; return { st with failed := true }
  | fuel+1 => do
  let lines := input.splitOn "\n"
  let mut st := st
  let mut buf := ""
  let mut bufLine := 0
  let mut n := 0
  for l in lines do
    n := n + 1
    if st.quit then break
    if st.bail && st.failed then break
    if buf.isEmpty && l.trimAscii.toString.startsWith "." then
      if st.echo then out.putStrLn l
      let w := dotArgs l
      if w.headD "" == ".read" then
        let path := (w[1]?).getD ""
        match ← (IO.FS.readFile path).toBaseIO with
        | .ok text => st ← runInput out err st text fuel
        | .error _ =>
          errLine out err s!"Error: cannot open \"{path}\""
          st := { st with failed := true }
      else st ← dotCommand out err st l
      continue
    if buf.isEmpty then
      -- a line of only whitespace and comments starts no statement
      if (Lex.lexTok l 0).kind == .eof && !(Lex.openComment l 0 (l.utf8ByteSize + 1)) then continue
      bufLine := n
    buf := buf ++ l ++ "\n"
    if Parse.isComplete buf then
      if st.echo then out.putStr buf
      st ← runSql out err st buf bufLine
      buf := ""
  if !buf.trimAscii.isEmpty && !st.quit then
    st ← runSql out err st buf bufLine
  return st

/-- All of a stream, read in 64 KiB blocks (a fuel-bounded loop: 2^40 blocks is more input than exists). -/
def readAll (h : IO.FS.Stream) : IO ByteArray :=
  go ByteArray.empty (2 ^ 40)
where
  go (acc : ByteArray) : Nat → IO ByteArray
    | 0 => pure acc
    | f+1 => do
      let b ← h.read 65536
      if b.isEmpty then pure acc else go (acc ++ b) f

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  let path := args.headD ":memory:"
  let bytes ← if path == ":memory:" || path == "" then pure ByteArray.empty
    else if ← System.FilePath.pathExists path then IO.FS.readBinFile path else pure ByteArray.empty
  match openBytes (if path == ":memory:" || path == "" then none else some path) bytes with
  | .error e =>
    errLine out err s!"Error: {e.msg}"
    return 1
  | .ok db =>
    let st : St := { db }
    let st ← match args[1]? with
      | some sql => runInput out err st sql 64
      | none => do
        let input ← readAll (← IO.getStdin)
        runInput out err st (textOfBytes input) 64
    out.flush
    return if st.failed then 1 else 0

end LSql.Shell
