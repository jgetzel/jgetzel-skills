import LuaLean.Run
import LuaLean.Print

/-! `lua-lean check`'s Lean side: `Check.lean <cwd> <cases.lua> <per> <file.lua>...`. For each file: whether it
parses; every construct and library call outside the subset (DESIGN.md, *The subset*) the source shows, with its
line; and `per` calls with random arguments of each function the chunk defines at its top level, under the
semantics, written to `cases.lua` for `test/luasem.lua` to run under LuaJIT (a call that reaches an effect, or a
chunk that does, is left out: those are not pure). A module the chunk requires, and what that requires, is source
when its file is under one of the script's directories, as `lua-lean run --lib` loads one. What only a run finds (a `#t` with two borders, a double past a
C cast's range) is the differential test's to find. -/

open Lua

namespace Check


/-- modules LuaJIT has that are outside the subset: `require` gives a handle -/
def outsideModules : List String :=
  ["jit", "jit.util", "jit.opt", "jit.profile", "string.buffer"]

/-- string.format's conversions the semantics stops at -/
def badConvs : List Char := ['a', 'A', 'o', 'u', 'p']

structure St where
  toks : Array (Token × Nat)
  pos : Nat := 0
  line : Nat := 1
  out : Array (Nat × String) := #[]
  reads : Array (Nat × String) := #[]
  writes : List String := []
  fieldReads : Array (Nat × String × String) := #[]
  fieldWrites : List (String × String) := []
  requires : Array (Nat × String) := #[]

abbrev W := StateM St

def tokText : Token → Option String
  | .name s => some s
  | .str s => some (String.ofList s)
  | _ => none

/-- the token `x` within the next 64: a name the walk meets is the next one in the source, unless the parser made
it (a method's `self`), so a miss leaves the place where it was -/
partial def findTok (toks : Array (Token × Nat)) (x : String) (i stop : Nat) : Option Nat :=
  if i < toks.size && i < stop then
    if tokText (toks[i]!).1 == some x then some i else findTok toks x (i + 1) stop
  else none

def see (x : String) : W Unit := modify fun s =>
  match findTok s.toks x s.pos (s.pos + 64) with
  | some i => { s with pos := i + 1, line := (s.toks[i]!).2 }
  | none => s

/-- a name being declared: the next name token if it is `x`, past `local`, `function`, `for`, `(` and `,` only -/
partial def seeDecl (x : String) : W Unit := modify fun s =>
  let rec go (i : Nat) : Option Nat :=
    match s.toks[i]? with
    | some (.kw "local", _) | some (.kw "function", _) | some (.kw "for", _) | some (.sym "(", _)
    | some (.sym ",", _) => go (i + 1)
    | some (t, _) => if tokText t == some x then some i else none
    | none => none
  match go s.pos with
  | some i => { s with pos := i + 1, line := (s.toks[i]!).2 }
  | none => s

def note (msg : String) : W Unit := modify fun s => { s with out := s.out.push (s.line, msg) }

def strip : Exp → Exp
  | .site _ e => strip e
  | .paren e => strip e
  | e => e

def stripS : Stat → Stat
  | .site _ s => stripS s
  | s => s

partial def convs : List Char → List Char
  | '%' :: '%' :: r => convs r
  | '%' :: r =>
    match r.dropWhile fun c => "-+ #0.".toList.contains c || Num.isDigit c with
    | c :: r => c :: convs r
    | [] => []
  | _ :: r => convs r
  | [] => []

def fmtNote (fmt : List Char) : W Unit :=
  for c in (convs fmt).eraseDups do
    if badConvs.contains c then note s!"string.format's %{c}: outside the subset, the run stops"

def gotoNote (l : String) (bs : List Block) : W Unit :=
  match bs.find? (hasLabel · l) with
  | some b => if labelAtEnd b l then pure () else
    note s!"goto {l}: to a label that does not end its block (the subset has the continue idiom only)"
  | none => note s!"goto {l}: no visible label (LuaJIT rejects the file, the parser does not)"

/-- the debug library's calls that need what the semantics lacks: a Lua function's active lines, a type's metatable
(`debugFn` in LuaLean/Interp.lean) -/
def debugNote (f : String) (as : List Exp) : W Unit :=
  match f, as with
  | "getinfo", _ :: .str o :: _ =>
    if o.contains 'L' then
      note "debug.getinfo with 'L': a Lua function's active lines are not modelled, the run stops at one"
    else pure ()
  | "setmetatable", .str _ :: _ | "setmetatable", .num _ :: _ | "setmetatable", .nil :: _ =>
    note "debug.setmetatable of a value not a table: the metatable of its type, the run stops"
  | _, _ => pure ()

/-- getfenv's and setfenv's levels the semantics has no frame for (`fenvLevel` in LuaLean/Interp.lean): past 1, 1 in
a tail call (`tail`), and setfenv's 0, the thread's -/
def fenvNote (f : String) (as : List Exp) (tail : Bool) : W Unit :=
  let lvl : Option Int := match f, as with
    | "getfenv", [] => some 1
    | _, .num (.int k) :: _ => some k
    | _, _ => none
  match lvl with
  | some k => do
    if !tail && k == 0 && f == "setfenv" then
      note "setfenv of level 0: the thread's environment is not modelled, the run stops"
  | none => pure ()

mutual
partial def exp (sc : List String) (bs : List Block) (e : Exp) : W Unit := do
  match e with
  | .var x =>
    see x
    if !sc.contains x then modify fun s => { s with reads := s.reads.push (s.line, x) }
  | .str c => let k := String.ofList c; see k
  | .func ps _ b _ => func sc ps b
  | .index t k =>
    exp sc bs t; exp sc bs k
    if let (.var lib, .str f) := (strip t, strip k) then
      if !sc.contains lib then
        modify fun s => { s with fieldReads := s.fieldReads.push (s.line, lib, String.ofList f) }
  | .call f as =>
    exp sc bs f; as.forM (exp sc bs)
    match strip f, as.map strip with
    | .var "require", .str m :: _ => if !sc.contains "require" then
        modify fun s => { s with requires := s.requires.push (s.line, String.ofList m) }
    | .var "setmetatable", .var "_G" :: _ => if !sc.contains "_G" then
        note "setmetatable(_G, ...): a metatable on _G stops the run"
    | .index (.var "string") (.str f), .str fmt :: _ => if f == "format".toList then fmtNote fmt
    | .index (.var "debug") (.str f), as => if !sc.contains "debug" then debugNote (String.ofList f) as
    | .var g, as => if (g == "getfenv" || g == "setfenv") && !sc.contains g then fenvNote g as false
    | _, _ => pure ()
  | .method o m as =>
    exp sc bs o; see m; as.forM (exp sc bs)
    if let .str fmt := strip o then if m == "format" then fmtNote fmt
  | .bin _ a b | .and a b | .or a b => exp sc bs a; exp sc bs b
  | .site st a =>
    exp sc bs a
    if let .call (.var g) as := strip a then
      if st.tail && (g == "getfenv" || g == "setfenv") && !sc.contains g then fenvNote g (as.map strip) true
  | .un _ a | .paren a => exp sc bs a
  | .table fs => fs.forM (field sc bs)
  | _ => pure ()

partial def field (sc : List String) (bs : List Block) : Field → W Unit
  | .pos e => exp sc bs e
  | .named k e => do see k; exp sc bs e
  | .keyed k e _ => do exp sc bs k; exp sc bs e

partial def func (sc : List String) (ps : List String) (b : Block) : W Unit := do
  ps.forM seeDecl
  let _ ← block (ps.reverse ++ sc) [] b

partial def target (sc : List String) (bs : List Block) (e : Exp) : W Unit :=
  match e with
  | .site _ t => target sc bs t
  | .var x => do
    see x
    if !sc.contains x then modify fun s => { s with writes := x :: s.writes }
  | .index t k => do
    exp sc bs t; exp sc bs k
    if let (.var lib, .str f) := (strip t, strip k) then
      if !sc.contains lib then modify fun s => { s with fieldWrites := (lib, String.ofList f) :: s.fieldWrites }
  | e => exp sc bs e

partial def block (sc : List String) (bs : List Block) (b : Block) : W (List String) := do
  let mut sc := sc
  for s in b do sc ← stat sc (b :: bs) s
  return sc

partial def stat (sc : List String) (bs : List Block) (st : Stat) : W (List String) := do
  match st with
  | .loc ns es => ns.forM seeDecl; es.forM (exp sc bs); return ns.reverse ++ sc
  | .assign ts es => ts.forM (target sc bs); es.forM (exp sc bs); return sc
  | .call e => exp sc bs e; return sc
  | .block b => let _ ← block sc bs b; return sc
  | .while c b => exp sc bs c; let _ ← block sc bs b; return sc
  | .rpt b c => let sc' ← block sc bs b; exp sc' (b :: bs) c; return sc
  | .ite c t e => exp sc bs c; let _ ← block sc bs t; let _ ← block sc bs e; return sc
  | .fornum v a b step body =>
    seeDecl v; exp sc bs a; exp sc bs b
    if let some s := step then exp sc bs s
    let _ ← block (v :: sc) bs body; return sc
  | .forin vs es body =>
    vs.forM seeDecl; es.forM (exp sc bs); let _ ← block (vs.reverse ++ sc) bs body; return sc
  | .locfn n ps _ b _ => seeDecl n; func (n :: sc) ps b; return n :: sc
  | .ret es => es.forM (exp sc bs); return sc
  | .brk => return sc
  | .goto l => see l; gotoNote l bs; return sc
  | .label l => see l; return sc
  | .site _ s => stat sc bs s
end

/-- a value of the initial heap's `_G`, or of one of its library tables -/
def global (x : String) : Val :=
  match (initHeap[0]? : Option Obj) with
  | some (.tbl g) => g.get (lstr x)
  | _ => .nil

def libField (lib f : String) : Val :=
  match global lib with
  | .tbl a => match (initHeap[a]? : Option Obj) with
    | some (.tbl t) => t.get (lstr f)
    | _ => .nil
  | _ => .nil

/-- LuaJIT's modules loaded at the start, and table.new and table.clear -/
def loadedModule (m : String) : Bool :=
  m == "table.new" || m == "table.clear" || (match (initHeap[1]? : Option Obj) with
    | some (.tbl t) => !(t.get (lstr m)).isNil && !outsideModules.contains m
    | _ => false)

/-- the findings: (line, what, outside the subset); an effect or a global no one defines is not outside it -/
def findings (st : St) (isGiven : String → Bool) : List (Nat × String × Bool) :=
  let globalRead (line : Nat) (x : String) : List (Nat × String × Bool) :=
    if st.writes.contains x then [] else
    match global x with
    | .nil => [(line, s!"undefined global '{x}': nil, as in LuaJIT (a host that defines it is outside the subset)", false)]
    | .eff _ => [(line, s!"global '{x}': LuaJIT's, not modelled (a handle: a run that uses it stops)", true)]
    | _ => []
  let gs := st.reads.toList.flatMap fun (l, x) => globalRead l x
  let fs := st.fieldReads.toList.flatMap fun (l, lib, f) =>
    if lib == "_G" then globalRead l f
    else if st.writes.contains lib || st.fieldWrites.contains (lib, f) then [] else
    match libField lib f with
    | .eff n =>
      if n.startsWith "package." || n.startsWith "debug." then
        [(l, s!"{lib}.{f}: LuaJIT's, not modelled (a handle: a run that uses it stops)", true)]
      else [(l, s!"effect {lib}.{f}: the world's (DESIGN.md, Effects), so a function calling it is not pure", false)]
    | _ => []
  let rs := st.requires.toList.flatMap fun (l, m) =>
    if outsideModules.contains m then [(l, s!"require '{m}': outside the subset (a handle: a run that uses it stops)", true)]
    else if loadedModule m || isGiven m then []
    else [(l, s!"require '{m}': a module not given as source (a handle: a run that uses it stops)", true)]
  let os := st.out.toList.map fun (l, m) => (l, m, true)
  (gs ++ fs ++ rs ++ os).eraseDups.mergeSort fun a b => a.1 ≤ b.1

def fnOf : Exp → Option (List String × Bool)
  | .site _ e => fnOf e
  | .func ps va _ _ => some (ps, va)
  | _ => none

/-- the functions the chunk defines at its top level: how to call one, its object if a method, its parameters -/
def topFns (b : Block) : List (String × Option String × List String × Bool) :=
  b.flatMap fun st => match stripS st with
    | .locfn n ps va _ _ => [(n, none, ps, va)]
    | .loc [n] [e] => match fnOf e, strip e with
      | some (ps, va), _ => [(n, none, ps, va)]
      | none, .table fs => fs.filterMap fun f => match f with
        | .named k e => (fnOf e).map fun (ps, va) => (s!"{n}.{k}", (if ps.head? == some "self" then some n else none), ps, va)
        | _ => none
      | _, _ => []
    | .assign [t] [e] => match fnOf e with
      | some (ps, va) =>
        let self := if ps.head? == some "self" then (match strip t with | .index o _ => some (Print.exp o) | _ => none)
          else none
        [(Print.exp t, self, ps, va)]
      | none => []
    | _ => []

def pool : Array String := #["nil", "true", "false", "0", "1", "-1", "2", "3", "10", "0.5", "-2.5", "1e300", "2^53",
  "\"\"", "\"a\"", "\"abc\"", "\"hello world\"", "\"10\"", "\"1.5\"", "\"a,b;c\"", "{}", "{1, 2, 3}",
  "{\"b\", \"a\", \"c\"}", "{x = 1, y = \"z\"}", "{1, {2, 3}, n = 2}", "function(...) return ... end",
  "function(a, b) return a < b end"]

def dropRet (b : Block) : Block :=
  match b.getLast? with
  | some s => if let .ret _ := stripS s then b.dropLast else b
  | none => b

/-- `per` calls of each top-level function as chunks, after `pre`: the chunk's text and the function's name. A call
is an argument, not a tail call, so an error of level 2 in the function (`error(msg, 2)`) has the chunk's place -/
def calls (pre : String) (b : Block) (per seed : Nat) : List (String × String) := Id.run do
  let pre := pre ++ Print.block (dropRet b)
  let mut g := mkStdGen seed
  let mut r := []
  for (f, self, ps, va) in topFns b do
    let ps := if self.isSome then ps.drop 1 else ps
    for _ in [0:per] do
      let (extra, g') := if va then randNat g 0 2 else (0, g)
      g := g'
      let mut as := self.toList
      for _ in [0:ps.length + extra] do
        let (i, g') := randNat g 0 (pool.size - 1)
        g := g'
        as := as ++ [pool[i]!]
      r := (pre ++ s!"return (function(...) return ... end)({f}({", ".intercalate as}))\n", f) :: r
  return r.reverse

/-- a module is given as source when a file for it is under one of the script's directories -/
def givenIn (dirs : List System.FilePath) (m : String) : IO Bool :=
  dirs.anyM fun d => do
    let p := m.replace "." "/"
    return (← (d / (p ++ ".lua")).pathExists) || (← (d / p / "init.lua").pathExists)

def ancestors (p : System.FilePath) : Nat → List System.FilePath
  | 0 => [p]
  | n + 1 => p :: (p.parent.map (ancestors · n)).getD []

/-- the files a `require` of each of `ms` loads through package.path `path`, and of what they require, as source:
the modules by name, and each file by its path (as `require` names it) -/
partial def modSources (path : String) (ms : List String) (seen : List String := [])
    (srcs : List (String × Block) := []) : IO (List String × List (String × Block)) := do
  match ms with
  | [] => return (seen, srcs)
  | m :: ms =>
    if seen.contains m || loadedModule m || outsideModules.contains m then return ← modSources path ms seen srcs
    match ← (pathFiles path.toList (modPath m.toList)).findM? (fun (f : String) => do pure ((← System.FilePath.pathExists f) && !(← System.FilePath.isDir f))) with
    | none => modSources path ms seen srcs
    | some f =>
      match parseChunk (bytesOf (← IO.FS.readBinFile f)) (shortSrc ("@" ++ f).toList) with
      | .error _ => modSources path ms (m :: seen) srcs
      | .ok b =>
        let (_, st) := (block [] [] b).run { toks := #[] }
        modSources path (ms ++ st.requires.toList.map (·.2)) (m :: seen) ((f, b) :: srcs)

end Check

open Check in
def main (args : List String) : IO UInt32 := do
  let cwd :: casesFile :: per :: files := args
    | do IO.eprintln "usage: Check.lean <cwd> <cases.lua> <per> <file.lua>..."; return 2
  let mut bad := false
  let mut cases : Array String := #[]
  for file in files do
    let name := if file.startsWith (cwd ++ "/") then (file.drop (cwd.length + 1)).toString else file
    let src := bytesOf (← IO.FS.readBinFile file)
    match parseChunk src (shortSrc ("@" ++ file).toList), lex src #[] with
    | .error e, _ | _, .error e => IO.println s!"{name}: parse error: {e}"; bad := true
    | .ok b, .ok toks =>
      let (_, st) := (block [] [] b).run { toks }
      let dirs := ancestors ((System.FilePath.mk file).parent.getD ".") 4
      let gv ← (st.requires.toList.map (·.2)).filterM (givenIn dirs)
      let fs := findings st gv.contains
      for (l, m, _) in fs do IO.println s!"{name}:{l}: {m}"
      let outside := (fs.filter (·.2.2)).length
      if outside > 0 then bad := true
      -- the chunk alone, then each call
      -- the modules found beside it as source; under LuaJIT each chunk sets the path and forgets what one before loaded
      let path := ";".intercalate (dirs.flatMap fun d => [(d / "?.lua").toString, (d / "?" / "init.lua").toString])
      let (mods, srcs) ← modSources path (st.requires.toList.map (·.2))
      let pre := s!"package.path = {String.ofList (serStr path.toList)}\nfor _, m in ipairs(\{" ++
        ", ".intercalate (mods.map fun m => String.ofList (serStr m.toList)) ++ "}) do package.loaded[m] = nil end\n"
      let top := runCase (srcsOf srcs) .dual [] (pre ++ Print.block (dropRet b)).toList
      let fns := topFns b
      let mut n := 0
      let mut left : List String := []
      if top.startsWith "ok:" || top.startsWith "error:" then
        for (src, _) in calls pre b per.toNat! (hash file).toNat do
          let out := runCase (srcsOf srcs) .dual [] src.toList
          let out1 := runCase (srcsOf srcs) .single [] src.toList
          if out.startsWith "ok:" || out.startsWith "error:" then
            let single := if out1 == out then "" else s!", single = {String.ofList (serStr out1.toList)}"
            cases := cases.push
              s!"\{src = {String.ofList (serStr src.toList)}, out = {String.ofList (serStr out.toList)}{single}},"
            n := n + 1
          else left := out :: left
      else left := [s!"the chunk: {top}"]
      let why := match left.getLast? with | some w => s!" ({left.length} left out, the first: {w})" | none => ""
      IO.println s!"{name}: parses, {outside} outside the subset, {fns.length} functions, {n} cases{why}"
  IO.FS.writeFile casesFile ("return {\n" ++ "\n".intercalate cases.toList ++ "\n}\n")
  return if bad then 1 else 0
