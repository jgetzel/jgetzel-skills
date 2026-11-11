import LuaLean.Syntax
import LuaLean.Pat

/-! The semantics: an interpreter for the subset, on fuel. A value is nil, a boolean, a number, a string (its bytes),
a table or a closure (heap addresses), a builtin, or an effect handle. Every local is a heap cell, so closures share
upvalues as Lua's do; `pcall` keeps what the failed call wrote, as Lua does (`EStateM` keeps the state on error).

Effects are not interpreted: `io`, `os`, `print`, and every module not given as source (`posix.*`, `lfs`, `cjson`, a
script's own C modules, …) are `Val.eff` handles, and calling one asks `oracle`; `none` stops the run with
`Err.eff`. Fuel bounds the depth of the evaluation (each nested evaluation, call and loop iteration takes one);
running out is `Err.fuel`, never a Lua error, so `pcall` does not catch it. -/

namespace Lua

inductive Val where
  | nil
  | bool (b : Bool)
  | num (n : Num)
  | str (s : List Char)
  | tbl (a : Nat)
  | fn (a : Nat)
  | prim (name : String) (bound : List Val)
  | eff (name : String)
  deriving Inhabited

abbrev Env := List (String × Nat)

structure Clo where
  params : List String
  va : Bool
  body : Block
  env : Env

structure Tbl where
  kv : List (Val × Val) := []
  mt : Option Nat := none

inductive Obj where
  | tbl (t : Tbl)
  | clo (c : Clo)
  | cell (v : Val)

instance : Inhabited Obj := ⟨.cell .nil⟩

abbrev Heap := Array Obj

/-- a runtime error's message before it has a place: LuaJIT's message for an operator on an operand (`i`, of the
site's names; `none`, the callee), a bad argument to a builtin, or a value (a string or number) -/
inductive Msg where
  | op (what : String) (i : Option Nat) (tname : String)
  | arg (narg : Nat) (msg : String)
  | val (v : Val)
  deriving Inhabited

inductive Err where
  /-- a Lua error and its value -/
  | val (v : Val)
  | fuel
  /-- an effect the oracle does not answer -/
  | eff (name : String) (args : List Val)
  /-- a runtime error to be reported in the frame `lvl` calls out from the one raising it (0: that frame, at its
  innermost site; `Site`): LuaJIT adds `chunk:line:` there, or nothing if that frame is a builtin's -/
  | rt (lvl : Nat) (m : Msg)
  deriving Inhabited

abbrev M := EStateM Err Heap

inductive Flow where
  | norm | brk
  | ret (vs : List Val)
  | goto (l : String)

structure Ctx where
  env : Env
  va : List Val

def lstr (s : String) : Val := .str s.toList
/-- an error of the semantics' own (a run outside what it models), not LuaJIT's -/
def die {α} (msg : String) : M α := throw (.val (lstr msg))

namespace Val
def truthy : Val → Bool
  | .nil | .bool false => false
  | _ => true

def isNil : Val → Bool
  | .nil => true
  | _ => false

mutual
/-- raw equality -/
def rawEq : Val → Val → Bool
  | .nil, .nil => true
  | .bool a, .bool b => a == b
  | .num a, .num b => a.eq b
  | .str a, .str b => a == b
  | .tbl a, .tbl b => a == b
  | .fn a, .fn b => a == b
  | .prim a xs, .prim b ys => a == b && rawEqs xs ys
  | .eff a, .eff b => a == b
  | _, _ => false
def rawEqs : List Val → List Val → Bool
  | [], [] => true
  | x :: xs, y :: ys => rawEq x y && rawEqs xs ys
  | _, _ => false
end

def typeName : Val → String
  | .nil => "nil" | .bool _ => "boolean" | .num _ => "number" | .str _ => "string" | .tbl _ => "table"
  | .fn _ | .prim .. => "function" | .eff _ => "userdata"

def toNum : Val → Option Num
  | .num n => some n
  | .str s => Num.parse s
  | _ => none

/-- tostring without metamethods -/
def text : Val → List Char
  | .nil => "nil".toList
  | .bool b => (if b then "true" else "false").toList
  | .num n => n.toText
  | .str s => s
  | .tbl a => s!"table: {a}".toList
  | .fn a => s!"function: {a}".toList
  | .prim n _ => s!"function: builtin {n}".toList
  | .eff n => s!"userdata: {n}".toList
end Val

namespace Tbl
def get (t : Tbl) (k : Val) : Val :=
  match t.kv.find? (fun (x, _) => Val.rawEq x k) with
  | some (_, v) => v
  | none => .nil

/-- an existing key keeps its place; a new key goes last -/
def set (t : Tbl) (k v : Val) : Tbl :=
  if t.kv.any (fun (x, _) => Val.rawEq x k) then
    { t with kv := t.kv.map fun (x, w) => if Val.rawEq x k then (x, v) else (x, w) }
  else if v.isNil then t
  else { t with kv := t.kv ++ [(k, v)] }

def int (i : Int) : Val := .num (.int i)

/-- the border #t: the least n with t[n+1] nil -/
def len (t : Tbl) : Nat :=
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | fuel + 1 => if (t.get (int (i + 1))).isNil then i else go (i + 1) fuel
  go 0 (t.kv.length + 1)

/-- the entry after key k with a value (k nil: the first) -/
def next (t : Tbl) (k : Val) : Option (Option (Val × Val)) :=
  let rest := if k.isNil then some t.kv else
    match t.kv.findIdx? (fun (x, _) => Val.rawEq x k) with
    | some i => some (t.kv.drop (i + 1))
    | none => none
  rest.map fun r => r.find? fun (_, v) => !v.isNil
end Tbl

-- ---------- runtime errors ----------

/-- an error of the running instruction (index, call, an operator, a `for`), reported at its site -/
def rtErr {α} (msg : String) : M α := throw (.rt 0 (.val (lstr msg)))
/-- an operator's error on operand `i` (`none`: the callee) -/
def opErr {α} (what : String) (i : Option Nat) (v : Val) : M α := throw (.rt 0 (.op what i v.typeName))
/-- a builtin's error, reported where it was called from (lj_err_caller) -/
def callerErr {α} (msg : String) : M α := throw (.rt 1 (.val (lstr msg)))
/-- a builtin's bad argument (lj_err_arg): `narg` counts from 1 -/
def argErr {α} (narg : Nat) (msg : String) : M α := throw (.rt 1 (.arg narg msg))

namespace Msg
/-- the message with no place: raised in a builtin, or reported in one -/
def bare : Msg → Val
  | .op what _ t => lstr s!"attempt to {what} a {t} value"
  | .arg narg msg => lstr s!"bad argument #{narg} to '?' ({msg})"
  | .val v => .str v.text

/-- the message at site `s` (lj_debug_addloc; err_argmsg names the callee and counts a method's arguments from its
self) -/
def render (s : Site) : Msg → Val
  | .op what i t =>
    let (kind, x) := match i with | some i => s.names.getD i ("", "") | none => s.fn
    if kind == "" then lstr s!"{s.src}:{s.line}: attempt to {what} a {t} value"
    else lstr s!"{s.src}:{s.line}: attempt to {what} {kind} '{x}' (a {t} value)"
  | .arg narg msg =>
    let (kind, x) := s.fn
    let x := if kind == "" then "?" else x
    if kind == "method" then
      if narg == 1 then lstr s!"{s.src}:{s.line}: calling '{x}' on bad self ({msg})"
      else lstr s!"{s.src}:{s.line}: bad argument #{narg - 1} to '{x}' ({msg})"
    else lstr s!"{s.src}:{s.line}: bad argument #{narg} to '{x}' ({msg})"
  | .val v => .str (s!"{s.src}:{s.line}: ".toList ++ v.text)
end Msg

/-- the node at site `s`: an error of its own frame gets the place; a tail call's callee reports out of the frame
the call replaces -/
def atSite {α} (s : Site) (m : M α) : M α := fun h =>
  match m h with
  | .error (.rt k msg) h =>
    let k := if s.tail && (match msg with | .op .. => false | _ => true) then k + 1 else k
    match k with
    | 0 => .error (.val (msg.render s)) h
    | k => .error (.rt k msg) h
  | r => r

/-- `m`, its errors reported at `s` if there is one -/
def atSite? {α} : Option Site → M α → M α
  | some s, m => atSite s m
  | none, m => m

/-- a call's frame: an error reported in it that no site took is in a builtin, so it has no place; the rest are
one frame further out -/
def frame {α} (m : M α) : M α := fun h =>
  match m h with
  | .error (.rt 0 msg) h => .error (.val msg.bare) h
  | .error (.rt (k + 1) msg) h => .error (.rt k msg) h
  | r => r

-- ---------- the heap ----------

def getObj (a : Nat) : M Obj := do
  match (← get)[a]? with
  | some o => pure o
  | none => die "dangling address"

def alloc (o : Obj) : M Nat := do
  let h ← get
  set (h.push o)
  pure h.size

def getTbl (a : Nat) : M Tbl := do
  match ← getObj a with
  | .tbl t => pure t
  | _ => die "not a table"

def putTbl (a : Nat) (t : Tbl) : M Unit := modify fun h => h.set! a (.tbl t)

def readCell (a : Nat) : M Val := do
  match ← getObj a with
  | .cell v => pure v
  | _ => die "not a cell"

def writeCell (a : Nat) (v : Val) : M Unit := modify fun h => h.set! a (.cell v)

def rawget (a : Nat) (k : Val) : M Val := do pure ((← getTbl a).get k)

def rawset (a : Nat) (k v : Val) : M Unit := do
  match k with
  | .nil => rtErr "table index is nil"
  | .num (.flt f) =>
    if f.isNaN then rtErr "table index is NaN" else
    -- an integral key is stored as an integer, -0 as 0
    let k := if f.floor == f && f.abs < 2147483648.0 then Val.num (.int (Num.floatToInt f)) else k
    putTbl a ((← getTbl a).set k v)
  | _ => putTbl a ((← getTbl a).set k v)

/-- fixed addresses of the initial heap -/
def G : Nat := 0
def LOADED : Nat := 1
def STRING : Nat := 2
def TABLE : Nat := 3

def getVar (cx : Ctx) (x : String) : M Val :=
  match cx.env.lookup x with
  | some c => readCell c
  | none => rawget G (lstr x)

def setVar (cx : Ctx) (x : String) (v : Val) : M Unit :=
  match cx.env.lookup x with
  | some c => writeCell c v
  | none => rawset G (lstr x) v

def bindLocals (cx : Ctx) : List String → List Val → M Ctx
  | [], _ => pure cx
  | x :: xs, vs => do
    let c ← alloc (.cell (vs.headD .nil))
    bindLocals { cx with env := (x, c) :: cx.env } xs vs.tail

/-- v's metamethod `ev`, read from its metatable when the operation runs (lj_meta_lookup); only tables have one here,
but strings, whose metatable has `__index` alone (`index`) -/
def metaOf (v : Val) (ev : String) : M Val := do
  match v with
  | .tbl a => match (← getTbl a).mt with
    | some m => rawget m (lstr ev)
    | none => pure .nil
  | _ => pure .nil

/-- a metamethod the semantics does not model yet stops the run where LuaJIT would call it (DESIGN.md, *The subset*) -/
def noMeta (vs : List Val) (evs : List String) : M Unit := do
  for v in vs do
    for ev in evs do
      if !(← metaOf v ev).isNil then throw (.eff s!"metamethod {ev}" [])

-- ---------- operators ----------

def strLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => if a == b then strLt s t else a < b

def arith (tgt : Target) (op : BinOp) (x y : Val) : M Val :=
  match x.toNum, y.toNum with
  | some a, some b => pure (.num (match op with
      | .add => a.add b | .sub => a.sub b | .mul => a.mul tgt b | .div => a.div b | .mod => a.mod b | _ => a.pow b))
  | _, _ => do
    noMeta [x, y] [match op with
      | .add => "__add" | .sub => "__sub" | .mul => "__mul" | .div => "__div" | .mod => "__mod" | _ => "__pow"]
    if x.toNum.isNone then opErr "perform arithmetic on" (some 0) x else opErr "perform arithmetic on" (some 1) y

def less (x y : Val) (orEq : Bool) : M Bool :=
  match x, y with
  | .num a, .num b => pure (if orEq then a.le b else a.lt b)
  | .str a, .str b => pure (if orEq then a == b || strLt a b else strLt a b)
  | _, _ => do
    -- LuaJIT looks for `__lt`/`__le` only on two values of one type
    if let (.tbl _, .tbl _) := (x, y) then noMeta [x, y] ["__lt", "__le"]
    if x.typeName == y.typeName then rtErr s!"attempt to compare two {x.typeName} values"
    else rtErr s!"attempt to compare {x.typeName} with {y.typeName}"

/-- `==`: two distinct tables may have `__eq` -/
def eqv (x y : Val) : M Bool := do
  if let (.tbl a, .tbl b) := (x, y) then
    if a != b then noMeta [x, y] ["__eq"]
  pure (x.rawEq y)

def concatText : Val → Option (List Char)
  | .str s => some s
  | .num n => some n.toText
  | _ => none

def binop (tgt : Target) (op : BinOp) (x y : Val) : M Val :=
  match op with
  | .eq => do pure (.bool (← eqv x y))
  | .ne => do pure (.bool !(← eqv x y))
  | .lt => .bool <$> less x y false
  | .le => .bool <$> less x y true
  | .gt => .bool <$> less y x false
  | .ge => .bool <$> less y x true
  | .concat =>
    match concatText x, concatText y with
    | some a, some b => pure (.str (a ++ b))
    | _, _ => do
      noMeta [x, y] ["__concat"]
      if (concatText x).isNone then opErr "concatenate" (some 0) x else opErr "concatenate" (some 1) y
  | op => arith tgt op x y

def unop (op : UnOp) (x : Val) : M Val :=
  match op with
  | .not => pure (.bool !x.truthy)
  | .neg => match x.toNum with
    | some a => pure (.num a.neg)
    | none => do
      noMeta [x] ["__unm"]
      opErr "perform arithmetic on" (some 0) x
  -- a table's `__len` is not looked at: LuaJIT 2.1 without LUAJIT_ENABLE_LUA52COMPAT
  | .len => match x with
    | .str s => pure (.num (.int s.length))
    | .tbl a => do pure (.num (.int (← getTbl a).len))
    | _ => opErr "get length of" (some 0) x

-- ---------- arguments of builtins ----------

/-- an argument's type in lj_err_argtype: "no value" past the last -/
def argType (i : Nat) (args : List Val) : String :=
  if i < args.length then (args.getD i .nil).typeName else "no value"

/-- lj_lib_checkany -/
def anyArg (i : Nat) (args : List Val) : M Unit :=
  if i < args.length then pure () else argErr (i + 1) "value expected"

def badType {α} (what : String) (i : Nat) (args : List Val) : M α :=
  argErr (i + 1) s!"{what} expected, got {argType i args}"

def argStr (_fname : String) (i : Nat) (args : List Val) : M (List Char) :=
  match args.getD i .nil with
  | .str s => pure s
  | .num n => pure n.toText
  | _ => badType "string" i args

def argNum (_fname : String) (i : Nat) (args : List Val) : M Num :=
  match (args.getD i .nil).toNum with
  | some n => pure n
  | none => badType "number" i args

/-- the argument through a C cast to a `bits`-bit integer; a double outside that range (inf, NaN) stops the run:
the cast is undefined in C and LuaJIT leaves it to the CPU (x86-64 gives the least integer) -/
def argIntN (bits : Nat) (fname : String) (i : Nat) (args : List Val) : M Int := do
  let v ← argNum fname i args
  let k := v.trunc
  if let .flt f := v then
    if !(f.isFinite && -2 ^ (bits - 1) ≤ k && k < 2 ^ (bits - 1)) then
      throw (.eff s!"{fname}: {bits}-bit cast out of range" [])
  pure k

/-- lj_lib_checkint -/
def argInt (fname : String) (i : Nat) (args : List Val) : M Int := argIntN 32 fname i args

def optInt (fname : String) (i : Nat) (args : List Val) (d : Int) : M Int :=
  match args.getD i .nil with
  | .nil => pure d
  | _ => argInt fname i args

/-- a function (CHECK_func); an effect handle passes, the oracle answers its calls -/
def argFn (_fname : String) (i : Nat) (args : List Val) : M Val :=
  match args.getD i .nil with
  | f@(.fn _) | f@(.prim ..) | f@(.eff _) => pure f
  | _ => badType "function" i args

def argTbl (_fname : String) (i : Nat) (args : List Val) : M Nat :=
  match args.getD i .nil with
  | .tbl a => pure a
  | _ => badType "table" i args

/-- a negative position counts from the end -/
def posrelat (pos : Int) (len : Nat) : Int := if pos ≥ 0 then pos else len + pos + 1

def strs (l : List Char) : Val := .str l
def nums (i : Int) : Val := .num (Num.ofInt i)

-- ---------- string.format ----------

def pad (left zero : Bool) (w : Nat) (sign body : List Char) : List Char :=
  let n := sign.length + body.length
  if n ≥ w then sign ++ body
  else if left then sign ++ body ++ List.replicate (w - n) ' '
  else if zero then sign ++ List.replicate (w - n) '0' ++ body
  else List.replicate (w - n) ' ' ++ sign ++ body

/-- LuaJIT's %q -/
def quoteStr (s : List Char) : List Char :=
  let rec go : List Char → List Char
    | [] => []
    | c :: r =>
      if c == '"' || c == '\\' || c == '\n' then '\\' :: c :: go r
      else if c.toNat < 32 || c.toNat == 127 then
        let d := c.toNat
        let nextDigit := match r with | x :: _ => Num.isDigit x | [] => false
        let ds := if d ≥ 100 || nextDigit then Num.padLeft '0' 3 (Num.digits d) else Num.digits d
        '\\' :: ds ++ go r
      else c :: go r
  '"' :: go s ++ ['"']

def hexDigits (n : Nat) (upper : Bool) : List Char :=
  (Nat.toDigits 16 n).map fun c => if upper then Pat.toLower c |> fun c => if 'a' ≤ c && c ≤ 'f' then Char.ofNat (c.toNat - 32) else c else c

/-- string.format: `args` its arguments, the format the first (lj_strfmt_parse, lj_strfmt_putarg) -/
def format (fmt : List Char) (args : List Val) : M (List Char) := do
  let rec go (f : List Char) (i : Nat) (fuel : Nat) : M (List Char) := do
    match fuel with
    | 0 => pure []
    | fuel + 1 =>
    match f with
    | [] => pure []
    | '%' :: '%' :: r => pure ('%' :: (← go r i fuel))
    | '%' :: r =>
      let flags := r.takeWhile fun c => "-+ #0".toList.contains c
      let r := r.drop flags.length
      let wd := (r.takeWhile Num.isDigit).take 2
      let r := r.drop wd.length
      let (pr, r) := match r with
        | '.' :: r => let p := (r.takeWhile Num.isDigit).take 2; (some p, r.drop p.length)
        | r => (none, r)
      let spec := '%' :: flags ++ wd ++ (match pr with | some p => '.' :: p | none => [])
      let bad (c : List Char) : M (List Char) :=
        callerErr s!"invalid option '{String.ofList (spec ++ c.filter (·.toNat ≥ 32))}' to 'format'"
      let toN (l : List Char) := l.foldl (fun a c => 10 * a + (c.toNat - '0'.toNat)) 0
      let w := toN wd
      let left := flags.contains '-'
      let zero := flags.contains '0'
      let plus := flags.contains '+'
      let space := flags.contains ' '
      let alt := flags.contains '#'
      match r with
      | [] => bad []
      | c :: r =>
        if !"AEFGXacdefgiopqsux".toList.contains c then bad [c] else
        if "Aaoup".toList.contains c then throw (.eff s!"string.format %{c}" []) else
        if i ≥ args.length then argErr (i + 1) "value expected" else
        let arg := args.getD i .nil
        let fn := "format"
        let piece ← match c with
          | 'd' | 'i' => do
            let v ← argIntN 64 fn i args
            let body := Num.digits v.natAbs
            -- precision: the fewest digits; none at all for 0 at precision 0
            let body := match pr with | some p => if toN p == 0 && v == 0 then [] else Num.padLeft '0' (toN p) body | none => body
            let sign := if v < 0 then ['-'] else if plus then ['+'] else if space then [' '] else []
            pure (pad left (zero && pr.isNone) w sign body)
          | 'x' | 'X' => do
            let v ← argIntN 64 fn i args
            let u : Nat := if v < 0 then (2 ^ 64 - v.natAbs) else v.natAbs
            let body := hexDigits u (c == 'X')
            let body := match pr with | some p => if toN p == 0 && u == 0 then [] else Num.padLeft '0' (toN p) body | none => body
            let body := if alt && u != 0 then (if c == 'X' then "0X" else "0x").toList ++ body else body
            pure (pad left (zero && pr.isNone) w [] body)
          | 'c' => do
            let v ← argInt fn i args
            pure (pad left false w [] [Char.ofNat (v.toNat % 256)])
          | 'e' | 'E' | 'f' | 'F' | 'g' | 'G' => do
            let v ← argNum fn i args
            let fl := v.toFloat
            let upper := c == 'E' || c == 'G' || c == 'F'
            let body := Num.convMag fl c ((pr.map toN).getD 6) alt
            let body := if !fl.isFinite && upper then body.map fun d => Char.ofNat (d.toNat - 32) else body
            -- NaN takes no sign, only the space flag (lj_strfmt_num.c)
            if (c == 'f' || c == 'F') && fl != 0 && fl.abs < 1e-150 then
              -- LuaJIT's %f of a tiny number overruns its 64-limb buffer and prints garbage: not modelled
              throw (.eff "lj_strfmt %f below 1e-150" [])
            let sign := if fl.isNaN then (if space then [' '] else []) else if Num.negative fl then ['-'] else if plus then ['+'] else if space then [' '] else []
            pure (pad left (zero && fl.isFinite) w sign body)
          | 'q' => do noMeta [arg] ["__tostring"]; pure (quoteStr arg.text)
          | _ => do
            noMeta [arg] ["__tostring"]
            let s := match pr with | some p => arg.text.take (toN p) | none => arg.text
            pure (pad left false w [] s)
        pure (piece ++ (← go r (i + 1) fuel))
    | c :: r => pure (c :: (← go r i fuel))
  go fmt 1 (fmt.length + 1)

-- ---------- builtins without callbacks ----------

def capVals (cs : List Pat.CapVal) : List Val :=
  cs.map fun | .str s => .str s | .pos n => .num (.int n)

/-- string.find (find) and string.match -/
def strFind (find : Bool) (args : List Val) : M (List Val) := do
  let fname := if find then "find" else "match"
  let s ← argStr fname 0 args
  let p ← argStr fname 1 args
  let init := posrelat (← optInt fname 2 args 1) s.length
  let init : Nat := if init < 1 then 0 else if init > s.length + 1 then s.length else (init - 1).toNat
  if init > s.length then return [.nil] else
  if find && ((args.getD 3 .nil).truthy || !Pat.hasSpecials p) then
    match Pat.findPlain s p init with
    | some i => return [nums (i + 1), nums (i + p.length)]
    | none => return [.nil]
  match Pat.find s p init with
  | .error e => callerErr e
  | .ok none => return [.nil]
  | .ok (some (st, e, caps)) =>
    let ms : Pat.MS := ⟨s.toArray, (if p.head? == some '^' then p.tail else p).toArray⟩
    match Pat.captures ms caps st e (!find) with
    | .error e => callerErr e
    | .ok cs => return (if find then [nums (st + 1), nums e] else []) ++ capVals cs

/-- one step of a gmatch iterator: the bound subject, pattern and a cell with the position -/
def gmatchStep (s p : List Char) (cell : Nat) : M (List Val) := do
  let pos ← match ← readCell cell with
    | .num (.int i) => pure i.toNat
    | _ => pure 0
  let ms : Pat.MS := ⟨s.toArray, p.toArray⟩
  let fuel := Pat.fuelFor s.length p.length
  let rec go (src : Nat) (k : Nat) : M (List Val) := do
    match k with
    | 0 => pure []
    | k + 1 =>
      if src > s.length then pure [] else
      match Pat.doMatch ms fuel src 0 #[] with
      | .error e => callerErr e
      | .ok (some (e, caps)) =>
        writeCell cell (.num (.int (if e == src then e + 1 else e)))
        match Pat.captures ms caps src e true with
        | .error e => callerErr e
        | .ok cs => pure (capVals cs)
      | .ok none => go (src + 1) k
  go pos (s.length + 2)

def mathFn (name : String) (args : List Val) : M (List Val) := do
  match name with
  | "floor" => return [.num (← argNum name 0 args).floor]
  | "ceil" => return [.num (← argNum name 0 args).ceil]
  | "abs" => match ← argNum name 0 args with
    | .int i => return [nums i.natAbs]
    | .flt f => return [.num (.flt f.abs)]
  | "sqrt" => return [.num (.flt (← argNum name 0 args).toFloat.sqrt)]
  | "max" | "min" => do
    -- LuaJIT, on arm64 and x86-64 alike: the running result is replaced unless it is strictly better (so NaN and -0
    -- fall where the comparison leaves them); integers stay integers only if all are
    let x ← argNum name 0 args
    let mut best := x
    let mut allInt := match x with | .int _ => true | _ => false
    for i in [1:args.length] do
      let y ← argNum name i args
      if let .flt _ := y then allInt := false
      if !(if name == "max" then y.lt best else best.lt y) then best := y
    return [.num (if allInt then best else .flt best.toFloat)]
  -- libm's, as LuaJIT calls them (the host's, like `^`: DESIGN.md, Trust); every result a double
  | "exp" | "log10" | "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "sinh" | "cosh" | "tanh" => do
    let x := (← argNum name 0 args).toFloat
    return [.num (.flt (match name with
      | "exp" => x.exp | "log10" => x.log10 | "sin" => x.sin | "cos" => x.cos | "tan" => x.tan | "asin" => x.asin
      | "acos" => x.acos | "atan" => x.atan | "sinh" => x.sinh | "cosh" => x.cosh | _ => x.tanh))]
  | "log" => do
    let x := (← argNum name 0 args).toFloat
    -- a base: log2(x) * (1 / log2(base)), as lib_math.c writes it
    if args.length ≥ 2 then return [.num (.flt (x.log2 * (1 / (← argNum name 1 args).toFloat.log2)))]
    return [.num (.flt x.log)]
  | "pow" | "atan2" | "fmod" => do
    let x := (← argNum name 0 args).toFloat
    let y := (← argNum name 1 args).toFloat
    return [.num (.flt (match name with | "pow" => x.pow y | "atan2" => x.atan2 y | _ => Num.fmodC x y))]
  | "modf" => do let (i, r) := Num.modfC (← argNum name 0 args).toFloat; return [.num (.flt i), .num (.flt r)]
  | "frexp" => do let (m, e) := Num.frexpC (← argNum name 0 args).toFloat; return [.num (.flt m), nums e]
  | "ldexp" => do
    let x := (← argNum name 0 args).toFloat
    return [.num (.flt (x.scaleB (← argInt name 1 args)))]
  -- x * 57.29577951308232 and x * 0.017453292519943295 in lib_math.c's Lua
  | "deg" => return [.num (.flt ((← argNum name 0 args).toFloat * Float.ofBits 0x404CA5DC1A63C1F8))]
  | "rad" => return [.num (.flt ((← argNum name 0 args).toFloat * Float.ofBits 0x3F91DF46A2529D39))]
  | _ => die s!"math.{name}: not in the subset"

def strFn (name : String) (args : List Val) : M (List Val) := do
  match name with
  | "len" => return [nums (← argStr name 0 args).length]
  | "sub" => do
    let s ← argStr name 0 args
    let l := s.length
    let i := posrelat (← optInt name 1 args 1) l
    let j := posrelat (← optInt name 2 args (-1)) l
    let i := if i < 1 then 1 else i
    let j : Int := if j > (l : Int) then l else j
    return [.str (if i ≤ j then (s.drop (i - 1).toNat).take (j - i + 1).toNat else [])]
  | "upper" => return [.str ((← argStr name 0 args).map fun c => if Pat.isLower c then Char.ofNat (c.toNat - 32) else c)]
  | "lower" => return [.str ((← argStr name 0 args).map Pat.toLower)]
  | "reverse" => return [.str (← argStr name 0 args).reverse]
  | "rep" => do
    let s ← argStr name 0 args
    let n ← argInt name 1 args
    let sep ← match args.getD 2 .nil with | .nil => pure [] | _ => argStr name 2 args
    if n ≤ 0 then return [.str []]
    return [.str (List.intercalate sep (List.replicate n.toNat s))]
  | "byte" => do
    let s ← argStr name 0 args
    let l := s.length
    let i := posrelat (← optInt name 1 args 1) l
    let j := posrelat (← optInt name 2 args i) l
    let i := if i < 1 then 1 else i
    let j : Int := if j > (l : Int) then l else j
    if i > j then return []
    return ((s.drop (i - 1).toNat).take (j - i + 1).toNat).map fun c => nums c.toNat
  | "char" => do
    let mut r := []
    for i in [0:args.length] do
      let c ← argInt name i args
      if c < 0 || c > 255 then argErr (i + 1) "invalid value"
      r := r ++ [Char.ofNat c.toNat]
    return [.str r]
  | "format" => return [.str (← format (← argStr name 0 args) args)]
  | "find" => strFind true args
  | "match" => strFind false args
  | "gmatch" => do
    let s ← argStr name 0 args
    let p ← argStr name 1 args
    let c ← alloc (.cell (.num (.int 0)))
    return [.prim "gmatch_it" [.str s, .str p, .num (.int c)]]
  | _ => die s!"string.{name}: not in the subset"

/-- CHECK_int in lib_table.c's Lua: dual-number makes it an integer (lj_lib_checkint), single-number keeps the number -/
def libInt (tgt : Target) (fname : String) (i : Nat) (args : List Val) : M Num :=
  match tgt with
  | .dual => do pure (.int (← argInt fname i args))
  | .single => argNum fname i args

/-- the key of a raw access in lib_table.c's Lua (TGETR, TSETR): the number truncated to 32 bits -/
def libKey (fname : String) (k : Num) : M Val := do pure (nums (← argIntN 32 fname 0 [.num k]))

/-- `for i=a,b` (`down`: `for i=a,b,-1`): a, a + 1, ... to b; past 2^32 numbers the run stops, its keys leave the
32 bits -/
def libRange (a b : Num) (down : Bool := false) : M (List Num) := do
  let span := if down then a.sub b else b.sub a
  if span.lt (.int 0) then return []
  let c := span.floor.trunc
  if !span.toFloat.isFinite || c ≥ 2 ^ 32 then throw (.eff "table: a loop past 2^32" [])
  return (List.range (c.toNat + 1)).map fun (k : Nat) => if down then a.sub (.int k) else a.add (.int k)

def tableFn (tgt : Target) (name : String) (args : List Val) : M (List Val) := do
  match name with
  | "insert" => do
    let t ← argTbl name 0 args
    let n := (← getTbl t).len
    match args.length with
    | 2 => rawset t (nums (n + 1)) (args.getD 1 .nil); return []
    | 3 => do
      let pos ← argInt name 1 args
      let mut i : Int := n + 1
      for _ in [0:(n + 1)] do
        if i > pos then
          rawset t (nums i) (← rawget t (nums (i - 1)))
          i := i - 1
      rawset t (nums i) (args.getD 2 .nil)
      return []
    | _ => callerErr "wrong number of arguments to 'insert'"
  | "remove" => do
    let t ← argTbl name 0 args
    let n := (← getTbl t).len
    match args.getD 1 .nil with
    | .nil =>
      if n == 0 then return []
      let old ← rawget t (nums n)
      rawset t (nums n) .nil
      return [old]
    | _ => do
      let pos ← libInt tgt name 1 args
      if (Num.int 1).le pos && pos.le (.int n) then
        let old ← rawget t (← libKey name pos)
        for k in ← libRange (pos.add (.int 1)) (.int n) do
          rawset t (← libKey name (k.sub (.int 1))) (← rawget t (← libKey name k))
        rawset t (nums n) .nil
        return [old]
      return []
  | "concat" => do
    let t ← argTbl name 0 args
    let sep ← match args.getD 1 .nil with | .nil => pure [] | _ => argStr name 1 args
    let i ← optInt name 2 args 1
    let j ← optInt name 3 args (← getTbl t).len
    let mut r : List (List Char) := []
    let mut k := i
    for _ in [0:(j - i + 1).toNat] do
      match concatText (← rawget t (nums k)) with
      | some s => r := r ++ [s]
      | none => callerErr s!"invalid value ({(← rawget t (nums k)).typeName}) at index {k} in table for 'concat'"
      k := k + 1
    return [.str (List.intercalate sep r)]
  | "maxn" => do
    let t ← getTbl (← argTbl name 0 args)
    let m := t.kv.foldl (fun m (k, v) => match k, v with
      | _, .nil => m
      | .num x, _ => if m.lt x then x else m
      | _, _ => m) (Num.int 0)
    return [.num m]
  | "getn" => do return [nums (← getTbl (← argTbl name 0 args)).len]
  | "move" => do
    -- lib_table.c's Lua, its tables raw (CHECK_tab)
    let a1 ← argTbl name 0 args
    let f ← libInt tgt name 1 args
    let e ← libInt tgt name 2 args
    let t ← libInt tgt name 3 args
    let a2 ← match args.getD 4 .nil with | .nil => pure a1 | _ => argTbl name 4 args
    if f.le e then
      let d := t.sub f
      for i in ← (if e.lt t || t.le f || a2 != a1 then libRange f e else libRange e f true) do
        rawset a2 (← libKey name (i.add d)) (← rawget a1 (← libKey name i))
    return [.tbl a2]
  -- require "table.new" and "table.clear"
  | "new" => do
    let a ← argInt name 0 args
    let h ← argInt name 1 args
    -- shortcut: a size above 65536 stops the run (LuaJIT's memory may refuse it), model "table overflow" if one is needed
    if a > 65536 || h > 65536 then throw (.eff "table.new of a large size" [])
    return [.tbl (← alloc (.tbl {}))]
  | "clear" => do let t ← argTbl name 0 args; putTbl t { (← getTbl t) with kv := [] }; return []
  | _ => die s!"table.{name}: not in the subset"

def unpackFn (args : List Val) : M (List Val) := do
  let t ← argTbl "unpack" 0 args
  let i ← optInt "unpack" 1 args 1
  let j ← optInt "unpack" 2 args (← getTbl t).len
  -- lua_checkstack: the results and the arguments within LUAI_MAXCSTACK
  if i ≤ j && j - i + 1 + args.length > 8000 then callerErr "too many results to unpack"
  (List.range (j - i + 1).toNat).mapM fun (k : Nat) => rawget t (nums (i + k))

def basicFn (tgt : Target) (name : String) (bound args : List Val) : M (List Val) := do
  match name with
  | "type" => do anyArg 0 args; return [lstr (args.headD .nil).typeName]
  | "tostring" => do anyArg 0 args; noMeta [args.headD .nil] ["__tostring"]; return [.str (args.headD .nil).text]
  | "tonumber" => do
    let b ← optInt "tonumber" 1 args 10
    if b == 10 then
      anyArg 0 args
      match args.headD .nil with
      | .num n => return [.num n]
      | .str s => return [(Num.parse s).elim .nil .num]
      | _ => return [.nil]
    else
      let s ← argStr "tonumber" 0 args
      if b < 2 || b > 36 then argErr 2 "base out of range"
      if Num.binPrefix s b.toNat then throw (.eff "tonumber: 0b in base 2" [])
      return [(Num.parseBase tgt s b.toNat).elim .nil .num]
  | "ipairs" => do anyArg 0 args; let t ← argTbl name 0 args; return [.prim "ipairs_it" [], .tbl t, .num (.int 0)]
  | "ipairs_it" => do
    let t ← argTbl name 0 args
    let i ← argInt name 1 args
    let v ← rawget t (nums (i + 1))
    return if v.isNil then [.nil] else [nums (i + 1), v]
  | "pairs" => do anyArg 0 args; let t ← argTbl name 0 args; return [.prim "next" [], .tbl t, .nil]
  | "next" => do
    let t ← getTbl (← argTbl name 0 args)
    match t.next (args.getD 1 .nil) with
    | none => rtErr "invalid key to 'next'"
    | some none => return [.nil]
    | some (some (k, v)) => return [k, v]
  | "select" => do
    match args.headD .nil with
    | .str ('#' :: _) => return [nums (args.length - 1)]
    | _ => do
      let n ← argInt "select" 0 args
      let rest := args.tail
      if n < 0 then
        if -n > rest.length then argErr 1 "index out of range"
        return rest.drop (rest.length - n.natAbs)
      if n == 0 then argErr 1 "index out of range"
      return rest.drop (n.toNat - 1)
  | "unpack" => unpackFn args
  | "rawget" => do let t ← argTbl name 0 args; anyArg 1 args; return [← rawget t (args.getD 1 .nil)]
  | "rawset" => do
    let t ← argTbl name 0 args; anyArg 1 args; anyArg 2 args
    rawset t (args.getD 1 .nil) (args.getD 2 .nil); return [.tbl t]
  | "rawequal" => do anyArg 0 args; anyArg 1 args; return [.bool ((args.getD 0 .nil).rawEq (args.getD 1 .nil))]
  | "setmetatable" => do
    let t ← argTbl name 0 args
    let m ← match args.getD 1 .nil with
      | .nil => pure none
      | .tbl m => do
        -- weak tables lose entries when the collector runs, which the semantics does not model
        if !((← getTbl m).get (lstr "__mode")).isNil then throw (.eff "metamethod __mode" [])
        pure (some m)
      | _ => argErr 2 "nil or table expected"
    noMeta [.tbl t] ["__metatable"]
    -- globals are read and written raw (`getVar`), so _G takes no metatable
    if t == G then throw (.eff "setmetatable(_G)" [])
    putTbl t { (← getTbl t) with mt := m }
    return [.tbl t]
  | "getmetatable" => match args.headD .nil with
    | .tbl t => do noMeta [.tbl t] ["__metatable"]; return [((← getTbl t).mt.map Val.tbl).getD .nil]
    | _ => return [.nil]
  | "error" => do
    -- a string or number gets the place of the function `level` calls out (1: error's caller)
    let level ← optInt "error" 1 args 1
    match args.headD .nil with
    | v@(.str _) | v@(.num _) => if level > 0 then throw (.rt level.toNat (.val v)) else throw (.val v)
    | v => throw (.val v)
  | "assert" => do
    anyArg 0 args
    if (args.headD .nil).truthy then return args
    else match args with
      | [_] => callerErr "assertion failed!"
      | _ :: m@(.str _) :: _ | _ :: m@(.num _) :: _ => throw (.rt 1 (.val (.str m.text)))
      | _ => throw (.val (args.getLast?.getD .nil))
  | "gmatch_it" => match bound with
    | [.str s, .str p, .num (.int c)] => gmatchStep s p c.toNat
    | _ => die "bad gmatch iterator"
  | _ =>
    match name.splitOn "." with
    | ["string", f] => strFn f args
    | ["table", f] => tableFn tgt f args
    | ["math", f] => mathFn f args
    | _ => die s!"{name}: not in the subset"

-- ---------- evaluation ----------

/-- the label l ends the block: the continue idiom, the one goto the subset has -/
def labelAtEnd (b : Block) (l : String) : Bool :=
  match b.reverse.dropWhile (fun s => match s with | .label x => x != l | _ => false) with
  | .label x :: rest => x == l && (b.length - rest.length - 1 == b.length - 1 ∨
      ((b.drop (rest.length + 1)).all fun s => match s with | .label _ => true | _ => false))
  | _ => false

def hasLabel (b : Block) (l : String) : Bool := b.any fun s => match s with | .label x => x == l | _ => false

/-- pcall's catch: a runtime error reported in the builtin catching it has no place; one reported further out has
the place of a call this one cannot see, so the run stops -/
def catchVal {α} (x : M α) (ok : α → M β) (bad : Val → M β) : M β := fun h =>
  match x h with
  | .ok a h => ok a h
  | .error (.val v) h => bad v h
  | .error (.rt 0 m) h => bad m.bare h
  | .error (.rt (k + 1) _) h => .error (.eff s!"error level {k + 1} past a builtin" []) h
  | .error e h => .error e h

/-- a replacement string: %0 the match, %1-%9 a capture, %x the character x -/
def substRepl (r whole : List Char) (cap : Nat → M Val) : M (List Char) :=
  match r with
  | [] => pure []
  | '%' :: d :: rest => do
    if Pat.isDigit d then
      let v ← if d == '0' then pure (.str whole) else cap (d.toNat - '1'.toNat)
      pure (v.text ++ (← substRepl rest whole cap))
    else pure (d :: (← substRepl rest whole cap))
  | c :: rest => do pure (c :: (← substRepl rest whole cap))

set_option maxRecDepth 100000

section
variable (srcs : String → Option Block) (oracle : String → List Val → Option (List Val)) (tgt : Target)

mutual
def eval (n : Nat) (cx : Ctx) (e : Exp) : M Val :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match e with
  | .nil => pure .nil
  | .tru => pure (.bool true)
  | .fls => pure (.bool false)
  | .num x => pure (.num x)
  | .str s => pure (.str s)
  | .vararg => pure (cx.va.headD .nil)
  | .site s e => atSite s (eval n cx e)
  | .func ps va b => do pure (.fn (← alloc (.clo ⟨ps, va, b, cx.env⟩)))
  | .var x => getVar cx x
  | .index t k => do
    let tv ← eval n cx t
    let kv ← eval n cx k
    index n tv kv
  | .call .. | .method .. => do pure ((← evalMulti n cx e).headD .nil)
  | .paren e => eval n cx e
  | .and a b => do
    let x ← eval n cx a
    if x.truthy then eval n cx b else pure x
  | .or a b => do
    let x ← eval n cx a
    if x.truthy then pure x else eval n cx b
  | .un op a => do unop op (← eval n cx a)
  | .bin op a b => do
    let x ← eval n cx a
    let y ← eval n cx b
    binop tgt op x y
  | .table fs => tableCons n cx fs

/-- an expression's values: all of a call's, all of `...`, else one -/
def evalMulti (n : Nat) (cx : Ctx) (e : Exp) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match e with
  | .call f args => do
    let fv ← eval n cx f
    let as ← evalList n cx args
    call n fv as
  | .method o m args => do
    let ov ← eval n cx o
    let fv ← index n ov (.str m.toList)
    let as ← evalList n cx args
    call n fv (ov :: as)
  | .vararg => pure cx.va
  | .site s e => atSite s (evalMulti n cx e)
  | e => do pure [← eval n cx e]

/-- an expression list: one value each, all of the last's -/
def evalList (n : Nat) (cx : Ctx) (es : List Exp) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match es with
  | [] => pure []
  | [e] => evalMulti n cx e
  | e :: es => do
    let v ← eval n cx e
    let vs ← evalList n cx es
    pure (v :: vs)

def tableCons (n : Nat) (cx : Ctx) (fs : List Field) : M Val :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    let t ← alloc (.tbl {})
    -- keyed fields in order; the positional ones last, as SETLIST does
    let pos ← fields n cx t fs
    let mut i : Int := 1
    for v in pos do
      rawset t (nums i) v
      i := i + 1
    pure (.tbl t)

def fields (n : Nat) (cx : Ctx) (t : Nat) (fs : List Field) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match fs with
  | [] => pure []
  | [.pos e] => evalMulti n cx e
  | .pos e :: fs => do
    let v ← eval n cx e
    let vs ← fields n cx t fs
    pure (v :: vs)
  | .named k e :: fs => do
    let v ← eval n cx e
    rawset t (lstr k) v
    fields n cx t fs
  | .keyed k e :: fs => do
    let kv ← eval n cx k
    let v ← eval n cx e
    rawset t kv v
    fields n cx t fs

/-- o[k], with __index -/
def index (n : Nat) (o k : Val) : M Val :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match o with
  | .tbl a => do
    let t ← getTbl a
    let v := t.get k
    if !v.isNil then pure v else
    match t.mt with
    | none => pure .nil
    | some m => do
      match (← getTbl m).get (lstr "__index") with
      | .nil => pure .nil
      | h@(.fn _) | h@(.prim ..) => do pure ((← call n h [o, k]).headD .nil)
      | h => index n h k
  | .str _ => rawget STRING k
  | .eff name => match k with
    | .str s => pure (.eff (name ++ "." ++ String.ofList s))
    | _ => pure (.eff name)
  | _ => opErr "index" (some 0) o

def call (n : Nat) (f : Val) (args : List Val) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match f with
  | .fn a => do
    match ← getObj a with
    | .clo c => frame do
      let cx ← bindLocals ⟨c.env, []⟩ c.params args
      let cx := { cx with va := if c.va then args.drop c.params.length else [] }
      match ← execBlock n cx c.body with
      | .ret vs => pure vs
      | .norm => pure []
      | .brk => die "break outside a loop"
      | .goto l => die s!"no visible label '{l}' for goto"
    | _ => die "not a function"
  | .prim name bound => frame (callPrim n name bound args)
  | .eff name => match oracle name args with
    | some vs => pure vs
    | none => throw (.eff name args)
  | .tbl _ => do
    -- `__call`, which must be a function: LuaJIT follows no chain of them (lj_meta_call)
    match ← metaOf f "__call" with
    | h@(.fn _) | h@(.prim ..) => call n h (f :: args)
    | _ => opErr "call" none f
  | v => opErr "call" none v

def execBlock (n : Nat) (cx : Ctx) (b : Block) : M Flow :=
  match n with
  | 0 => throw .fuel
  | n + 1 => execSeq n cx b b none

/-- the statements `rest` of block `full`; `fin` is a repeat's condition, in the body's scope: true stops (`brk`) -/
def execSeq (n : Nat) (cx : Ctx) (full rest : Block) (fin : Option Exp) : M Flow :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match rest with
  | [] => match fin with
    | none => pure .norm
    | some c => do pure (if (← eval n cx c).truthy then .brk else .norm)
  | .loc names es :: rest => do
    let vs ← evalList n cx es
    let cx ← bindLocals cx names vs
    execSeq n cx full rest fin
  | .locfn name ps va b :: rest => do
    let c ← alloc (.cell .nil)
    let cx := { cx with env := (name, c) :: cx.env }
    let f ← alloc (.clo ⟨ps, va, b, cx.env⟩)
    writeCell c (.fn f)
    execSeq n cx full rest fin
  | s :: rest => do
    match ← execStat n cx s with
    | .norm => execSeq n cx full rest fin
    | .goto l =>
      if labelAtEnd full l then pure .norm
      else if hasLabel full l then die "goto: only to a label that ends its block"
      else pure (.goto l)
    | fl => pure fl

def execStat (n : Nat) (cx : Ctx) (s : Stat) : M Flow :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match s with
  | .assign targets es => do
    let places ← places n cx targets
    let vs ← evalList n cx es
    assign n cx places.reverse (vs ++ List.replicate places.length Val.nil |>.take places.length).reverse
    pure .norm
  | .call e => do let _ ← evalMulti n cx e; pure .norm
  | .block b => execBlock n cx b
  | .while c b => whileLoop n cx c b
  | .rpt b c => rptLoop n cx b c
  | .ite c t e => do
    if (← eval n cx c).truthy then execBlock n cx t else execBlock n cx e
  | .fornum v a b st body => do
    let num (x : Val) (what : String) : M Num := match x.toNum with
      | some x => pure x
      | none => rtErr s!"'for' {what} must be a number"
    let a ← num (← eval n cx a) "initial value"
    let b ← num (← eval n cx b) "limit"
    let st ← match st with
      | some st => do num (← eval n cx st) "step"
      | none => pure (.int 1)
    -- an integer loop if all three are integers, else all doubles
    match a, b, st with
    | .int _, .int _, .int _ => numLoop n cx v a b st body
    | _, _, _ => numLoop n cx v (.flt a.toFloat) (.flt b.toFloat) (.flt st.toFloat) body
  | .forin vs es body => do
    let r ← evalList n cx es
    inLoop n cx vs (r.getD 0 .nil) (r.getD 1 .nil) (r.getD 2 .nil) body
  | .ret es => do pure (.ret (← evalList n cx es))
  | .brk => pure .brk
  | .goto l => pure (.goto l)
  | .site s st => atSite s (execStat n cx st)
  | .label _ | .loc .. | .locfn .. => pure .norm

/-- assignment targets, their table and key evaluated first: `inl` is a name, `inr` a table write and where its
errors are reported -/
def places (n : Nat) (cx : Ctx) (ts : List Exp) : M (List (String ⊕ (Val × Val × Option Site))) :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match ts with
  | [] => pure []
  | .var x :: ts => do pure (.inl x :: (← places n cx ts))
  | .site s (.index t k) :: ts => do
    let tv ← eval n cx t
    let kv ← eval n cx k
    pure (.inr (tv, kv, some s) :: (← places n cx ts))
  | .index t k :: ts => do
    let tv ← eval n cx t
    let kv ← eval n cx k
    pure (.inr (tv, kv, none) :: (← places n cx ts))
  | _ :: _ => die "cannot assign"

/-- the assignments, last first, as Lua 5.1 does them -/
def assign (n : Nat) (cx : Ctx) (ps : List (String ⊕ (Val × Val × Option Site))) (vs : List Val) : M Unit :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match ps with
  | [] => pure ()
  | p :: ps => do
    match p with
    | .inl x => setVar cx x (vs.headD .nil)
    | .inr (o, k, s) => atSite? s (setindex n o k (vs.headD .nil))
    assign n cx ps vs.tail

/-- o[k] = v, with `__newindex` (lj_meta_tset): a key with a value is set raw, else the metamethod, a function called
with (o, k, v) or a value to assign into instead -/
def setindex (n : Nat) (o k v : Val) : M Unit :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match o with
  | .tbl a => do
    if !((← getTbl a).get k).isNil then rawset a k v else
    match ← metaOf o "__newindex" with
    | .nil => rawset a k v
    | h@(.fn _) | h@(.prim ..) => do let _ ← call n h [o, k, v]
    | h => setindex n h k v
  | _ => opErr "index" (some 0) o

def whileLoop (n : Nat) (cx : Ctx) (c : Exp) (b : Block) : M Flow :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if !(← eval n cx c).truthy then return .norm
    match ← execBlock n cx b with
    | .norm => whileLoop n cx c b
    | .brk => pure .norm
    | fl => pure fl

def rptLoop (n : Nat) (cx : Ctx) (b : Block) (c : Exp) : M Flow :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    match ← execSeq n cx b b (some c) with
    | .norm => rptLoop n cx b c
    | .brk => pure .norm
    | fl => pure fl

def numLoop (n : Nat) (cx : Ctx) (v : String) (i lim st : Num) (body : Block) : M Flow :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if !(if (Num.int 0).lt st then i.le lim else lim.le i) then return .norm
    let cx' ← bindLocals cx [v] [.num i]
    match ← execBlock n cx' body with
    | .norm => numLoop n cx v (i.add st) lim st body
    | .brk => pure .norm
    | fl => pure fl

/-- ITERC: its error for a value it cannot call names no operand -/
def iterCall (n : Nat) (f s ctl : Val) : M (List Val) := do
  let callable ← match f with
    | .fn _ | .prim .. | .eff _ => pure true
    | .tbl _ => do pure (match ← metaOf f "__call" with | .fn _ | .prim .. => true | _ => false)
    | _ => pure false
  if callable then call n f [s, ctl] else opErr "call" (some 0) f

def inLoop (n : Nat) (cx : Ctx) (vs : List String) (f s ctl : Val) (body : Block) : M Flow :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    let rs ← iterCall n f s ctl
    let v1 := rs.headD .nil
    if v1.isNil then return .norm
    let cx' ← bindLocals cx vs rs
    match ← execBlock n cx' body with
    | .norm => inLoop n cx vs f s v1 body
    | .brk => pure .norm
    | fl => pure fl

/-- builtins that call back into Lua, then the rest -/
def callPrim (n : Nat) (name : String) (bound args : List Val) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match name with
  | "pcall" => do
    anyArg 0 args
    catchVal (call n (args.headD .nil) args.tail) (fun vs => pure (.bool true :: vs)) (fun e => pure [.bool false, e])
  | "xpcall" => do
    anyArg 0 args
    match args.getD 1 .nil with
    | .fn _ | .prim .. => pure ()
    | _ => badType "function" 1 args
    catchVal (call n (args.headD .nil) (args.drop 2)) (fun vs => pure (.bool true :: vs))
      (fun e => do pure [.bool false, (← call n (args.getD 1 .nil) [e]).headD .nil])
  | "require" => do
    let m ← argStr "require" 0 args
    let v ← rawget LOADED (.str m)
    if !v.isNil then return [v]
    -- package.preload's two: each also becomes a field of `table`
    if m == "table.new".toList || m == "table.clear".toList then
      let f := Val.prim (String.ofList m) []
      rawset TABLE (.str (m.drop 6)) f
      rawset LOADED (.str m) f
      return [f]
    let v ← match srcs (String.ofList m) with
      | some b => do
        let f ← alloc (.clo ⟨[], true, b, []⟩)
        let rs ← call n (.fn f) [.str m]
        pure (match rs.headD .nil with | .nil => .bool true | v => v)
      | none => pure (.eff (String.ofList m))
    rawset LOADED (.str m) v
    return [v]
  | "string.gsub" => gsub n args
  | "table.foreachi" => do
    let t ← argTbl "foreachi" 0 args
    let f ← argFn "foreachi" 1 args
    foreachi n t f 1 (← getTbl t).len
  | "table.foreach" => do
    let t ← argTbl "foreach" 0 args
    foreachK n t (← argFn "foreach" 1 args) .nil
  | "table.sort" => do
    let t ← argTbl "sort" 0 args
    let cmp := args.getD 1 .nil
    match cmp with
    | .nil | .fn _ | .prim .. => pure ()
    | _ => badType "function" 1 args
    let len := (← getTbl t).len
    sortAux n t cmp 1 len
    pure []
  | _ => basicFn tgt name bound args

/-- table.foreachi from i: f(i, t[i]) until a result is not nil -/
def foreachi (n : Nat) (t : Nat) (f : Val) (i len : Int) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if i > len then return []
    let r := (← call n f [nums i, ← rawget t (nums i)]).headD .nil
    if !r.isNil then return [r]
    foreachi n t f (i + 1) len

/-- table.foreach after key k: f(k, v), as `next` visits them, until a result is not nil -/
def foreachK (n : Nat) (t : Nat) (f k : Val) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    match (← getTbl t).next k with
    | none => rtErr "invalid key to 'next'"
    | some none => return []
    | some (some (k, v)) =>
      let r := (← call n f [k, v]).headD .nil
      if !r.isNil then return [r]
      foreachK n t f k

def lessThan (n : Nat) (cmp a b : Val) : M Bool :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match cmp with
  | .nil => less a b false
  | f => do pure ((← call n f [a, b]).headD .nil).truthy

/-- ltablib.c's auxsort -/
def sortAux (n : Nat) (t : Nat) (cmp : Val) (l u : Int) : M Unit :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if !(l < u) then return
    let get (i : Int) := rawget t (nums i)
    let put (i : Int) (v : Val) := rawset t (nums i) v
    let al ← get l
    let au ← get u
    if ← lessThan n cmp au al then put l au; put u al
    if u - l == 1 then return
    let i := (l + u) / 2
    let ai ← get i
    let al ← get l
    if ← lessThan n cmp ai al then put i al; put l ai
    else
      let au ← get u
      if ← lessThan n cmp au ai then put i au; put u ai
    if u - l == 2 then return
    let p ← get i
    let au1 ← get (u - 1)
    put i au1; put (u - 1) p
    let i ← sortPart n t cmp p l u l (u - 1)
    let au1 ← get (u - 1)
    let ai ← get i
    put (u - 1) ai; put i au1
    if i - l < u - i then
      sortAux n t cmp l (i - 1)
      sortAux n t cmp (i + 1) u
    else
      sortAux n t cmp (i + 1) u
      sortAux n t cmp l (i - 1)

/-- the partition loop: the final i -/
def sortPart (n : Nat) (t : Nat) (cmp p : Val) (l u i j : Int) : M Int :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    let i ← sortUp n t cmp p u (i + 1)
    let j ← sortDown n t cmp p l (j - 1)
    if j < i then return i
    let ai ← rawget t (nums i)
    let aj ← rawget t (nums j)
    rawset t (nums i) aj; rawset t (nums j) ai
    sortPart n t cmp p l u i j

/-- while a[i] < P: i++ -/
def sortUp (n : Nat) (t : Nat) (cmp p : Val) (u i : Int) : M Int :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if ← lessThan n cmp (← rawget t (nums i)) p then
      if i ≥ u then callerErr "invalid order function for sorting"
      sortUp n t cmp p u (i + 1)
    else return i

/-- while P < a[j]: j-- -/
def sortDown (n : Nat) (t : Nat) (cmp p : Val) (l j : Int) : M Int :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if ← lessThan n cmp p (← rawget t (nums j)) then
      if j ≤ l then callerErr "invalid order function for sorting"
      sortDown n t cmp p l (j - 1)
    else return j

/-- string.gsub, with a string, table or function replacement -/
def gsub (n : Nat) (args : List Val) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    let s ← argStr "gsub" 0 args
    let p ← argStr "gsub" 1 args
    let repl := args.getD 2 .nil
    match repl with
    | .str _ | .num _ | .tbl _ | .fn _ | .prim .. => pure ()
    | _ => argErr 3 "string/function/table expected"
    let maxS ← optInt "gsub" 3 args (s.length + 1)
    let anchor := p.head? == some '^'
    let ms : Pat.MS := ⟨s.toArray, (if anchor then p.tail else p).toArray⟩
    gsubGo n ms repl anchor maxS 0 0 []

def gsubGo (n : Nat) (ms : Pat.MS) (repl : Val) (anchor : Bool) (maxS : Int) (src cnt : Nat) (acc : List Char) :
    M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    let s := ms.s
    let rest := fun () => pure [Val.str (acc ++ (s.extract src s.size).toList), nums cnt]
    if !((cnt : Int) < maxS) then return ← rest ()
    let r ← match Pat.doMatch ms (Pat.fuelFor s.size ms.p.size) src 0 #[] with
      | .error e => callerErr e
      | .ok r => pure r
    let (acc, cnt) ← match r with
      | some (e, caps) => do pure (acc ++ (← addValue n ms repl caps src e), cnt + 1)
      | none => pure (acc, cnt)
    let step (acc : List Char) (cnt : Nat) : M (List Val) := do
      if src < s.size then
        let acc := acc ++ [s.getD src 'x']
        if anchor then return [Val.str (acc ++ (s.extract (src + 1) s.size).toList), nums cnt]
        gsubGo n ms repl anchor maxS (src + 1) cnt acc
      else return [Val.str acc, nums cnt]
    match r with
    | some (e, _) =>
      if e > src then
        if anchor then return [Val.str (acc ++ (s.extract e s.size).toList), nums cnt]
        gsubGo n ms repl anchor maxS e cnt acc
      else step acc cnt
    | none => step acc cnt

/-- the replacement of one match -/
def addValue (n : Nat) (ms : Pat.MS) (repl : Val) (caps : Array Pat.Cap) (s e : Nat) : M (List Char) :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    let whole := (ms.s.extract s e).toList
    let cap (i : Nat) : M Val := match Pat.getCapture ms caps i s e with
      | .error m => callerErr m
      | .ok (.str x) => pure (.str x)
      | .ok (.pos k) => pure (nums k)
    match repl with
    | .str _ | .num _ =>
      substRepl (match repl with | .str r => r | v => v.text) whole cap
    | _ => do
      let k ← cap 0
      let v ← match repl with
        | .tbl _ => index n repl k
        | f => do
          let ncap := if caps.size == 0 then 1 else caps.size
          let cs ← (List.range ncap).mapM cap
          pure ((← call n f cs).headD .nil)
      match v with
      | .nil | .bool false => pure whole
      | .str x => pure x
      | .num x => pure x.toText
      | v => callerErr s!"invalid replacement value (a {v.typeName})"
end

/-- a chunk run as a function of no arguments -/
def runChunk (n : Nat) (b : Block) (args : List Val := []) : M (List Val) := do
  let f ← alloc (.clo ⟨[], true, b, []⟩)
  call srcs oracle tgt n (.fn f) args
end

-- ---------- the initial heap ----------

def libTable (lib : String) (names : List String) : Tbl :=
  { kv := names.map fun f => (lstr f, .prim (lib ++ "." ++ f) []) }

def basics : List String :=
  ["type", "tostring", "tonumber", "ipairs", "pairs", "next", "select", "unpack", "rawget", "rawset", "rawequal",
   "setmetatable", "getmetatable", "error", "assert", "pcall", "xpcall", "require"]

/-- _G (0), package.loaded (1), string (2), table (3), math (4), package (5) -/
def initHeap : Heap :=
  let g : Tbl := { kv := basics.map (fun f => (lstr f, Val.prim f [])) ++
    [(lstr "string", .tbl 2), (lstr "table", .tbl 3), (lstr "math", .tbl 4), (lstr "package", .tbl 5),
     (lstr "_G", .tbl 0), (lstr "io", .eff "io"), (lstr "os", .eff "os"), (lstr "print", .eff "print"),
     (lstr "debug", .eff "debug")] }
  let str := libTable "string" ["len", "sub", "upper", "lower", "reverse", "rep", "byte", "char", "format", "find",
    "match", "gmatch", "gsub"]
  let tab := libTable "table" ["insert", "remove", "concat", "sort", "maxn", "getn", "move", "foreach", "foreachi"]
  let math := (libTable "math" ["floor", "ceil", "abs", "sqrt", "max", "min", "exp", "log", "log10", "sin", "cos", "tan",
    "asin", "acos", "atan", "sinh", "cosh", "tanh", "pow", "atan2", "fmod", "modf", "frexp", "ldexp", "deg", "rad"]).set
    (lstr "huge") (.num (.flt (1.0 / 0.0))) |>.set (lstr "pi") (.num (.flt (Float.ofBits 0x400921FB54442D18)))
    -- LuaJIT's generator state is the oracle's
    |>.set (lstr "random") (.eff "math.random") |>.set (lstr "randomseed") (.eff "math.randomseed")
  let pkg : Tbl := { kv := [(lstr "loaded", .tbl 1), (lstr "path", lstr "")] }
  #[.tbl g, .tbl {}, .tbl str, .tbl tab, .tbl math, .tbl pkg]

end Lua
