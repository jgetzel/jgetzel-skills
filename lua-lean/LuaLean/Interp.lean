import LuaLean.Parse
import LuaLean.Pat
import LuaLean.CDecl

/-! The semantics: an interpreter for the subset, on fuel. A value is nil, a boolean, a number, a string (its bytes),
a table or a closure (heap addresses), a builtin, or an effect handle. Every local is a heap cell, so closures share
upvalues as Lua's do; `pcall` keeps what the failed call wrote, as Lua does (`EStateM` keeps the state on error).

Effects are not interpreted: the world's part of `io`, `os` and `print`, and every module not given as source
(`posix.*`, `lfs`, `cjson`, a script's own C modules, …) are effects: `Val.eff` handles, or a builtin's call into the
world (`print`'s write, `os.time`'s clock). Calling one asks `oracle`, which answers from the trace of the effects
before it (the heap's cell `LOG`), and the call joins the trace; `none` stops the run with `Err.eff`. Fuel bounds the
depth of the evaluation (each nested evaluation, call and loop iteration takes one); running out is `Err.fuel`,
never a Lua error, so `pcall` does not catch it. -/

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
  /-- a coroutine -/
  | thr (a : Nat)
  /-- `string.dump` of the closure at `f`, stripped or not: a string whose bytes (LuaJIT's bytecode) are not
  modelled, so a run that reads them stops; `load` gives the function back -/
  | dump (f : Nat) (strip : Bool)
  /-- a cdata (the FFI's): its object, a typed view of bytes (`Obj.cdata`) or a ctype (`Obj.ctype`) -/
  | cdata (a : Nat)
  deriving Inhabited

/-- one call into the world: the effect, its arguments, and the world's answer -/
structure Event where
  name : String
  args : List Val
  res : List Val

/-- the world: an effect's answer to its arguments, after the trace of the calls before it (newest first) -/
abbrev Oracle := String → List Val → List Event → Option (List Val)

abbrev Env := List (String × Nat)

structure Clo where
  params : List String
  va : Bool
  body : Block
  env : Env
  /-- its environment, the table its globals are (lj_func's `env`): its creator's when made, `setfenv`'s after -/
  fenv : Nat

structure Tbl where
  kv : List (Val × Val) := []
  mt : Option Nat := none
  /-- moves on when a key gets a value it lacked, the one time LuaJIT may move keys (a new node, a rehash) -/
  ver : Nat := 0
  /-- the dead keys dropped so far: a node of LuaJIT's may still hold one -/
  gone : List Val := []

/-- a coroutine's status: `ready` to resume (not started, or suspended in a yield), `active` (running, or resuming
another), `dead` (returned or failed) -/
inductive CoSt where
  | ready | active | dead
  deriving DecidableEq

/-- a coroutine (DESIGN.md, *Coroutines*): its function; each resume so far, its arguments and the heap the coroutine
went on in, oldest first; during a replay, the resumes still to replay; its status; and what it is running inside
that a yield cannot cross (0: nothing, 1: a builtin calling back into Lua, LuaJIT's C-call boundary; 2: an error
handler) -/
structure Thr (H : Type) where
  fn : Val
  hist : List (List Val × H) := []
  script : List (List Val × H) := []
  st : CoSt := .ready
  bound : Nat := 0

inductive Obj where
  | tbl (t : Tbl)
  | clo (c : Clo)
  | cell (v : Val)
  | thr (t : Thr (Array Obj))
  /-- the trace of effects, newest first: the cell `LOG` -/
  | log (evs : List Event)
  /-- a cdata of C type `ct`: the bytes at `off` of the bytes object `mem`; `ref`, an element or field read out of
  another cdata (LuaJIT's reference: a new object over the same bytes) -/
  | cdata (ct : CType) (mem off : Nat) (ref : Bool)
  /-- a cdata's storage, little-endian -/
  | bytes (b : ByteArray)
  /-- a ctype object (`ffi.typeof`'s) -/
  | ctype (ct : CType)
  /-- what `ffi.cdef` declared: the cell `CDECLS` -/
  | cdecls (d : CDecls)

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
  /-- the running coroutine yields these values: its resume replays it to here (DESIGN.md, *Coroutines*) -/
  | yld (vs : List Val)
  deriving Inhabited

abbrev M := EStateM Err Heap

inductive Flow where
  | norm | brk
  | ret (vs : List Val)
  | goto (l : String)

structure Ctx where
  env : Env
  va : List Val
  /-- the running closure: its environment holds the globals, and it is level 1 of `getfenv` and `setfenv` -/
  self : Nat
  /-- false inside a tail call, whose callee's level 1 is a frame the semantics does not keep -/
  top : Bool := true

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
  | .thr a, .thr b => a == b
  -- equal bytes; dumps of two closures may be equal too, so `==` and a key stop there (`noDump2`, `noDump`)
  | .dump a s, .dump b t => a == b && s == t
  | .cdata a, .cdata b => a == b
  | _, _ => false
def rawEqs : List Val → List Val → Bool
  | [], [] => true
  | x :: xs, y :: ys => rawEq x y && rawEqs xs ys
  | _, _ => false
end

def typeName : Val → String
  | .nil => "nil" | .bool _ => "boolean" | .num _ => "number" | .str _ | .dump .. => "string"
  | .tbl _ => "table"
  | .fn _ | .prim .. => "function" | .eff _ => "userdata" | .thr _ => "thread" | .cdata _ => "cdata"

/-- an object the collector frees when nothing holds it, so a weak table may lose it; strings, numbers and booleans
it keeps (lj_gc's gc_mayclear) -/
def gcable : Val → Bool
  | .tbl _ | .fn _ | .prim .. | .eff _ | .thr _ | .cdata _ => true
  | _ => false

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
  | .thr a => s!"thread: {a}".toList
  -- not LuaJIT's bytes: every reader of a dump's text stops first
  | .dump a _ => s!"dump: {a}".toList
  -- not LuaJIT's (its type and address, or a 64-bit integer's digits): tostring of one stops (`noCdata`)
  | .cdata a => s!"cdata: {a}".toList

def isDump : Val → Bool
  | .dump .. => true
  | _ => false
end Val

namespace Tbl
def get (t : Tbl) (k : Val) : Val :=
  match t.kv.find? (fun (x, _) => Val.rawEq x k) with
  | some (_, v) => v
  | none => .nil

/-- a key with a value keeps its place, and set to nil stays as a dead key (`next` goes on from it, as LuaJIT's
node keeps it); a key that gets a value it lacked goes last, the dead keys go (LuaJIT's rehash drops them), and the
version moves on -/
def set (t : Tbl) (k v : Val) : Tbl :=
  if !(t.get k).isNil then
    { t with kv := t.kv.map fun (x, w) => if Val.rawEq x k then (x, v) else (x, w) }
  else if v.isNil then t
  else
    let (live, dead) := t.kv.partition fun (_, w) => !w.isNil
    { t with kv := live ++ [(k, v)], ver := t.ver + 1, gone := dead.map (·.1) ++ t.gone }

def int (i : Int) : Val := .num (.int i)

/-- the least border: the least n with t[n+1] nil -/
def len (t : Tbl) : Nat :=
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | fuel + 1 => if (t.get (int (i + 1))).isNil then i else go (i + 1) fuel
  go 0 (t.kv.length + 1)

/-- where LuaJIT's layout puts key k of the table at address a, version ver. LuaJIT hashes strings with a seed
drawn per process and tables and functions by address, so its order is not a function of the program: the rank is
opaque, no proof can compute it, and a proved spec holds for every order. Run, it keeps the insertion order. -/
opaque rank (a ver : Nat) (k : Val) : Nat := 0

/-- the entry after key k with a value (k nil: the first), in rank order; none if k is not a key -/
def next (a : Nat) (t : Tbl) (k : Val) : Option (Option (Val × Val)) :=
  let kv := t.kv.mergeSort fun x y => rank a t.ver x.1 ≤ rank a t.ver y.1
  let rest := if k.isNil then some kv else
    match kv.findIdx? (fun (x, _) => Val.rawEq x k) with
    | some i => some (kv.drop (i + 1))
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

/-- a dump's bytes, LuaJIT's bytecode, are not modelled: a run that reads them stops -/
def dumpBytes {α} : M α := throw (.eff "string.dump: a dump's bytes" [])

/-- a value whose bytes the operation reads: a dump stops the run -/
def noDump (v : Val) : M Unit := if v.isDump then dumpBytes else pure ()

/-- two values compared by their bytes: a dump with a string or another closure's dump stops (its bytes may be the
other's); two of one closure are equal if both are stripped or neither (the header's flag); a dump and any other
value are unequal -/
def noDump2 (x y : Val) : M Unit :=
  match x, y with
  | .dump .., .str _ | .str _, .dump .. => dumpBytes
  | .dump a _, .dump b _ => if a == b then pure () else dumpBytes
  | _, _ => pure ()

/-- the run stops at what of the FFI the semantics does not model -/
def ffiStop {α} (what : String) : M α := throw (.eff ("ffi: " ++ what) [])

/-- tostring of a cdata: LuaJIT's text is its type and address, or a 64-bit integer's digits -/
def noCdata (v : Val) : M Unit := match v with | .cdata _ => ffiStop "tostring of a cdata" | _ => pure ()

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

/-- the name the message gives the operand or callee at `s` is a local's in a stripped function (`Site.strip`) -/
def Msg.strippedName (s : Site) : Msg → Bool
  | .op _ i _ => (match i with | some i => s.names.getD i ("", "") | none => s.fn).1 == "stripped"
  | .arg .. => s.fn.1 == "stripped"
  | .val _ => false

/-- the node at site `s`: an error of its own frame gets the place; a tail call's callee reports out of the frame
the call replaces -/
def atSite {α} (s : Site) (m : M α) : M α := fun h =>
  match m h with
  | .error (.rt k msg) h =>
    let k := if s.tail && (match msg with | .op .. => false | _ => true) then k + 1 else k
    match k with
    | 0 => if msg.strippedName s then .error (.eff "a stripped function's local named in an error" []) h
      else .error (.val (msg.render s)) h
    | k => .error (.rt k msg) h
  | r => r

/-- `m`, its errors reported at `s` if there is one -/
def atSite? {α} : Option Site → M α → M α
  | some s, m => atSite s m
  | none, m => m

/-- `m` in the frame of the call it replaces, as a builtin's tail call is (tostring's of `__tostring`) -/
def unframe {α} (m : M α) : M α := fun h =>
  match m h with
  | .error (.rt k msg) h => .error (.rt (k + 1) msg) h
  | r => r

/-- a call's frame: an error reported in it that no site took is in a builtin, so it has no place; the rest are
one frame further out -/
def frame {α} (m : M α) : M α := fun h =>
  match m h with
  | .error (.rt 0 msg) h => .error (.val msg.bare) h
  | .error (.rt (k + 1) msg) h => .error (.rt k msg) h
  | r => r

/-- an operator's metamethod `ev` called: a builtin's bad argument names it `ev` (lj_debug_funcname) -/
def mmFrame {α} (ev : String) (m : M α) : M α := fun h =>
  match m h with
  | .error (.rt 0 (.arg narg msg)) h => .error (.rt 0 (.val (lstr s!"bad argument #{narg} to '{ev}' ({msg})"))) h
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

/-- a weak table's weak parts, keys and values: its metatable's `__mode` now, a string LuaJIT reads for `k` and `v`
(up to a NUL) at each collection (gc_traverse_tab). DESIGN.md, *Tables*: the semantics never collects, and a read
that could see an entry the collector freed stops the run -/
def weakOf (t : Tbl) : M (Bool × Bool) := do
  match t.mt with
  | none => pure (false, false)
  | some m => match (← getTbl m).get (lstr "__mode") with
    | .str s => let s := s.takeWhile (· != '\x00'); pure (s.contains 'k', s.contains 'v')
    | .dump .. => dumpBytes
    | _ => pure (false, false)

/-- value v read from table t by its key: an object under weak values may be gone in LuaJIT. The reader holds the
key, so a weak key keeps its entry -/
def held (t : Tbl) (v : Val) : M Unit := do
  if (← weakOf t).2 && v.gcable then throw (.eff "weak table: a value the collector may free" [])

/-- `rawget` of a value a weak table may have lost (`held`) -/
def wget (a : Nat) (k : Val) : M Val := do
  let t ← getTbl a
  let v := t.get k
  held t v
  pure v

/-- #t when it has one border. With holes LuaJIT's binary search finds one of them by its array part's size, which
the rehashes set and string hashing moves, so the run stops -/
def tlen (a : Nat) : M Nat := do
  let t ← getTbl a
  let b := t.len
  if t.kv.any fun (k, v) => !v.isNil && match k with | .num (.int i) => i > b + 1 | _ => false then
    throw (.eff "#t of a table with holes" [])
  -- a weak value the collector frees makes a hole
  if (← weakOf t).2 && t.kv.any fun (k, v) => v.gcable && match k with | .num (.int _) => true | _ => false then
    throw (.eff "#t of a weak table" [])
  pure b

/-- `next` from key k. A key the table does not hold is LuaJIT's error, but where its array part may hold it (an
integer) or a node may still (a key the table had): there the run stops -/
def tnext (a : Nat) (k : Val) : M (Option (Val × Val)) := do
  noDump k
  let t ← getTbl a
  match t.next a k with
  | some r =>
    -- from a key whose weak value may be gone (its node dead, then dropped by a rehash), or to an entry whose weak
    -- part may be (LuaJIT's next skips it)
    let (wk, wv) ← weakOf t
    if wv && (t.get k).gcable || r.any fun (x, v) => wk && x.gcable || wv && v.gcable then
      throw (.eff "next in a weak table" [])
    pure r
  | none =>
    let held := match k with | .num (.int _) => true | _ => t.gone.any (Val.rawEq · k)
    if held then throw (.eff "next of a key not in the table" []) else rtErr "invalid key to 'next'"

def rawset (a : Nat) (k v : Val) : M Unit := do
  -- a weak table may have lost entries under the mode it had: a mode stays once set
  if k.rawEq (lstr "__mode") then
    let old := (← getTbl a).get k
    if !old.isNil && !old.rawEq v then throw (.eff "__mode changed" [])
  match k with
  | .dump .. => dumpBytes
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
def PACKAGE : Nat := 5
def COROUTINE : Nat := 6
/-- a cell holding the running coroutine, nil in the main thread -/
def CUR : Nat := 7
def LOG : Nat := 8
/-- the ffi module (13) and what ffi.cdef declared (14) -/
def FFI : Nat := 13
def CDECLS : Nat := 14

/-- the effects so far, newest first -/
def trace (h : Heap) : List Event :=
  match h[LOG]? with
  | some (.log l) => l
  | _ => []

/-- the environment of closure `a` -/
def fenvOf (a : Nat) : M Nat := do
  match ← getObj a with
  | .clo c => pure c.fenv
  | _ => die "not a function"

def bindLocals (cx : Ctx) : List String → List Val → M Ctx
  | [], _ => pure cx
  | x :: xs, vs => do
    let c ← alloc (.cell (vs.headD .nil))
    bindLocals { cx with env := (x, c) :: cx.env } xs vs.tail

/-- v's metamethod `ev`, read from its metatable when the operation runs (lj_meta_lookup); only tables have one here,
but strings, whose metatable has `__index` alone (`index`), and cdata, whose are the FFI's (`cdIndex`, `cdSet`,
`cdEq`, a ctype's call): any other of theirs (arithmetic, `..`, `__tostring`) stops the run -/
def metaOf (v : Val) (ev : String) : M Val := do
  match v with
  | .tbl a => match (← getTbl a).mt with
    | some m => wget m (lstr ev)
    | none => pure .nil
  | .cdata _ => ffiStop s!"a cdata's {ev}"
  | _ => pure .nil

-- ---------- coroutines ----------

def getThr (a : Nat) : M (Thr Heap) := do
  match ← getObj a with
  | .thr t => pure t
  | _ => die "not a thread"

def putThr (a : Nat) (t : Thr Heap) : M Unit := modify fun h => h.set! a (.thr t)

/-- `m` where a yield cannot suspend the running coroutine: inside a builtin calling back into Lua (`b` = 1, LuaJIT's
C-call boundary) or an error handler (`b` = 2); in the main thread nothing can yield -/
def bounded {α} (b : Nat) (m : M α) : M α := do
  match ← readCell CUR with
  | .thr a =>
    let old := (← getThr a).bound
    putThr a { (← getThr a) with bound := b }
    let restore : M Unit := do putThr a { (← getThr a) with bound := old }
    tryCatch (do let x ← m; restore; pure x) fun e => do restore; throw e
  | _ => m

/-- the start of a resume of coroutine `a` on `args` (ffh_resume): the error's message if it cannot be resumed; else
the coroutine that was running, the history with this resume, and the call to run: `a` is marked running and the
heap is that of its first resume, the later ones to replay -/
def resumeBegin (a : Nat) (args : List Val) :
    M (Except String (Val × List (List Val × Heap) × Val × List Val)) := do
  let t ← getThr a
  match t.st with
  | .dead => return .error "cannot resume dead coroutine"
  | .active => return .error "cannot resume running coroutine"
  | .ready =>
    let prev ← readCell CUR
    putThr a { t with st := .active }
    writeCell CUR (.thr a)
    let hcur ← get
    let hist := t.hist ++ [(args, hcur)]
    let (a1, h1, rest) := match t.hist with
      | [] => (args, hcur, [])
      | (a1, h1) :: _ => (a1, h1, hist.tail)
    set h1
    putThr a { (← getThr a) with script := rest }
    return .ok (prev, hist, t.fn, a1)

/-- a coroutine's run: `(true, vs)` it yielded `vs`, `(false, vs)` it returned them, or the value it failed with (a
runtime error has no place: there is no frame beyond the coroutine's own) -/
def coRun (x : M (List Val)) : M (Except Val (Bool × List Val)) := fun h =>
  match x h with
  | .ok vs h => .ok (.ok (false, vs)) h
  | .error (.yld vs) h => .ok (.ok (true, vs)) h
  | .error (.val v) h => .ok (.error v) h
  | .error (.rt _ m) h => .ok (.error m.bare) h
  | .error e h => .error e h

/-- the end of a resume: `a` suspended with its history, or dead; the coroutine that resumed it running again -/
def resumeEnd (a : Nat) (prev : Val) (hist : List (List Val × Heap)) (r : Except Val (Bool × List Val)) : M Unit := do
  let t ← getThr a
  writeCell CUR prev
  match r with
  | .ok (true, _) => putThr a { t with st := .ready, hist := hist, script := [] }
  | _ => putThr a { t with st := .dead, hist := [], script := [] }

/-- what coroutine.resume returns for a run's outcome -/
def resumeVals : Except Val (Bool × List Val) → List Val
  | .ok (_, vs) => .bool true :: vs
  | .error v => [.bool false, v]

/-- what a function of coroutine.wrap returns: the values, or the coroutine's error value raised again, a string with
the caller's place (lj_ffh_coroutine_wrap_err) -/
def wrapVals : Except Val (Bool × List Val) → M (List Val)
  | .ok (_, vs) => pure vs
  | .error v@(.str _) => throw (.rt 1 (.val v))
  | .error (.dump ..) => dumpBytes
  | .error v => throw (.val v)

/-- coroutine.yield: in a replay, the next resume's arguments and heap; else the run stops here (`Err.yld`) -/
def yieldFn (args : List Val) : M (List Val) := do
  match ← readCell CUR with
  | .thr a => do
    let t ← getThr a
    -- an error handler's yield: LuaJIT's xpcall then fails with "error in error handling"
    if t.bound == 2 then throw (.eff "coroutine.yield in an error handler" [])
    if t.bound != 0 then callerErr "attempt to yield across C-call boundary"
    match t.script with
    | [] => throw (.yld args)
    | (vs, h) :: rest => do
      set h
      putThr a { (← getThr a) with script := rest }
      return vs
  | _ => callerErr "attempt to yield across C-call boundary"

-- ---------- operators ----------

def strLt : List Char → List Char → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => if a == b then strLt s t else a < b

/-- the arithmetic operators' events -/
def arithEv : BinOp → String
  | .add => "__add" | .sub => "__sub" | .mul => "__mul" | .div => "__div" | .mod => "__mod" | _ => "__pow"

/-- a metamethod as an operator calls it: a table through its `__call`; any other value it cannot call is LuaJIT's
error, with no place (nil stays nil) -/
def metaFn (h : Val) : M Val :=
  match h with
  | .nil | .fn _ | .prim .. | .eff _ => pure h
  | .tbl _ => do
    match ← metaOf h "__call" with
    | .fn _ | .prim .. => pure h
    | _ => throw (.val (lstr s!"attempt to call a {h.typeName} value"))
  | _ => throw (.val (lstr s!"attempt to call a {h.typeName} value"))

/-- an operator's metamethod `ev` (lj_meta_arith, lj_meta_cat): x's, else y's; nil when neither has one. It is called
as a call is, a table through its `__call`; one that cannot be is LuaJIT's error, with no place -/
def metaOf2 (ev : String) (x y : Val) : M Val := do
  let h ← metaOf x ev
  metaFn (← if h.isNil then metaOf y ev else pure h)

def compErr {α} (x y : Val) : M α :=
  if x.typeName == y.typeName then rtErr s!"attempt to compare two {x.typeName} values"
  else rtErr s!"attempt to compare {x.typeName} with {y.typeName}"

def concatText : Val → Option (List Char)
  | .str s => some s
  | .num n => some n.toText
  | _ => none

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
  | .dump .. => dumpBytes
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

/-- string.format: `args` its arguments, the format the first (lj_strfmt_parse, lj_strfmt_putarg); `ts` is what `%s`
and `%q` do first to a value neither a string nor a number (a `__tostring` call, which LuaJIT makes once and in order) -/
def format (fmt : List Char) (args : List Val) (ts : Val → M Val) : M (List Char) := do
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
        let strArg (v : Val) : M Val := do
          let r ← match v with | .str _ | .num _ => pure v | v => ts v
          noDump r; pure r
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
          | 'q' => do pure (quoteStr (← strArg arg).text)
          | _ => do
            let arg ← strArg arg
            noCdata arg
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

-- ---------- bit ----------

/-- an integer's int32: its value mod 2^32 as a signed integer -/
def wrap32 (i : Int) : Int := i.bmod (2 ^ 32)

/-- lj_num2bit: an integer as it is, a double plus 2^52 + 2^51 and its low 32 bits (x mod 2^32 rounded to even for
|x| < 2^51; inf and NaN 0) -/
def Num.toBit : Num → Int
  | .int i => wrap32 i
  | .flt f => wrap32 ((f + 6755399441055744.0).toBits.toNat % 2 ^ 32)

/-- lj_carith_check64 of a number or a string, as an int32 -/
def argBit (fname : String) (i : Nat) (args : List Val) : M Int := do pure (← argNum fname i args).toBit

/-- an int32's bits -/
def u32 (i : Int) : Nat := (i % 2 ^ 32).toNat

/-- LuaJIT's bit library (lib_bit.c, its asm fast functions): each argument an int32 by lj_num2bit, each result an
int32; a shift's count mod 32 -/
def bitFn (name : String) (args : List Val) : M (List Val) := do
  let res (n : Nat) : M (List Val) := pure [.num (.int (wrap32 n))]
  match name with
  | "bit.tobit" => return [.num (.int (← argBit name 0 args))]
  | "bit.bnot" => res (2 ^ 32 - 1 - u32 (← argBit name 0 args))
  | "bit.bswap" => do
    let x := u32 (← argBit name 0 args)
    res ((x % 256) * 2 ^ 24 + (x / 2 ^ 8 % 256) * 2 ^ 16 + (x / 2 ^ 16 % 256) * 2 ^ 8 + x / 2 ^ 24)
  | "bit.band" | "bit.bor" | "bit.bxor" => do
    let op : Nat → Nat → Nat := if name == "bit.band" then (· &&& ·) else if name == "bit.bor" then (· ||| ·) else (· ^^^ ·)
    -- every argument checked, the first even when there is none
    let x ← argBit name 0 args
    let ys ← (List.range (args.length - 1)).mapM fun i => argBit name (i + 1) args
    res (ys.foldl (fun a y => op a (u32 y)) (u32 x))
  | "bit.lshift" | "bit.rshift" | "bit.arshift" | "bit.rol" | "bit.ror" => do
    let x ← argBit name 0 args
    let s := u32 (← argBit name 1 args) % 32
    let u := u32 x
    match name with
    | "bit.lshift" => res (u <<< s)
    | "bit.rshift" => res (u >>> s)
    | "bit.arshift" => return [.num (.int (x >>> s))]
    | "bit.rol" => res (u <<< s ||| u >>> (32 - s))
    | _ => res (u >>> s ||| u <<< (32 - s))
  | "bit.tohex" => do
    let b := u32 (← argBit name 0 args)
    let n ← if args.length < 2 then pure 8 else argBit name 1 args
    let w := (n.natAbs).min 254
    let b := if w < 8 then b % 16 ^ w else b
    let ds := if b == 0 then [] else Nat.toDigits 16 b
    let ds := List.replicate (w - ds.length) '0' ++ ds
    return [.str (if n < 0 then ds.map Char.toUpper else ds)]
  | _ => die s!"{name}: not in the subset"

#guard (Num.toBit (.flt 1.5), Num.toBit (.flt 2.5), Num.toBit (.flt (-0.5)), Num.toBit (.flt 2147483648),
  Num.toBit (.flt 9007199254740995), Num.toBit (.flt (1/0)), Num.toBit (.int 4294967297)) == (2, 2, 0, -2147483648, 2, 0, 1)

-- ---------- the FFI ----------

/-! A pure subset of LuaJIT's FFI (DESIGN.md, *The subset*): cdata of scalar, array, struct and union types over
little-endian bytes, as LuaJIT's lj_cconv.c converts Lua values to C and back and lj_cdata.c indexes them. What is
the ABI's (plain `char`'s sign, a 1-byte integer's name), undefined in C (an index out of bounds, a double past
int64's range into an integer) or another task's (pointers, 64-bit integers, arithmetic on cdata) stops the run. -/

/-- LuaJIT's name for a type, where it is the same on every ABI (`CType.repr`) -/
def ctName (t : CType) : M String := match t.repr with
  | some s => pure s
  | none => ffiStop "a type whose name is the ABI's or LuaJIT's numbering"

/-- one cdata allocation's size bound in the semantics (a larger one stops the run) -/
def CDMAX : Nat := 2 ^ 16

def getBytes (m : Nat) : M ByteArray := do
  match ← getObj m with
  | .bytes b => pure b
  | _ => die "not a cdata's bytes"

def readMem (m off len : Nat) : M (List UInt8) := do
  let b ← getBytes m
  if off + len > b.size then ffiStop "a read past a cdata's bytes"
  pure ((List.range len).map fun i => b.get! (off + i))

def writeMem (m off : Nat) (bs : List UInt8) : M Unit := do
  let b ← getBytes m
  if off + bs.length > b.size then ffiStop "a write past a cdata's bytes"
  let b := (bs.zip (List.range bs.length)).foldl (fun b (x, i) => b.set! (off + i) x) b
  modify fun h => h.set! m (.bytes b)

def zeroMem (m off len : Nat) : M Unit := writeMem m off (List.replicate len 0)

/-- n mod 2^(8 size), little-endian -/
def leBytes (n : Int) (size : Nat) : List UInt8 :=
  (List.range size).map fun i => ((n % 2 ^ (8 * size)).toNat / 2 ^ (8 * i) % 256).toUInt8

def leNat (bs : List UInt8) : Nat := bs.foldr (fun b a => a * 256 + b.toNat) 0

/-- a C number: an integer, or a double (a float widened) -/
inductive CNum where
  | i (v : Int)
  | f (x : Float)

/-- a double as an integer target takes it (lj_num2i64, then its low bytes): truncated; past int64's range (and
NaN) x64's cvttsd2si and arm64's fcvtzs differ, so the run stops -/
def numToInt (x : Float) : M Int :=
  if -9223372036854775808.0 ≤ x && x < 9223372036854775808.0 then pure (Num.floatToInt x)
  else ffiStop "a double past int64's range into an integer"

/-- an integer as a double (`(double)i`), exact below 2^53 -/
def intToFloat (i : Int) : M Float :=
  if i.natAbs < 2 ^ 53 then pure (Float.ofInt i) else ffiStop "an integer past 2^53 into a double"

/-- x's bytes as the scalar type t holds it (lj_cconv_ct_ct to t); a NaN stored stops the run: its bits are the
CPU's, which the semantics's numbers do not keep -/
def encode (t : CType) (x : CNum) : M (List UInt8) := do
  match t, x with
  | .bool, .i v => pure [if v != 0 then 1 else 0]
  | .bool, .f d => pure [if d != 0 then 1 else 0]
  | .ch, .i v => pure (leBytes v 1)
  | .int s _, .i v => pure (leBytes v s)
  | .ch, .f d => do pure (leBytes (← numToInt d) 1)
  | .int s _, .f d => do pure (leBytes (← numToInt d) s)
  | .float, x => do
    let d ← match x with | .i v => intToFloat v | .f d => pure d
    if d.isNaN then ffiStop "a NaN stored"
    pure (leBytes d.toFloat32.toBits.toNat 4)
  | .double, x => do
    let d ← match x with | .i v => intToFloat v | .f d => pure d
    if d.isNaN then ffiStop "a NaN stored"
    pure (leBytes d.toBits.toNat 8)
  | _, _ => die "not a scalar type"

/-- the scalar of type t its bytes hold; a NaN read (other bytes as a double) stops the run, as one LuaJIT would
not canonicalize -/
def decode (t : CType) (bs : List UInt8) : M CNum := do
  let n := leNat bs
  match t with
  | .bool => pure (.i (if n != 0 then 1 else 0))
  | .ch => if n < 128 then pure (.i n) else ffiStop "a char past 127 (its sign is the ABI's)"
  | .int s sg => pure (.i (if sg && n ≥ 2 ^ (8 * s - 1) then n - 2 ^ (8 * s) else n))
  | .float =>
    let d := (Float32.ofBits n.toUInt32).toFloat
    if d.isNaN then ffiStop "a NaN read" else pure (.f d)
  | .double =>
    let d := Float.ofBits n.toUInt64
    if d.isNaN then ffiStop "a NaN read" else pure (.f d)
  | _ => die "not a scalar type"

/-- a cdata's object: its type, bytes, offset and whether it is a reference -/
def getCd (a : Nat) : M (CType × Nat × Nat × Bool) := do
  match ← getObj a with
  | .cdata ct m off r => pure (ct, m, off, r)
  | .ctype _ => ffiStop "a ctype as a value (its id)"
  | _ => die "not a cdata"

/-- where a conversion's error goes: the index's site (a cdata's __newindex), the caller of an ffi function, or its
argument -/
inductive CErr where
  | site | caller | arg (k : Nat)

def CErr.raise {α} (e : CErr) (msg : String) : M α := match e with
  | .site => rtErr msg
  | .caller => callerErr msg
  | .arg k => argErr k msg

def convErr {α} (e : CErr) (src : String) (dst : CType) : M α := do
  e.raise s!"cannot convert '{src}' to '{← ctName dst}'"

/-- a Lua value's name as a conversion's error gives its source (cconv_err_conv, cconv_err_convtv) -/
def srcName (v : Val) : M String := do
  match v with
  | .num _ => pure "number"
  | .bool _ => pure "bool"
  | .str _ | .dump .. => pure "string"
  | .cdata a => do let (ct, _) ← getCd a; ctName ct.strip.1
  | .eff _ => ffiStop "a handle into C"
  | v => pure v.typeName

/-- v as a C number for the scalar type d (lj_cconv_ct_tv): `cast` (ffi.cast's) to an integer takes nil as NULL's 0;
a string or an array there would be its address -/
def srcNum (e : CErr) (d : CType) (v : Val) (cast : Bool) : M CNum := do
  let cast := cast && (d matches .int .. | .ch)
  match v with
  | .num (.int i) => pure (.i i)
  | .num (.flt x) => pure (.f x)
  | .bool b => pure (.i (if b then 1 else 0))
  | .nil => if cast then pure (.i 0) else convErr e "nil" d
  | .str _ | .dump .. => if cast then ffiStop "an address (a string's)" else convErr e "string" d
  | .cdata a => do
    let (ct, m, off, _) ← getCd a
    let s := ct.strip.1
    if s.isScalar then decode s (← readMem m off (s.size.getD 0))
    else match s with
      | .arr .. => if cast then ffiStop "an address (an array's)" else convErr e (← ctName s) d
      | .agg .. => convErr e (← ctName s) d
      | _ => ffiStop "a pointer"
  | .eff _ => ffiStop "a handle into C"
  | v => convErr e v.typeName d

/-- an initializer's overflow -/
def initOv {α} (e : CErr) (d : CType) : M α := do e.raise s!"too many initializers for '{← ctName d}'"

/-- whether a cdata v is of the aggregate type d itself (lj_cconv_multi_init's last case, CCX(S, S), CCX(A, A)) -/
def sameAgg (d : CType) (v : Val) : M Bool := do
  match v with
  | .cdata a => match ← getObj a with
    | .cdata ct .. => match CType.same ct.strip.1 d with
      | some b => pure b
      | none => ffiStop "a plain char's type (the ABI's)"
    | _ => pure false
  | _ => pure false

/-- the bytes of a cdata v -/
def cdBytes (v : Val) (len : Nat) : M (List UInt8) := do
  match v with
  | .cdata a => do let (_, m, off, _) ← getCd a; readMem m off len
  | _ => die "not a cdata"

mutual
/-- v stored to type d at off of m (lj_cconv_ct_tv), d's own `const` not looked at (the caller has) -/
partial def store (e : CErr) (d : CType) (m off : Nat) (v : Val) : M Unit := do
  let d := d.strip.1
  match d with
  | .arr et (some n) =>
    let esz := et.size.getD 0
    match v with
    | .tbl t => arrTab e d et (esz * n) m off t
    | .str s =>
      if !et.strip.1.isByte then convErr e "string" d
      -- the string and its NUL, cut to the array (a `char[0]` takes it all)
      let sz := if esz * n != 0 && esz * n < s.length + 1 then esz * n else s.length + 1
      writeMem m off (((s ++ ['\x00']).take sz).map (·.toNat.toUInt8))
    | .cdata a => do
      if ← sameAgg d v then writeMem m off (← cdBytes v (esz * n)) else
      let (ct, _) ← getCd a
      -- LuaJIT copies one whose element type it finds compatible (lj_cconv_compatptr)
      if (ct.strip.1 matches .arr ..) && ct.strip.1.size == some (esz * n) then
        ffiStop "an array of another type, the same size"
      convErr e (← srcName v) d
    | v => convErr e (← srcName v) d
  | .agg u _ fs =>
    match v with
    | .tbl t => do zeroMem m off (d.size.getD 0); aggTab e u (CType.offsets u fs) m off t 0 true
    | .cdata _ => if ← sameAgg d v then writeMem m off (← cdBytes v (d.size.getD 0)) else convErr e (← srcName v) d
    | v => convErr e (← srcName v) d
  | .arr _ none => ffiStop "a variable-length array stored to"
  | .ptr _ => ffiStop "a pointer"
  | .void => die "void stored to"
  | d => writeMem m off (← encode d (← srcNum e d v false))

/-- an array from a table (cconv_array_tab): from t[0] if it is not nil, else t[1], to the first nil; one element
fills the array, more leave the rest zero -/
partial def arrTab (e : CErr) (d et : CType) (sz m off : Nat) (t : Nat) : M Unit := do
  let esz := et.size.getD 0
  let k0 : Int := if (← wget t (nums 0)).isNil then 1 else 0
  let rec go (k : Int) (ofs : Nat) : M Nat := do
    let v ← wget t (nums k)
    if v.isNil then return ofs
    if ofs ≥ sz then initOv e d
    store e et m (off + ofs) v
    go (k + 1) (ofs + esz)
  let ofs ← go k0 0
  fill d m off sz ofs esz

/-- the rest of an array after `ofs` bytes: the one element again, or zero -/
partial def fill (_d : CType) (m off sz ofs esz : Nat) : M Unit := do
  if ofs == esz && esz > 0 then
    let el ← readMem m off esz
    let rec rep (o : Nat) : M Unit := do
      if o + esz ≤ sz then writeMem m (off + o) el; rep (o + esz)
    rep ofs
  else zeroMem m (off + ofs) (sz - ofs)

/-- a struct's or union's fields from a table (cconv_struct_tab, after clearing it): by position from t[0] or t[1]
to the first nil, or, when the first field has neither, by name; a union's first one alone -/
partial def aggTab (e : CErr) (u : Bool) (fs : List (String × Nat × CType)) (m off t : Nat) (i : Int) (first : Bool) :
    M Unit := do
  match fs with
  | [] => pure ()
  | (n, o, ft) :: rest =>
    let named (i : Int) : M Unit := do
      let v ← wget t (lstr n)
      if v.isNil then aggTab e u rest m off t i false else do
        store e ft m (off + o) v
        if !u then aggTab e u rest m off t i false
    if i < 0 then named i else
    let v ← wget t (nums i)
    let (v, i) ← if v.isNil && i == 0 then do pure ((← wget t (nums 1)), (1 : Int)) else pure (v, i)
    if v.isNil then
      if first then named (-1) else pure ()
    else do
      store e ft m (off + o) v
      if !u then aggTab e u rest m off t (i + 1) false
end

def cdInitArr (e : CErr) (d et : CType) (m sz : Nat) (vs : List Val) : M Unit := do
  let esz := et.size.getD 0
  if vs.length * esz > sz then initOv e d
  for (v, i) in vs.zip (List.range vs.length) do store e et m (i * esz) v
  fill d m 0 sz (vs.length * esz) esz

def cdInitAgg (e : CErr) (d : CType) (m sz : Nat) (vs : List Val) : M Unit := do
  match d with
  | .arr et _ => cdInitArr e d et m sz vs
  | .agg u _ fs => do
    zeroMem m 0 sz
    let fs := (CType.offsets u fs).take (if u then 1 else fs.length)
    for ((_, o, ft), v) in fs.zip vs do store e ft m o v
    if vs.length > fs.length then initOv e d
  | _ => initOv e d

/-- a value an aggregate takes as itself (lj_cconv_multi_init false): a table, a string (an array's), a cdata of
its type -/
def asItself (d : CType) (v : Val) : M Bool := do
  match d, v with
  | .arr .. , .tbl _ | .agg .., .tbl _ | .arr .., .str _ | .arr .., .dump .. => pure true
  | .arr .., v | .agg .., v => sameAgg d v
  | _, _ => pure true

/-- ffi.new's initializers (lj_cconv_ct_init): none, zero; one a value of the type (a table, a string, a cdata of
it), stored; else an array's elements or a struct's fields in order, a union's first. A variable-length array a
string or table leaves partly uninitialized (LuaJIT fills no rest of one) stops the run -/
def cdInit (e : CErr) (d : CType) (m sz : Nat) (vs : List Val) : M Unit := do
  let d := d.strip.1
  match vs with
  | [] => zeroMem m 0 sz
  | [v] =>
    if !(← asItself d v) then cdInitAgg e d m sz vs
    else match d, v with
      | .arr et none, .str s =>
        if s.length + 1 == sz && et.strip.1.isByte then writeMem m 0 ((s ++ ['\x00']).map (·.toNat.toUInt8))
        else ffiStop "a variable-length array a string leaves partly uninitialized"
      | .arr _ none, _ => ffiStop "a variable-length array a table leaves partly uninitialized"
      -- LuaJIT copies the string and its NUL, and leaves the rest of the new array as it was
      | .arr _ _, .str s =>
        if s.length + 1 < sz then ffiStop "an array a string leaves partly uninitialized" else store e d m 0 v
      | d, v => store e d m 0 v
  | _ => cdInitAgg e d m sz vs

/-- a scalar's Lua value (lj_cconv_tv_ct): an integer of up to 4 bytes or a float a number, a bool a boolean; an
8-byte integer is LuaJIT's boxed one (another task's) -/
def toLua (t : CType) (bs : List UInt8) : M Val := do
  match t with
  | .int 8 _ => ffiStop "a 64-bit integer (a boxed cdata)"
  | .bool => match ← decode t bs with | .i v => pure (.bool (v != 0)) | _ => die "bool"
  | t => match ← decode t bs with
    | .i v => pure (.num (Num.ofInt v))
    | .f x => pure (.num (.flt x))

/-- the element or field `k` of a cdata of type t at off of m: its type (`const` when t is) and offset
(lj_cdata_index); a key it has not is LuaJIT's error at the index's site -/
def cdLookup (t : CType) (q : Bool) (m off : Nat) (k : Val) : M (CType × Nat) := do
  match t, k with
  | .arr et n, .num x =>
    let i ← match x with | .int i => pure i | .flt d => numToInt d
    let esz := et.size.getD 0
    let n ← match n with
      | some n => pure n
      | none => do let b ← getBytes m; pure (if esz == 0 then 0 else b.size / esz)
    if i < 0 || i ≥ n then ffiStop "an index out of bounds"
    pure (et.qual q, off + i.toNat * esz)
  | .agg u _ fs, .str s => match (CType.offsets u fs).find? (·.1 == String.ofList s) with
    | some (_, o, ft) => pure (ft.qual q, off + o)
    | none => rtErr s!"'{← ctName t}' has no member named '{String.ofList s}'"
  | .ptr _, _ => ffiStop "a pointer"
  | _, .str s => rtErr s!"'{← ctName t}' has no member named '{String.ofList s}'"
  | _, .cdata _ => ffiStop "a cdata key"
  | _, .dump .. => dumpBytes
  | _, k => rtErr s!"'{← ctName t}' cannot be indexed with '{k.typeName}'"

/-- c[k] for a cdata c: a scalar element's or field's value, an aggregate's a new reference to its bytes -/
def cdIndex (a : Nat) (k : Val) : M Val := do
  match ← getObj a with
  | .cdata ct m off _ =>
    let (t, q) := ct.strip
    let (et, eo) ← cdLookup t q m off k
    let s := et.strip.1
    if s.isScalar then toLua s (← readMem m eo (s.size.getD 0))
    else match s with
      | .arr .. | .agg .. => do pure (.cdata (← alloc (.cdata et m eo true)))
      | _ => ffiStop "a pointer"
  | _ => ffiStop "a ctype indexed (its constants)"

/-- c[k] = v for a cdata c (lj_cdata_set): a const element is LuaJIT's error -/
def cdSet (a : Nat) (k v : Val) : M Unit := do
  match ← getObj a with
  | .cdata ct m off _ =>
    let (t, q) := ct.strip
    let (et, eo) ← cdLookup t q m off k
    if et.strip.2 then rtErr "attempt to write to constant location"
    store .site et m eo v
  | _ => ffiStop "a ctype indexed (its constants)"

/-- `==` with a cdata c on one side (lj_carith_op's MM_eq): two arrays or structs are equal where their bytes start
at one place; one and a value not a cdata never; two ctypes as one type. A scalar's is 64-bit arithmetic -/
def cdEq (a : Nat) (y : Val) : M Bool := do
  match ← getObj a, y with
  | .ctype t, .cdata b => match ← getObj b with
    | .ctype t' => match CType.same t t' with
      | some r => pure r
      | none => ffiStop "a plain char's type (the ABI's)"
    | _ => ffiStop "a ctype compared with a cdata"
  | .ctype _, .num _ => ffiStop "a ctype compared with a number (its id)"
  | .ctype _, _ => pure false
  | .cdata ct m off _, y =>
    match ct.strip.1 with
    | .arr .. | .agg .. => match y with
      | .cdata b => match ← getObj b with
        | .cdata ct' m' off' _ => match ct'.strip.1 with
          | .arr .. | .agg .. => pure (m == m' && off == off')
          | _ => ffiStop "arithmetic on a scalar cdata"
        | _ => ffiStop "a ctype compared with a cdata"
      | _ => pure false
    | _ => ffiStop "arithmetic on a scalar cdata"
  | _, _ => die "not a cdata"

def cdeclsOf : M CDecls := do
  match ← getObj CDECLS with
  | .cdecls d => pure d
  | _ => die "no C declarations"

/-- an ffi function's C type argument (ffi_checkctype): a declaration (`"int[4]"`), a ctype, or a cdata's type; and
whether that cdata is a reference (its type a C++ reference type, which the semantics does not keep) -/
def ctArg (args : List Val) : M (CType × Bool) := do
  match args with
  | [] => argErr 1 "C type expected, got no value"
  | .str s :: _ => do
    match parseType s (← cdeclsOf) with
    | some (t, d) => modify (·.set! CDECLS (.cdecls d)); pure (t, false)
    | none => ffiStop "a C declaration outside the subset (or LuaJIT's error)"
  | .cdata a :: _ => match ← getObj a with
    | .ctype t => pure (t, false)
    | .cdata ct _ _ r => pure (ct, r)
    | _ => die "not a cdata"
  | .dump .. :: _ => dumpBytes
  | v :: _ => argErr 1 s!"C type expected, got {v.typeName}"

/-- ffi_checkint: argument k (from 1) as an int32 -/
def intArg (args : List Val) (k : Nat) : M Int := do
  if args.length < k then argErr k "value expected"
  match ← srcNum (.arg k) (.int 4 true) (args.getD (k - 1) .nil) false with
  | .i v => pure (wrap32 v)
  | .f x => do pure (wrap32 (← numToInt x))

/-- a new cdata of type ct, zeroed, of `sz` bytes -/
def cdNew (ct : CType) (sz : Nat) : M (Nat × Nat) := do
  if sz > CDMAX then ffiStop "an allocation past the semantics' bound"
  let m ← alloc (.bytes (ByteArray.mk (Array.replicate sz 0)))
  pure (← alloc (.cdata ct m 0 false), m)

/-- a variable-length array's size for `n` elements (lj_ctype_vlsize): none when negative or 2^31 bytes or more -/
def vlSize (et : CType) (n : Int) : Option Nat :=
  let n := n % 2 ^ 32
  let s := (et.size.getD 0) * n.toNat
  if s < 2 ^ 31 then some s else none

/-- ffi.new(ct, [n,] init...) and a ctype's call -/
def ffiNew (args : List Val) : M (List Val) := do
  let (ct, r) ← ctArg args
  if r then ffiStop "a reference's type"
  let (sz, inits) ← match ct.strip.1 with
    | .arr et none => do
      match vlSize et (← intArg args 2) with
      | some s => pure (s, args.drop 2)
      | none => argErr 1 "size of C type is unknown or too large"
    | t => match t.size with
      | some s => pure (s, args.drop 1)
      | none => argErr 1 "size of C type is unknown or too large"
  if (ct.strip.1 matches .ptr _) then ffiStop "a pointer"
  let (a, m) ← cdNew ct sz
  cdInit .caller ct m sz inits
  return [.cdata a]

/-- ffi.string(v[, len]): len bytes of v as a const void *, else up to its NUL as a const char * -/
def ffiString (args : List Val) : M (List Val) := do
  anyArg 0 args
  let v := args.headD .nil
  let bad (to : String) : M (List UInt8) := do argErr 1 s!"cannot convert '{← srcName v}' to '{to}'"
  let chars (bs : List UInt8) : List Val := [.str (bs.map fun b => Char.ofNat b.toNat)]
  match args.getD 1 .nil with
  | .nil =>
    let bs ← match v with
      | .str s => pure (s.map (·.toNat.toUInt8) ++ [0])
      | .cdata a => do
        let (ct, m, off, _) ← getCd a
        match ct.strip.1 with
        | .arr et _ =>
          if et.strip.1.isByte then do
            let b ← getBytes m
            pure ((List.range (b.size - off)).map fun i => b.get! (off + i))
          else bad "const char *"
        | .ptr _ => ffiStop "a pointer"
        | _ => bad "const char *"
      | .nil => ffiStop "ffi.string of NULL"
      | .eff _ => ffiStop "a handle into C"
      | _ => bad "const char *"
    match bs.findIdx? (· == 0) with
    | some i => return chars (bs.take i)
    | none => ffiStop "a read past a cdata's bytes (no NUL)"
  | _ =>
    let len ← intArg args 2
    if len < 0 then ffiStop "ffi.string's negative length"
    let len := len.toNat
    let bs ← match v with
      | .str s =>
        if len ≤ s.length + 1 then pure (((s ++ ['\x00']).take len).map (·.toNat.toUInt8))
        else ffiStop "a read past a string's bytes"
      | .cdata a => do
        let (ct, m, off, _) ← getCd a
        match ct.strip.1 with
        | .arr .. | .agg .. => readMem m off len
        | .ptr _ => ffiStop "a pointer"
        | _ => bad "const void *"
      | .nil => ffiStop "ffi.string of NULL"
      | .eff _ => ffiStop "a handle into C"
      | _ => bad "const void *"
    return chars bs

/-- the FFI's functions of the subset (lib_ffi.c) -/
def ffiFn (name : String) (args : List Val) : M (List Val) := do
  match name with
  | "ffi.cdef" => do
    let s ← argStr name 0 args
    match parseCdef s (← cdeclsOf) with
    | some d => modify (·.set! CDECLS (.cdecls d)); return []
    | none => ffiStop "a C declaration outside the subset (or LuaJIT's error)"
  | "ffi.typeof" => do
    if args.length > 1 then ffiStop "ffi.typeof's parameters"
    let (ct, r) ← ctArg args
    if r then ffiStop "a reference's type"
    return [.cdata (← alloc (.ctype ct))]
  | "ffi.new" => ffiNew args
  | "ffi.cast" => do
    let (ct, r) ← ctArg args
    if r then ffiStop "a reference's type"
    let d := ct.strip.1
    anyArg 1 args
    match d with
    | .ptr _ => ffiStop "a pointer"
    | d => if !d.isScalar then argErr 1 "invalid C type"
    let v := args.getD 1 .nil
    -- a cdata of the type itself is its own cast
    if let .cdata a := v then
      if let .cdata ct' _ _ _ ← getObj a then if ct' == ct then return [v]
    let (a, m) ← cdNew ct (d.size.getD 0)
    writeMem m 0 (← encode d (← srcNum .caller d v true))
    return [.cdata a]
  | "ffi.sizeof" => do
    let (ct, _) ← ctArg args
    -- a variable-length array's cdata: its own length
    if let .cdata a :: _ := args then
      if let .cdata (.arr _ none) m _ false ← getObj a then return [nums (← getBytes m).size]
    match ct.strip.1 with
    | .arr et none => return [match vlSize et (← intArg args 2) with | some s => nums s | none => .nil]
    | .void => ffiStop "sizeof void"
    | t => return [match t.size with | some s => nums s | none => .nil]
  | "ffi.string" => ffiString args
  | _ => die s!"{name}: not in the subset"

/-- tonumber of a cdata: a scalar's number (an 8-byte integer's as a double), any other's nil -/
def cdToNumber (a : Nat) : M Val := do
  let (ct, m, off, _) ← getCd a
  let s := ct.strip.1
  if !s.isScalar then return .nil
  match ← decode s (← readMem m off (s.size.getD 0)) with
  | .i v => if s.size == some 8 then return .num (.flt (← intToFloat v)) else return .num (Num.ofInt v)
  | .f x => return .num (.flt x)

/-- a ctype's call, ffi.new of it (ffi_meta___call); its bad argument's message names no function LuaJIT's way
the semantics has, so it stops the run -/
def ctypeCall (a : Nat) (args : List Val) : M (List Val) := do
  match ← getObj a with
  | .ctype _ => fun h => match ffiNew (.cdata a :: args) h with
    | .error (.rt _ (.arg ..)) h => .error (.eff "ffi: a ctype call's bad argument" []) h
    | r => r
  | _ => ffiStop "a cdata called"

/-- the ffi functions the subset models; the rest of the module are handles -/
def ffis : List String := ["cdef", "new", "cast", "typeof", "sizeof", "string"]


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
    let n := (← tlen t)
    match args.length with
    | 2 => rawset t (nums (n + 1)) (args.getD 1 .nil); return []
    | 3 => do
      let pos ← argInt name 1 args
      let mut i : Int := n + 1
      for _ in [0:(n + 1)] do
        if i > pos then
          rawset t (nums i) (← wget t (nums (i - 1)))
          i := i - 1
      rawset t (nums i) (args.getD 2 .nil)
      return []
    | _ => callerErr "wrong number of arguments to 'insert'"
  | "remove" => do
    let t ← argTbl name 0 args
    let n := (← tlen t)
    match args.getD 1 .nil with
    | .nil =>
      if n == 0 then return []
      let old ← wget t (nums n)
      rawset t (nums n) .nil
      return [old]
    | _ => do
      let pos ← libInt tgt name 1 args
      if (Num.int 1).le pos && pos.le (.int n) then
        let old ← wget t (← libKey name pos)
        for k in ← libRange (pos.add (.int 1)) (.int n) do
          rawset t (← libKey name (k.sub (.int 1))) (← wget t (← libKey name k))
        rawset t (nums n) .nil
        return [old]
      return []
  | "concat" => do
    let t ← argTbl name 0 args
    let sep ← match args.getD 1 .nil with | .nil => pure [] | _ => argStr name 1 args
    let i ← optInt name 2 args 1
    let j ← match args.getD 3 .nil with | .nil => Int.ofNat <$> tlen t | _ => argInt name 3 args
    let mut r : List (List Char) := []
    let mut k := i
    for _ in [0:(j - i + 1).toNat] do
      noDump (← wget t (nums k))
      match concatText (← wget t (nums k)) with
      | some s => r := r ++ [s]
      | none => callerErr s!"invalid value ({(← wget t (nums k)).typeName}) at index {k} in table for 'concat'"
      k := k + 1
    return [.str (List.intercalate sep r)]
  | "maxn" => do
    let t ← getTbl (← argTbl name 0 args)
    let m := t.kv.foldl (fun m (k, v) => match k, v with
      | _, .nil => m
      | .num x, _ => if m.lt x then x else m
      | _, _ => m) (Num.int 0)
    return [.num m]
  | "getn" => do return [nums (← tlen (← argTbl name 0 args))]
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
        rawset a2 (← libKey name (i.add d)) (← wget a1 (← libKey name i))
    return [.tbl a2]
  -- require "table.new" and "table.clear"
  | "new" => do
    let a ← argInt name 0 args
    let h ← argInt name 1 args
    -- shortcut: a size above 65536 stops the run (LuaJIT's memory may refuse it), model "table overflow" if one is needed
    if a > 65536 || h > 65536 then throw (.eff "table.new of a large size" [])
    return [.tbl (← alloc (.tbl {}))]
  | "clear" => do
    let t ← argTbl name 0 args
    if !((← getTbl t).get (lstr "__mode")).isNil then throw (.eff "__mode changed" [])
    putTbl t { (← getTbl t) with kv := [] }; return []
  | _ => die s!"table.{name}: not in the subset"

def unpackFn (args : List Val) : M (List Val) := do
  let t ← argTbl "unpack" 0 args
  let i ← optInt "unpack" 1 args 1
  let j ← match args.getD 2 .nil with | .nil => Int.ofNat <$> tlen t | _ => argInt "unpack" 2 args
  -- lua_checkstack: the results and the arguments within LUAI_MAXCSTACK
  if i ≤ j && j - i + 1 + args.length > 8000 then callerErr "too many results to unpack"
  (List.range (j - i + 1).toNat).mapM fun (k : Nat) => wget t (nums (i + k))

-- ---------- os: dates ----------

/-- a broken-down time as `os.date("*t")` gives it: month 1..12, wday 1..7 from Sunday, yday 1..366 -/
structure Tm where
  sec : Int
  min : Int
  hour : Int
  day : Int
  month : Int
  year : Int
  wday : Int
  yday : Int
  isdst : Bool

/-- the days from 1970-01-01 to a date of the proleptic Gregorian calendar (H. Hinnant's days_from_civil) -/
def daysFromCivil (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let doy := (153 * ((m + 9) % 12) + 2) / 5 + d - 1
  era * 146097 + yoe * 365 + yoe / 4 - yoe / 100 + doy - 719468

/-- gmtime: the UTC date of a time -/
def gmtime (t : Int) : Tm :=
  let days := t / 86400
  let s := t % 86400
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
  { sec := s % 60, min := s / 60 % 60, hour := s / 3600, day := doy - (153 * mp + 2) / 5 + 1, month := m, year := y,
    wday := (days + 4) % 7 + 1, yday := days - daysFromCivil y 1 1 + 1, isdst := false }

def tmTable (tm : Tm) : Tbl :=
  { kv := [(lstr "sec", nums tm.sec), (lstr "min", nums tm.min), (lstr "hour", nums tm.hour), (lstr "day", nums tm.day),
      (lstr "month", nums tm.month), (lstr "year", nums tm.year), (lstr "wday", nums tm.wday),
      (lstr "yday", nums tm.yday), (lstr "isdst", .bool tm.isdst)] }

def dayNames : List String := ["Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]
def monthNames : List String := ["January", "February", "March", "April", "May", "June", "July", "August",
  "September", "October", "November", "December"]

/-- one of strftime's conversions in the C locale, but those that expand to others; `none`: one the semantics leaves
out (glibc's and macOS's differ, or it needs the zone: `%Z %z %s %G %g %V`, flags, widths, `%E`, `%O`) -/
def tmConv (tm : Tm) (c : Char) : Option (List Char) :=
  let pad (w : Nat) (p : Char) (n : Int) := Num.padLeft p w (Num.digits n.toNat)
  let name (l : List String) (i : Int) := (l.getD (i.toNat - 1) "?").toList
  match c with
  | 'a' => some ((name dayNames tm.wday).take 3) | 'A' => some (name dayNames tm.wday)
  | 'b' | 'h' => some ((name monthNames tm.month).take 3) | 'B' => some (name monthNames tm.month)
  | 'C' => some (pad 2 '0' (tm.year / 100)) | 'y' => some (pad 2 '0' (tm.year % 100)) | 'Y' => some (pad 4 '0' tm.year)
  | 'd' => some (pad 2 '0' tm.day) | 'e' => some (pad 2 ' ' tm.day) | 'm' => some (pad 2 '0' tm.month)
  | 'H' => some (pad 2 '0' tm.hour) | 'I' => some (pad 2 '0' (if tm.hour % 12 == 0 then 12 else tm.hour % 12))
  | 'M' => some (pad 2 '0' tm.min) | 'S' => some (pad 2 '0' tm.sec)
  | 'p' => some (if tm.hour < 12 then "AM" else "PM").toList
  | 'j' => some (pad 3 '0' tm.yday) | 'w' => some (pad 1 '0' (tm.wday - 1))
  | 'u' => some (pad 1 '0' (if tm.wday == 1 then 7 else tm.wday - 1))
  | 'U' => some (pad 2 '0' ((tm.yday - 1 + 7 - (tm.wday - 1)) / 7))
  | 'W' => some (pad 2 '0' ((tm.yday - 1 + 7 - (tm.wday + 5) % 7) / 7))
  | 'n' => some ['\n'] | 't' => some ['\t'] | '%' => some ['%']
  | _ => none

/-- the conversions that stand for others -/
def tmAlias : Char → Option String
  | 'c' => some "%a %b %e %H:%M:%S %Y" | 'D' | 'x' => some "%m/%d/%y" | 'F' => some "%Y-%m-%d"
  | 'r' => some "%I:%M:%S %p" | 'R' => some "%H:%M" | 'T' | 'X' => some "%H:%M:%S"
  | _ => none

def strftimeBasic (tm : Tm) : List Char → Option (List Char)
  | [] => some []
  | '%' :: c :: rest => do pure ((← tmConv tm c) ++ (← strftimeBasic tm rest))
  | ['%'] => none
  | c :: rest => (c :: ·) <$> strftimeBasic tm rest

/-- strftime in the C locale, for years 1000..9999 (C libraries pad and sign other years their own ways) -/
def strftime (tm : Tm) : List Char → Option (List Char)
  | [] => some []
  | '%' :: c :: rest => do
    if tm.year < 1000 || tm.year > 9999 then none
    let x ← match tmAlias c with
      | some f => strftimeBasic tm f.toList
      | none => tmConv tm c
    pure (x ++ (← strftime tm rest))
  | ['%'] => none
  | c :: rest => (c :: ·) <$> strftime tm rest

/-- an optional string argument (lj_lib_optstr) -/
def optStr (fname : String) (i : Nat) (args : List Val) : M (Option (List Char)) :=
  match args.getD i .nil with
  | .nil => pure none
  | _ => some <$> argStr fname i args

-- ---------- upvalues ----------

mutual
/-- the names `e` reads or writes that `bd` (the locals in scope) does not hold, in the order LuaJIT's parser meets
them (lj_parse.c var_lookup), repeats and all -/
def freeE (bd : List String) : Exp → List String
  | .var x => if bd.contains x then [] else [x]
  | .func ps _ b => (freeB (ps ++ bd) b).1
  | .index t k | .bin _ t k | .and t k | .or t k => freeE bd t ++ freeE bd k
  | .call f as => freeE bd f ++ freeEs bd as
  | .method o _ as => freeE bd o ++ freeEs bd as
  | .un _ a | .paren a | .site _ a => freeE bd a
  | .table fs => freeFs bd fs
  | _ => []
def freeEs (bd : List String) : List Exp → List String
  | [] => []
  | e :: es => freeE bd e ++ freeEs bd es
def freeFs (bd : List String) : List Field → List String
  | [] => []
  | .pos e :: fs | .named _ e :: fs => freeE bd e ++ freeFs bd fs
  | .keyed k e :: fs => freeE bd k ++ freeE bd e ++ freeFs bd fs
/-- a block's free names, and the locals in scope at its end (a `repeat`'s condition is read there) -/
def freeB (bd : List String) : Block → List String × List String
  | [] => ([], bd)
  | .loc ns es :: rest => let r := freeB (ns ++ bd) rest; (freeEs bd es ++ r.1, r.2)
  | .locfn x ps _ b :: rest => let r := freeB (x :: bd) rest; ((freeB (ps ++ x :: bd) b).1 ++ r.1, r.2)
  | s :: rest => let r := freeB bd rest; (freeS bd s ++ r.1, r.2)
def freeS (bd : List String) : Stat → List String
  | .assign ts es => freeEs bd ts ++ freeEs bd es
  | .call e => freeE bd e
  | .block b => (freeB bd b).1
  | .while c b => freeE bd c ++ (freeB bd b).1
  | .rpt b c => let r := freeB bd b; r.1 ++ freeE r.2 c
  | .ite c t e => freeE bd c ++ (freeB bd t).1 ++ (freeB bd e).1
  | .fornum v a b st body => freeE bd a ++ freeE bd b ++ freeOpt bd st ++ (freeB (v :: bd) body).1
  | .forin vs es body => freeEs bd es ++ (freeB (vs ++ bd) body).1
  | .ret es => freeEs bd es
  | .site _ s => freeS bd s
  | .loc _ es => freeEs bd es
  | .locfn x ps _ b => (freeB (ps ++ x :: bd) b).1
  | .brk | .goto _ | .label _ => []
def freeOpt (bd : List String) : Option Exp → List String
  | none => []
  | some e => freeE bd e
end

/-- a closure's upvalues as LuaJIT numbers them: the names its body takes from the enclosing functions' locals, in
the order the parser meets them, each with its cell -/
def Clo.upvals (c : Clo) : List (String × Nat) :=
  (freeB c.params c.body).1.eraseDups.filterMap fun x => (c.env.lookup x).map (x, ·)

-- ---------- string.dump ----------

/-- a site as a stripped dump reports it: the chunk named as load names it (`src`), line 0, an upvalue without its
name, a global, field or method by its constant. A local's name LuaJIT finds by scanning the bytecode back
(lj_debug_slotname without varinfo), not modelled: `atSite` stops where a message names one -/
def Site.strip (src : String) (s : Site) : Site :=
  let nm := fun (p : String × String) =>
    if p.1 == "local" then ("stripped", p.2) else if p.1 == "upvalue" then ("upvalue", "") else p
  { s with src := src, line := 0, names := s.names.map nm, fn := nm s.fn }

/-- the first statement of a function body that a stripped dump made: its upvalues have no names -/
def STRIPPED : Stat := .label "(stripped)"

def Block.stripped : Block → Bool
  | .label "(stripped)" :: _ => true
  | _ => false

mutual
def stripE (src : String) : Exp → Exp
  | .func ps va b => .func ps va (STRIPPED :: stripSs src b)
  | .index t k => .index (stripE src t) (stripE src k)
  | .call f as => .call (stripE src f) (stripEs src as)
  | .method o m as => .method (stripE src o) m (stripEs src as)
  | .bin op a b => .bin op (stripE src a) (stripE src b)
  | .and a b => .and (stripE src a) (stripE src b)
  | .or a b => .or (stripE src a) (stripE src b)
  | .un op a => .un op (stripE src a)
  | .table fs => .table (stripFs src fs)
  | .paren e => .paren (stripE src e)
  | .site s e => .site (s.strip src) (stripE src e)
  | e => e
def stripEs (src : String) : List Exp → List Exp
  | [] => []
  | e :: es => stripE src e :: stripEs src es
def stripFs (src : String) : List Field → List Field
  | [] => []
  | .pos e :: fs => .pos (stripE src e) :: stripFs src fs
  | .named k e :: fs => .named k (stripE src e) :: stripFs src fs
  | .keyed k e :: fs => .keyed (stripE src k) (stripE src e) :: stripFs src fs
def stripS (src : String) : Stat → Stat
  | .loc ns es => .loc ns (stripEs src es)
  | .assign ts es => .assign (stripEs src ts) (stripEs src es)
  | .call e => .call (stripE src e)
  | .block b => .block (stripSs src b)
  | .while c b => .while (stripE src c) (stripSs src b)
  | .rpt b c => .rpt (stripSs src b) (stripE src c)
  | .ite c t e => .ite (stripE src c) (stripSs src t) (stripSs src e)
  | .fornum v a b st body => .fornum v (stripE src a) (stripE src b) (stripO src st) (stripSs src body)
  | .forin vs es body => .forin vs (stripEs src es) (stripSs src body)
  | .locfn x ps va b => .locfn x ps va (STRIPPED :: stripSs src b)
  | .ret es => .ret (stripEs src es)
  | .site s st => .site (s.strip src) (stripS src st)
  | st => st
def stripSs (src : String) : List Stat → List Stat
  | [] => []
  | st :: ss => stripS src st :: stripSs src ss
def stripO (src : String) : Option Exp → Option Exp
  | none => none
  | some e => some (stripE src e)
end

/-- a function body as a stripped dump of it loads, as chunk `src`: no lines, no names of locals or upvalues, nested
functions too -/
def stripBody (src : String) (b : Block) : Block := STRIPPED :: stripSs src (if b.stripped then b.tail else b)

/-- a closure's upvalues as debug.getupvalue names them: no names once stripped -/
def Clo.dbgUpvals (c : Clo) : List (String × Nat) :=
  if c.body.stripped then c.upvals.map fun (_, u) => ("", u) else c.upvals

/-- string.dump's second argument: a string strips if it has an `s` (lib_string's mode), any other value if it is
true (a dump, whose bytes it would read, stops first: `dumpFn`) -/
def dumpStrip : Val → Bool
  | .str m => m.contains 's'
  | v => v.truthy

/-- `string.dump(f, strip)`: a Lua function's dump. A builtin cannot be dumped (lj_err_caller) -/
def dumpFn (args : List Val) : M (List Val) := do
  match args.headD .nil with
  | .fn a => do noDump (args.getD 1 .nil); return [.dump a (dumpStrip (args.getD 1 .nil))]
  | .prim .. => callerErr "unable to dump given function"
  | .eff _ => throw (.eff "string.dump of a handle" [])
  | _ => badType "function" 0 args

/-- `load` of a dump: a closure of the dumped one's function, each upvalue a new cell holding nil (lj_func_newL_empty),
stripped as the dump was: a stripped one is chunk `src`, what load names it (lj_bcread), an unstripped one keeps its
own; its environment `fenv`, as a source's -/
def loadDump (a : Nat) (strip : Bool) (src : String) (mode : Option (List Char)) (fenv : Nat := G) : M (List Val) := do
  if let some m := mode then
    if !m.contains 'b' then return [.nil, lstr "attempt to load chunk with wrong mode"]
  match ← getObj a with
  | .clo c =>
    let env ← c.upvals.mapM fun (x, _) => do pure (x, ← alloc (.cell .nil))
    return [.fn (← alloc (.clo ⟨c.params, c.va, if strip then stripBody src c.body else c.body, env, fenv⟩))]
  | _ => die "not a function"

-- ---------- debug ----------

/-- setmetatable's write, `debug.setmetatable`'s too -/
def setMeta (t : Nat) (m : Option Nat) : M Unit := do
  -- a weak table may have lost entries under the mode it has: it keeps its metatable
  let tt ← getTbl t
  if (← weakOf tt) != (false, false) && m != tt.mt then throw (.eff "setmetatable of a weak table" [])
  -- _G and package.loaded are read raw (print's tostring, `require`), so they take no metatable (one with `__mode`
  -- could lose entries)
  if t == G then throw (.eff "setmetatable(_G)" [])
  if t == LOADED then throw (.eff "setmetatable(package.loaded)" [])
  putTbl t { tt with mt := m }

/-- the upvalues a builtin has in LuaJIT (lj_lib's LJLIB_PUSH), where it has any: their values are LuaJIT's own -/
def primNups : String → Nat
  | "type" => 14 | "pairs" | "ipairs" | "print" | "coroutine.wrap_aux" => 1 | "gmatch_it" => 3 | _ => 0

/-- a function's upvalues as debug.getupvalue numbers them: a closure's, or none for a builtin that has none; an
effect handle, or a builtin with upvalues, stops the run -/
def upvalsOf (f : Val) : M (List (String × Nat)) := do
  match f with
  | .fn a => match ← getObj a with
    | .clo c => pure c.dbgUpvals
    | _ => die "not a function"
  | .prim p _ => if primNups p == 0 then pure [] else throw (.eff s!"debug: the upvalues of {p}" [])
  | _ => throw (.eff "debug: a handle's upvalues" [])

/-- the debug library (lib_debug.c) without a call stack: what needs one (a level, a traceback's text, a Lua
function's lines) stops the run; a thread as the first argument is skipped, as getthread does -/
def debugFn (name : String) (args : List Val) : M (List Val) := do
  let off := match args with | .thr _ :: _ => 1 | _ => 0
  match name with
  | "debug.getmetatable" => do
    anyArg 0 args
    match args.headD .nil with
    | .tbl t => return [((← getTbl t).mt.map Val.tbl).getD .nil]
    | .str _ | .dump .. => throw (.eff "debug.getmetatable of a string" [])
    | .eff _ => throw (.eff "debug.getmetatable of a handle" [])
    | _ => return [.nil]
  | "debug.setmetatable" => do
    let m ← match args.getD 1 .nil with
      | .tbl m => pure (some m)
      | .nil => if args.length < 2 then argErr 2 "nil or table expected" else pure none
      | _ => argErr 2 "nil or table expected"
    match args.headD .nil with
    | .tbl t => setMeta t m; return [.bool true]
    -- the metatable of every value of that type
    | v => throw (.eff s!"debug.setmetatable of a {v.typeName}" [])
  | "debug.getupvalue" | "debug.setupvalue" => do
    let get := name == "debug.getupvalue"
    if !get then anyArg 2 args
    let i ← argInt name 1 args
    let us ← match args.headD .nil with
      | f@(.fn _) | f@(.prim ..) | f@(.eff _) => upvalsOf f
      | _ => badType "function" 0 args
    match if i < 1 then none else us[(i - 1).toNat]? with
    | some (x, c) => if get then return [lstr x, ← readCell c] else do writeCell c (args.getD 2 .nil); return [lstr x]
    | none => return []
  | "debug.getinfo" => do
    let opts := (← optStr name (off + 1) args).getD "flnSu".toList
    let f ← match args.getD off .nil with
      | v@(.fn _) | v@(.prim ..) => pure v
      | .eff _ => throw (.eff "debug.getinfo of a handle" [])
      | v => match v.toNum with
        -- lua_tointeger's level: below 0 none, else a frame of the stack
        | some l =>
          let neg := match l with | .int i => decide (i < 0) | .flt x => decide (x ≤ -1.0)
          if neg then pure .nil else throw (.eff "debug.getinfo of a stack level" [])
        | none => argErr (off + 1) "function or level expected"
    if f.isNil then return [.nil]
    if !opts.all ("SlunfL".toList.contains ·) then argErr (off + 2) "invalid option"
    let lua := match f with | .fn _ => true | _ => false
    if lua && (opts.contains 'S' || opts.contains 'L') then throw (.eff "debug.getinfo: a Lua function's lines" [])
    let (nups, np, va) ← match f with
      | .fn a => do match ← getObj a with
        | .clo c => pure (c.upvals.length, c.params.length, c.va)
        | _ => die "not a function"
      | .prim p _ => pure (primNups p, 0, true)
      | _ => pure (0, 0, true)
    let set (t : Tbl) (k : String) (v : Val) : Tbl := t.set (lstr k) v
    let t := opts.foldl (fun t o => match o with
      | 'S' => [("source", lstr "=[C]"), ("short_src", lstr "[C]"), ("linedefined", Tbl.int (-1)),
          ("lastlinedefined", Tbl.int (-1)), ("what", lstr "C")].foldl (fun t (k, v) => set t k v) t
      | 'l' => set t "currentline" (Tbl.int (-1))
      | 'u' => set (set (set t "nups" (nums nups)) "nparams" (nums np)) "isvararg" (.bool va)
      | 'n' => set t "namewhat" (lstr "")
      | _ => t) {}
    -- 'L' gives a builtin no activelines
    let t := if opts.contains 'f' then set t "func" f else t
    return [.tbl (← alloc (.tbl t))]
  | "debug.traceback" => do
    match args.drop off with
    | .str _ :: _ | .dump .. :: _ | .num _ :: _ | [] => throw (.eff "debug.traceback: the stack" [])
    | v :: _ => return [v]
  | _ => die s!"{name}: not in the subset"

/-- the closure at a level of the stack, for getfenv and setfenv (lj_debug_frame): `caller`, the Lua function
calling, is level 1 when it is known (a call from Lua, not a tail call: `Ctx.top`). Another level stops the run: the
semantics keeps no stack -/
def fenvLevel (fname : String) (caller : Option Nat) (lvl : Int) : M Nat := do
  if lvl < 0 then argErr 1 "invalid level"
  match lvl, caller with
  | 1, some a => pure a
  | _, _ => throw (.eff s!"{fname} of level {lvl}" [])

/-- getfenv (lib_base.c): a builtin's environment is the thread's, `_G` (`setfenv(0, …)` stops) -/
def getfenvFn (caller : Option Nat) (args : List Val) : M (List Val) := do
  match args.headD .nil with
  | .fn a => return [.tbl (← fenvOf a)]
  | .prim .. => return [.tbl G]
  | .eff e => throw (.eff s!"getfenv of {e}" [])
  | _ =>
    let l ← optInt "getfenv" 0 args 1
    if l == 0 then return [.tbl G]
    return [.tbl (← fenvOf (← fenvLevel "getfenv" caller l))]

def setFenv (a t : Nat) : M Unit := do
  match ← getObj a with
  | .clo c => modify fun h => h.set! a (.clo { c with fenv := t })
  | _ => die "not a function"

/-- setfenv (lib_base.c): of a Lua function, which it returns; a builtin's is LuaJIT's error, the thread's (level 0)
stops the run -/
def setfenvFn (caller : Option Nat) (args : List Val) : M (List Val) := do
  let t ← argTbl "setfenv" 1 args
  match args.headD .nil with
  | .fn a => setFenv a t; return [.fn a]
  | .prim .. => callerErr "'setfenv' cannot change environment of given object"
  | .eff e => throw (.eff s!"setfenv of {e}" [])
  | _ =>
    let l ← argInt "setfenv" 0 args
    if l == 0 then throw (.eff "setfenv of level 0: the thread's environment" [])
    let a ← fenvLevel "setfenv" caller l
    setFenv a t
    return [.fn a]

/-- level 1 of a call from Lua in `cx`, when the semantics knows it -/
def Ctx.caller (cx : Ctx) : Option Nat := if cx.top then some cx.self else none

/-- a call from Lua whose level 1 is `caller`: getfenv and setfenv see it, the rest are `k`, the call -/
def fenvCall (caller : Option Nat) (f : Val) (args : List Val) (k : M (List Val)) : M (List Val) :=
  match f with
  | .prim "getfenv" [] => frame (getfenvFn caller args)
  | .prim "setfenv" [] => frame (setfenvFn caller args)
  | _ => k

def basicFn (tgt : Target) (name : String) (bound args : List Val) : M (List Val) := do
  match name with
  | "type" => do anyArg 0 args; return [lstr (args.headD .nil).typeName]
  | "string.dump" => dumpFn args
  | "getfenv" => getfenvFn none args
  | "setfenv" => setfenvFn none args
  | "os.difftime" => do
    -- difftime((time_t)a, (time_t)b), a double; past 2^53 C libraries round it differently
    let a ← argIntN 64 "difftime" 0 args
    let b ← match args.getD 1 .nil with | .nil => pure 0 | _ => argIntN 64 "difftime" 1 args
    if (a - b).natAbs ≥ 2 ^ 53 then throw (.eff "os.difftime past 2^53" [])
    return [.num (.flt (Float.ofInt (a - b)))]
  | "tonumber" => do
    let b ← optInt "tonumber" 1 args 10
    if b == 10 then
      anyArg 0 args
      match args.headD .nil with
      | .num n => return [.num n]
      | .str s => return [(Num.parse s).elim .nil .num]
      | .cdata a => return [← cdToNumber a]
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
    let v ← wget t (nums (i + 1))
    return if v.isNil then [.nil] else [nums (i + 1), v]
  | "pairs" => do anyArg 0 args; let t ← argTbl name 0 args; return [.prim "next" [], .tbl t, .nil]
  | "next" => do
    match ← tnext (← argTbl name 0 args) (args.getD 1 .nil) with
    | none => return [.nil]
    | some (k, v) => return [k, v]
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
  | "rawget" => do
    let t ← argTbl name 0 args; anyArg 1 args; noDump (args.getD 1 .nil); return [← wget t (args.getD 1 .nil)]
  | "rawset" => do
    let t ← argTbl name 0 args; anyArg 1 args; anyArg 2 args
    rawset t (args.getD 1 .nil) (args.getD 2 .nil); return [.tbl t]
  | "rawequal" => do
    anyArg 0 args; anyArg 1 args
    noDump2 (args.getD 0 .nil) (args.getD 1 .nil)
    return [.bool ((args.getD 0 .nil).rawEq (args.getD 1 .nil))]
  | "setmetatable" => do
    let t ← argTbl name 0 args
    let m ← match args.getD 1 .nil with
      | .nil => pure none
      | .tbl m => pure (some m)
      | _ => argErr 2 "nil or table expected"
    if !(← metaOf (.tbl t) "__metatable").isNil then callerErr "cannot change a protected metatable"
    setMeta t m
    return [.tbl t]
  | "getmetatable" => do
    anyArg 0 args
    match args.headD .nil with
    | .tbl t => match (← getTbl t).mt with
      | some m => do
        -- a protected metatable: its `__metatable` instead
        let p ← wget m (lstr "__metatable")
        return [if p.isNil then .tbl m else p]
      | none => return [.nil]
    -- every cdata's metatable is protected: its __metatable is "ffi"
    | .cdata _ => return [lstr "ffi"]
    | _ => return [.nil]
  | "error" => do
    -- a string or number gets the place of the function `level` calls out (1: error's caller)
    let level ← optInt "error" 1 args 1
    match args.headD .nil with
    | v@(.str _) | v@(.num _) => if level > 0 then throw (.rt level.toNat (.val v)) else throw (.val v)
    | v@(.dump ..) => if level > 0 then dumpBytes else throw (.val v)
    | v => throw (.val v)
  | "assert" => do
    anyArg 0 args
    if (args.headD .nil).truthy then return args
    else match args with
      | [_] => callerErr "assertion failed!"
      | _ :: m@(.str _) :: _ | _ :: m@(.num _) :: _ => throw (.rt 1 (.val (.str m.text)))
      | _ :: .dump .. :: _ => dumpBytes
      | _ => throw (.val (args.getLast?.getD .nil))
  | "coroutine.create" | "coroutine.wrap" => do
    let f ← match args.headD .nil with
      | f@(.fn _) | f@(.prim ..) | f@(.eff _) => pure f
      | _ => badType "function" 0 args
    let a ← alloc (.thr { fn := f })
    return [if name == "coroutine.wrap" then .prim "coroutine.wrap_aux" [.thr a] else .thr a]
  | "coroutine.yield" => yieldFn args
  | "coroutine.status" => match args.headD .nil with
    | .thr a => do
      let t ← getThr a
      let cur ← readCell CUR
      return [lstr (match t.st with
        | .ready => "suspended"
        | .dead => "dead"
        | .active => if cur.rawEq (.thr a) then "running" else "normal")]
    | _ => argErr 1 "coroutine expected"
  | "coroutine.running" => do
    match ← readCell CUR with
    | v@(.thr _) => return [v]
    | _ => return [.nil]
  | "coroutine.isyieldable" => do
    match ← readCell CUR with
    | .thr a => return [.bool ((← getThr a).bound == 0)]
    | _ => return [.bool false]
  | "debug.getmetatable" | "debug.setmetatable" | "debug.getupvalue" | "debug.setupvalue" | "debug.getinfo"
  | "debug.traceback" => debugFn name args
  | "bit.tobit" | "bit.bnot" | "bit.band" | "bit.bor" | "bit.bxor" | "bit.lshift" | "bit.rshift" | "bit.arshift"
  | "bit.rol" | "bit.ror" | "bit.bswap" | "bit.tohex" => bitFn name args
  | "ffi.cdef" | "ffi.new" | "ffi.cast" | "ffi.typeof" | "ffi.sizeof" | "ffi.string" => ffiFn name args
  | "gmatch_it" => match bound with
    | [.str s, .str p, .num (.int c)] => gmatchStep s p c.toNat
    | _ => die "bad gmatch iterator"
  | _ =>
    match name.splitOn "." with
    | ["string", f] => strFn f args
    | ["table", f] => tableFn tgt f args
    | ["math", f] => mathFn f args
    | _ => die s!"{name}: not in the subset"

-- ---------- chunks: load, dofile, require ----------

/-- a chunk's name as its error messages give it (lj_debug_shortname, LUA_IDSIZE 60): `=name` as its first 59 bytes,
`@file` as the file, its last 56 bytes after `...` when it has 60 or more, a source as `[string "..."]` of its first
line, cut to 45 bytes and `...` when that line is cut or longer than 48. The name is a C string: it ends at a NUL -/
def shortSrc (s : List Char) : String :=
  let c (l : List Char) := l.takeWhile (· != '\x00')
  String.ofList <| match s with
  | '=' :: r => (c r).take 59
  | '@' :: r => if r.length ≥ 60 then "...".toList ++ c (r.drop (r.length - 56)) else c r
  | _ =>
    let s := c s
    let len := (s.takeWhile (·.toNat ≥ 32)).length.min 48
    if len < s.length then "[string \"".toList ++ s.take (len.min 45) ++ "...\"]".toList
    else "[string \"".toList ++ s ++ "\"]".toList

/-- package.path's templates (`;` between them, empty ones skipped), each with `?` the name -/
def pathFiles (path name : List Char) : List String :=
  ((String.ofList path).splitOn ";").filter (· != "") |>.map fun t => t.replace "?" (String.ofList name)

/-- a module's name as a path: `.` the directory separator -/
def modPath (m : List Char) : List Char := m.map fun c => if c == '.' then '/' else c

/-- what `require` leaves in package.loaded while a module loads: a light userdata in LuaJIT -/
def SENTINEL : Val := .eff "require sentinel"

def isSentinel : Val → Bool
  | .eff "require sentinel" => true
  | _ => false

/-- a chunk's source as a function of no parameters and every argument, its free names globals; a source
LuaJIT would load as bytecode, or the parser rejects, stops the run: its messages are LuaJIT's parser's -/
def loadSrc (src name : List Char) (mode : Option (List Char)) (env : Nat := G) : M (List Val) := do
  if src.head? == some '\x1b' then throw (.eff "load: a bytecode chunk" [])
  if let some m := mode then
    if !m.contains 't' then return [.nil, lstr "attempt to load chunk with wrong mode"]
  match parseChunk src (shortSrc name) with
  | .ok b => return [.fn (← alloc (.clo ⟨[], true, b, [], env⟩))]
  | .error _ => throw (.eff "load: a syntax error" [])

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
variable (srcs : String → Option Block) (oracle : Oracle) (tgt : Target)

/-- a call into the world: the oracle answers it after the trace so far, and it joins the trace -/
def effect (name : String) (args : List Val) : M (List Val) := fun h =>
  match oracle name args (trace h) with
  | some vs => .ok vs (h.set! LOG (.log (⟨name, args, vs⟩ :: trace h)))
  | none => .error (.eff name args) h

/-- an effect answering a time_t, `[.num (.int t)]` -/
def timeFx (name : String) (args : List Val) : M Int := do
  match ← effect oracle name args with
  | [.num (.int t)] => pure t
  | _ => throw (.eff s!"{name}: an answer not a time" [])

/-- a time_t as os.time returns it: a double (-1 too: LuaJIT 2.1 returns it) -/
def timeVal (t : Int) : Val := .num (.flt (Float.ofInt t))

/-- print without a `__tostring` to call: each value as the builtin `tostring` gives it, tab-separated, and a newline:
one write to stdout (lj_cf_print). A `tostring` of the script's own stops the run, its calls coming between print's
writes -/
def printFn (args : List Val) : M (List Val) := do
  match ← rawget G (lstr "tostring") with
  | .prim "tostring" [] => pure ()
  | _ => throw (.eff "print with a tostring of its own" [])
  if args.any Val.isDump then dumpBytes
  let _ ← effect oracle "print" [.str (List.intercalate ['\t'] (args.map Val.text) ++ ['\n'])]
  pure []

/-- io.write: each argument a string or a number (as tostring writes it), one write to the default output, whose
answer is io.write's (true, or nil and the error); a bad argument raises its error after those before it are
written (io_file_write) -/
def ioWrite (args : List Val) : M (List Val) := do
  if args.any Val.isDump then dumpBytes
  let pieces := args.map fun v => match v with | .str s => some s | .num n => some n.toText | _ => none
  let good := (pieces.takeWhile Option.isSome).filterMap id
  let rs ← if good.isEmpty then pure [.bool true] else effect oracle "io.write" [.str good.flatten]
  match pieces.findIdx? Option.isNone with
  | some i => badType "string" i args
  | none => pure rs

/-- os.date(fmt, t): `!` the UTC date, computed; else the local one, the world's (`os.localtime`, answering the
`*t` fields, or nothing where localtime fails); no t, the clock's (`os.time`) -/
def osDate (args : List Val) : M (List Val) := do
  let fmt ← match args.getD 0 .nil with | .nil => pure "%c".toList | _ => argStr "date" 0 args
  let t ← match args.getD 1 .nil with | .nil => timeFx oracle "os.time" [] | _ => argIntN 64 "date" 1 args
  -- gmtime fails past an int's years, 2^55 s or so
  if t.natAbs ≥ 2 ^ 53 then throw (.eff "os.date of a time past 2^53" [])
  let (utc, fmt) := match fmt with | '!' :: f => (true, f) | f => (false, f)
  let tm ← if utc then pure (some (gmtime t)) else do
    match ← effect oracle "os.localtime" [.num (.int t)] with
    | [] => pure none
    | [.num (.int sec), .num (.int min), .num (.int hour), .num (.int day), .num (.int month), .num (.int year),
       .num (.int wday), .num (.int yday), .bool isdst] =>
      if 0 ≤ sec && sec ≤ 60 && 0 ≤ min && min < 60 && 0 ≤ hour && hour < 24 && 1 ≤ day && day ≤ 31 &&
        1 ≤ month && month ≤ 12 && 1 ≤ wday && wday ≤ 7 && 1 ≤ yday && yday ≤ 366 then
        pure (some ⟨sec, min, hour, day, month, year, wday, yday, isdst⟩)
      else throw (.eff "os.localtime: an answer not a date" [])
    | _ => throw (.eff "os.localtime: an answer not a date" [])
  match tm with
  | none => return [.nil]
  | some tm =>
    if fmt == "*t".toList then return [.tbl (← alloc (.tbl (tmTable tm)))]
    -- the names and %c, %x, %X are the C locale's
    if (trace (← get)).any (·.name == "os.setlocale") then throw (.eff "os.date after os.setlocale" [])
    match strftime tm fmt with
    | some s => return [.str s]
    | none => throw (.eff s!"os.date {String.ofList fmt}" [])

/-- a field of os.time's table (getfield): a number truncated to an int, or the default `d`, or (none) an error -/
def tmField (k : String) (d : Option Int) (v : Val) : M Int :=
  match v.toNum, d with
  | some x, _ => do
    let i := x.trunc
    -- (int)(lua_Integer)x: undefined in C past int64, the low 32 bits past int32; far inside both here
    if !(x.toFloat.isFinite && i.natAbs < 2 ^ 30) then throw (.eff "os.time: a field past 2^30" [])
    pure i
  | none, some d => pure d
  | none, none => callerErr s!"field '{k}' missing in date table"

set_option maxHeartbeats 400000 in
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
  | .func ps va b => do pure (.fn (← alloc (.clo ⟨ps, va, b, cx.env, ← fenvOf cx.self⟩)))
  | .var x => match cx.env.lookup x with
    | some c => readCell c
    | none => do index n (.tbl (← fenvOf cx.self)) (lstr x)
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
  | .un op a => do unop n op (← eval n cx a)
  | .bin op a b => do
    let x ← eval n cx a
    let y ← eval n cx b
    binop n op x y
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
    fenvCall cx.caller fv as (call n fv as)
  | .method o m args => do
    let ov ← eval n cx o
    let fv ← index n ov (.str m.toList)
    let as ← evalList n cx args
    fenvCall cx.caller fv (ov :: as) (call n fv (ov :: as))
  | .vararg => pure cx.va
  | .site s e => atSite s (evalMulti n { cx with top := cx.top && !s.tail } e)
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
    noDump k
    let t ← getTbl a
    let v := t.get k
    if !v.isNil then do held t v; pure v else
    match t.mt with
    | none => pure .nil
    | some m => do
      match ← wget m (lstr "__index") with
      | .nil => pure .nil
      | h@(.fn _) | h@(.prim ..) => do pure ((← call n h [o, k]).headD .nil)
      | h => index n h k
  | .str _ => wget STRING k
  -- a method of the string library: its bytes next
  | .dump .. => dumpBytes
  | .eff name => match k with
    | .str s => pure (.eff (name ++ "." ++ String.ofList s))
    | _ => pure (.eff name)
  | .cdata a => cdIndex a k
  | _ => opErr "index" (some 0) o

def call (n : Nat) (f : Val) (args : List Val) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match f with
  | .fn a => do
    match ← getObj a with
    | .clo c => frame do
      let cx ← bindLocals ⟨c.env, [], a, true⟩ c.params args
      let cx := { cx with va := if c.va then args.drop c.params.length else [] }
      match ← execBlock n cx c.body with
      | .ret vs => pure vs
      | .norm => pure []
      | .brk => die "break outside a loop"
      | .goto l => die s!"no visible label '{l}' for goto"
    | _ => die "not a function"
  | .prim name bound => frame (callPrim n name bound args)
  | .eff name => effect oracle name args
  | .tbl _ => do
    -- `__call`, which must be a function: LuaJIT follows no chain of them (lj_meta_call)
    match ← metaOf f "__call" with
    | h@(.fn _) | h@(.prim ..) => call n h (f :: args)
    | _ => opErr "call" none f
  | .cdata a => frame (ctypeCall a args)
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
    let f ← alloc (.clo ⟨ps, va, b, cx.env, ← fenvOf cx.self⟩)
    writeCell c (.fn f)
    execSeq n cx full rest fin
  | s :: rest => do
    match ← execStat n cx s with
    | .norm => execSeq n cx full rest fin
    | .goto l =>
      if labelAtEnd full l then pure .norm
      else if hasLabel full l then throw (.eff "goto: a label that does not end its block" [])
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
    | .inl x => (match cx.env.lookup x with
      | some c => writeCell c (vs.headD .nil)
      | none => do setindex n (.tbl (← fenvOf cx.self)) (lstr x) (vs.headD .nil))
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
    noDump k
    let t ← getTbl a
    let old := t.get k
    if !old.isNil then do
      -- LuaJIT calls __newindex where the collector freed the value
      if !(← metaOf o "__newindex").isNil then held t old
      rawset a k v
    else
    match ← metaOf o "__newindex" with
    | .nil => rawset a k v
    | h@(.fn _) | h@(.prim ..) => do let _ ← call n h [o, k, v]
    | h => setindex n h k v
  | .cdata a => cdSet a k v
  | _ => opErr "index" (some 0) o

/-- a binary operator; fuel only for a metamethod -/
def binop (n : Nat) (op : BinOp) (x y : Val) : M Val :=
  match op with
  | .eq => do pure (.bool (← eqv n x y))
  | .ne => do pure (.bool !(← eqv n x y))
  | .lt => .bool <$> less n x y false (some "__lt")
  | .le => .bool <$> less n x y true (some "__le")
  | .gt => .bool <$> less n y x false (some "__lt")
  | .ge => .bool <$> less n y x true (some "__le")
  | .concat =>
    match concatText x, concatText y with
    | some a, some b => pure (.str (a ++ b))
    | _, _ => match n with
      | 0 => throw .fuel
      | n + 1 => do
        match ← metaOf2 "__concat" x y with
        | .nil =>
          -- the first operand neither a string nor a number; a dump is a string, whose bytes are not modelled
          let cat (v : Val) := (concatText v).isSome || v.isDump
          if !cat x then opErr "concatenate" (some 0) x else if !cat y then opErr "concatenate" (some 1) y
          else dumpBytes
        | h => do pure ((← mmFrame "__concat" (call n h [x, y])).headD .nil)
  | op =>
    match x.toNum, y.toNum with
    | some a, some b => pure (.num (match op with
        | .add => a.add b | .sub => a.sub b | .mul => a.mul tgt b | .div => a.div b | .mod => a.mod b | _ => a.pow b))
    | _, _ => match n with
      | 0 => throw .fuel
      | n + 1 => do
        match ← metaOf2 (arithEv op) x y with
        | .nil =>
          if x.toNum.isNone then opErr "perform arithmetic on" (some 0) x else opErr "perform arithmetic on" (some 1) y
        | h => do pure ((← mmFrame (arithEv op) (call n h [x, y])).headD .nil)

/-- `<` (`orEq` false) and `<=` (lj_meta_comp): numbers and strings by value; two other values of one type by `__lt`
or `__le`, which both must have, the same; without `__le`, `not (y < x)`. A builtin metamethod's bad argument names
`nm`, the operator's event (none from C: table.sort). Fuel only for a metamethod -/
def less (n : Nat) (x y : Val) (orEq : Bool) (nm : Option String) : M Bool :=
  match x, y with
  | .num a, .num b => pure (if orEq then a.le b else a.lt b)
  | .str a, .str b => pure (if orEq then a == b || strLt a b else strLt a b)
  | .dump .., .str _ | .str _, .dump .. | .dump .., .dump .. => dumpBytes
  | .cdata _, _ | _, .cdata _ => ffiStop "a cdata compared (its address, or 64-bit arithmetic)"
  | _, _ => match n with
    | 0 => throw .fuel
    | n + 1 => do
      if x.typeName != y.typeName then compErr x y
      let ev := if orEq then "__le" else "__lt"
      let h ← metaOf x ev
      if !h.isNil && h.rawEq (← metaOf y ev) then
        let r ← match nm with
          | some e => mmFrame e (call n (← metaFn h) [x, y])
          | none => call n (← metaFn h) [x, y]
        return (r.headD .nil).truthy
      if orEq then return !(← less n y x false nm)
      compErr x y

/-- `==` (lj_meta_equal): two distinct tables by x's `__eq`, if y has x's metatable or one with the same `__eq`; the
first value's truth. Fuel only for a metamethod -/
def eqv (n : Nat) (x y : Val) : M Bool :=
  match x, y with
  | .tbl a, .tbl b => if a == b then pure true else match n with
    | 0 => throw .fuel
    | n + 1 => do
      let h ← metaOf x "__eq"
      if h.isNil then return false
      if (← getTbl a).mt != (← getTbl b).mt && !h.rawEq (← metaOf y "__eq") then return false
      return ((← mmFrame "__eq" (call n (← metaFn h) [x, y])).headD .nil).truthy
  | .cdata a, y => cdEq a y
  | x, .cdata b => cdEq b x
  | _, _ => do noDump2 x y; pure (x.rawEq y)

/-- print (lj_cf_print) with a `__tostring` among its arguments, from `vs` on, `acc` what is not written yet: a string
or number as it is, any other value as the builtin tostring gives it, a call for one with `__tostring`; before that
call what is ready is written, as LuaJIT writes each argument once it has its text -/
def printArgs (n : Nat) (vs : List Val) (acc : List Char) (first : Bool) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match vs with
  | [] => do let _ ← effect oracle "print" [.str (acc ++ ['\n'])]; pure []
  | v :: vs => do
    let sep := if first then [] else ['\t']
    noDump v
    let plain := match v with | .str _ | .num _ => true | _ => false
    if plain || (← metaOf v "__tostring").isNil then return ← printArgs n vs (acc ++ sep ++ v.text) false
    if !acc.isEmpty then let _ ← effect oracle "print" [.str acc]
    let s ← match (← bounded 1 (call n (.prim "tostring" []) [v])).headD .nil with
      | .str s => pure s
      | .num x => pure x.toText
      | .dump .. => dumpBytes
      | _ => callerErr "'tostring' must return a string to 'print'"
    printArgs n vs (sep ++ s) false

/-- a unary operator; `__unm` is called with (x, x), as BC_UNM calls lj_meta_arith -/
def unop (n : Nat) (op : UnOp) (x : Val) : M Val :=
  match op with
  | .not => pure (.bool !x.truthy)
  | .neg => match x.toNum with
    | some a => pure (.num a.neg)
    | none => match n with
      | 0 => throw .fuel
      | n + 1 => do
        match ← metaOf2 "__unm" x x with
        | .nil => opErr "perform arithmetic on" (some 0) x
        | h => do pure ((← mmFrame "__unm" (call n h [x, x])).headD .nil)
  -- a table's `__len` is not looked at: LuaJIT 2.1 without LUAJIT_ENABLE_LUA52COMPAT; only tables have metatables
  | .len => match x with
    | .str s => pure (.num (.int s.length))
    | .dump .. => dumpBytes
    | .tbl a => do pure (.num (.int (← tlen a)))
    | .cdata _ => ffiStop "the length of a cdata"
    | _ => opErr "get length of" (some 0) x

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
      (fun e => do pure [.bool false, (← bounded 2 (call n (args.getD 1 .nil) [e])).headD .nil])
  | "coroutine.resume" | "coroutine.wrap_aux" => do
    let wrap := name == "coroutine.wrap_aux"
    let a ← match (if wrap then bound else args).headD .nil with
      | .thr a => pure a
      | _ => argErr 1 "coroutine expected"
    match ← resumeBegin a (if wrap then args else args.tail) with
    -- wrap's error is its caller's (lj_err_caller)
    | .error m => if wrap then callerErr m else return [.bool false, lstr m]
    | .ok (prev, hist, f, a1) =>
      let r ← coRun (call n f a1)
      resumeEnd a prev hist r
      if wrap then wrapVals r else return resumeVals r
  | "load" | "loadstring" => do
    let cn ← optStr name 1 args
    let mode ← optStr name 2 args
    -- a table becomes the chunk's environment, anything else is ignored (load_aux)
    let env := match args.getD 3 .nil with
      | .tbl t => t
      | _ => G
    match args.headD .nil with
    | .str s => loadSrc s (cn.getD s) mode env
    | .num x => loadSrc x.toText (cn.getD x.toText) mode env
    -- a string's own name for itself (its bytes) is `=?` (lj_bcread)
    | .dump a s => loadDump a s (shortSrc (cn.getD "=?".toList)) mode env
    | _ => do
      let f ← argFn name 0 args
      -- LuaJIT checks the mode after the reader's first piece, not after all of them
      if mode.any (!·.contains 't') then throw (.eff "load: a reader and a mode without t" [])
      loadSrc (← readChunk n f []) (cn.getD "=(load)".toList) mode env
  | "dofile" => do
    -- no name: stdin
    let p ← match ← optStr "dofile" 0 args with
      | some p => pure (String.ofList p)
      | none => throw (.eff "dofile: stdin" [])
    match srcs p with
    | some b => bounded 1 (do call n (.fn (← alloc (.clo ⟨[], true, b, [], G⟩))) [])
    | none => throw (.eff s!"dofile {p}" [])
  | "require" => do
    let m ← argStr "require" 0 args
    let v ← rawget LOADED (.str m)
    if v.truthy then
      if isSentinel v then callerErr s!"loop or previous error loading module '{String.ofList m}'"
      return [v]
    -- package.preload's two: each also becomes a field of `table`
    if m == "table.new".toList || m == "table.clear".toList then
      let f := Val.prim (String.ofList m) []
      rawset TABLE (.str (m.drop 6)) f
      rawset LOADED (.str m) f
      return [f]
    let path ← match ← rawget PACKAGE (lstr "path") with
      | .str p => pure p
      | _ => throw (.eff "require: package.path not a string" [])
    -- the first file of the path given as source (lib_package.c's loader_Lua), else a C module: a handle
    match (pathFiles path (modPath m)).findSome? srcs with
    | some b => do
      rawset LOADED (.str m) SENTINEL
      let r := (← bounded 1 (do call n (.fn (← alloc (.clo ⟨[], true, b, [], G⟩))) [.str m])).headD .nil
      if !r.isNil then rawset LOADED (.str m) r
      let v ← rawget LOADED (.str m)
      if isSentinel v then rawset LOADED (.str m) (.bool true); return [.bool true]
      return [v]
    | none =>
      let v := Val.eff (String.ofList m)
      rawset LOADED (.str m) v
      return [v]
  | "string.gsub" => gsub n args
  | "print" => do
    if !(← args.anyM fun v => do pure !(← metaOf v "__tostring").isNil) then return ← printFn oracle args
    match ← rawget G (lstr "tostring") with
    | .prim "tostring" [] => printArgs n args [] true
    | _ => throw (.eff "print with a tostring of its own" [])
  | "tostring" => do
    anyArg 0 args
    let v := args.headD .nil
    match ← metaOf v "__tostring" with
    | .nil => return [if v.isDump then v else .str v.text]
    -- FFH_TAILCALL: the metamethod's frame takes tostring's place
    | h => unframe (call n h [v])
  | "string.format" => do
    -- each `__tostring` through lua_call, its first value
    let ts (v : Val) : M Val := do
      match ← metaOf v "__tostring" with
      | .nil => pure v
      | h => do pure ((← bounded 1 (call n h [v])).headD .nil)
    return [.str (← format (← argStr name 0 args) args ts)]
  | "io.write" => ioWrite oracle args
  | "os.date" => osDate oracle args
  -- the run ends there, with no result for a spec to be about
  | "os.exit" => throw (.eff "os.exit" args)
  | "os.time" => do
    match args.headD .nil with
    | .nil => return [timeVal (← timeFx oracle "os.time" [])]
    | t@(.tbl _) => do
      -- lua_getfield, metamethods and all; mktime is the world's (`os.mktime`, the struct tm's fields)
      let sec ← tmField "sec" (some 0) (← index n t (lstr "sec"))
      let min ← tmField "min" (some 0) (← index n t (lstr "min"))
      let hour ← tmField "hour" (some 12) (← index n t (lstr "hour"))
      let day ← tmField "day" none (← index n t (lstr "day"))
      let month ← tmField "month" none (← index n t (lstr "month"))
      let year ← tmField "year" none (← index n t (lstr "year"))
      let d ← index n t (lstr "isdst")
      let isdst : Int := if d.isNil then -1 else if d.truthy then 1 else 0
      let tm := [sec, min, hour, day, month - 1, year - 1900, isdst].map (.num ∘ .int)
      return [timeVal (← timeFx oracle "os.mktime" tm)]
    | _ => badType "table" 0 args
  | "table.foreachi" => do
    let t ← argTbl "foreachi" 0 args
    let f ← argFn "foreachi" 1 args
    foreachi n t f 1 (← tlen t)
  | "table.foreach" => do
    let t ← argTbl "foreach" 0 args
    foreachK n t (← argFn "foreach" 1 args) .nil
  | "table.sort" => do
    let t ← argTbl "sort" 0 args
    let cmp := args.getD 1 .nil
    match cmp with
    | .nil | .fn _ | .prim .. => pure ()
    | _ => badType "function" 1 args
    let len := (← tlen t)
    bounded 1 (sortAux n t cmp 1 len)
    pure []
  | _ => basicFn tgt name bound args

/-- load's reader: f's results concatenated until nil or the empty string. LuaJIT's parser calls the reader as it
reads, so an error in it, which load returns, may come at another call, and a result neither nil nor a string is
LuaJIT's own error (`load(function() return 1 end)` is "not enough memory"): both stop the run -/
def readChunk (n : Nat) (f : Val) (acc : List Char) : M (List Char) :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    match ← catchVal (bounded 1 (call n f [])) (fun vs => pure (some (vs.headD .nil))) (fun _ => pure none) with
    | some .nil | some (.str []) => pure acc
    | some (.dump ..) => throw (.eff "load: a reader's dump" [])
    | some (.str s) => readChunk n f (acc ++ s)
    | none => throw (.eff "load: an error in the reader" [])
    | some _ => throw (.eff "load: a reader result not a string" [])

/-- table.foreachi from i: f(i, t[i]) until a result is not nil -/
def foreachi (n : Nat) (t : Nat) (f : Val) (i len : Int) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if i > len then return []
    let r := (← call n f [nums i, ← wget t (nums i)]).headD .nil
    if !r.isNil then return [r]
    foreachi n t f (i + 1) len

/-- table.foreach after key k: f(k, v), as `next` visits them, until a result is not nil -/
def foreachK (n : Nat) (t : Nat) (f k : Val) : M (List Val) :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    match ← tnext t k with
    | none => return []
    | some (k, v) =>
      let r := (← call n f [k, v]).headD .nil
      if !r.isNil then return [r]
      foreachK n t f k

def lessThan (n : Nat) (cmp a b : Val) : M Bool :=
  match n with
  | 0 => throw .fuel
  | n + 1 =>
  match cmp with
  | .nil => less n a b false none
  | f => do pure ((← call n f [a, b]).headD .nil).truthy

/-- ltablib.c's auxsort -/
def sortAux (n : Nat) (t : Nat) (cmp : Val) (l u : Int) : M Unit :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if !(l < u) then return
    let get (i : Int) := wget t (nums i)
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
    let ai ← wget t (nums i)
    let aj ← wget t (nums j)
    rawset t (nums i) aj; rawset t (nums j) ai
    sortPart n t cmp p l u i j

/-- while a[i] < P: i++ -/
def sortUp (n : Nat) (t : Nat) (cmp p : Val) (u i : Int) : M Int :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if ← lessThan n cmp (← wget t (nums i)) p then
      if i ≥ u then callerErr "invalid order function for sorting"
      sortUp n t cmp p u (i + 1)
    else return i

/-- while P < a[j]: j-- -/
def sortDown (n : Nat) (t : Nat) (cmp p : Val) (l j : Int) : M Int :=
  match n with
  | 0 => throw .fuel
  | n + 1 => do
    if ← lessThan n cmp p (← wget t (nums j)) then
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
    | .dump .. => dumpBytes
    | _ => argErr 3 "string/function/table expected"
    let maxS ← optInt "gsub" 3 args (s.length + 1)
    let anchor := p.head? == some '^'
    let ms : Pat.MS := ⟨s.toArray, (if anchor then p.tail else p).toArray⟩
    bounded 1 (gsubGo n ms repl anchor maxS 0 0 [])

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
      | .dump .. => dumpBytes
      | v => callerErr s!"invalid replacement value (a {v.typeName})"
end

/-- a chunk run as a function of no arguments -/
def runChunk (n : Nat) (b : Block) (args : List Val := []) : M (List Val) := do
  let f ← alloc (.clo ⟨[], true, b, [], G⟩)
  call srcs oracle tgt n (.fn f) args
end

-- ---------- the initial heap ----------

def libTable (lib : String) (names : List String) : Tbl :=
  { kv := names.map fun f => (lstr f, .prim (lib ++ "." ++ f) []) }

def basics : List String :=
  ["type", "tostring", "tonumber", "ipairs", "pairs", "next", "select", "unpack", "rawget", "rawset", "rawequal",
   "setmetatable", "getmetatable", "error", "assert", "pcall", "xpcall", "require", "load", "loadstring", "dofile", "getfenv", "setfenv"]

/-- LuaJIT 2.1's globals the semantics does not model: handles, so a run that uses one stops (`lua-lean check` names
each use) -/
def unmodelled : List String :=
  ["jit", "collectgarbage", "gcinfo", "module", "newproxy", "loadfile", "arg"]

def bits : List String :=
  ["tobit", "bnot", "band", "bor", "bxor", "lshift", "rshift", "arshift", "rol", "ror", "bswap", "tohex"]

def coroutines : List String := ["create", "resume", "yield", "status", "wrap", "running", "isyieldable"]

/-- _G (0), package.loaded (1), string (2), table (3), math (4), package (5), coroutine (6), the running coroutine
(7: the main thread), the trace (8), io (9), os (10), debug (11), bit (12), ffi (13), ffi.cdef's declarations (14) -/
def initHeap : Heap :=
  let g : Tbl := { kv := basics.map (fun f => (lstr f, Val.prim f [])) ++
    [(lstr "string", .tbl 2), (lstr "table", .tbl 3), (lstr "math", .tbl 4), (lstr "package", .tbl 5),
     (lstr "coroutine", .tbl 6), (lstr "_G", .tbl 0), (lstr "io", .tbl 9), (lstr "os", .tbl 10),
     (lstr "print", .prim "print" []), (lstr "_VERSION", lstr "Lua 5.1"),
     (lstr "debug", .tbl 11), (lstr "bit", .tbl 12)] ++ unmodelled.map fun f => (lstr f, .eff f) }
  let str := libTable "string" ["len", "sub", "upper", "lower", "reverse", "rep", "byte", "char", "format", "find",
    "match", "gmatch", "gsub", "dump"]
  let tab := libTable "table" ["insert", "remove", "concat", "sort", "maxn", "getn", "move", "foreach", "foreachi"]
  let math := (libTable "math" ["floor", "ceil", "abs", "sqrt", "max", "min", "exp", "log", "log10", "sin", "cos", "tan",
    "asin", "acos", "atan", "sinh", "cosh", "tanh", "pow", "atan2", "fmod", "modf", "frexp", "ldexp", "deg", "rad"]).set
    (lstr "huge") (.num (.flt (1.0 / 0.0))) |>.set (lstr "pi") (.num (.flt (Float.ofBits 0x400921FB54442D18)))
    -- LuaJIT's generator state is the oracle's
    |>.set (lstr "random") (.eff "math.random") |>.set (lstr "randomseed") (.eff "math.randomseed")
  -- package.path is LUA_PATH=./?.lua's: LuaJIT's default adds directories of the system's
  let pkg : Tbl := { kv := [(lstr "loaded", .tbl 1), (lstr "path", lstr "./?.lua")] ++
    ["cpath", "config", "preload", "loadlib", "searchpath", "seeall", "loaders"].map fun f =>
      (lstr f, .eff ("package." ++ f)) }
  let loaded : Tbl := { kv := [(lstr "_G", .tbl 0), (lstr "package", .tbl 5), (lstr "string", .tbl 2),
    (lstr "table", .tbl 3), (lstr "math", .tbl 4), (lstr "coroutine", .tbl 6), (lstr "io", .tbl 9), (lstr "os", .tbl 10),
    (lstr "debug", .tbl 11), (lstr "bit", .tbl 12), (lstr "ffi", .tbl 13), (lstr "jit", .eff "jit"), (lstr "jit.opt", .eff "jit.opt")] }
  -- the rest of io and os are the world's
  let fx (lib : String) (names : List String) : List (Val × Val) := names.map fun f => (lstr f, .eff (lib ++ "." ++ f))
  let io : Tbl := { kv := (lstr "write", .prim "io.write" []) :: fx "io" ["close", "flush", "input", "lines", "open",
    "output", "popen", "read", "tmpfile", "type", "stdin", "stdout", "stderr"] }
  let os : Tbl := { kv := [(lstr "date", .prim "os.date" []), (lstr "difftime", .prim "os.difftime" []),
    (lstr "time", .prim "os.time" []), (lstr "exit", .prim "os.exit" [])] ++ (fx "os" ["clock", "execute", "getenv",
    "remove", "rename", "setlocale", "tmpname"]) }
  -- debug's functions that need a call stack, hooks or environments are handles
  let dbg : Tbl := { kv := (libTable "debug" ["getmetatable", "setmetatable", "getupvalue", "setupvalue", "getinfo",
    "traceback"]).kv ++ fx "debug" ["getregistry", "getfenv", "setfenv", "getlocal", "setlocal", "upvalueid",
    "upvaluejoin", "sethook", "gethook", "debug"] }
  let bit := libTable "bit" bits
  -- the rest of ffi: handles (ffi.C's functions are the world's)
  let ffi : Tbl := { kv := (libTable "ffi" ffis).kv ++ fx "ffi" ["C", "metatype", "gc", "copy", "fill", "offsetof",
    "alignof", "istype", "errno", "load", "abi", "os", "arch", "typeinfo"] }
  #[.tbl g, .tbl loaded, .tbl str, .tbl tab, .tbl math, .tbl pkg, .tbl (libTable "coroutine" coroutines), .cell .nil,
    .log [], .tbl io, .tbl os, .tbl dbg, .tbl bit, .tbl ffi, .cdecls {}]

end Lua
