import LuaLean.Num

/-! The abstract syntax of the Lua 5.1 subset (DESIGN.md, *The subset*). A string is
its bytes, as `Char`s below 256. -/

namespace Lua

inductive BinOp where
  | add | sub | mul | div | mod | pow | concat | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited

inductive UnOp where | neg | not | len
  deriving DecidableEq, Repr, Inhabited

/-- where LuaJIT reports a runtime error of the node it wraps: the chunk's name and the line, and the names its
messages give the operands and the callee: `("local", "x")`, `("global", "x")`, `("upvalue", "x")`, `("field", "k")`,
`("method", "m")`, or `("", "")` for none (lj_debug_slotname). `tail`: `return f(...)`, a tail call. -/
structure Site where
  src : String
  line : Nat
  names : List (String × String) := []
  fn : String × String := ("", "")
  tail : Bool := false
  deriving Inhabited

mutual
inductive Exp where
  | nil | tru | fls | vararg
  | num (n : Num)
  | str (s : List Char)
  /-- an FFI numeral (`1LL`, `1ULL`): its bits, an `int64_t`, or a `uint64_t` if `u` -/
  | cnum (v : Nat) (u : Bool)
  /-- `lines`: the lines of its `function` and its `end`, getinfo's linedefined and lastlinedefined -/
  | func (params : List String) (va : Bool) (body : List Stat) (lines : Nat × Nat)
  | var (name : String)
  | index (t k : Exp)
  | call (f : Exp) (args : List Exp)
  | method (o : Exp) (name : String) (args : List Exp)
  | bin (op : BinOp) (a b : Exp)
  | and (a b : Exp)
  | or (a b : Exp)
  | un (op : UnOp) (a : Exp)
  | table (fields : List Field)
  /-- `(e)`: one value -/
  | paren (e : Exp)
  /-- `e`, its runtime errors reported at `s`: an index, call, method call, operator, or assignment target -/
  | site (s : Site) (e : Exp)

inductive Field where
  | pos (e : Exp)
  | named (k : String) (e : Exp)
  | keyed (k e : Exp)

inductive Stat where
  | loc (names : List String) (es : List Exp)
  | assign (targets : List Exp) (es : List Exp)
  | call (e : Exp)
  | block (b : List Stat)
  | while (c : Exp) (b : List Stat)
  | rpt (b : List Stat) (c : Exp)
  /-- if c1 then b1 elseif c2 then b2 ... else e end -/
  | ite (c : Exp) (t e : List Stat)
  | fornum (v : String) (a b : Exp) (step : Option Exp) (body : List Stat)
  | forin (vs : List String) (es : List Exp) (body : List Stat)
  | locfn (name : String) (params : List String) (va : Bool) (body : List Stat) (lines : Nat × Nat)
  | ret (es : List Exp)
  | brk
  | goto (l : String)
  | label (l : String)
  /-- a `for` loop, its errors reported at `s` -/
  | site (s : Site) (st : Stat)
end

instance : Inhabited Exp := ⟨.nil⟩
instance : Inhabited Stat := ⟨.brk⟩

abbrev Block := List Stat

end Lua
