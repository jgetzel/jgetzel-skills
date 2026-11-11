import SwarmModel.Lua.Num

/-! The abstract syntax of the Lua 5.1 subset swarm/lua/swarm is written in (README.md, *Lua semantics*). A string is
its bytes, as `Char`s below 256. -/

namespace Swarm.Lua

inductive BinOp where
  | add | sub | mul | div | mod | pow | concat | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited

inductive UnOp where | neg | not | len
  deriving DecidableEq, Repr, Inhabited

mutual
inductive Exp where
  | nil | tru | fls | vararg
  | num (n : Num)
  | str (s : List Char)
  | func (params : List String) (va : Bool) (body : List Stat)
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
  | locfn (name : String) (params : List String) (va : Bool) (body : List Stat)
  | ret (es : List Exp)
  | brk
  | goto (l : String)
  | label (l : String)
end

instance : Inhabited Exp := ⟨.nil⟩
instance : Inhabited Stat := ⟨.brk⟩

abbrev Block := List Stat

end Swarm.Lua
