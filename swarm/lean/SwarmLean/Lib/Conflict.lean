import SwarmLean.Lib.Re
import SwarmLean.Lib.Difflib

/-! conflict.lua's pure parts: diff3 hunks, the edits each side made, and whether two edits clash. -/

namespace SwarmLean.Conflict

/-- A token: a word, one other non-space character, or a newline (conflict.TOK). -/
def TOK : String := "\\w+|[^\\w\\s]|\\n"

/-- diff3 conflict hunks as (ours, base, theirs), each keeping its trailing newline, by scanning lines for the
markers (conflict.hunks). -/
def hunks (text : String) : List (String × String × String) := Id.run do
  let ls := ((text.splitOn "\n").map (· ++ "\n")).toArray
  -- the last piece has no newline after it
  let ls := if text.endsWith "\n" then ls.pop else ls.modify (ls.size - 1) fun l => String.ofList l.toList.dropLast
  let n := ls.size
  let next (start : Nat) (mark : String) : Option Nat := Id.run do
    for k in [start:n] do
      if ls[k]!.startsWith mark then return some k
    return none
  let cat (a b : Nat) : String := String.join (ls.extract a b).toList
  let mut res : Array (String × String × String) := #[]
  let mut pos := 0
  for _ in [0:n + 1] do
    let some a := next pos "<<<<<<< " | break
    let b := next (a + 1) "||||||| "
    let c := b.bind fun b => next (b + 1) "=======\n"
    let some dd := c.bind fun c => next (c + 1) ">>>>>>> " | break
    let (b, c) := (b.get!, c.get!)
    res := res.push (cat (a + 1) b, cat (b + 1) c, cat (c + 1) dd)
    pos := dd + 1
  return res.toList

/-- The base-token spans one side changed, half-open; an empty span is an insertion there (conflict.edits). -/
def edits (base side : Array String) : List (Nat × Nat) :=
  (Difflib.opcodes base side).toList.filterMap fun (t, i1, i2, _) => if t == "equal" then none else some (i1, i2)

/-- Two spans clash if both change a common base token, or one inserts strictly inside the other's change. -/
def clash (a b : Nat × Nat) : Bool :=
  let (a1, a2) := a
  let (b1, b2) := b
  if a1 == a2 && b1 == b2 then false
  else if a1 == a2 then b1 < a1 && a1 < b2
  else if b1 == b2 then a1 < b1 && b1 < a2
  else a1 < b2 && b1 < a2

/-- A text's tokens. -/
def toks (s : String) : Array String :=
  match Re.findall TOK s with
  | .ok l => (l.map (·.headD "")).toArray
  | .error _ => #[]

/-- Whether a hunk is a real conflict: some edit of ours clashes with one of theirs (conflict.real_hunk). -/
def realHunk (base ours theirs : String) : Bool :=
  let b := toks base
  let eb := edits b (toks theirs)
  (edits b (toks ours)).any fun x => eb.any (clash x)

end SwarmLean.Conflict
