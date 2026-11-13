import SwarmLean.Lib.Conflict
import SwarmLean.Db.Locks

/-! conflict_spec.lua's asserts: real_hunk, difflib's opcodes as Python's, lock covers and overlaps, hunks.
(locks_model_spec.lua checks the Lua against Glob.lean, which `Locks.covers` and `Locks.overlaps` are.) -/

namespace SwarmLean.Test.Conflict
open SwarmLean.Conflict

/-- realHunk. -/
def rh := realHunk

#guard !rh "module L (a, b) where\n" "module L (a, b, c) where\n" "module L (a, b, d) where\n"
#guard !rh "f a b\n" "f a x b\n" "g a b\n"
#guard rh "x = f a\n" "x = g a\n" "x = h a\n"
#guard !rh "f a b c\n" "f a b c d\n" "f z\n"  -- insertion at the edge of a replaced span merges
#guard rh "f a b c\n" "f a x b c\n" "f z\n"  -- insertion inside a replaced span does not
#guard rh "é = f\n" "é = g\n" "é = h\n" && !rh "é f\n" "é f g\n" "é h f\n"  -- \w is Unicode

/-- The opcodes as the spec prints them. -/
def ops (a b : String) : String :=
  ",".intercalate ((Difflib.opcodes (a.toList.map toString).toArray (b.toList.map toString).toArray).toList.map
    fun (t, i1, i2, j1, j2) => s!"{t} {i1} {i2} {j1} {j2}")

-- expected values from Python's difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes()
#guard ops "abxcd" "abcd" == "equal 0 2 0 2,delete 2 3 2 2,equal 3 5 2 4"
#guard ops "qabxcd" "abycdf" == "delete 0 1 0 0,equal 1 3 0 2,replace 3 4 2 3,equal 4 6 3 5,insert 6 6 5 6"
#guard ops "aaabab" "babaa" == "replace 0 2 0 1,equal 2 5 1 4,replace 5 6 4 5"
#guard ops "" "ab" == "insert 0 0 0 2" && ops "ab" "" == "delete 0 2 0 0" && ops "" "" == ""

open Locks in
#guard covers "migrations/0070_x.sql" "migrations/0070*" && covers "docs/x/y.md" "docs/"
open Locks in
#guard covers "a/b.txt" "*.txt" && !covers "docsx/y" "docs/" && covers "docs/y" "docs//"

-- overlaps: some path both patterns cover (as globs, or as directories)
open Locks in
#guard overlaps "m/*.lua" "m/a*" && overlaps "m/a*" "m/*.lua" && !overlaps "m/*.lua" "m/*.txt"
open Locks in
#guard overlaps "docs/" "docs/x.md" && overlaps "docs" "*.md" && !overlaps "docs/" "src/"
open Locks in
#guard overlaps "a?c" "ab*" && !overlaps "a?c" "abd" && overlaps "[ab]x" "bx" && overlaps "*" "x"
open Locks in
#guard overlaps "migrations/0070*" "migrations/0070_a.sql" && !overlaps "migrations/0070*" "migrations/0071*"

-- hunks: marker scan; large inputs must not hit a limit
#guard
  let h := hunks "a\n<<<<<<< x\no1\no2\n||||||| y\nb\n=======\nt\n>>>>>>> z\nmid\n<<<<<<< x\n||||||| y\n=======\nt2\n>>>>>>> z\nend\n"
  h == [("o1\no2\n", "b\n", "t\n"), ("", "", "t2\n")]
#guard (hunks "no markers\n").isEmpty && (hunks "<<<<<<< x\no\n||||||| y\nb\n").isEmpty

/-- conflict_spec's big input: 3000 hunks of 50 lines a side, over a megabyte. -/
def big : String :=
  String.join (List.replicate 3000 ("<<<<<<< x\n" ++ String.join (List.replicate 50 "o\n") ++ "||||||| y\n" ++
    String.join (List.replicate 50 "b\n") ++ "=======\n" ++ String.join (List.replicate 50 "t\n") ++ ">>>>>>> z\n"))

#guard big.utf8ByteSize > 1000000 && (hunks big).length == 3000

end SwarmLean.Test.Conflict
