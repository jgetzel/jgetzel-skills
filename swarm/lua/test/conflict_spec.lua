-- conflict: real_hunk (test_real_hunk_probe_asserts), difflib opcodes as Python's, lock covers.
local conflict, difflib, locks = require "swarm.conflict", require "swarm.difflib", require "swarm.locks"

local rh = conflict.real_hunk
assert(not rh("module L (a, b) where\n", "module L (a, b, c) where\n", "module L (a, b, d) where\n"))
assert(not rh("f a b\n", "f a x b\n", "g a b\n"))
assert(rh("x = f a\n", "x = g a\n", "x = h a\n"))
assert(not rh("f a b c\n", "f a b c d\n", "f z\n"))  -- insertion at the edge of a replaced span merges
assert(rh("f a b c\n", "f a x b c\n", "f z\n"))  -- insertion inside a replaced span does not
assert(rh("é = f\n", "é = g\n", "é = h\n") and not rh("é f\n", "é f g\n", "é h f\n"))  -- \w is Unicode

local function ops(a, b)
  local r = {}
  for _, o in ipairs(difflib.SequenceMatcher(a, b):get_opcodes()) do r[#r + 1] = table.concat(o, " ") end
  return table.concat(r, ",")
end
local function chars(s) local t = {} for ch in s:gmatch(".") do t[#t + 1] = ch end return t end
-- expected values from Python's difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes()
assert(ops(chars("abxcd"), chars("abcd")) == "equal 0 2 0 2,delete 2 3 2 2,equal 3 5 2 4")
assert(ops(chars("qabxcd"), chars("abycdf")) ==
  "delete 0 1 0 0,equal 1 3 0 2,replace 3 4 2 3,equal 4 6 3 5,insert 6 6 5 6")
assert(ops(chars("aaabab"), chars("babaa")) == "replace 0 2 0 1,equal 2 5 1 4,replace 5 6 4 5")
assert(ops({}, chars("ab")) == "insert 0 0 0 2" and ops(chars("ab"), {}) == "delete 0 2 0 0" and ops({}, {}) == "")

assert(locks.covers("migrations/0070_x.sql", "migrations/0070*") and locks.covers("docs/x/y.md", "docs/"))
assert(locks.covers("a/b.txt", "*.txt") and not locks.covers("docsx/y", "docs/") and locks.covers("docs/y", "docs//"))
