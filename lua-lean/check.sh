#!/bin/sh
# lua-lean's checks: no open proof and no axiom (Audit.lean: every theorem rests on Lean's three), the library builds,
# the example's specs check on their named axioms (Examples/),
# the committed chunks (test/cases.lua.gz) give the Lean semantics' results for this LuaJIT's target, JIT on and off,
# and the test scripts parse to LuaJIT's bytecode and lift with their proofs (test/stmts.lua also through the one
# theorem, LuaLean/Denote.lean). Needs lake (elan) on the PATH, or nix
# to fetch it, and nix or luajit (the reference LuaJIT, as lua-lean finds it).
cd "$(dirname "$0")" || exit 1
LUAJIT=$(./lua-lean luajit) && export LUAJIT || exit 1
if grep -rnEw 'sorry|admit|native_decide|axiom' LuaLean tools; then echo "an open proof or an axiom" >&2; exit 1; fi
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
lean_do build && lean_do env lean Audit.lean || exit 1
# the example: Examples/World.lean is test/world.lua lifted, its specs rest on the axioms their #guard_msgs name, and
# each axiom has its test against LuaJIT
if grep -rnEw 'sorry|admit|native_decide' Examples; then echo "an open proof in Examples" >&2; exit 1; fi
./lua-lean lift test/world.lua World | cmp -s - Examples/World.lean ||
  { echo "Examples/World.lean is not test/world.lua lifted (lua-lean lift test/world.lua World)" >&2; exit 1; }
for a in $(sed -n 's/^axiom \([A-Za-z0-9_]*\) :.*/\1/p' Examples/*.lean); do
  grep -qw "$a" Examples/world_axioms.lua || { echo "axiom $a has no case in Examples/world_axioms.lua" >&2; exit 1; }
done
lean_do build Examples && "$LUAJIT" Examples/world_axioms.lua || exit 1
"$LUAJIT" test/luasem.lua --cases test/cases.lua.gz && "$LUAJIT" -joff test/luasem.lua --cases test/cases.lua.gz || exit 1
# LuaJIT's syntax beyond Lua 5.1 that the subset leaves out: LuaJIT loads each line, the parser refuses it
"$LUAJIT" -e 'for l in io.lines("test/out.txt") do assert(loadstring(l), l) end' &&
  lean_do env lean --run test/Refused.lean test/out.txt || exit 1
p=$(./lua-lean parsecheck test/*.lua test/mods/*.lua) || { printf '%s\n' "$p" | grep -v 'same bytecode'; exit 1; }
./lua-lean prove test/*.lua test/mods/*.lua && ./lua-lean prove1 test/stmts.lua
