#!/bin/sh
# lua-lean's checks: no open proof and no axiom (Audit.lean: every theorem rests on Lean's three), the library builds,
# the committed chunks (test/cases.lua.gz) give the Lean semantics' results for this LuaJIT's target, JIT on and off,
# and the test scripts parse to LuaJIT's bytecode and lift with their proofs. Needs lake (elan) on the PATH, or nix
# to fetch it, and luajit.
cd "$(dirname "$0")" || exit 1
if grep -rnEw 'sorry|admit|native_decide|axiom' LuaLean tools; then echo "an open proof or an axiom" >&2; exit 1; fi
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
lean_do build && lean_do env lean Audit.lean || exit 1
luajit test/luasem.lua --cases test/cases.lua.gz && luajit -joff test/luasem.lua --cases test/cases.lua.gz || exit 1
p=$(./lua-lean parsecheck test/*.lua) || { printf '%s\n' "$p" | grep -v 'same bytecode'; exit 1; }
./lua-lean prove test/*.lua
