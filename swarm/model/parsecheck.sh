#!/bin/sh
# Checks the Lua parser against LuaJIT: each swarm/lua/swarm/*.lua, parsed and printed back (LuaPrint.lean), must
# compile to the same bytecode as the source (replay.sh runs it). Needs lake (elan), or nix to fetch it, and luajit.
cd "$(dirname "$0")" || exit 1
tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT
lake_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
# every number constant at full precision: the listing shows them at %.14g
cat > "$tmp/k.lua" <<'EOF'
local u = require("jit.util")
local function dump(f)
  for n = -1, -1e9, -1 do local k = u.funck(f, n); if k == nil then break end; if type(k) == "proto" then dump(k) end end
  for n = 0, 1e9 do local k = u.funck(f, n); if k == nil then break end; print(string.format("KNUM %.17g", k)) end
end
dump(assert(loadfile(arg[1])))
EOF
# the listing without file names and line numbers, then the number constants
bc() {
  luajit -bl "$1" > "$2.raw" && LC_ALL=C sed -e 's/^-- BYTECODE -- .*/-- BYTECODE --/' -e '/ FNEW /s/ *;.*$//' "$2.raw" > "$2" &&
  luajit "$tmp/k.lua" "$1" >> "$2"
}
fail=0
for f in ../lua/swarm/*.lua; do
  n=$(basename "$f")
  if ! lake_do env lean --run SwarmModel/LuaPrint.lean "$f" > "$tmp/$n"; then echo "$n: parse error"; fail=1; continue; fi
  if ! bc "$f" "$tmp/$n.src" || ! bc "$tmp/$n" "$tmp/$n.out"; then echo "$n: luajit failed"; fail=1; continue; fi
  if diff -u "$tmp/$n.src" "$tmp/$n.out" > "$tmp/$n.diff"; then echo "$n: same bytecode"
  else echo "$n: bytecode differs"; cat "$tmp/$n.diff"; fail=1; fi
done
exit $fail
