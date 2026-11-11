#!/bin/sh
# Lifts Lua modules to Lean with SwarmModel/LuaLift.lean (board #31): each function, its shallow form and the proof they
# are the same. lift.sh: regenerate SwarmModel/Lifted/Locks.lean and Tasks.lean (check.sh builds them).
# lift.sh --check: fail if either is stale (replay.sh runs it). lift.sh --all: lift every module under ../lua/swarm into
# a scratch directory and check each there (about 2 minutes).
here=$(cd "$(dirname "$0")" && pwd)
lua=$here/../lua/swarm
cd "$here" || exit 1
lake_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT
lake_do build SwarmModel.Lua.Show SwarmModel.Lua.Shallow SwarmModel.LockSrc >/dev/null || exit 1

if [ "$1" = --all ]; then
  bad=0
  for f in "$lua"/*.lua; do
    m=$(basename "$f" .lua)
    M=$(printf %s "$m" | awk '{print toupper(substr($0,1,1)) substr($0,2)}')
    if ! lake_do env lean --run SwarmModel/LuaLift.lean "$M" "$f" >"$tmp/$M.lean"; then echo "$m: not translated"; bad=1; continue; fi
    if lake_do env lean "$tmp/$M.lean" >"$tmp/$M.out" 2>&1; then echo "$m: $(grep -c '^theorem .*_ok' "$tmp/$M.lean") functions proved"
    else echo "$m: proof fails"; grep error "$tmp/$M.out" | head -5; bad=1; fi
  done
  exit $bad
fi

mkdir -p "$tmp/Lifted"
lake_do env lean --run SwarmModel/LuaLift.lean Locks "$lua/locks.lua" SwarmModel.LockSrc:LocksSrc >"$tmp/Lifted/Locks.lean" || exit 1
lake_do env lean --run SwarmModel/LuaLift.lean Tasks "$lua/tasks.lua" >"$tmp/Lifted/Tasks.lean" || exit 1
if [ "$1" = --check ]; then
  for m in Locks Tasks; do
    cmp -s "$tmp/Lifted/$m.lean" "SwarmModel/Lifted/$m.lean" || { echo "SwarmModel/Lifted/$m.lean is stale: run swarm/model/lift.sh" >&2; exit 1; }
  done
else mkdir -p SwarmModel/Lifted && cp "$tmp/Lifted/Locks.lean" "$tmp/Lifted/Tasks.lean" SwarmModel/Lifted/; fi
