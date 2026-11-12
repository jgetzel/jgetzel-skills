#!/bin/sh
# Lifts locks.lua, tasks.lua and watchd.lua's M.loop and iteration with `lua-lean lift` (../../lua-lean): each function, its
# shallow form and the proof they are the same (D.fn_ok). lift.sh: regenerate SwarmModel/Lifted/Locks.lean, Tasks.lean
# and Watchd.lean (check.sh builds them). lift.sh --check: fail if one is stale (replay.sh runs it). lift.sh --all: lift every module under ../lua/swarm into
# a scratch directory and check each there (`lua-lean prove`, about 2 minutes).
here=$(cd "$(dirname "$0")" && pwd)
lua=$here/../lua/swarm
ll=$here/../../lua-lean/lua-lean
[ "$1" = --all ] && exec "$ll" prove "$lua"/*.lua
tmp=$(mktemp -d) || exit 1
trap 'rm -rf "$tmp"' EXIT
"$ll" lift "$lua/locks.lua" Swarm.Lifted.Locks SwarmModel.LockSrc:LocksSrc >"$tmp/Locks.lean" || exit 1
"$ll" lift "$lua/tasks.lua" Swarm.Lifted.Tasks >"$tmp/Tasks.lean" || exit 1
"$ll" lift "$lua/watchd.lua" Swarm.Lifted.Watchd --only M_loop,iteration >"$tmp/Watchd.lean" || exit 1
if [ "$1" = --check ]; then
  for m in Locks Tasks Watchd; do
    cmp -s "$tmp/$m.lean" "$here/SwarmModel/Lifted/$m.lean" || { echo "SwarmModel/Lifted/$m.lean is stale: run swarm/model/lift.sh" >&2; exit 1; }
  done
else cp "$tmp/Locks.lean" "$tmp/Tasks.lean" "$tmp/Watchd.lean" "$here/SwarmModel/Lifted/"; fi
