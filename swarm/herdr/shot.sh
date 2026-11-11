#!/bin/sh
# Screenshot this checkout's Swarm panel in a private, headless Herdr; never the person's window, mods or board.
#   swarm/herdr/shot.sh [--screen home|agents|board[:done|dropped]|task:ID|agent:NAME|more:activity|more:system][+ask] [--width PX] [--db FILE] [--theme light|dark|NAME] [--fixture DIR] [--before CMD] out.png
# --screen: the screen the panel opens on (default home); +ask also opens its confirmation (End agent, Release task,
#   Restart watchd on more:system); board+new opens the new-task form.
# --before: a shell command run just before the shot, in the sandbox (its DISPLAY, HERDR_APP_HOME, and $DEMO_DB the
#   board's copy): clicks and keys for the private display (xdotool), or a swarm command against the copy.
# --db (default $SWARM_DB): the board to show, copied in; with neither, a backup of this repo's real board.
# --theme: light/dark set settings.json's appearance; anything else is a theme name (themes/ or Herdr's own).
# --fixture: a made-up swarm from `luajit swarm/herdr/demo.lua DIR`: its board, machine reading, processes and cost history.
# Everything lives under one /tmp/hs.* dir (socket paths must be shorter than SUN_LEN): its own Xvfb display,
# HERDR_APP_HOME, hc session and a demo repo holding the board; on exit it stops only what it started.
set -eu
screen=home width=860 db=${SWARM_DB:-} theme= fx= out= before=
while [ $# -gt 0 ]; do
  case $1 in
    --screen) screen=$2; shift 2 ;;
    --width) width=$2; shift 2 ;;
    --db) db=$2; shift 2 ;;
    --theme) theme=$2; shift 2 ;;
    --fixture) fx=$(cd "$2" && pwd); shift 2 ;;
    --before) before=$2; shift 2 ;;
    -h|--help) sed -n 2,11p "$0"; exit 0 ;;
    -*) echo "shot.sh: unknown option $1" >&2; exit 2 ;;
    *) out=$1; shift ;;
  esac
done
[ -n "$out" ] || { sed -n 3p "$0" >&2; exit 2; }
case ${screen%+*} in home|agents|board|board:done|board:dropped|task:[0-9]*|agent:?*|more:activity|more:system) ;; *) echo "shot.sh: no screen $screen" >&2; exit 2 ;; esac
case $width in ''|*[!0-9]*) echo "shot.sh: --width takes px" >&2; exit 2 ;; esac
case $out in /*) ;; *) out=$PWD/$out ;; esac

here=$(cd -P "$(dirname "$0")" && pwd)
# The rocks install.sh puts in the per-user tree (Homebrew/apt; Nix's luajit has them built in).
lua_tree=${XDG_DATA_HOME:-$HOME/.local/share}/swarm/lua
export LUA_PATH="$lua_tree/share/lua/5.1/?.lua;$lua_tree/share/lua/5.1/?/init.lua;${LUA_PATH:-;}" LUA_CPATH="$lua_tree/lib/lua/5.1/?.so;${LUA_CPATH:-;}"
repo=$(cd "$here/../.." && pwd)
real=$(git -C "$repo" rev-parse --path-format=absolute --git-common-dir)/swarm/swarm.db
[ -n "$db" ] || db=$real
# the panel's `swarm state` inherits these: the fixture's /proc, `ps` and cmd-cost history instead of this machine's
[ -z "$fx" ] || { db=$fx/swarm.db; export SWARM_PROC="$fx/proc" XDG_STATE_HOME="$fx/state" PATH="$fx/bin:$PATH"; }
[ -f "$db" ] || { echo "shot.sh: no board at $db" >&2; exit 1; }

# Tripwire: every Herdr window outside a shot.sh sandbox now must still be running after cleanup.
others=
for p in $(pgrep '^\.?herdr-app' || :); do
  tr '\0' '\n' </proc/"$p"/environ 2>/dev/null | grep -q '^HERDR_APP_HOME=/tmp/hs\.' || others="$others $p"
done

D=$(mktemp -d /tmp/hs.XXXXXX)
H=$D/h S=hs$$ xpid= hpid=
# Herdr and hc must not find the person's window, terminal or core through the environment.
unset HC_TERMINAL_SOCKET HC_TERMINAL_ID HC_SCOPE WAYLAND_DISPLAY SWARM_DB
export HERDR_APP_HOME=$H HC_SESSION=$S
cleanup() {
  [ -z "$hpid" ] || { timeout 5 herdr-app do app.quit >/dev/null 2>&1 || :; kill "$hpid" 2>/dev/null || :; }
  [ -z "$hpid" ] || { hc server stop >/dev/null 2>&1 || :; rm -rf "${XDG_STATE_HOME:-$HOME/.local/state}/herdr-core/$S"; }
  [ -z "$xpid" ] || kill "$xpid" 2>/dev/null || :
  rm -rf "$D"
  for p in $others; do
    kill -0 "$p" 2>/dev/null || { echo "shot.sh: a Herdr window outside the sandbox exited during this run (pid $p)" >&2; exit 3; }
  done
}
trap cleanup EXIT
trap 'exit 1' INT TERM HUP

# The board: the panel unsets SWARM_DB and reads <cwd's git common dir>/swarm/swarm.db, so a demo repo holds it.
mkdir -p "$D/demo/.git/swarm" "$H"
git -C "$D/demo" init -q
luajit - "$db" "$D/demo/.git/swarm/swarm.db" <<'L'
local s = require "lsqlite3"
local h = assert(s.open("file:" .. arg[1] .. "?mode=ro", s.OPEN_READONLY + s.OPEN_URI))
assert(h:exec("vacuum into '" .. arg[2]:gsub("'", "''") .. "'") == s.OK, h:errmsg())
L

# The panel runs <app home>/../swarm: this checkout's CLI.
ln -s "$repo/swarm/swarm" "$D/swarm"

wait_for() { # wait_for <seconds> <command...>: retry until it succeeds
  n=$1; shift
  until "$@" >/dev/null 2>&1; do
    n=$((n - 1)); [ "$n" -gt 0 ] || { echo "shot.sh: timed out on: $*" >&2; exit 1; }
    sleep 1
  done
}

# A fresh home's first start: window.json maximizes it to the screen (Xvfb has no window manager for
# window.maximize), shared.json marks the welcome as seen, update-notes.json skips the "Updated to" toast.
W=$((width + 900))
printf '{"state":"maximized","bounds":[0,0,%s,1000]}\n' "$W" >"$H/window.json"
printf '{"frame.welcomed":"finished"}\n' >"$H/shared.json"
printf '{"last_run":"%s","presented":[]}\n' "$(herdr-app --version | cut -d' ' -f2)" >"$H/update-notes.json"
Xvfb -displayfd 3 -screen 0 "${W}x1000x24" -nolisten tcp 3>"$D/dpy" >/dev/null 2>&1 &
xpid=$!
wait_for 10 test -s "$D/dpy"
export DISPLAY=:$(cat "$D/dpy")

(cd "$D/demo" && exec herdr-app) >"$D/herdr.log" 2>&1 &
hpid=$!
wait_for 30 herdr-app status
wait_for 30 test -f "$H/layouts/main.json" -a -d "$H/mods/tabs"

# Install like a person would, then swap the mods/swarm symlink for a real copy: hot reload and icon
# loading don't follow a symlinked mod dir. The copy opens on --screen (the anchor is main.js's SCREEN line).
echo '{"url_command": "true"}' > "$H/calendar.json" # no calendar: never ask a keyring
luajit "$here/../../herdr-mods/install.lua" >/dev/null
rm "$H/mods/swarm"
cp -r "$here/mods/swarm" "$H/mods/swarm"
sed -i "s|^const SCREEN = \"home\";|const SCREEN = \"$screen\";|" "$H/mods/swarm/main.js"
grep -q "^const SCREEN = \"$screen\";" "$H/mods/swarm/main.js" || { echo "shot.sh: main.js no longer has the line const SCREEN = \"home\"; update shot.sh" >&2; exit 1; }

if [ -n "$theme" ]; then
  key=theme; case $theme in light|dark) key=appearance ;; esac
  luajit - "$H/settings.json" "$key" "$theme" <<'L'
local j = require "cjson"
local f = io.open(arg[1])
local s = f and j.decode(f:read "*a") or {}
if f then f:close() end
s[arg[2]] = arg[3]
f = assert(io.open(arg[1], "w")); f:write(j.encode(s)); f:close()
L
fi

hd() { herdr-app do "$@" >/dev/null; }
hd layout.switch --name jgetzel
hd space.new --name demo --folder "$D/demo"
hd layout.show --id panel
hd layout.select --stack panel-body --child swarm
hd layout.resize --id panel --px "$width"
sleep 8 # the panel's first `swarm state` and icon copy, then a frame
# First-run overlays (the welcome) can open late; close whatever is up just before the shot.
for o in $(herdr-app status | luajit -e 'for _, o in ipairs(require("cjson").decode(io.read "*a").overlays or {}) do print(o) end'); do
  hd overlay.close --id "$o"
done
case $screen in *+ask) hd swarm.ask ;; esac
sleep 1
[ -z "$before" ] || { DEMO_DB=$D/demo/.git/swarm/swarm.db sh -c "$before"; sleep 5; } # 5 s: the command's result and the next poll
errs=$(herdr-app status | luajit -e 'local e = require("cjson").decode(io.read "*a").errors or {}
for _, x in ipairs(e) do print(type(x) == "table" and require("cjson").encode(x) or x) end')
[ -z "$errs" ] || echo "shot.sh: Herdr reports: $errs" >&2
herdr-app shot "$out" >/dev/null
echo "$out"
