#!/bin/sh
# Symlink every skill in this repo into ~/.claude/skills. Safe to re-run.
set -e
cd "$(dirname "$0")"
dest="$HOME/.claude/skills"
mkdir -p "$dest"
for skill in */SKILL.md; do
  name=${skill%/SKILL.md}
  if [ -e "$dest/$name" ] && [ ! -L "$dest/$name" ]; then
    echo "skipped $name: $dest/$name is a real directory, remove it and re-run" >&2
    continue
  fi
  ln -sfn "$PWD/$name" "$dest/$name"
  echo "linked $name"
done
# The swarm CLI runs on LuaJIT plus 7 rocks (swarm/research/sw-lua.md section 4). Installs only into the
# per-user rock tree the swarm/swarm launcher reads; never runs sudo.
ROCKS="lsqlite3 lua-cjson luaposix lrexlib-pcre2 luafilesystem argparse luautf8"
tree=${XDG_DATA_HOME:-$HOME/.local/share}/swarm/lua
lua_missing() {
  command -v luajit >/dev/null 2>&1 || { echo luajit; return; }
  LUA_PATH="$tree/share/lua/5.1/?.lua;$tree/share/lua/5.1/?/init.lua;;" LUA_CPATH="$tree/lib/lua/5.1/?.so;;" \
    luajit -e 'for _, m in ipairs{"lsqlite3", "cjson", "posix.unistd", "rex_pcre2", "lfs", "argparse", "lua-utf8"} do
      if not pcall(require, m) then io.write(m, " ") end end'
}
rocks() {  # $1: luarocks --lua-dir, $2/$3: SQLITE_DIR/PCRE2_DIR args (empty on distros)
  lr="luarocks --lua-version=5.1 --tree $tree"; [ -n "$1" ] && lr="$lr --lua-dir=$1"
  $lr install lsqlite3 $2 && $lr install lrexlib-pcre2 $3 &&
    for r in lua-cjson luaposix luafilesystem argparse luautf8; do $lr install $r || return; done
}
if [ -n "$(lua_missing)" ]; then
  if command -v nix >/dev/null 2>&1; then
    echo "swarm needs LuaJIT: add to home.packages, or run nix profile install --impure --expr with the same:" >&2
    echo "  (luajit.withPackages (p: with p; [ $ROCKS ]))" >&2
  elif command -v brew >/dev/null 2>&1; then
    brew install luajit luarocks sqlite pcre2 &&
      rocks "$(brew --prefix luajit)" "SQLITE_DIR=$(brew --prefix sqlite)" "PCRE2_DIR=$(brew --prefix pcre2)"
  elif command -v apt-get >/dev/null 2>&1 || command -v dnf >/dev/null 2>&1; then
    command -v luarocks >/dev/null 2>&1 || {
      echo "swarm needs LuaJIT; install it, then re-run:" >&2
      echo "  sudo apt install luajit libluajit-5.1-dev luarocks libsqlite3-dev libpcre2-dev build-essential" >&2
      echo "  (or: sudo dnf install luajit luajit-devel luarocks sqlite-devel pcre2-devel gcc)" >&2
    }
    command -v luarocks >/dev/null 2>&1 && rocks
  fi
  m=$(lua_missing)
  if [ -n "$m" ]; then echo "swarm: still missing: $m" >&2; exit 1; fi
fi
# The swarm skill's Herdr panel (runs on the LuaJIT checked above), when the Herdr desktop app is installed.
if [ -d "${HERDR_APP_HOME:-$HOME/.config/herdr-app}/mods/tabs" ]; then
  luajit swarm/herdr/install.lua || echo "skipped the Herdr Swarm panel (see above)" >&2
fi
