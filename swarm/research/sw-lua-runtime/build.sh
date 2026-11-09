#!/bin/sh
# Build the swarm runtime: one static LuaJIT with swarm's C rocks preloaded (research/sw-lua-runtime.md §1).
# usage: build.sh <zig target> <src dir> <out file>   e.g. build.sh x86_64-linux-musl ./src ./swarm-lua
# <src dir> holds the unpacked sources: luajit sqlite-amalgamation-* pcre2-* lsqlite3 cjson lfs lrexlib luaposix
# luautf8-* argparse. Needs zig, make and od; nothing else.
set -eu
T=$1; S=$(cd "$2" && pwd); OUT=$3
here=$(cd "$(dirname "$0")" && pwd)
B=${BUILD_DIR:-$PWD/build-$T}
VER=${SWARM_RUNTIME:-0-dev}
rm -rf "$B"; mkdir -p "$B/o" "$(dirname "$OUT")"
case $T in
  *macos*) OS=-D_DARWIN_C_SOURCE; SYS=Darwin; LD="-Wl,-dead_strip"; export MACOSX_DEPLOYMENT_TARGET=11.0 ;;
  *)       OS="-D_DEFAULT_SOURCE -D_BSD_SOURCE -D_GNU_SOURCE"; SYS=Linux; LD="-static -s -Wl,--gc-sections" ;;
esac
CC="zig cc -target $T"
CF="-O2 -w -ffunction-sections -fdata-sections -DNDEBUG"

# LuaJIT: its own Makefile, cross by HOST_CC (buildvm runs on the build host) + TARGET_SYS.
cp -R "$S/luajit" "$B/luajit"; chmod -R u+w "$B/luajit"
make -s -C "$B/luajit/src" -j"$(nproc 2>/dev/null || sysctl -n hw.ncpu)" libluajit.a luajit.o \
  CC="$CC" HOST_CC="zig cc" TARGET_SYS=$SYS TARGET_AR="zig ar rcus" BUILDMODE=static \
  CFLAGS="-ffunction-sections -fdata-sections"
LJ=$B/luajit/src

# pcre2 8-bit, Unicode, no JIT: pcre2_jit_compile.c only stubs it out (Apple's hardened runtime would need an entitlement for it; swarm's patterns are tiny).
P=$(echo "$S"/pcre2-*/src); PB=$B/pcre2; mkdir -p "$PB"
cp "$P/config.h.generic" "$PB/config.h"; cp "$P/pcre2.h.generic" "$PB/pcre2.h"
cp "$P/pcre2_chartables.c.dist" "$PB/pcre2_chartables.c"
for f in auto_possess chkdint compile compile_cgroup compile_class config context convert dfa_match error extuni \
         find_bracket jit_compile maketables match match_data match_next newline ord2utf pattern_info script_run serialize \
         string_utils study substitute substring tables ucd valid_utf xclass; do
  src=$P/pcre2_$f.c; [ $f = chartables ] && src=$PB/pcre2_chartables.c
  $CC $CF -DHAVE_CONFIG_H -DPCRE2_CODE_UNIT_WIDTH=8 -DPCRE2_STATIC -DSUPPORT_UNICODE -DHAVE_MEMMOVE \
    -DHAVE_STRERROR -I"$PB" -I"$P" -c "$src" -o "$B/o/pcre2_$f.o" &
done
$CC $CF -DHAVE_CONFIG_H -DPCRE2_CODE_UNIT_WIDTH=8 -DPCRE2_STATIC -DSUPPORT_UNICODE -I"$PB" -I"$P" \
  -c "$PB/pcre2_chartables.c" -o "$B/o/pcre2_chartables.o" &
wait

L="-I$LJ"
# sqlite: the amalgamation, not the older copy lsqlite3 ships.
$CC $CF -DSQLITE_THREADSAFE=1 -DSQLITE_DEFAULT_WAL_SYNCHRONOUS=1 \
  -c "$(echo "$S"/sqlite-amalgamation-*/sqlite3.c)" -o "$B/o/sqlite3.o" &
$CC $CF $L -I"$(echo "$S"/sqlite-amalgamation-*)" -c "$S/lsqlite3/lsqlite3.c" -o "$B/o/lsqlite3.o" &
for f in lua_cjson strbuf fpconv; do $CC $CF $L -c "$S/cjson/$f.c" -o "$B/o/cjson_$f.o" & done
$CC $CF $L -c "$S/lfs/src/lfs.c" -o "$B/o/lfs.o" &
$CC $CF $L -c "$(echo "$S"/luautf8-*/lutf8lib.c)" -o "$B/o/lutf8lib.o" &
for f in common pcre2/lpcre2 pcre2/lpcre2_f; do
  $CC $CF $L -I"$PB" -DPCRE2_CODE_UNIT_WIDTH=8 -DPCRE2_STATIC -DVERSION='"2.9.2"' \
    -c "$S/lrexlib/src/$f.c" -o "$B/o/rex_$(basename $f).o" &
done
# luaposix: only the C modules swarm requires.
PX="-D_POSIX_C_SOURCE=200809L -D_XOPEN_SOURCE=700 $OS -DPACKAGE='\"luaposix\"' -DVERSION='\"37.0\"' \
  -DHAVE_CLOCK_GETTIME -DHAVE_TM_GMTOFF -DHAVE_TM_ZONE -DHAVE_GETHOSTID \
  -DHAVE_SETGROUPS"
case $T in *macos*) ;; *) PX="$PX -DHAVE_POSIX_FADVISE -DHAVE_FDATASYNC -DHAVE_DECL_FDATASYNC" ;; esac
# One unit for all of them: each .c pulls in compat-5.2.c, whose functions aren't static (duplicate symbols).
for f in fcntl fnmatch glob poll signal stdlib sys/stat sys/wait time unistd; do
  echo "#include \"$S/luaposix/ext/posix/$f.c\""
done > "$B/posix_all.c"
eval "$CC $CF $L -I$S/luaposix/ext/include $PX -c $B/posix_all.c -o $B/o/posix_all.o" &
# argparse is pure Lua: its source goes in as a byte array (zig 0.17 trips over #embed's dep-file entry).
od -An -v -tu1 "$S/argparse/src/argparse.lua" | tr -s ' \n' ',,' | sed 's/^,//' > "$B/argparse.inc"
$CC $CF $L -I"$B" -DSWARM_RUNTIME="\"$VER\"" -c "$here/init.c" -o "$B/o/init.o" &
wait

# init.o comes before libluajit.a, so its luaL_openlibs wins and lib_init.o stays out.
# LuaJIT throws errors through the system unwinder; zig builds and links its bundled libunwind for -lunwind.
$CC $LD -o "$OUT" "$LJ/luajit.o" "$B"/o/*.o "$LJ/libluajit.a" -lunwind -lm
ls -l "$OUT"
