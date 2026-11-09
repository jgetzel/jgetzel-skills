/* luaL_openlibs for the swarm runtime: LuaJIT's own lib_init.c, plus the rocks swarm needs in package.preload.
** Linked ahead of libluajit.a, so the archive's lib_init.o is never pulled in. */
#include "lua.h"
#include "lauxlib.h"
#include "lualib.h"

#define C(n) int luaopen_##n(lua_State *L);
C(lsqlite3) C(cjson) C(lfs) C(rex_pcre2) C(utf8)
C(posix_fcntl) C(posix_fnmatch) C(posix_glob) C(posix_poll) C(posix_signal) C(posix_stdlib)
C(posix_sys_stat) C(posix_sys_wait) C(posix_time) C(posix_unistd)

static const char argparse_src[] = {
#include "argparse.inc"
};
static int luaopen_argparse(lua_State *L)
{
  if (luaL_loadbuffer(L, argparse_src, sizeof argparse_src, "=argparse")) return lua_error(L);
  lua_call(L, 0, 1);
  return 1;
}

static const luaL_Reg lj_lib_load[] = {
  { "", luaopen_base }, { LUA_LOADLIBNAME, luaopen_package }, { LUA_TABLIBNAME, luaopen_table },
  { LUA_IOLIBNAME, luaopen_io }, { LUA_OSLIBNAME, luaopen_os }, { LUA_STRLIBNAME, luaopen_string },
  { LUA_MATHLIBNAME, luaopen_math }, { LUA_DBLIBNAME, luaopen_debug }, { LUA_BITLIBNAME, luaopen_bit },
  { LUA_JITLIBNAME, luaopen_jit }, { NULL, NULL }
};

static const luaL_Reg lj_lib_preload[] = {
  { LUA_FFILIBNAME, luaopen_ffi },
  { "lsqlite3", luaopen_lsqlite3 }, { "cjson", luaopen_cjson }, { "lfs", luaopen_lfs },
  { "rex_pcre2", luaopen_rex_pcre2 }, { "lua-utf8", luaopen_utf8 }, { "argparse", luaopen_argparse },
  { "posix.fcntl", luaopen_posix_fcntl }, { "posix.fnmatch", luaopen_posix_fnmatch },
  { "posix.glob", luaopen_posix_glob }, { "posix.poll", luaopen_posix_poll },
  { "posix.signal", luaopen_posix_signal }, { "posix.stdlib", luaopen_posix_stdlib },
  { "posix.sys.stat", luaopen_posix_sys_stat },
  { "posix.sys.wait", luaopen_posix_sys_wait }, { "posix.time", luaopen_posix_time },
  { "posix.unistd", luaopen_posix_unistd },
  { NULL, NULL }
};

LUALIB_API void luaL_openlibs(lua_State *L)
{
  const luaL_Reg *lib;
  for (lib = lj_lib_load; lib->func; lib++) {
    lua_pushcfunction(L, lib->func);
    lua_pushstring(L, lib->name);
    lua_call(L, 1, 0);
  }
  luaL_findtable(L, LUA_REGISTRYINDEX, "_PRELOAD", sizeof(lj_lib_preload)/sizeof(lj_lib_preload[0])-1);
  for (lib = lj_lib_preload; lib->func; lib++) {
    lua_pushcfunction(L, lib->func);
    lua_setfield(L, -2, lib->name);
  }
  lua_pop(L, 1);
  lua_pushliteral(L, SWARM_RUNTIME);  /* the runtime version the launcher checks */
  lua_setglobal(L, "SWARM_RUNTIME");
}
