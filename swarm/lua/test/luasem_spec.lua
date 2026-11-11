-- lua-lean's Lean semantics of Lua (../../../lua-lean) against LuaJIT, on random chunks from
-- swarm/model/SwarmModel/LuaCases.lean, among them calls of util.lua, locks.lua and difflib.lua, each with the Lean
-- interpreter's results, which LuaJIT must give too (lua-lean/test/luasem.lua). Cases: $SWARM_LUASEM_CASES, else the
-- committed swarm/model/luasem.lua.gz (swarm/model/replay.sh makes fresh ones).
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local luasem = dofile(here .. "/../../../lua-lean/test/luasem.lua")
luasem.check(os.getenv("SWARM_LUASEM_CASES") or (here .. "/../../model/luasem.lua.gz"))
