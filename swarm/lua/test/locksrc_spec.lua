-- swarm/model/SwarmModel/LockSrc.lean (locks.lua and util.lua as syntax trees) and SwarmModel/Lifted/*.lean (locks.lua
-- and tasks.lua lifted, board #31; watchd.lua's M.loop and iteration, boards #67 and #75) must be from the sources as they are: their checksums are lua-lean's
-- LuaLean/Show.lean's, over the bytes. Regenerate: swarm/model/gen-lock-src.sh, swarm/model/lift.sh
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local function slurp(p) local f = assert(io.open(p, "rb")); local s = f:read("*a"); f:close(); return s end
local function checksum(s)
  local h = 7
  for i = 1, #s do h = (h * 31 + s:byte(i)) % 4294967296 end
  return h
end
local gen = slurp(here .. "/../../model/SwarmModel/LockSrc.lean")
for name, file in pairs({ Locks = "locks.lua", Util = "util.lua" }) do
  local want = ("-- checksum %s %d\n"):format(name, checksum(slurp(here .. "/../swarm/" .. file)))
  assert(gen:find(want, 1, true), ("LockSrc.lean is stale for %s: run swarm/model/gen-lock-src.sh"):format(file))
end
for name, file in pairs({ Locks = "locks.lua", Tasks = "tasks.lua", Watchd = "watchd.lua" }) do
  local gen = slurp(here .. "/../../model/SwarmModel/Lifted/" .. name .. ".lean")
  local want = ("-- checksum Swarm.Lifted.%s %d"):format(name, checksum(slurp(here .. "/../swarm/" .. file)))
  assert(gen:find(want, 1, true), ("Lifted/%s.lean is stale: run swarm/model/lift.sh"):format(name))
end
