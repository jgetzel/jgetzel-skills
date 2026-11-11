-- swarm/model/SwarmModel/LockSrc.lean (locks.lua and util.lua as syntax trees, which LockProof.lean is about) must be
-- from the sources as they are: its checksums are LuaDump.lean's, over the bytes. Regenerate: swarm/model/gen-lock-src.sh
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
