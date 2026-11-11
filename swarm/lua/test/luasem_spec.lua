-- The Lean semantics of our Lua subset (swarm/model/SwarmModel/Lua) against LuaJIT: random chunks from
-- SwarmModel/LuaCases.lean, each with the Lean interpreter's results, which LuaJIT must give too (luasem.lua writes
-- both sides' results alike). Cases: $SWARM_LUASEM_CASES, else the committed swarm/model/luasem.json.gz
-- (swarm/model/replay.sh makes fresh ones).
local json, luasem = require "swarm.json", require "test.luasem"
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local file = os.getenv("SWARM_LUASEM_CASES") or (here .. "/../../model/luasem.json.gz")
local h = assert(io.popen((file:match("%.gz$") and "gzip -dc '" or "cat '") .. file .. "'"))
local cases = json.decode(h:read("*a")).cases
h:close()
assert(#cases > 0, "no cases in " .. file)

local bad, errs = {}, 0
for i, k in ipairs(cases) do
  local got = luasem.run(k.src)
  if got ~= k.out then bad[#bad + 1] = ("case %d:\n%s\n  LuaJIT: %s\n  Lean:   %s"):format(i, k.src, got, k.out) end
  if k.out == "error" then errs = errs + 1 end
end
if #bad > 0 then error(("%d of %d cases differ; the first:\n%s"):format(#bad, #cases, table.concat(bad, "\n", 1, math.min(3, #bad))), 0) end
-- the cases must mostly run
assert(errs < #cases / 4, ("%d of %d cases end in an error"):format(errs, #cases))
