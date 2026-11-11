-- locks.lua's lock patterns against the Lean model's (swarm/model/SwarmModel/Glob.lean): random patterns and paths
-- from SwarmModel/GlobCases.lean, each with Lean's tokens, covers and overlaps, which the Lua must give too; and the
-- glob semantics (Glob.gm) against fnmatch on tame patterns, where both read a pattern alike.
-- Cases: $SWARM_MODEL_GLOBS, else the committed swarm/model/globs.json.gz (swarm/model/replay.sh makes fresh ones).
local json, locks = require "swarm.json", require "swarm.locks"
local fnmatch = require "posix.fnmatch"
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local file = os.getenv("SWARM_MODEL_GLOBS") or (here .. "/../../model/globs.json.gz")
local h = assert(io.popen((file:match("%.gz$") and "gzip -dc '" or "cat '") .. file .. "'"))
local cases = json.decode(h:read("*a")).cases
h:close()
assert(#cases > 0, "no cases in " .. file)

local function show(t)  -- tokens as text: * ? c [set]
  local r = {}
  for _, k in ipairs(t) do r[#r + 1] = type(k) == "string" and k or k.c and ("'" .. k.c .. "'") or ("[" .. k.set .. "]") end
  return table.concat(r, " ")
end

local ov, cov = 0, 0
for i, k in ipairs(cases) do
  local function check(what, got, want)
    if got ~= want then
      error(("case %d (p %q, q %q, x %q): %s: Lua has %s, Lean has %s"):format(i, k.p, k.q, k.x, what,
        tostring(got), tostring(want)), 0)
    end
  end
  check("tokens", show(locks.tokens(k.p)), show(k.tok))
  check("covers", locks.covers(k.x, k.p), k.cov)
  check("overlaps", locks.overlaps(k.p, k.q), k.ov)
  if k.tame then check("fnmatch vs gm", fnmatch.fnmatch(k.p, k.x, 0) == 0, k.gm) end
  if k.ov then ov = ov + 1 end
  if k.cov then cov = cov + 1 end
end
-- the cases must not be one-sided
assert(ov > #cases / 10 and ov < #cases * 9 / 10 and cov > #cases / 10 and cov < #cases * 9 / 10,
  ("%d cases: %d overlap, %d cover"):format(#cases, ov, cov))
