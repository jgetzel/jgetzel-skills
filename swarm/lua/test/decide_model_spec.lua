-- The Lua's pure decisions against their lifts in the Lean model (swarm/model/SwarmModel/Decide.lean): random inputs
-- from SwarmModel/DecideCases.lean, each with Lean's answer, which watchd.keeps, watchd.fate, msgs.wakes and ci.pr_act
-- must give.
-- Cases: $SWARM_MODEL_DECIDE, else the committed swarm/model/decide.json.gz (swarm/model/replay.sh makes fresh ones).
local json, watchd, msgs, ci = require "swarm.json", require "swarm.watchd", require "swarm.msgs", require "swarm.ci"
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local file = os.getenv("SWARM_MODEL_DECIDE") or (here .. "/../../model/decide.json.gz")
local h = assert(io.popen((file:match("%.gz$") and "gzip -dc '" or "cat '") .. file .. "'"))
local cases = json.decode(h:read("*a"))
h:close()
assert(#cases.keeps > 0 and #cases.fate > 0 and #cases.wakes > 0 and #cases.pr > 0, "no cases in " .. file)

local function check(what, i, k, got, want)
  if got ~= want then
    error(("%s case %d (%s): Lua has %s, Lean has %s"):format(what, i, json.encode(k), tostring(got), tostring(want)), 0)
  end
end
local function const(v) return function() return v end end
local function set(l)
  if not l then return nil end
  local s = {}
  for _, x in ipairs(l) do s[x] = true end
  return s
end

local seen = {}
for i, k in ipairs(cases.keeps) do
  local r = watchd.keeps(k.o, k.bg, set(k.live))
  check("keeps", i, k, r and true or false, k.r)
  seen["keeps " .. tostring(k.r)] = true
end
-- F1 (Decide.lean fateRec): what fate's recorder hears, plain and with f.all, is Lean's list of checks and values
local function recorded(k, all)
  local f, got = k.f, {}
  local v = watchd.fate(k.a, k.t, k.x, k.terms, { ours = const(f.ours), claims = const(f.claims), locks = const(f.locks),
    unlanded = const(f.unlanded), job = const(f.job), pool = f.pool, passed_over = const(f.passed_over), alive = const(f.alive),
    all = all, rec = function(label, h) got[#got + 1] = label .. "=" .. tostring(h) end })
  return v, table.concat(got, " ")
end
local function want(l)
  local r = {}
  for i, p in ipairs(l) do r[i] = p[1] .. "=" .. tostring(p[2]) end
  return table.concat(r, " ")
end
for i, k in ipairs(cases.fate) do
  local v, rec = recorded(k, false)
  check("fate", i, k, v, k.r)
  check("fate rec", i, k, rec, want(k.rec))
  check("fate rec all", i, k, select(2, recorded(k, true)), want(k.all))
  seen["fate " .. tostring(k.r)] = true
end
for i, k in ipairs(cases.wakes) do
  local w, u = msgs.wakes(k.rows, const(k.cold))
  check("wakes", i, k, w and #w or nil, k.r and k.r.n)
  if w then check("wakes urgent", i, k, u, k.r.urgent) end
  seen["wakes " .. tostring(k.r ~= nil)] = true
end
for i, k in ipairs(cases.pr) do
  local r = ci.pr_act(k.pr, k.gated, k.told)
  check("pr_act", i, k, r, k.r)
  seen["pr " .. tostring(k.r)] = true
end
-- every answer turns up
for _, s in ipairs({ "keeps true", "keeps false", "fate nil", "fate unclean", "fate reuse", "fate end", "wakes true", "wakes false",
    "pr nil", "pr done", "pr wake" }) do
  assert(seen[s], "no case answers " .. s)
end
