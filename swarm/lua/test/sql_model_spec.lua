-- The SQL semantics (swarm/model/SwarmModel/Sql.lean) against real sqlite: each case from SqlCases.lean is tables,
-- statements with their `?` values, and what Lean says each does; here the same statements run through db.lua
-- (prepare, all_cols, exec, script) on those tables, and the rows, column names, changes(), last_insert_rowid(),
-- errors and the tables after must agree. Rows Lean puts in one tie group (equal ORDER BY keys, or no ORDER BY)
-- compare as multisets; a group LIMIT cut compares by count.
-- And the corpus is the code's: its statements are exactly sql_inventory.lua's, read from swarm/lua/swarm now.
-- Cases: $SWARM_MODEL_SQL, else the committed swarm/model/sqlcases.json.gz (swarm/model/replay.sh makes fresh ones).
local db = require "swarm.db"
local json = require("cjson").new()  -- NULL stays json.null: an array of values keeps its length
local sqlite3 = require "lsqlite3"
local inv = require "test.sql_inventory"
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local file = os.getenv("SWARM_MODEL_SQL") or (here .. "/../../model/sqlcases.json.gz")
local h = assert(io.popen((file:match("%.gz$") and "gzip -dc '" or "cat '") .. file .. "'"))
local data = json.decode(h:read("*a"))
h:close()
assert(data and #data.cases > 0, "no cases in " .. file)

-- the corpus covers exactly the statements in the source
local have, want = {}, {}
for _, s in ipairs(data.statements) do have[s] = true end
for _, x in ipairs(inv.inventory()) do
  local s = x.sql:gsub("\n", " ")
  want[s] = true
  assert(have[s], ("%s: no cases for %q; regenerate swarm/model/sqlcases.json.gz (swarm/model/README.md, Running)"):format(x.site, s))
end
for s in pairs(have) do assert(want[s], ("stale cases for %q, a statement no longer in the source"):format(s)) end

local function val(v)  -- Lean's value as Lua sees it
  if v == json.null then return nil end
  if type(v) == "table" then return v.r end
  return v
end

local function show(v)
  if v == nil then return "NULL" end
  if type(v) == "number" then return ("%.17g"):format(v) end
  return ("%q"):format(v)
end

local function canon(names, getter)  -- a row as text: name=value, by name, the last of a name (get_named_values)
  local m, ks = {}, {}
  for i, n in ipairs(names) do
    if m[n] == nil and not ks[n] then ks[#ks + 1] = n end
    ks[n] = true
    m[n] = { getter(i, n) }
  end
  local r = {}
  for _, n in ipairs(ks) do r[#r + 1] = n .. "=" .. show(m[n][1]) end
  table.sort(r)
  return table.concat(r, " ")
end

local function bag(xs)
  local c = {}
  for _, x in ipairs(xs) do c[x] = (c[x] or 0) + 1 end
  return c
end

local function same_bag(a, b)
  local x, y = bag(a), bag(b)
  for k, n in pairs(x) do if y[k] ~= n then return false end end
  for k, n in pairs(y) do if x[k] ~= n then return false end end
  return true
end

local function typed(v)  -- a stored value as text with its storage class
  if v == json.null then return "null" end
  if type(v) == "table" then return "real:" .. ("%.17g"):format(v.r) end
  if type(v) == "number" then return "integer:" .. ("%d"):format(v) end
  return "text:" .. ("%q"):format(v)
end

local dir = os.tmpname()
os.remove(dir)
assert(os.execute("mkdir -p '" .. dir .. "'") == 0 or true)
local p = dir .. "/sql.db"

local function setup(k)
  local s = assert(sqlite3.open(p))
  s:exec("pragma synchronous=off")  -- a scratch db: no fsync per case
  local old = {}
  for r in s:nrows("select name from sqlite_master where type='table' and name not like 'sqlite_%'") do old[#old + 1] = r.name end
  for _, t in ipairs(old) do assert(s:exec("drop table " .. t) == sqlite3.OK, s:errmsg()) end
  s:exec("delete from sqlite_sequence")
  for _, t in ipairs(k.tables) do
    assert(s:exec(t.ddl) == sqlite3.OK, s:errmsg())
    for _, r in ipairs(t.rows) do
      local q, binds = {}, {}
      for i, v in ipairs(r) do
        if v == json.null then q[i] = "null"
        elseif type(v) == "number" then q[i] = ("%d"):format(v)
        else q[i] = "?"; binds[#binds + 1] = val(v) end
      end
      local st = assert(s:prepare(("insert into %s values(%s)"):format(t.name, table.concat(q, ","))), s:errmsg())
      for i, b in ipairs(binds) do st:bind(i, b) end
      assert(st:step() == sqlite3.DONE, s:errmsg())
      st:finalize()
    end
    if t.seq and t.seq > 0 then
      assert(s:exec(("delete from sqlite_sequence where name='%s'; insert into sqlite_sequence(name,seq) values('%s',%d)")
        :format(t.name, t.name, t.seq)) == sqlite3.OK, s:errmsg())
    end
  end
  s:close()
end

local function final(c)
  local r = {}
  for _, t in ipairs(c:all("select name from sqlite_master where type='table' and name not like 'sqlite_%'")) do
    local info = c:all("pragma table_info(" .. t.name .. ")")
    local cols, sel = {}, {}
    for _, x in ipairs(info) do
      cols[#cols + 1] = { x.cid, x.name, x.type, x.notnull, x.dflt_value, x.pk }
      sel[#sel + 1] = "typeof(" .. x.name .. ") t" .. x.cid .. ", " .. x.name .. " v" .. x.cid
    end
    local rows = {}
    for _, x in ipairs(c:all("select " .. table.concat(sel, ", ") .. " from " .. t.name)) do
      local cells = {}
      for i = 0, #info - 1 do
        local ty, v = x["t" .. i], x["v" .. i]
        cells[#cells + 1] = ty == "null" and "null" or ty == "real" and "real:" .. ("%.17g"):format(v)
          or ty == "integer" and "integer:" .. ("%d"):format(v) or ty .. ":" .. ("%q"):format(v)
      end
      rows[#rows + 1] = table.concat(cells, "|")
    end
    local sq = c:one("select 1 from sqlite_master where name='sqlite_sequence'")
      and c:one("select seq from sqlite_sequence where name=?", t.name)
    r[t.name] = { info = cols, rows = rows, seq = sq and sq.seq or 0 }
  end
  return r
end

local runs, errs = 0, 0
for i, k in ipairs(data.cases) do
  setup(k)
  local c = db.open_at(p, "")
  c:script("pragma synchronous=off")
  local function fail(what, ...)
    local steps = {}
    for _, s in ipairs(k.steps) do steps[#steps + 1] = s.sql .. "  " .. json.encode(s.params) end
    error(("case %d (%s): %s\n  steps: %s\n  tables: %s"):format(i, k.sites, what:format(...),
      table.concat(steps, "\n         "), json.encode(k.tables)), 0)
  end
  for j, st in ipairs(k.steps) do
    local ps, n = {}, #st.params
    for x = 1, n do ps[x] = val(st.params[x]) end
    local word = st.sql:match("^%s*(%a+)"):lower()
    local ok, res = pcall(function()
      if st.script or word == "begin" or word == "commit" or word == "rollback" then c:script(st.sql); return {}
      elseif word == "select" or word == "pragma" or st.sql:find(" returning ") then
        local rows, names = c:all_cols(st.sql, unpack(ps, 1, n))
        return { rows = rows, names = names }
      else c:exec(st.sql, unpack(ps, 1, n)); return {} end
    end)
    local want = k.out[j]
    if want.err then
      errs = errs + 1
      if ok then fail("step %d: Lean refuses it (%s), sqlite ran it", j, want.err) end
    else
      if not ok then fail("step %d: sqlite refuses it (%s), Lean ran it", j, tostring(res)) end
      runs = runs + 1
      if c.h:changes() ~= want.changes then fail("step %d: changes() %d, Lean %d", j, c.h:changes(), want.changes) end
      if want.last ~= json.null and c.h:last_insert_rowid() ~= want.last then
        fail("step %d: last_insert_rowid() %d, Lean %d", j, c.h:last_insert_rowid(), want.last)
      end
      if res.rows then
        if table.concat(res.names, ",") ~= table.concat(want.names, ",") then
          fail("step %d: columns %s, Lean %s", j, table.concat(res.names, ","), table.concat(want.names, ","))
        end
        if #res.rows ~= #want.rows then fail("step %d: %d rows, Lean %d", j, #res.rows, #want.rows) end
        local g1, g2, last = {}, {}, -1
        for x, r in ipairs(want.rows) do
          local g = want.grps[x]
          last = math.max(last, g)
          g1[g] = g1[g] or {}; g2[g] = g2[g] or {}
          table.insert(g1[g], canon(want.names, function(y) return val(r[y]) end))
          table.insert(g2[g], canon(res.names, function(_, nm) return res.rows[x][nm] end))
        end
        for g = 0, last do
          if not (want.cut and g == last) and not same_bag(g1[g], g2[g]) then
            fail("step %d: rows\n    %s\n  Lean\n    %s", j, table.concat(g2[g], "\n    "), table.concat(g1[g], "\n    "))
          end
        end
      end
    end
  end
  local got = final(c)
  c.h:close()
  for _, t in ipairs(k.final) do
    local g = got[t.name] or fail("table %s is gone", t.name)
    local wi, gi = {}, {}
    for _, x in ipairs(t.info) do wi[#wi + 1] = table.concat({ x[1], x[2], x[3], x[4], tostring(val(x[5])), x[6] }, " ") end
    for _, x in ipairs(g.info) do gi[#gi + 1] = table.concat({ x[1], x[2], x[3], x[4], tostring(x[5]), x[6] }, " ") end
    if table.concat(wi, "; ") ~= table.concat(gi, "; ") then
      fail("table %s's columns:\n    %s\n  Lean\n    %s", t.name, table.concat(gi, "; "), table.concat(wi, "; "))
    end
    local wr = {}
    for _, r in ipairs(t.rows) do
      local cells = {}
      for x = 1, #t.info do cells[x] = typed(r[x]) end
      wr[#wr + 1] = table.concat(cells, "|")
    end
    if not same_bag(wr, g.rows) then
      fail("table %s after:\n    %s\n  Lean\n    %s", t.name, table.concat(g.rows, "\n    "), table.concat(wr, "\n    "))
    end
    if g.seq ~= t.seq then fail("table %s: sqlite_sequence %d, Lean %d", t.name, g.seq, t.seq) end
    got[t.name] = nil
  end
  if next(got) then fail("table %s isn't Lean's", next(got)) end
end
for _, f in ipairs({ p, p .. "-wal", p .. "-shm" }) do os.remove(f) end
os.remove(dir)
-- not one-sided
assert(runs > #data.cases / 2 and errs > 0, ("%d cases: %d steps ran, %d refused"):format(#data.cases, runs, errs))
