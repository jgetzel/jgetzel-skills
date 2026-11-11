-- Every SQL statement swarm/lua/swarm hands sqlite, read from the source: each db call (`:exec(`, `:one(`, `:all(`,
-- `:all_cols(`, `:script(`) whose first argument is string literals joined by `..` is its text; one with code in it
-- (a column name, a `?` list, a `:format`) is a template, and DYNAMIC lists the statements it can be.
-- M.inventory() -> { {site="tasks.lua:233", sql="..."}, ... } (one row per statement per site), M.templates() too.
-- `luajit swarm/lua/test/sql_inventory.lua` prints the statements, one per line, for SqlCases.lean.
local M = {}
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local src = here .. "/../swarm"
local main = arg and arg[0] and arg[0]:match("sql_inventory%.lua$")
if main then
  local tree = (os.getenv("XDG_DATA_HOME") or ((os.getenv("HOME") or "") .. "/.local/share")) .. "/swarm/lua"
  package.path = here .. "/../?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. package.path
  package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
end

local KINDS = "'task-add','claim','spawn','done','block','unblock','release','drop'"  -- tasks.TASK_KINDS
local function qs(n) local r = {} for i = 1, n do r[i] = "?" end return table.concat(r, ",") end
local function each(xs, f) local r = {} for _, x in ipairs(xs) do r[#r + 1] = f(x) end return r end

-- template (holes as «code») -> the statements it can be
M.DYNAMIC = {
  -- agents.touch's kw keys: set_status (status, last_active, ctx_tokens), msgs.wait (status), hook (claude_pid, compacted_at)
  ["update agent set «k»=? where name=? and ended is null and (hc is null or hc is ?)"] =
    each({ "status", "last_active", "ctx_tokens", "claude_pid", "compacted_at" }, function(k)
      return "update agent set " .. k .. "=? where name=? and ended is null and (hc is null or hc is ?)" end),
  ["update agent set «col»=null where name=?"] = { "update agent set ctx_tokens=null where name=?" },
  ["select ts,agent,kind,data from event where kind in ('«table.concat(M.TASK_KINDS, \"','\")»') order by id"] =
    { "select ts,agent,kind,data from event where kind in (" .. KINDS .. ") order by id" },
  ["select * from task where id in («table.concat(q, \",\")») and state!='done'"] =
    each({ 1, 2, 3 }, function(n) return "select * from task where id in (" .. qs(n) .. ") and state!='done'" end),
  ["update task set lease_until=?«mine»"] = { "update task set lease_until=? where id=? and owner=? and state='claimed'" },
  ["update task set evidence=?«mine»"] = { "update task set evidence=? where id=? and owner=? and state='claimed'" },
  ["update task set state='done', evidence=?, lease_until=null, done_at=?, done_ctx=(select ctx_tokens from agent where name=?)«mine»"] =
    { "update task set state='done', evidence=?, lease_until=null, done_at=?, done_ctx=(select ctx_tokens from agent where name=?)"
      .. " where id=? and owner=? and state='claimed'" },
  ["select * from task «(a.all and \"\" or \"where state in ('open','claimed','blocked') \")»order by title like '«M.RED_TASK»%' and state!='done' desc, id"] =
    { "select * from task order by title like 'main red: %' and state!='done' desc, id",
      "select * from task where state in ('open','claimed','blocked') order by title like 'main red: %' and state!='done' desc, id" },
  ["select kind from event where kind in (%s) order by id desc limit 1"] =  -- watchd.last_event: two kinds
    { "select kind from event where kind in (?,?) order by id desc limit 1" },
  ["select repo,key,count(*) n,max(peak_kb) peak,max(cpu_s) cpu,max(wall_s) wall from cmd %s group by repo,key order by max(%s) desc limit 5"] =
    (function()
      local r = {}
      for _, w in ipairs({ "where machine=?", "where machine=? and repo=?" }) do
        for _, by in ipairs({ "peak_kb", "cpu_s" }) do
          r[#r + 1] = "select repo,key,count(*) n,max(peak_kb) peak,max(cpu_s) cpu,max(wall_s) wall from cmd " .. w
            .. " group by repo,key order by max(" .. by .. ") desc limit 5"
        end
      end
      return r
    end)(),
  -- db.connect: the column migrations (db.COLUMNS) and table_info of the tables they touch
  ["alter table %s add column %s"] = (function()
    local db = require "swarm.db"
    return each(db.COLUMNS, function(tc) return ("alter table %s add column %s"):format(tc[1], tc[2]) end)
  end)(),
  ["pragma table_info(«tbl»)"] = each({ "agent", "lock", "task", "ci" }, function(t) return "pragma table_info(" .. t .. ")" end),
  -- the schemas: db.SCHEMA and cost.SCHEMA, each a script of create statements
  ["«M.SCHEMA»"] = { (require "swarm.db").SCHEMA },
  ["«schema»"] = { (require "swarm.cost").SCHEMA },
}

-- the Lua string literal starting at s[i] (a quote or [[): its value and the index after it
local function literal(s, i)
  local q = s:sub(i, i)
  if q == "[" then
    local eq = s:match("^%[(=*)%[", i)
    local close = "]" .. eq .. "]"
    local e = s:find(close, i, true)
    local body = s:sub(i + #eq + 2, e - 1):gsub("^\n", "")
    return body, e + #close
  end
  local out, j = {}, i + 1
  while true do
    local ch = s:sub(j, j)
    if ch == q then return table.concat(out), j + 1 end
    if ch == "\\" then
      local n = s:sub(j + 1, j + 1)
      out[#out + 1] = ({ n = "\n", t = "\t", ["\\"] = "\\", ['"'] = '"', ["'"] = "'" })[n] or error("escape \\" .. n)
      j = j + 2
    else
      out[#out + 1] = ch
      j = j + 1
    end
  end
end

-- the first argument of the call whose `(` is at s[i]: its literal text, holes as «code»; and whether it has holes
local first_arg
function first_arg(s, i)
  local open = s:match("^%s*()%(", i + 1)
  if open then return (first_arg(s, open)), true end  -- ("..."):format(...)
  local parts, holes, depth, j, code = {}, false, 0, i + 1, {}
  local function flush()
    local c = table.concat(code):gsub("^%s+", ""):gsub("%s+$", ""):gsub("^%.%.", ""):gsub("%.%.$", "")
      :gsub("^%s+", ""):gsub("%s+$", "")
    if c ~= "" and c ~= "(" and c ~= ")" then parts[#parts + 1] = "«" .. c .. "»"; holes = true end
    code = {}
  end
  while j <= #s do
    local ch = s:sub(j, j)
    if ch == '"' or ch == "'" or (ch == "[" and s:match("^%[=*%[", j)) then
      local v, k = literal(s, j)
      if depth > 0 then code[#code + 1] = s:sub(j, k - 1)  -- a literal inside code is code
      else flush(); parts[#parts + 1] = v end
      j = k
    elseif ch == "-" and s:sub(j, j + 1) == "--" and depth == 0 then
      j = s:find("\n", j) or #s + 1
    elseif ch == "(" or ch == "{" then depth = depth + 1; code[#code + 1] = ch; j = j + 1
    elseif ch == ")" or ch == "}" then
      if depth == 0 then break end
      depth = depth - 1; code[#code + 1] = ch; j = j + 1
    elseif ch == "," and depth == 0 then break
    else
      if ch == ":" and s:match("^:format%(", j) and depth == 0 then break end  -- a format's args are not the template
      if not ch:match("%s") or #code > 0 then code[#code + 1] = ch end
      j = j + 1
    end
  end
  flush()
  return table.concat(parts), holes
end

local CALL = { "exec", "one", "all", "all_cols", "script" }

function M.templates()
  local lfs = require "lfs"
  local files = {}
  for f in lfs.dir(src) do if f:match("%.lua$") then files[#files + 1] = f end end
  table.sort(files)
  local r = {}
  for _, f in ipairs(files) do
    local h = assert(io.open(src .. "/" .. f))
    local s = h:read("*a")
    h:close()
    for _, call in ipairs(CALL) do
      local pos = 1
      while true do
        local a, b = s:find(":" .. call .. "%(", pos)
        if not a then break end
        pos = b + 1
        local line = select(2, s:sub(1, a):gsub("\n", "")) + 1
        local def = s:sub(1, a):match("function [%w_.]*$")
        local recv = s:sub(1, a - 1):match("([%w_]+)$")
        local tpl, holes = first_arg(s, b)
        -- not a statement: db.lua's wrappers passing `sql` on, a regex's exec
        if not def and recv ~= "r" and not (f == "db.lua" and tpl == "«sql»") then
          r[#r + 1] = { site = f .. ":" .. line, tpl = (tpl:gsub("%s*\n%s*", " ")), dynamic = holes or tpl:find("%%s") ~= nil }
        end
      end
    end
  end
  table.sort(r, function(x, y) return x.site < y.site end)
  return r
end

function M.inventory()
  local r = {}
  for _, t in ipairs(M.templates()) do
    if t.dynamic then
      for _, s in ipairs(M.DYNAMIC[t.tpl] or error("no DYNAMIC entry for " .. t.site .. ": " .. t.tpl)) do
        r[#r + 1] = { site = t.site, sql = s }
      end
    else
      r[#r + 1] = { site = t.site, sql = t.tpl }
    end
  end
  return r
end

if main then
  for _, x in ipairs(M.inventory()) do print(x.site .. "\t" .. (x.sql:gsub("\n", " "))) end
end

return M
