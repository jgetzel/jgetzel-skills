-- What luasem_spec.lua compares with the Lean interpreter (swarm/model/SwarmModel/Lua/Run.lean): a chunk's results
-- as text, `ok:` and each value, or `error`. Strings: bytes 32..126 but " and \ as themselves, the rest \ddd;
-- numbers %.17g; a table's entries sorted; one already on the path <cycle>.
local M = {}

local function str(s)
  return '"' .. s:gsub('[%z\1-\31"\\\127-\255]', function(c) return ("\\%03d"):format(c:byte()) end) .. '"'
end

local function ser(v, path, depth)
  local t = type(v)
  if depth >= 100 then return "<deep>" end
  if t == "nil" or t == "boolean" then return tostring(v) end
  if t == "number" then return ("%.17g"):format(v) end
  if t == "string" then return str(v) end
  if t == "table" then
    if path[v] then return "<cycle>" end
    path[v] = true
    local es = {}
    for k, x in pairs(v) do es[#es + 1] = ser(k, path, depth + 1) .. "=" .. ser(x, path, depth + 1) end
    path[v] = nil
    table.sort(es)
    return "{" .. table.concat(es, ",") .. "}"
  end
  if t == "function" then return "function" end
  return "userdata"
end

function M.outcome(ok, ...)
  if not ok then return "error" end
  local r = {}
  for i = 1, select("#", ...) do r[i] = ser((select(i, ...)), {}, 0) end
  return "ok:" .. table.concat(r, ",")
end

-- src's results under LuaJIT, as text
function M.run(src)
  local f, err = loadstring(src, "=c")
  if not f then return "parse error: " .. err end
  return M.outcome(pcall(f))
end

-- luajit luasem.lua <file.lua>...: each chunk's results
if arg and arg[0] and arg[0]:match("luasem%.lua$") then
  local dir = arg[0]:match("^(.*)/[^/]*$") or "."
  local tree = (os.getenv("XDG_DATA_HOME") or ((os.getenv("HOME") or "") .. "/.local/share")) .. "/swarm/lua"
  package.path = dir .. "/../?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. package.path  -- as run.lua does
  package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
  for i = 1, #arg do
    local h = assert(io.open(arg[i], "rb")); local src = h:read("*a"); h:close()
    print(arg[i] .. ": " .. M.run(src))
  end
end

return M
