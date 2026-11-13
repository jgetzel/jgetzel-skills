-- die/exit, time formats, strings (split, strip, utf8 cut), shlex.
local utf8 = require "lua-utf8"
local M = {}

-- die and exit unwind as error({exit = code}) so db.tx rolls back; main turns it into os.exit (sw-lua §2).
function M.exit(code)
  error({ exit = code or 0 }, 0)
end

function M.die(msg, code)
  io.stderr:write("swarm: " .. msg .. "\n")
  M.exit(code or 1)
end

function M.now()
  return os.time()
end

function M.d(n)  -- an integer as text: tostring(1e15) is "1e+15"
  return ("%d"):format(n)
end

function M.ago(t)
  local s = math.max(0, M.now() - (t or 0))
  if s >= 3600 then
    return ("%dh%02dm"):format(math.floor(s / 3600), math.floor(s % 3600 / 60))
  end
  return ("%dm"):format(math.floor(s / 60))
end

function M.hhmm(t)
  return os.date("%H:%M", t)
end

function M.dur(s)
  local n, u = s:match("^(%d+)([smh]?)$")
  if not n then
    M.die(("bad duration '%s' (use 90s, 30m, 2h)"):format(s))
  end
  return tonumber(n) * ({ s = 1, m = 60, h = 3600, [""] = 1 })[u]
end

function M.strip(s)
  return (s:gsub("^%s+", ""):gsub("%s+$", ""))
end

-- Python s.split(sep); no sep splits on runs of whitespace and drops empty ends.
function M.split(s, sep)
  local r = {}
  if not sep then
    for w in s:gmatch("%S+") do r[#r + 1] = w end
    return r
  end
  local i = 1
  while true do
    local j = s:find(sep, i, true)
    if not j then
      r[#r + 1] = s:sub(i)
      return r
    end
    r[#r + 1] = s:sub(i, j - 1)
    i = j + #sep
  end
end

function M.splitlines(s)  -- shortcut: \n only (no \r), as git and the db write
  local r = {}
  s = s or ""
  if s ~= "" and s:sub(-1) ~= "\n" then s = s .. "\n" end
  for l in s:gmatch("([^\n]*)\n") do r[#r + 1] = l end
  return r
end

function M.startswith(s, p)
  return s:sub(1, #p) == p
end

function M.endswith(s, p)
  return p == "" or s:sub(-#p) == p
end

-- Python s[:n] on characters: a byte cut can split a UTF-8 character and write invalid text.
function M.cut(s, n)
  return utf8.sub(s, 1, n)
end

function M.basename(p)
  return p:match("[^/]*$")
end

function M.dirname(p)
  local d = p:match("^(.*)/[^/]*$")
  return d == nil and "" or (d == "" and "/" or d)
end

function M.join(...)  -- os.path.join
  local r = ""
  for _, p in ipairs({ ... }) do
    if p:sub(1, 1) == "/" or r == "" then r = p
    elseif r:sub(-1) == "/" then r = r .. p
    else r = r .. "/" .. p end
  end
  return r
end

function M.shquote(s)
  if s ~= "" and not s:find("[^%w@%%+=:,./_-]") then return s end
  return "'" .. s:gsub("'", "'\"'\"'") .. "'"
end

function M.shjoin(argv)
  local r = {}
  for i, a in ipairs(argv) do r[i] = M.shquote(a) end
  return table.concat(r, " ")
end

function M.slurp(path)  -- file contents, or nil; "-" reads stdin
  if path == "-" then return io.stdin:read("*a") end
  local f = io.open(path, "rb")
  if not f then return nil end
  local s = f:read("*a")
  f:close()
  return s
end

return M
