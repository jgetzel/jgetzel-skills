-- Shared helpers for the harness-retro tools (LuaJIT). Each tool puts this dir and ../swarm/lua on package.path.
local utf8 = require "lua-utf8"
local lfs = require "lfs"
local unistd = require "posix.unistd"
local M = {}

M.HOME = os.getenv("HOME") or ""

function M.read(path)  -- file text with invalid UTF-8 replaced (Python's errors="replace"), or nil
  local f = io.open(path, "rb")
  if not f then return nil end
  local s = f:read("*a")
  f:close()
  return utf8.clean(s)
end

function M.mode(p) return lfs.attributes(p, "mode") end
function M.isfile(p) return M.mode(p) == "file" end

function M.plain_replace(s, old, new)  -- str.replace
  if old == "" then return s end
  local out, i = {}, 1
  while true do
    local a, b = s:find(old, i, true)
    if not a then break end
    out[#out + 1] = s:sub(i, a - 1) .. new
    i = b + 1
  end
  out[#out + 1] = s:sub(i)
  return table.concat(out)
end

function M.expanduser(p)
  if p == "~" or p:sub(1, 2) == "~/" then return M.HOME .. p:sub(2) end
  return p
end

function M.normpath(p)
  local abs, out = p:sub(1, 1) == "/", {}
  for c in p:gmatch("[^/]+") do
    if c == ".." then
      if #out > 0 and out[#out] ~= ".." then out[#out] = nil elseif not abs then out[#out + 1] = c end
    elseif c ~= "." then
      out[#out + 1] = c
    end
  end
  local r = (abs and "/" or "") .. table.concat(out, "/")
  return r == "" and "." or r
end

-- os.path.realpath: symlinks resolved as far as the path exists, the rest normalised lexically.
function M.realpath(p)
  if p:sub(1, 1) ~= "/" then p = unistd.getcwd() .. "/" .. p end
  p = M.normpath(p)
  local rest = {}
  while true do
    local r = require("posix.stdlib").realpath(p)
    if r then
      for i = #rest, 1, -1 do r = (r == "/" and "" or r) .. "/" .. rest[i] end
      return r
    end
    if p == "/" then return p end
    table.insert(rest, p:match("[^/]*$"))
    p = p:match("^(.*)/[^/]*$"); if p == "" then p = "/" end
  end
end

-- Files under dir (recursive, hidden names skipped, as glob's **) whose name ends in ext; sorted.
function M.walk(dir, ext, depth, out)
  out, depth = out or {}, depth or 0
  if depth > 20 then return out end
  local ok, iter, st = pcall(lfs.dir, dir)
  if not ok then return out end
  for n in iter, st do
    if n:sub(1, 1) ~= "." then
      local p, m = dir .. "/" .. n, M.mode(dir .. "/" .. n)
      if m == "directory" then M.walk(p, ext, depth + 1, out)
      elseif m == "file" and (not ext or n:sub(-#ext) == ext) then out[#out + 1] = p end
    end
  end
  table.sort(out)
  return out
end

function M.subdirs(dir)  -- glob(dir/*/): sorted, without the trailing slash
  local r = {}
  local ok, iter, st = pcall(lfs.dir, dir)
  if ok then
    for n in iter, st do
      if n:sub(1, 1) ~= "." and M.mode(dir .. "/" .. n) == "directory" then r[#r + 1] = dir .. "/" .. n end
    end
  end
  table.sort(r)
  return r
end

-- sorted() with a key: stable, ascending; ties keep input order.
function M.sorted(t, key)
  local idx = {}
  for i, v in ipairs(t) do idx[i] = { v, key(v), i } end
  table.sort(idx, function(a, b)
    if a[2] ~= b[2] then return a[2] < b[2] end
    return a[3] < b[3]
  end)
  local r = {}
  for i, x in ipairs(idx) do r[i] = x[1] end
  return r
end

-- Seconds since the epoch for an ISO 8601 time. Without a zone the time is local. nil if it isn't one.
local function days(y, m, d)  -- days from civil
  y = m <= 2 and y - 1 or y
  local era = math.floor(y / 400)
  local yoe = y - era * 400
  local doy = math.floor((153 * (m + (m > 2 and -3 or 9)) + 2) / 5) + d - 1
  return era * 146097 + yoe * 365 + math.floor(yoe / 4) - math.floor(yoe / 100) + doy - 719468
end

function M.parse_iso(s)
  local y, mo, d, rest = s:match("^(%d%d%d%d)-(%d%d)-(%d%d)(.*)$")
  if not y then return nil end
  local h, mi, sec, frac, zone = 0, 0, 0, 0, ""
  if rest ~= "" then
    local hh, mm, r2 = rest:match("^[T ](%d%d):?(%d%d)(.*)$")
    if not hh then hh, r2 = rest:match("^[T ](%d%d)(.*)$"); mm = "0" end
    if not hh then return nil end
    h, mi, zone = tonumber(hh), tonumber(mm), r2
    local ss, r3 = zone:match("^:?(%d%d)(.*)$")
    if ss then
      sec, zone = tonumber(ss), r3
      local fr, r4 = zone:match("^[.,](%d+)(.*)$")
      if fr then frac, zone = tonumber("0." .. fr), r4 end
    end
  end
  y, mo, d = tonumber(y), tonumber(mo), tonumber(d)
  if zone == "" then
    return os.time { year = y, month = mo, day = d, hour = h, min = mi, sec = sec } + frac, false  -- isdst nil: mktime decides
  end
  local off = 0
  if zone ~= "Z" and zone ~= "z" then
    local sg, oh, om = zone:match("^([+-])(%d%d):?(%d%d)$")
    if not sg then return nil end
    off = (sg == "-" and -1 or 1) * (tonumber(oh) * 3600 + tonumber(om) * 60)
  end
  return days(y, mo, d) * 86400 + h * 3600 + mi * 60 + sec + frac - off, true
end

return M
