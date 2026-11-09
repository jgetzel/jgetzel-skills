#!/usr/bin/env luajit
-- Today's and tomorrow's events from a Google Calendar secret iCal address, as JSON for the Calendar panel.
--   luajit events.lua [--ics FILE] [--date YYYY-MM-DD]     --test runs the self-test
-- Config, every key optional: <Herdr app home>/calendar.json
--   url_command       a shell command that prints the secret iCal address. Default: the macOS Keychain
--                     (security find-generic-password -s herdr-gcal-ics -w), on Linux the Secret Service
--                     (secret-tool lookup service herdr-gcal-ics).
--   internal_domains  guests outside these domains get "external": true; unset, nobody does.
-- Exit 3: no address configured. A rule or time zone it can't read is skipped with a line on stderr,
-- which the panel shows.

-- install.sh's rock tree (Homebrew/apt; Nix's luajit has the rocks built in)
local tree = os.getenv("XDG_DATA_HOME")
tree = ((tree and tree ~= "") and tree or os.getenv("HOME") .. "/.local/share") .. "/swarm/lua"
package.path = tree .. "/share/lua/5.1/?.lua;" .. tree .. "/share/lua/5.1/?/init.lua;" .. package.path
package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
local cjson, utf8 = require "cjson", require "lua-utf8"
local setenv = require("posix.stdlib").setenv
cjson.encode_empty_table_as_object(false)
local NULL = cjson.null

local warned = {}
local function warn(msg)
  if not warned[msg] then warned[msg] = true; io.stderr:write(msg, "\n") end
end

-- Calendar days as day numbers since 1970-01-01 (proleptic Gregorian).
local floor = math.floor
local function days(y, m, d)
  y = m <= 2 and y - 1 or y
  local era = floor(y / 400)
  local yoe = y - era * 400
  local doy = floor((153 * (m > 2 and m - 3 or m + 9) + 2) / 5) + d - 1
  return era * 146097 + yoe * 365 + floor(yoe / 4) - floor(yoe / 100) + doy - 719468
end
local function civil(z)
  z = z + 719468
  local era = floor(z / 146097)
  local doe = z - era * 146097
  local yoe = floor((doe - floor(doe / 1460) + floor(doe / 36524) - floor(doe / 146096)) / 365)
  local doy = doe - (365 * yoe + floor(yoe / 4) - floor(yoe / 100))
  local mp = floor((5 * doy + 2) / 153)
  local m = mp < 10 and mp + 3 or mp - 9
  return yoe + era * 400 + (m <= 2 and 1 or 0), m, doy - floor((153 * mp + 2) / 5) + 1
end
local function wday(z) return (z + 4) % 7 end -- 0 = Sunday
local function dim(y, m) return m == 12 and 31 or days(y, m + 1, 1) - days(y, m, 1) end

-- Time zones go through the process TZ and the system zoneinfo, so no tz database ships here.
local ORIG_TZ, ZONES, zone_ok = os.getenv("TZ"), (os.getenv("TZDIR") or "/usr/share/zoneinfo") .. "/", {}
local function in_tz(tz, f) -- f() with local time in tz (nil: the user's own)
  if tz and zone_ok[tz] == nil then
    local h = io.open(ZONES .. tz)
    zone_ok[tz] = h ~= nil
    if h then h:close() end
  end
  if tz and not zone_ok[tz] then warn("unknown time zone " .. tz .. ", read as UTC"); tz = "UTC" end
  setenv("TZ", tz or ORIG_TZ)
  os.time({ year = 2000, month = 1, day = 1, hour = 0 }) -- mktime re-reads TZ; glibc's localtime_r doesn't
  local r = f()
  setenv("TZ", ORIG_TZ)
  return r
end

-- A DATE or DATE-TIME: day number, seconds into that day, and its frame: "date", "utc", "tz" (TZID) or "float" (local).
local function value_dt(v, params)
  local y, m, d, rest = v:match("^(%d%d%d%d)(%d%d)(%d%d)(.*)$")
  if not y then return nil end
  local x = { day = days(tonumber(y), tonumber(m), tonumber(d)), sec = 0, kind = "date" }
  if rest == "" then return x end
  local h, mi, s, z = rest:match("^T(%d%d)(%d%d)(%d%d)(Z?)$")
  if not h then return nil end
  x.sec = tonumber(h) * 3600 + tonumber(mi) * 60 + tonumber(s)
  x.kind = z == "Z" and "utc" or params.TZID and "tz" or "float"
  x.tz = x.kind == "tz" and params.TZID or nil
  return x
end

local function epoch(x, day) -- x's wall clock on day (default its own) as Unix seconds
  day = day or x.day
  if x.kind == "utc" then return day * 86400 + x.sec end
  local y, m, d = civil(day)
  return in_tz(x.tz, function()
    return os.time({ year = y, month = m, day = d, hour = floor(x.sec / 3600), min = floor(x.sec / 60) % 60, sec = x.sec % 60 })
  end)
end

local function frame(e, x) -- Unix seconds e as (day, sec) on x's wall clock
  if x.kind == "utc" then return floor(e / 86400), e % 86400 end
  local t = in_tz(x.tz, function() return os.date("*t", e) end)
  return days(t.year, t.month, t.day), t.hour * 3600 + t.min * 60 + t.sec
end

-- RFC 5545 duration (no months in iCal) as seconds.
local UNIT = { W = 604800, D = 86400, H = 3600, M = 60, S = 1 }
local function duration(v)
  local sign, body = v:match("^([+-]?)P(.+)$")
  if not body then return nil end
  local n = 0
  for num, u in body:gsub("T", ""):gmatch("(%d+)(%u)") do n = n + tonumber(num) * (UNIT[u] or 0) end
  return sign == "-" and -n or n
end

-- iCal text

local function unescape(v) return (v:gsub("\\(.)", function(c) return (c == "n" or c == "N") and "\n" or c end)) end

local function contentline(line)
  local name, pos = line:match("^([%w%-]+)()")
  if not name then return nil end
  local params = {}
  while line:sub(pos, pos) == ";" do
    local k, j = line:match("^([%w%-]+)=()", pos + 1)
    if not k then return nil end
    local v
    if line:sub(j, j) == '"' then v, pos = line:match('^"([^"]*)"()', j) else v, pos = line:match("^([^;:]*)()", j) end
    if not v then return nil end
    params[k:upper()] = v
  end
  if line:sub(pos, pos) ~= ":" then return nil end
  return name:upper(), params, line:sub(pos + 1)
end

-- The calendar's and each VEVENT's own properties (not their VALARMs'): name -> list of {value, params}.
local function parse(ics)
  ics = ics:gsub("\r\n", "\n"):gsub("\r", "\n"):gsub("\n[ \t]", "")
  local cal, stack, ev = { events = {} }, {}, nil
  for line in ics:gmatch("[^\n]+") do
    local name, params, value = contentline(line)
    if name == "BEGIN" then
      stack[#stack + 1] = value:upper()
      if value:upper() == "VEVENT" then ev = {} end
    elseif name == "END" then
      if table.remove(stack) == "VEVENT" and ev then cal.events[#cal.events + 1] = ev; ev = nil end
    elseif name then
      local top = stack[#stack]
      local into = top == "VEVENT" and ev or top == "VCALENDAR" and cal or nil
      if into then
        into[name] = into[name] or {}
        table.insert(into[name], { value = value, params = params })
      end
    end
  end
  return cal
end

local function prop(ev, name) return ev[name] and ev[name][1] end
local function text(ev, name, default)
  local p = prop(ev, name)
  if p then return unescape(p.value) end
  return default
end
local function prop_dt(ev, name)
  local p = prop(ev, name)
  return p and value_dt(p.value, p.params)
end
local function dts(ev, name) -- every value of a list property (EXDATE, RDATE)
  local out = {}
  for _, p in ipairs(ev[name] or {}) do
    for v in p.value:gmatch("[^,]+") do out[#out + 1] = value_dt(v, p.params) end
  end
  return out
end

-- Recurrence

local WD = { SU = 0, MO = 1, TU = 2, WE = 3, TH = 4, FR = 5, SA = 6 }
local PARTS = { FREQ = 1, INTERVAL = 1, COUNT = 1, UNTIL = 1, BYDAY = 1, BYMONTHDAY = 1, BYMONTH = 1, BYSETPOS = 1, WKST = 1 }
local FREQS = { DAILY = 1, WEEKLY = 1, MONTHLY = 1, YEARLY = 1 }

local function nums(v)
  if not v then return nil end
  local t = {}
  for n in v:gmatch("[^,]+") do t[#t + 1] = tonumber(n) end
  return t
end
local function has(list, x)
  for _, v in ipairs(list) do if v == x then return true end end
  return false
end

local function rule(s) -- RRULE value -> rule, or nil and the part it can't expand
  local r = {}
  for k, v in s:gmatch("([^;=]+)=([^;]*)") do r[k:upper()] = v end
  for k in pairs(r) do if not PARTS[k] then return nil, k end end
  if not FREQS[r.FREQ] then return nil, "FREQ=" .. tostring(r.FREQ) end
  local o = { freq = r.FREQ, interval = tonumber(r.INTERVAL) or 1, count = tonumber(r.COUNT), wkst = WD[r.WKST or "MO"] or 1,
    months = nums(r.BYMONTH), mdays = nums(r.BYMONTHDAY), setpos = nums(r.BYSETPOS) }
  if r.BYDAY then
    o.wdays = {}
    for n, w in r.BYDAY:gmatch("([+-]?%d*)(%u%u)") do
      if not WD[w] then return nil, "BYDAY=" .. r.BYDAY end
      o.wdays[#o.wdays + 1] = { n = tonumber(n), wd = WD[w] }
    end
  end
  if o.freq == "YEARLY" and o.wdays and not o.months then return nil, "YEARLY BYDAY without BYMONTH" end
  if r.UNTIL then o["until"] = value_dt(r.UNTIL, {}) end
  return o
end

local function month_days(o, y, m, d0) -- the set of days a MONTHLY/YEARLY rule picks in month m of year y
  local n, first, set = dim(y, m), days(y, m, 1), {}
  if o.mdays then
    for _, md in ipairs(o.mdays) do
      local d = md < 0 and n + 1 + md or md
      if d >= 1 and d <= n then set[first + d - 1] = true end
    end
  end
  if o.wdays then
    local w = {}
    for _, e in ipairs(o.wdays) do
      local hits = {}
      for z = first, first + n - 1 do if wday(z) == e.wd then hits[#hits + 1] = z end end
      if e.n then
        local z = hits[e.n > 0 and e.n or #hits + 1 + e.n]
        if z then w[z] = true end
      else
        for _, z in ipairs(hits) do w[z] = true end
      end
    end
    if o.mdays then
      for z in pairs(set) do if not w[z] then set[z] = nil end end
    else
      set = w
    end
  end
  if not o.mdays and not o.wdays and d0 <= n then set[first + d0 - 1] = true end
  return set
end

local function period(o, s, k) -- the k-th period's candidate days (sorted) and the day it starts on
  local y0, m0, d0 = civil(s)
  local set, start = {}, nil
  if o.freq == "DAILY" then
    start = s + k * o.interval
    set[start] = true
  elseif o.freq == "WEEKLY" then
    start = s - (wday(s) - o.wkst) % 7 + 7 * o.interval * k
    for _, e in ipairs(o.wdays or { { wd = wday(s) } }) do set[start + (e.wd - o.wkst) % 7] = true end
  elseif o.freq == "MONTHLY" then
    local i = y0 * 12 + m0 - 1 + k * o.interval
    local y, m = floor(i / 12), i % 12 + 1
    start, set = days(y, m, 1), month_days(o, y, m, d0)
  else
    local y = y0 + k * o.interval
    start = days(y, 1, 1)
    for _, m in ipairs(o.months or { m0 }) do
      for z in pairs(month_days(o, y, m, d0)) do set[z] = true end
    end
  end
  local out = {}
  for z in pairs(set) do
    local y, m, d = civil(z)
    local ok = not o.months or has(o.months, m)
    if ok and o.freq == "DAILY" and o.wdays then
      ok = false
      for _, e in ipairs(o.wdays) do ok = ok or e.wd == wday(z) end
    end
    if ok and o.freq == "DAILY" and o.mdays then
      local n = dim(y, m)
      ok = false
      for _, md in ipairs(o.mdays) do ok = ok or (md < 0 and n + 1 + md or md) == d end
    end
    if ok then out[#out + 1] = z end
  end
  table.sort(out)
  if o.setpos then
    local pick = {}
    for _, i in ipairs(o.setpos) do
      local z = out[i > 0 and i or #out + 1 + i]
      if z then pick[z] = true end
    end
    out = {}
    for z in pairs(pick) do out[#out + 1] = z end
    table.sort(out)
  end
  return out, start
end

-- The days in [lo, hi] the series starting at s occurs on, in s's frame, honoring COUNT and UNTIL.
-- DTSTART is always one, even off the rule (then outside COUNT), as dateutil and Google do.
local function occurrences(o, s, lo, hi)
  local ud, us = nil, nil -- UNTIL on s's wall clock
  local u = o["until"]
  if u then
    if u.kind == "date" or s.kind == "date" then ud, us = u.day, math.huge
    elseif u.kind == "utc" then ud, us = frame(epoch(u), s)
    else ud, us = u.day, u.sec end
  end
  local out, n = {}, 0
  if s.day >= lo and s.day <= hi then out[1] = s.day end
  for k = 0, 1e6 do
    local cand, start = period(o, s.day, k)
    if start > hi then break end
    for _, z in ipairs(cand) do
      if z >= s.day then
        if ud and (z > ud or z == ud and s.sec > us) then return out end
        n = n + 1
        if (o.count and n > o.count) or z > hi then return out end
        if z >= lo and z ~= s.day then out[#out + 1] = z end
      end
    end
  end
  return out
end

-- HTML in descriptions

local function cp(n) return n and n > 0 and n < 0x110000 and utf8.char(n) or nil end
-- HTML's Latin-1 entities (U+00A0..U+00FF in order) plus the punctuation calendar invites use.
local ENT = { amp = "&", lt = "<", gt = ">", quot = '"', apos = "'", rsquo = "’", lsquo = "‘", rdquo = "”", ldquo = "“",
  sbquo = "‚", bdquo = "„", ndash = "–", mdash = "—", hellip = "…", bull = "•", trade = "™", euro = "€", dagger = "†",
  ensp = cp(0x2002), emsp = cp(0x2003), thinsp = cp(0x2009), zwnj = cp(0x200C), zwj = cp(0x200D), lrm = cp(0x200E), rlm = cp(0x200F) }
do
  local n = 0xA0
  for name in ([[nbsp iexcl cent pound curren yen brvbar sect uml copy ordf laquo not shy reg macr deg plusmn sup2 sup3
    acute micro para middot cedil sup1 ordm raquo frac14 frac12 frac34 iquest Agrave Aacute Acirc Atilde Auml Aring AElig
    Ccedil Egrave Eacute Ecirc Euml Igrave Iacute Icirc Iuml ETH Ntilde Ograve Oacute Ocirc Otilde Ouml times Oslash Ugrave
    Uacute Ucirc Uuml Yacute THORN szlig agrave aacute acirc atilde auml aring aelig ccedil egrave eacute ecirc euml igrave
    iacute icirc iuml eth ntilde ograve oacute ocirc otilde ouml divide oslash ugrave uacute ucirc uuml yacute thorn yuml]]):gmatch("%a+%d*") do
    ENT[name] = cp(n)
    n = n + 1
  end
  assert(n == 0x100 and ENT.yuml == "ÿ")
end
local function unhtml(s)
  s = s:gsub("&#[xX](%x+);", function(h) return cp(tonumber(h, 16)) end)
  s = s:gsub("&#(%d+);", function(d) return cp(tonumber(d)) end)
  return (s:gsub("&(%a+);", ENT))
end

local NBSP = "\194\160"
local function rstrip(s)
  repeat
    local n = #s
    s = s:gsub("%s+$", "")
    if s:sub(-2) == NBSP then s = s:sub(1, -3) end
  until #s == n
  return s
end
local function strip(s)
  repeat
    local n = #s
    s = s:gsub("^%s+", "")
    if s:sub(1, 2) == NBSP then s = s:sub(3) end
  until #s == n
  return rstrip(s)
end

local function replace(s, find, with) -- plain substring replace
  if find == "" then return s end
  local out, i = {}, 1
  while true do
    local a, b = s:find(find, i, true)
    if not a then break end
    out[#out + 1] = s:sub(i, a - 1) .. with
    i = b + 1
  end
  return table.concat(out) .. s:sub(i)
end

-- Google's conference block and its "Join with Google Meet" tail.
local function drop_join(s)
  s = s:gsub("%-::~:~::~.-::~:~::%-", "")
  local j = s:find("\n*Join with Google Meet:")
  return j and s:sub(1, j - 1) or s
end

local function unquote_plus(s)
  return (s:gsub("%+", " "):gsub("%%(%x%x)", function(h) return string.char(tonumber(h, 16)) end))
end

local function urlparts(u) -- host, path, query
  local host, rest = u:match("^%a[%w+.-]*://([^/?#]*)(.*)$")
  if not host then return "", u:match("^[^?#]*"), u:match("%?([^#]*)") or "" end
  return host, rest:match("^[^?#]*"), rest:match("%?([^#]*)") or ""
end

local DOCS = { document = "Google Doc", spreadsheets = "Google Sheet", presentation = "Google Slides", forms = "Google Form" }
-- A readable name for a link: Google file type, else the last wordy path segment (Confluence titles), else the host.
local function pretty(url)
  local host, path = urlparts(url)
  if host == "docs.google.com" then return DOCS[path:match("^/([^/]*)") or ""] or "Google file" end
  local space = path:match("/spaces/([^/]+)/overview/?$")
  if space then return space .. " space" end
  local seg
  for s in path:gmatch("[^/]+") do if s:find("%a%a%a") then seg = s end end
  return seg and unquote_plus(seg) or host
end

local function unwrap(url) -- Google's /url?q= redirect -> its target
  local host, path, query = urlparts(url)
  if host:sub(-10) == "google.com" and path == "/url" then
    for k, v in query:gmatch("([^&=]+)=([^&]*)") do
      if unquote_plus(k) == "q" and v ~= "" then return unquote_plus(v) end
    end
  end
  return url
end

-- Links and attachments come from the invite's author, and the panel opens them: web addresses only.
local function web(url) return url:lower():find("^https?://") ~= nil end

local SKIP = { "meet.google.com", "tel.meet", "zoom.us/j", "support.google.com" }
local function links(raw)
  raw = drop_join(raw)
  local order, title = {}, {}
  local function add(u, t)
    if title[u] == nil then order[#order + 1] = u; title[u] = t end
  end
  for u, t in raw:gmatch('<[aA]%s[^>]-[hH][rR][eE][fF]="([^"]+)"[^>]*>(.-)</[aA]>') do
    u = unwrap(unhtml(u))
    if web(u) then add(u, strip(unhtml((t:gsub("<[^>]+>", ""))))) end
  end
  for u in unhtml((raw:gsub("<[^>]+>", " "))):gmatch('https?://[^%s<>"]+') do
    u = u:match("^(.-)" .. NBSP) or u
    add(unwrap((u:gsub("[.,)]+$", ""))), "")
  end
  local out = {}
  for _, u in ipairs(order) do
    local skip = false
    for _, s in ipairs(SKIP) do skip = skip or u:find(s, 1, true) ~= nil end
    if not skip then
      local t = title[u]
      out[#out + 1] = { title = (t ~= "" and t ~= u) and t or pretty(u), url = u, host = (urlparts(u)) }
    end
  end
  return out
end

local function plain(s, drop)
  s = drop_join(s):gsub("<[bB][rR]%s*/?>", "\n"):gsub("</[pP]>", "\n"):gsub("</[lL][iI]>", "\n")
  s = unhtml((s:gsub("<[^>]+>", "")))
  for _, u in ipairs(drop) do s = replace(s, u, "") end
  -- the line breaks Python's str.splitlines knows, as \n
  s = s:gsub("\r\n", "\n"):gsub("[\r\v\f\28\29\30]", "\n"):gsub("\194\133", "\n"):gsub("\226\128[\168\169]", "\n")
  local lines = {}
  for l in (s .. "\n"):gmatch("(.-)\n") do lines[#lines + 1] = rstrip(l) end
  s = table.concat(lines, "\n"):gsub("\n\n\n+", "\n\n")
  return utf8.sub(strip(s), 1, 3000)
end

local function first_link(s) -- the meeting's Meet or Zoom link
  local a1, b1 = s:find("https://meet%.google%.com/[a-z%-]+")
  local a2, b2 = s:find('https://[%w_%.%-]*zoom%.us/j/[^%s"<>\\]+')
  if a1 and (not a2 or a1 <= a2) then return s:sub(a1, b1) end
  return a2 and s:sub(a2, b2) or nil
end

local function files(ev)
  local out = {}
  for _, a in ipairs(ev.ATTACH or {}) do
    local url, fmt = a.value, a.params.FMTTYPE or ""
    local kind = fmt:sub(1, 6) == "video/" and "recording"
      or (fmt:find("google-apps", 1, true) or url:find("docs.google.com", 1, true)) and "doc" or "file"
    if web(url) then out[#out + 1] = { title = a.params.FILENAME or pretty(url), url = url, kind = kind } end
  end
  return out
end

local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"
local function b64url(s) -- unpadded
  local out = {}
  for i = 1, #s, 3 do
    local a, b, c = s:byte(i, i + 2)
    local n = a * 65536 + (b or 0) * 256 + (c or 0)
    for j = 1, b and (c and 4 or 3) or 2 do
      local v = floor(n / 64 ^ (4 - j)) % 64
      out[#out + 1] = B64:sub(v + 1, v + 1)
    end
  end
  return table.concat(out)
end

-- Google's event id: the UID's prefix, plus _<original start> for one instance of a recurring event.
local function google_id(ev, occ, recurring)
  local uid = text(ev, "UID", "")
  if uid:sub(-11) ~= "@google.com" then return nil end
  local base = uid:sub(1, -12):gsub("_R%d%d%d%d%d%d%d%dT%d%d%d%d%d%d$", "") -- a split series' UID carries _R<series start>
  if not recurring then return base end
  local x = prop_dt(ev, "RECURRENCE-ID") or occ
  return base .. "_" .. (x.kind == "date" and os.date("!%Y%m%d", x.day * 86400) or os.date("!%Y%m%dT%H%M%SZ", epoch(x)))
end

-- The panel's record for one occurrence; nil when cancelled or declined.
local function record(ev, x, st, en, recurring, me, calendar_id, internal)
  local mine
  for _, a in ipairs(ev.ATTENDEE or {}) do
    if a.value:lower() == me then mine = a.params.PARTSTAT; break end
  end
  if text(ev, "STATUS") == "CANCELLED" or mine == "DECLINED" then return nil end
  local org = prop(ev, "ORGANIZER")
  if org and org.value:lower() == me then mine = "ACCEPTED" end
  local attached, seen = files(ev), {}
  for _, f in ipairs(attached) do seen[f.url] = true end
  local found, drop = {}, {}
  for _, l in ipairs(links(text(ev, "DESCRIPTION", ""))) do
    if not seen[l.url] then found[#found + 1] = l; drop[#drop + 1] = l.url end
  end
  local people = {}
  for i, a in ipairs(ev.ATTENDEE or {}) do
    if i > 60 then break end
    local email = a.value:sub(8)
    people[i] = { name = a.params.CN or email, email = email, status = a.params.PARTSTAT or "NEEDS-ACTION",
      external = internal ~= nil and email ~= "" and not internal[(email:match("@(.*)$") or ""):lower()] }
  end
  local gid = google_id(ev, x, recurring)
  local link = first_link(text(ev, "X-GOOGLE-CONFERENCE", "") .. " " .. text(ev, "LOCATION", "") .. " " .. text(ev, "DESCRIPTION", ""))
  return {
    title = text(ev, "SUMMARY", "(no title)"),
    day = st and in_tz(nil, function() return os.date("%Y-%m-%d", st) end) or os.date("!%Y-%m-%d", x.day * 86400),
    all_day = st == nil,
    start = st and st * 1000 or NULL,
    ["end"] = en and en * 1000 or NULL,
    link = link or NULL,
    id = gid or NULL,
    open = gid and "https://www.google.com/calendar/event?eid=" .. b64url(gid .. " " .. calendar_id) or NULL,
    rsvp = mine or "ACCEPTED",
    location = text(ev, "LOCATION", ""),
    description = plain(text(ev, "DESCRIPTION", ""), drop),
    links = found,
    files = attached,
    organizer = org and (org.params.CN or org.value:sub(8)) or NULL,
    organizer_email = org and org.value:sub(8) or NULL,
    attendees = people,
  }
end

-- Events overlapping local days [today, today + 2), one record under each day it overlaps (`day`),
-- sorted by day, all-day first, then start.
local function events(cal, today, internal)
  local calendar_id = text(cal, "X-WR-CALNAME", "")
  local me = ("mailto:" .. calendar_id):lower()
  local local_midnight = { kind = "float", sec = 0 }
  local function key(x) return x.kind == "date" and "d" .. x.day or epoch(x) end
  local moved = {} -- uid -> instances an override replaces
  for _, ev in ipairs(cal.events) do
    local r = prop_dt(ev, "RECURRENCE-ID")
    if r then
      local uid = text(ev, "UID", "")
      moved[uid] = moved[uid] or {}
      moved[uid][key(r)] = true
    end
  end
  local out = {}
  for _, ev in ipairs(cal.events) do
    local s = prop_dt(ev, "DTSTART")
    if s then
      local e, d = prop_dt(ev, "DTEND"), prop(ev, "DURATION")
      d = d and duration(d.value)
      local len -- days when all-day, else seconds
      if s.kind == "date" then len = math.max(e and e.day - s.day or floor((d or 86400) / 86400), 1)
      else len = e and epoch(e) - epoch(s) or d or 0 end
      local rr, override = prop(ev, "RRULE"), prop(ev, "RECURRENCE-ID") ~= nil
      local starts = { s }
      if rr and not override then
        starts = {}
        local o, why = rule(rr.value)
        if not o then
          warn(("skipped %q: can't expand its RRULE %s"):format(text(ev, "SUMMARY", "?"), why))
        else
          local skip = moved[text(ev, "UID", "")] or {}
          for _, x in ipairs(dts(ev, "EXDATE")) do skip[key(x)] = true end
          local back = s.kind == "date" and len or math.ceil(len / 86400)
          for _, z in ipairs(occurrences(o, s, today - 2 - back, today + 3)) do
            local x = { day = z, sec = s.sec, kind = s.kind, tz = s.tz }
            if not skip[key(x)] then starts[#starts + 1] = x end
          end
          for _, x in ipairs(dts(ev, "RDATE")) do
            if not skip[key(x)] then starts[#starts + 1] = x end
          end
        end
      end
      for _, x in ipairs(starts) do
        local st = x.kind ~= "date" and epoch(x) or nil
        local en = st and st + len
        for d = today, today + 1 do
          local keep
          if st then
            local ds, de = epoch(local_midnight, d), epoch(local_midnight, d + 1)
            keep = st < de and (en > ds or st >= ds)
          else
            keep = x.day <= d and x.day + len > d
          end
          local rec = keep and record(ev, x, st, en, rr ~= nil or override, me, calendar_id, internal)
          if rec then
            rec.day = os.date("!%Y-%m-%d", d * 86400)
            out[#out + 1] = rec
          end
        end
      end
    end
  end
  table.sort(out, function(a, b)
    if a.day ~= b.day then return a.day < b.day end
    if a.all_day ~= b.all_day then return a.all_day end
    if not a.all_day and a.start ~= b.start then return a.start < b.start end
    return a.title .. tostring(a.id) < b.title .. tostring(b.id)
  end)
  return out
end

local function selftest()
  ORIG_TZ = "America/New_York"
  local ics = [[
BEGIN:VCALENDAR
X-WR-CALNAME:me@example.com
BEGIN:VEVENT
UID:a_R20260616T151000@google.com
SUMMARY:Standup
DTSTART:20261102T150000Z
DTEND:20261102T151500Z
RRULE:FREQ=DAILY
LOCATION:https://meet.google.com/abc-defg-hij
BEGIN:VALARM
DESCRIPTION:This is an event reminder
END:VALARM
END:VEVENT
BEGIN:VEVENT
UID:t
SUMMARY:Maybe
DTSTART:20261103T190000Z
DTEND:20261103T193000Z
DESCRIPTION:Agenda<br>item <a href="file:///Applications/Calculator.app">agenda</a> <a href="https://x.atlassian.net/wiki/pages/1/Retro+Notes">https://x.atlassian.net/wiki/pages/1/Retro+Notes</a> -::~:~::~join here::~:~::-\n\nJoin with Google Meet: https://meet.google.com/x\nOr dial: 1
ATTACH;FILENAME="Notes - 1:1";FMTTYPE=application/vnd.google-apps.document:https://docs.google.com/document/d/abc/edit
ATTACH;FILENAME="Recording";FMTTYPE=video/mp4:https://drive.google.com/file/d/def/view
ATTACH;FILENAME="Share":smb://host/share
ATTENDEE;CN=Me;PARTSTAT=TENTATIVE:mailto:me@example.com
ATTENDEE;PARTSTAT=ACCEPTED:mailto:guest@other.org
END:VEVENT
BEGIN:VEVENT
UID:b
SUMMARY:Declined
DTSTART:20261103T170000Z
DTEND:20261103T180000Z
ATTENDEE;PARTSTAT=DECLINED:mailto:me@example.com
END:VEVENT
BEGIN:VEVENT
UID:c
SUMMARY:Offsite
DTSTART;VALUE=DATE:20261104
DTEND;VALUE=DATE:20261105
END:VEVENT
END:VCALENDAR]]
  local got = events(parse((ics:gsub("\n", "\r\n"))), days(2026, 11, 3), { ["example.com"] = true })
  local function eq(a, b, what)
    local x, y = cjson.encode(a), cjson.encode(b)
    if x ~= y then error(what .. ": got " .. x .. ", want " .. y, 2) end
  end
  local titles = {}
  for i, e in ipairs(got) do titles[i] = e.title end
  eq(titles, { "Standup", "Maybe", "Offsite", "Standup" }, "titles")
  eq({ got[2].rsvp, got[2].description }, { "TENTATIVE", "Agenda\nitem agenda" }, "rsvp, description") -- the file:// link's text stays, its address goes
  eq(plain("a\226\128\168\nb\r\nc", {}), "a\n\nb\nc", "line separators")
  eq(got[2].attendees, { { name = "Me", email = "me@example.com", status = "TENTATIVE", external = false },
    { name = "guest@other.org", email = "guest@other.org", status = "ACCEPTED", external = true } }, "attendees")
  eq({ got[1].organizer_email, got[1].rsvp, got[1].links, got[1].files, got[1].description }, { NULL, "ACCEPTED", {}, {}, "" }, "standup")
  eq(got[2].links, { { title = "Retro Notes", url = "https://x.atlassian.net/wiki/pages/1/Retro+Notes", host = "x.atlassian.net" } }, "links")
  eq({ got[2].files[1].title, got[2].files[1].kind, got[2].files[2].title, got[2].files[2].kind }, { "Notes - 1:1", "doc", "Recording", "recording" }, "files")
  eq({ got[1].id, got[4].id, got[2].id }, { "a_20261103T150000Z", "a_20261104T150000Z", NULL }, "ids")
  eq({ got[1].link, got[3].all_day, got[3].day }, { "https://meet.google.com/abc-defg-hij", true, "2026-11-04" }, "link, all-day")
  eq(got[1].open, "https://www.google.com/calendar/event?eid=" .. b64url("a_20261103T150000Z me@example.com"), "open")

  -- Rules: window is Tue 2026-11-03 and Wed 2026-11-04, New York.
  local function ev(uid, summary, lines) return ("BEGIN:VEVENT\nUID:%s\nSUMMARY:%s\n%s\nEND:VEVENT\n"):format(uid, summary, lines) end
  got = events(parse("BEGIN:VCALENDAR\n"
    .. ev("tz", "Tue Thu NY", "DTSTART;TZID=America/New_York:20260303T090000\nDTEND;TZID=America/New_York:20260303T093000\nRRULE:FREQ=WEEKLY;BYDAY=TU,TH")
    .. ev("first-tue", "First Tuesday", "DTSTART:20260106T170000Z\nDTEND:20260106T180000Z\nRRULE:FREQ=MONTHLY;BYDAY=1TU")
    .. ev("last-day", "Last day", "DTSTART;VALUE=DATE:20260131\nRRULE:FREQ=MONTHLY;BYMONTHDAY=-1")
    .. ev("biweekly", "Every other Wed", "DTSTART:20261021T160000Z\nDTEND:20261021T163000Z\nRRULE:FREQ=WEEKLY;INTERVAL=2;BYDAY=WE")
    .. ev("off-week", "Other other Wed", "DTSTART:20261028T160000Z\nDTEND:20261028T163000Z\nRRULE:FREQ=WEEKLY;INTERVAL=2;BYDAY=WE")
    .. ev("count", "Counted out", "DTSTART:20261101T150000Z\nDTEND:20261101T160000Z\nRRULE:FREQ=DAILY;COUNT=2")
    .. ev("until", "Until Tue", "DTSTART:20261101T150000Z\nDTEND:20261101T160000Z\nRRULE:FREQ=DAILY;UNTIL=20261103T235959Z")
    .. ev("ex", "Skips Wed", "DTSTART:20261101T130000Z\nDTEND:20261101T133000Z\nRRULE:FREQ=DAILY\nEXDATE:20261104T130000Z")
    .. ev("sync", "Sync", "DTSTART:20261101T200000Z\nDTEND:20261101T203000Z\nRRULE:FREQ=DAILY")
    .. ev("sync", "Sync moved", "RECURRENCE-ID:20261103T200000Z\nDTSTART:20261103T220000Z\nDTEND:20261103T223000Z")
    .. ev("sync", "Sync", "RECURRENCE-ID:20261104T200000Z\nDTSTART:20261104T200000Z\nDTEND:20261104T203000Z\nSTATUS:CANCELLED")
    .. ev("yearly", "Anniversary", "DTSTART;VALUE=DATE:20201104\nRRULE:FREQ=YEARLY")
    .. ev("bad", "Hourly", "DTSTART:20261101T150000Z\nRRULE:FREQ=HOURLY")
    .. ev("span", "Conference", "DTSTART;VALUE=DATE:20261102\nDTEND;VALUE=DATE:20261105")
    .. ev("late", "Overnight", "DTSTART:20261104T030000Z\nDTEND:20261104T070000Z")
    .. "END:VCALENDAR\n"), days(2026, 11, 3))
  local seen = {}
  for _, e in ipairs(got) do seen[#seen + 1] = e.day .. " " .. (e.all_day and "all-day" or os.date("!%H:%M", e.start / 1000)) .. " " .. e.title end
  -- Conference (all-day, Mon to Wed) and Overnight (Tue 22:00 to Wed 02:00 New York) list under both days.
  eq(seen, { "2026-11-03 all-day Conference", "2026-11-03 13:00 Skips Wed", "2026-11-03 14:00 Tue Thu NY", "2026-11-03 15:00 Until Tue",
    "2026-11-03 17:00 First Tuesday", "2026-11-03 22:00 Sync moved", "2026-11-03 03:00 Overnight",
    "2026-11-04 all-day Anniversary", "2026-11-04 all-day Conference", "2026-11-04 03:00 Overnight", "2026-11-04 16:00 Every other Wed" }, "rules")
  eq(warned['skipped "Hourly": can\'t expand its RRULE FREQ=HOURLY'], true, "warning")
  print("ok")
end

local a = {}
for i = 1, #arg do
  if arg[i]:sub(1, 2) == "--" then a[arg[i]:sub(3)] = arg[i + 1] or true end
end
if a.test then return selftest() end

local home = os.getenv("HERDR_APP_HOME")
home = (home and home ~= "") and home or os.getenv("HOME") .. "/.config/herdr-app"
local conf = {}
local f = io.open(home .. "/calendar.json")
if f then
  local ok, c = pcall(cjson.decode, f:read("*a"))
  f:close()
  if not ok or type(c) ~= "table" then io.stderr:write(home, "/calendar.json is not a JSON object\n"); os.exit(2) end
  conf = c
end
local internal
if type(conf.internal_domains) == "table" and #conf.internal_domains > 0 then
  internal = {}
  for _, d in ipairs(conf.internal_domains) do internal[tostring(d):lower()] = true end
end

local function sh(cmd)
  local p = io.popen(cmd)
  local out = p:read("*a")
  p:close()
  return out
end

local ics
if a.ics then
  local h = assert(io.open(a.ics))
  ics = h:read("*a")
  h:close()
else
  local cmd = conf.url_command or (require("posix.sys.utsname").uname().sysname == "Darwin"
    and "security find-generic-password -s herdr-gcal-ics -w" or "secret-tool lookup service herdr-gcal-ics")
  local url = strip(sh("(" .. cmd .. ") 2>/dev/null"))
  if url == "" then
    io.stderr:write("No calendar: `", cmd, "` printed no iCal address. Set url_command in ", home, "/calendar.json\n")
    os.exit(3)
  end
  setenv("ICS_URL", url) -- through the environment, so the secret address never shows in a process list
  ics = sh([[printf 'url = "%s"\n' "$ICS_URL" | curl -fsSL --max-time 20 -K - 2>&1]])
  if not ics:find("BEGIN:VCALENDAR", 1, true) then
    io.stderr:write("fetching the calendar failed: ", strip(ics):sub(1, 300), "\n")
    os.exit(1)
  end
end
local today
if a.date then
  local y, m, d = a.date:match("^(%d+)-(%d+)-(%d+)$")
  today = days(tonumber(y), tonumber(m), tonumber(d))
else
  local t = in_tz(nil, function() return os.date("*t") end)
  today = days(t.year, t.month, t.day)
end
io.write(cjson.encode(events(parse(ics), today, internal)), "\n")
