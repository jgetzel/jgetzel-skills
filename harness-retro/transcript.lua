#!/usr/bin/env luajit
-- Render a Claude Code transcript (.jsonl) as compact Markdown, for reading or blind judging.
--
--   transcript.lua FILE.jsonl [--redact OLD=NEW]... [--last]
--
-- --last prints only the final assistant text (probe.sh checks it for PROBE DONE).
local d = (arg[0]:match("^(.*)/[^/]*$") or ".")
package.path = d .. "/?.lua;" .. d .. "/../swarm/lua/?.lua;" .. package.path
local hr, re, json = require "hr", require "swarm.re", require "swarm.json"
local utf8 = require "lua-utf8"

local function strip(s) return (s:gsub("^%s+", ""):gsub("%s+$", "")) end

local function clip(s, n)
  s = strip(re.sub("<system-reminder>.*?</system-reminder>", "", s, re.S))
  local len = utf8.len(s)
  if len <= n then return s end
  return utf8.sub(s, 1, n) .. " …[" .. (len - n) .. " more chars]"
end

local function text_of(c)
  if type(c) == "string" then return c end
  local t = {}
  for _, b in ipairs(c) do
    if type(b) == "table" and b.type == "text" then t[#t + 1] = b.text or "" end
  end
  return table.concat(t, "\n")
end

-- Python's json.dumps for a table: ", " and ": " separators, ASCII escapes; keys sorted (cjson loses the order).
local function ascii(s)  -- ensure_ascii: \uXXXX, surrogate pairs above the BMP
  return (s:gsub(utf8.charpattern, function(c)
    if #c == 1 then return c end
    local n = utf8.codepoint(c)
    if n < 0x10000 then return ("\\u%04x"):format(n) end
    n = n - 0x10000
    return ("\\u%04x\\u%04x"):format(0xd800 + math.floor(n / 1024), 0xdc00 + n % 1024)
  end))
end

local function dumps(v)
  if type(v) ~= "table" then return ascii(json.encode(v)) end
  if getmetatable(v) then
    local t = {}
    for i, x in ipairs(v) do t[i] = dumps(x) end
    return "[" .. table.concat(t, ", ") .. "]"
  end
  local ks = {}
  for k in pairs(v) do ks[#ks + 1] = k end
  table.sort(ks)
  for i, k in ipairs(ks) do ks[i] = ascii(json.encode(k)) .. ": " .. dumps(v[k]) end
  return "{" .. table.concat(ks, ", ") .. "}"
end

local function summary(inp)
  for _, k in ipairs { "command", "file_path", "pattern", "skill", "url", "query", "description" } do
    local v = inp[k]
    if v ~= nil and v ~= false and v ~= "" and v ~= 0 then
      return type(v) == "string" and v or dumps(v)
    end
  end
  return dumps(inp)
end

local function main()
  local ap = require("argparse")("transcript.lua")
  ap:argument("file")
  ap:option("--redact"):count("*")
  ap:flag("--last")
  local ok, a = ap:pparse()
  if not ok then io.stderr:write(tostring(a), "\n"); os.exit(2) end
  local recs = {}
  for line in io.lines(a.file) do
    local r = json.decode(line)
    if type(r) == "table" and (r.type == "user" or r.type == "assistant") and not r.isSidechain then
      recs[#recs + 1] = r
    end
  end
  if a.last then
    for i = #recs, 1, -1 do
      local r = recs[i]
      if r.type == "assistant" then
        local t = text_of(r.message.content)
        if strip(t) ~= "" then print(t); return end
      end
    end
    print("")
    return
  end
  local out, calls, errors = {}, 0, 0
  for _, r in ipairs(recs) do
    local c = r.message.content or ""
    if r.type == "user" and type(c) == "string" then
      local meta = r.isMeta  -- skill bodies, injected context, cross-session messages
      out[#out + 1] = "\n### user" .. (meta and " (meta)" or "") .. "\n" .. clip(c, meta and 600 or 3000) .. "\n"
    elseif type(c) == "table" then
      for _, b in ipairs(c) do
        local t = b.type
        if t == "text" and strip(b.text or "") ~= "" then
          out[#out + 1] = "\n**" .. r.type .. ":** " .. clip(b.text, 3000) .. "\n"
        elseif t == "tool_use" then
          calls = calls + 1
          out[#out + 1] = "→ " .. b.name .. ": " .. clip(summary(b.input or {}), 400)
        elseif t == "tool_result" then
          local body = b.content
          if type(body) == "table" then body = text_of(body) else body = body == nil and "" or tostring(body) end
          if b.is_error then errors = errors + 1 end
          out[#out + 1] = (("  ← " .. (b.is_error and "ERROR " or "") .. clip(body, 400)):gsub("\n", "\n    "))
        end
      end
    end
  end
  local first, last
  for _, r in ipairs(recs) do
    local t = r.timestamp and hr.parse_iso(r.timestamp)
    if t then first = first or t; last = t end
  end
  local mins = first and (last - first) / 60 or 0
  local text = ("# Transcript: %.0f min, %d tool calls, %d errors\n"):format(mins, calls, errors) .. table.concat(out, "\n")
  for _, r in ipairs(a.redact) do
    local old, new = r:match("^(.-)=(.*)$")
    text = hr.plain_replace(text, old, new)
  end
  print(text)
end

main()
