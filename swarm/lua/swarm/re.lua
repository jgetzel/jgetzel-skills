-- Python's re on PCRE2 (users write Python regexes into .claude/swarm.json). Always UTF|UCP, so \w matches é.
-- A match m has m[0] (whole), m[1..n] (groups, nil if unset), m.s and m.e (1-based, inclusive).
-- Subjects must be valid UTF-8 (PCRE2 raises on bad bytes): clean text read from files first.
local rex = require "rex_pcre2"
local F = rex.flags()
local M = { S = F.DOTALL, M = F.MULTILINE, I = F.CASELESS }
local BASE = F.UTF + F.UCP
local cache = {}

local bor = require("bit").bor  -- flags are bits: summing two sets that share one would double it

-- A compiled pattern; raises on a bad one (Python's re.error).
function M.compile(pat, flags)
  local key = pat .. "\0" .. (flags or 0)
  local r = cache[key]
  if not r then
    r = rex.new(pat, bor(BASE, flags or 0))
    cache[key] = r
  end
  return r
end

local function match_at(r, s, init)
  local st, en, off = r:exec(s, init)
  if not st then return nil end
  local m = { [0] = s:sub(st, en), s = st, e = en, n = #off / 2 }
  for i = 1, m.n do
    local a, b = off[2 * i - 1], off[2 * i]
    if a then m[i] = s:sub(a, b) end
  end
  return m
end

function M.search(pat, s, flags)
  return match_at(M.compile(pat, flags), s, 1)
end

function M.match(pat, s, flags)  -- anchored at the start only
  return match_at(M.compile("\\A(?:" .. pat .. ")", flags), s, 1)
end

function M.fullmatch(pat, s, flags)  -- \z, not $: $ also matches before a final \n
  return match_at(M.compile("\\A(?:" .. pat .. ")\\z", flags), s, 1)
end

-- Iterator over non-overlapping matches, as finditer.
function M.finditer(pat, s, flags)
  local r, init = M.compile(pat, flags), 1
  return function()
    if init > #s + 1 then return nil end
    local m = match_at(r, s, init)
    if not m then init = #s + 2; return nil end
    init = m.e + 1
    if m.e < m.s then  -- an empty match moves on one character, not into the middle of one
      init = m.s + 1
      while s:byte(init) and s:byte(init) >= 128 and s:byte(init) < 192 do init = init + 1 end
    end
    return m
  end
end

-- A list: whole matches without groups, the group with one, else tables of groups ("" if unset), as findall.
function M.findall(pat, s, flags)
  local r = {}
  for m in M.finditer(pat, s, flags) do
    if m.n == 0 then r[#r + 1] = m[0]
    elseif m.n == 1 then r[#r + 1] = m[1] or ""
    else
      local g = {}
      for i = 1, m.n do g[i] = m[i] or "" end
      r[#r + 1] = g
    end
  end
  return r
end

-- Every match replaced with the literal text repl (no backreferences: the CLI uses none).
function M.sub(pat, repl, s, flags)
  return (rex.gsub(s, M.compile(pat, flags), function() return repl end))
end

-- Python's re.escape: every ASCII character but letters, digits and _ gets a backslash.
function M.escape(s)
  return (s:gsub("[^%w_\128-\255]", "\\%0"))
end

return M
