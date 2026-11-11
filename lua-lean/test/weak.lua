-- Weak tables: a cache keyed by the objects it describes (__mode = "k"), read by a key the caller holds, and an
-- intern table of strings under weak values, which the collector never frees; no read can see a freed entry.
local cache = setmetatable({}, {__mode = "k"})

local function area(r)
  local a = cache[r]
  if a == nil then
    a = r.w * r.h
    cache[r] = a
  end
  return a
end

local names = setmetatable({}, {})
getmetatable(names).__mode = "v"

local function intern(s)
  local v = names[s]
  if v == nil then
    names[s] = s
    v = s
  end
  return v
end

local r = {w = 3, h = 4}
return area(r), area(r), cache[r], intern("a"), intern("a"), rawget(names, "a")
