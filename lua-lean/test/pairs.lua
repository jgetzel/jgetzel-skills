-- Traversals whose result does not hang on the order: a count, a sum, the keys sorted, a set's members cleared
-- during the walk; # of a list trimmed from the end, which keeps one border.
local function count(t)
  local n = 0
  for _ in pairs(t) do n = n + 1 end
  return n
end

local function sorted_keys(t)
  local ks = {}
  for k in pairs(t) do ks[#ks + 1] = k end
  table.sort(ks)
  return ks
end

local function drop_odd(t)
  local k, v = next(t)
  while k ~= nil do
    if v % 2 == 1 then t[k] = nil end
    k, v = next(t, k)
  end
  return t
end

local function pop(list)
  local top = list[#list]
  list[#list] = nil
  return top
end

local set = drop_odd({a = 1, b = 2, c = 4, d = 5})
local list = {3, 1, 2}
return count(set), table.concat(sorted_keys(set), ","), pop(list), #list
