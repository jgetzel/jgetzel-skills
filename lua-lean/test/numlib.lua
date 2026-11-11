-- Helpers of the kind a script has, over the rest of the math and table libraries, select and tonumber with a base
local M = {}

function M.mean(...)
  local n = select("#", ...)
  local s = 0
  for i = 1, n do s = s + select(i, ...) end
  return s / n
end

function M.wrap(a, lo, hi)
  return lo + math.fmod(a - lo, hi - lo)
end

function M.rgb(hex)
  local v = tonumber(hex:sub(2), 16)
  return math.floor(v / 65536), math.floor(v / 256) % 256, v % 256
end

function M.polar(x, y)
  local m, e = math.frexp(math.sqrt(x * x + y * y))
  return math.ldexp(m, e), math.deg(math.atan2(y, x)), math.modf(x / (y ~= 0 and y or 1))
end

function M.tail(t, k)
  local r = table.move(t, #t - k + 1, #t, 1, {})
  table.foreachi(r, function(i, v) r[i] = tostring(v) end)
  return table.concat(r, " ")
end

return M
