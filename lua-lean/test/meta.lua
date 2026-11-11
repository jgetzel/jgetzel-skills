-- Metamethods read when they are used: a counter whose methods come through an __index function, whose new fields
-- are logged through __newindex, and which is called through __call; all three set after setmetatable.
local Counter = {}

function Counter.get(c) return c.n end

local function new(start)
  local seen = {}
  local mt = {}
  local self = setmetatable({n = start}, mt)
  mt.__index = function(_, k) return Counter[k] end
  mt.__newindex = function(t, k, v) seen[#seen + 1] = k; rawset(t, k, v) end
  mt.__call = function(t, d) t.n = t.n + d; return t.n end
  return self, seen
end

local c, seen = new(1)
c(2)
c.extra = true
c.n = 10
return c:get(), seen[1], seen[2], c.extra
