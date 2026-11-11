-- Operator metamethods: a 2-vector with +, -, * by a number on either side, unary minus, and .. into text, all
-- read from the metatable when the operator runs; # on it is the array part's border (LuaJIT 2.1 never calls __len).
local V = {}

local function vec(x, y) return setmetatable({x, y}, V) end

V.__add = function(a, b) return vec(a[1] + b[1], a[2] + b[2]) end
V.__sub = function(a, b) return a + -b end
V.__unm = function(a) return vec(-a[1], -a[2]) end
V.__mul = function(a, b)
  if type(a) == "number" then a, b = b, a end
  return vec(a[1] * b, a[2] * b)
end
V.__concat = function(a, b)
  local function text(v) if type(v) == "table" then return "(" .. v[1] .. "," .. v[2] .. ")" end return v end
  return text(a) .. text(b)
end
V.__len = function() return 99 end

local p = vec(1, 2) + 2 * vec(3, 4) - vec(0, 1)
return "p = " .. p, #p, p[1], p[2]
