-- Every statement and every assignment target the parser accepts: names (local, upvalue, global), fields and
-- indices of a local, a call's value, a parenthesis and a string; several at once; function statements into fields
-- and methods; each kind of block and loop, goto as continue, break, a nested local function.
local t, log = {}, {}
local function f() return t end
g = nil

local function bump(k) log[#log + 1] = k end

t.a, (t).b, f().c, (f())["d"], t[1] = 1, 2, 3, 4
g, t.e = 5
do local x = 6; t[#t + 1] = x end

local o = {n = 0}
function o.inc(d) o.n = o.n + d end
function o:get() return self.n end
o.inc(7)

local s = 0
for i = 1, 3 do s = s + i end
for i = 10, 1, -4 do s = s + i end
for _, v in ipairs({1, 2}) do s = s + v end
while true do s = s + 1; if s > 30 then break end end
repeat local y = s; s = y - 1 until y < 30
for i = 1, 4 do
  if i % 2 == 0 then goto continue end
  bump(i)
  ::continue::
end
if s < 0 then s = -s elseif s == 0 then s = 1 else s = s + 0 end

local function fact(n) if n <= 1 then return 1 end return n * fact(n - 1) end
local ok = pcall(function() local q; ("str").x = 1 end)
f().z = fact(5)

return t.a, t.b, t.c, t.d, t[1], t[2], g, t.e, o:get(), s, log[1], log[2], t.z, ok
