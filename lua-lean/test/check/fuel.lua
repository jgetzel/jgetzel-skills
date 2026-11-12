-- a loop that runs out of fuel (rxi/json.lua's decode_error(str, 2^53)): each iteration binds a local, so a heap
-- copied on each alloc made this quadratic (board #51)
local n = 0
for i = 1, 2 ^ 53 do n = n + 1 end
return n
