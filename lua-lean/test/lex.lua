-- LuaJIT's syntax beyond Lua 5.1 that the subset keeps: `\u{...}` escapes, empty statements anywhere (after `break`
-- and `return` too), and `continue`, `const` and `goto` as names (soft keywords in LuaJIT: `goto` before a name is a
-- statement).
;;
local s = "\u{41}\u{7ff}\u{800}\u{ffff}\u{10000}\u{10FFFF}\u{0000041}";
local continue, const = 1, 2;;
local t = {continue = continue, const = const}
for i = 1, 3 do if i > 1 then break;; end ; end
local function f() return continue;; end
local goto = {goto = 0}
for i = 1, 3 do if i > 2 then goto continue end goto.goto = goto.goto + i ::continue:: end
return s, t.continue + t.const + f() + goto.goto;;
