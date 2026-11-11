-- Comparison and conversion metamethods: versions compared through __eq, __lt and __le (or __lt alone, which <=
-- falls back to), printed through __tostring, and a metatable protected by __metatable.
local Version = {}
Version.__index = Version
Version.__metatable = "Version"

function Version.__eq(a, b) return a.major == b.major and a.minor == b.minor end
function Version.__lt(a, b) return a.major < b.major or (a.major == b.major and a.minor < b.minor) end
function Version.__tostring(v) return v.major .. "." .. v.minor end

local function new(major, minor)
  return setmetatable({major = major, minor = minor}, Version)
end

local a, b, c = new(1, 2), new(1, 10), new(1, 2)
local sorted = {b, c, a}
table.sort(sorted)
local locked = pcall(setmetatable, a, nil)
return a == c, a ~= b, a < b, b <= a, a >= c, tostring(sorted[3]), ("%s<%s"):format(a, b), getmetatable(a), locked
