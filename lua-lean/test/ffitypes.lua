-- LuaJIT's FFI: a struct with methods and operators through its metatype, an enum's constants, and C calls into
-- the world's C library
local ffi = require("ffi")
ffi.cdef [[
typedef struct { double x, y; } vec2;
enum shape { CIRCLE, SQUARE = 4, TRIANGLE };
typedef struct { enum shape kind; double size; } fig;
size_t strlen(const char *s);
void *memset(void *s, int c, size_t n);
]]
local M = {}

local vec2
vec2 = ffi.metatype("vec2", {
  __add = function(a, b) return vec2(a.x + b.x, a.y + b.y) end,
  __eq = function(a, b) return a.x == b.x and a.y == b.y end,
  __index = { len2 = function(v) return v.x * v.x + v.y * v.y end },
})

-- a sum of two vectors, and its squared length through a method
function M.sum(ax, ay, bx, by)
  local v = vec2(ax, ay) + vec2(bx, by)
  return v.x, v.y, v:len2()
end

-- two vectors made apart, equal by __eq
function M.same(ax, ay)
  return vec2(ax, ay) == vec2(ax, ay)
end

-- an enum field from a constant's name, and a constant through ffi.C
function M.kind(name)
  return tonumber(ffi.new("fig", { name }).kind), ffi.C.TRIANGLE
end

function M.layout()
  return ffi.offsetof("fig", "size"), ffi.alignof("fig"), ffi.istype("vec2", vec2())
end

-- the world's: a string's length, a buffer filled
function M.len(s)
  return tonumber(ffi.C.strlen(s))
end

function M.fill(n, c)
  local b = ffi.new("uint8_t[?]", n)
  ffi.C.memset(b, c, n)
  return ffi.string(b, n)
end

return M
