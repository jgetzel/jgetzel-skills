-- LuaJIT's FFI, its pure subset: C arrays, structs and unions over bytes, as a codec would use them
local ffi = require("ffi")
ffi.cdef [[
typedef struct { uint8_t r, g, b, a; } rgba;
union word { uint32_t u; uint8_t b[4]; uint16_t h[2]; };
]]
local M = {}

-- a 32-bit integer's bytes, little-endian, as a string (md5.lua's lei2str)
local int1 = ffi.typeof("int[1]")
function M.lei2str(i)
  return ffi.string(int1(i), 4)
end

-- the bytes of a word, and its halves
function M.split(u)
  local w = ffi.new("union word", u)
  return w.b[0], w.b[3], w.h[1]
end

-- a pixel packed from a table, then darkened
function M.pixel(t)
  local p = ffi.new("rgba", t)
  p.r = p.r / 2
  return p.r, p.g, p.b, p.a, ffi.sizeof(p)
end

-- the sum of n doubles stored and read back
function M.sum(n)
  local a = ffi.new("double[?]", n)
  for i = 0, n - 1 do a[i] = i * 0.5 end
  local s = 0
  for i = 0, n - 1 do s = s + a[i] end
  return s
end

-- C's conversions: an integer's truncation, a narrowing, a bool
function M.casts(x)
  return tonumber(ffi.cast("int32_t", x)), tonumber(ffi.cast("uint8_t", x)), tonumber(ffi.cast("bool", x))
end

-- a 32-bit integer from a string's first 4 bytes, little-endian (md5.lua's str2lei)
local ct_constcharptr = ffi.typeof("const char*")
local ct_constintptr = ffi.typeof("const int*")
function M.str2lei(s)
  local int = ct_constcharptr(s)
  return ffi.cast(ct_constintptr, int)[0]
end

-- a string's bytes reversed, a pointer walking back from the end of a buffer
function M.reverse(s)
  local n = #s
  local buf = ffi.new("uint8_t[?]", n + 1)
  local src = ffi.cast("const uint8_t*", s)
  local p = buf + n
  for i = 0, n - 1 do
    p = p - 1
    p[0] = src[i]
  end
  return ffi.string(buf), p == buf, (buf + n) - p
end

-- a string cut or padded to n bytes with c
function M.pad(s, n, c)
  local buf = ffi.new("uint8_t[?]", n)
  ffi.fill(buf, n, c)
  ffi.copy(buf, s, math.min(#s, n))
  return ffi.string(buf, n)
end

return M
