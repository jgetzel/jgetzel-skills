-- LuaJIT's bit library, as the global and through require: int32 arithmetic for hashes and encodings
local bit = require("bit")
local band, bxor, lshift, rshift = bit.band, bit.bxor, bit.lshift, bit.rshift
local M = {}

-- FNV-1a over a string's bytes, 32 bits
function M.fnv1a(s)
  local h = -2128831035
  for i = 1, #s do
    h = bxor(h, s:byte(i))
    -- h * 16777619 in pieces, each exact in a double
    h = bit.tobit(lshift(h, 24) + h * 403)
  end
  return h
end

-- the low n bits, and a bit's test
function M.low(x, n)
  return band(x, lshift(1, n) - 1)
end

function M.has(x, i)
  return band(rshift(x, i), 1) == 1
end

-- three bytes as four base64 indices
function M.sextets(a, b, c)
  local n = bit.bor(lshift(a, 16), lshift(b, 8), c)
  return rshift(n, 18), band(rshift(n, 12), 63), band(rshift(n, 6), 63), band(n, 63)
end

function M.hex(x)
  return bit.tohex(bit.bswap(x)), _G.bit.tohex(bit.bnot(x), -4), bit.rol(x, 4), bit.arshift(x, 28)
end

return M
