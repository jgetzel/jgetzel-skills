-- cjson set up to read and write what Python's json does: null decodes to nil, arrays stay arrays.
local cjson = require("cjson").new()
cjson.encode_number_precision(16)  -- 14 prints 2^53 as 9.007199254741e+15
cjson.encode_escape_forward_slash(false)
cjson.decode_array_with_array_mt(true)  -- a decoded [] re-encodes as [], not {}
local M = {}

local function denull(v)
  if v == cjson.null then return nil end
  if type(v) == "table" then
    for k, x in pairs(v) do v[k] = denull(x) end
  end
  return v
end

-- The value, or nil and the error for text that isn't JSON (Python's ValueError).
function M.decode(s)
  local ok, v = pcall(cjson.decode, s)
  if not ok then return nil, v end
  return denull(v)
end

M.encode = cjson.encode

function M.array(t)  -- t (or a new table) encodes as a JSON array even when empty
  return setmetatable(t or {}, cjson.array_mt)
end

return M
