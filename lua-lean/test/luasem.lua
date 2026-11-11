-- What is compared with the Lean interpreter (LuaLean/Run.lean): a chunk's results
-- as text, `ok:` and each value, or `error`. Strings: bytes 32..126 but " and \ as themselves, the rest \ddd;
-- numbers %.17g; a table's entries sorted; one already on the path <cycle>.
local M = {}

-- the build, LuaLean/Num.lean's Target: single-number (x86-64's default) makes an integer 0 times -1 a -0
local z, n = 0, -1
M.target = 1 / (z * n) < 0 and "single" or "dual"

local function str(s)
  return '"' .. s:gsub('[%z\1-\31"\\\127-\255]', function(c) return ("\\%03d"):format(c:byte()) end) .. '"'
end

local function ser(v, path, depth)
  local t = type(v)
  if depth >= 100 then return "<deep>" end
  if t == "nil" or t == "boolean" then return tostring(v) end
  if t == "number" then return ("%.17g"):format(v) end
  if t == "string" then return str(v) end
  if t == "table" then
    if path[v] then return "<cycle>" end
    path[v] = true
    local es = {}
    for k, x in pairs(v) do es[#es + 1] = ser(k, path, depth + 1) .. "=" .. ser(x, path, depth + 1) end
    path[v] = nil
    table.sort(es)
    return "{" .. table.concat(es, ",") .. "}"
  end
  if t == "function" then return "function" end
  return "userdata"
end

function M.outcome(ok, ...)
  if not ok then return "error" end
  local r = {}
  for i = 1, select("#", ...) do r[i] = ser((select(i, ...)), {}, 0) end
  return "ok:" .. table.concat(r, ",")
end

-- src's results under LuaJIT, as text
function M.run(src)
  local f, err = loadstring(src, "=c")
  if not f then return "parse error: " .. err end
  return M.outcome(pcall(f))
end

-- a cases file (LuaLean/Gen.lean's writeCases, gzipped or not): each chunk under LuaJIT must give the Lean
-- interpreter's results for M.target (`single`, where given, else `out`); errors with the first differences
function M.check(file)
  local h = assert(io.popen((file:match("%.gz$") and "gzip -dc '" or "cat '") .. file .. "'"))
  local cases = assert(loadstring(h:read("*a"), "=" .. file))()
  h:close()
  assert(cases and #cases > 0, "no cases in " .. file)
  local bad, errs = {}, 0
  for i, k in ipairs(cases) do
    local got, want = M.run(k.src), M.target == "single" and k.single or k.out
    if got ~= want then bad[#bad + 1] = ("case %d:\n%s\n  LuaJIT: %s\n  Lean:   %s"):format(i, k.src, got, want) end
    if k.out == "error" then errs = errs + 1 end
  end
  if #bad > 0 then
    error(("%d of %d cases differ; the first:\n%s"):format(#bad, #cases, table.concat(bad, "\n", 1, math.min(3, #bad))), 0)
  end
  -- the cases must mostly run
  assert(errs < #cases / 4, ("%d of %d cases end in an error"):format(errs, #cases))
  return #cases
end

-- luajit luasem.lua <file.lua>...: each chunk's results; luajit luasem.lua --cases <file>: M.check
if arg and arg[0] and arg[0]:match("luasem%.lua$") then
  if arg[1] == "--cases" then
    local n = M.check(arg[2])
    print(("%s: %d cases agree (%s-number; %s %s, JIT %s)"):format(arg[2], n, M.target, jit.version, jit.arch,
      jit.status() and "on" or "off"))
  else
    for i = 1, #arg do
      local h = assert(io.open(arg[i], "rb")); local src = h:read("*a"); h:close()
      print(arg[i] .. ": " .. M.run(src))
    end
  end
end

return M
