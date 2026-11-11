-- What is compared with the Lean interpreter (LuaLean/Run.lean): a chunk's results as text, `ok:` and each value, or
-- `error:` and the error's value, then ` stdout:` and what it wrote there. Strings: bytes 32..126 but " and \ as
-- themselves, the rest \ddd; numbers %.17g; a table's entries sorted; one already on the path <cycle>.
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
  if t == "function" or t == "thread" then return t end
  return "userdata"
end

function M.outcome(ok, ...)
  if not ok then return "error:" .. ser((...), {}, 0) end
  local r = {}
  for i = 1, select("#", ...) do r[i] = ser((select(i, ...)), {}, 0) end
  return "ok:" .. table.concat(r, ",")
end

-- the world of LuaLean/Run.lean's caseFx: the local zone is UTC, and what a chunk writes to stdout (fd 1: print's
-- and io.write's) goes to a temporary file, to be read back
local ffi = require("ffi")
ffi.cdef [[
int setenv(const char *, const char *, int); void tzset(void);
int mkstemp(char *); int unlink(const char *); int dup(int); int dup2(int, int); int close(int); int fflush(void *);
int64_t lseek(int, int64_t, int); int ftruncate(int, int64_t); int64_t read(int, void *, size_t);
]]
ffi.C.setenv("TZ", "UTC", 1)
-- a chunk's ffi.cdef of a string an earlier chunk declared is not run again: LuaJIT's declarations outlive a chunk
-- (every chunk runs in this one state), the semantics' start from none
do
  local cdef, seen = ffi.cdef, {}
  ffi.cdef = function(s, ...)
    if seen[s] then return end
    cdef(s, ...)
    if type(s) == "string" then seen[s] = true end
  end
end
ffi.C.tzset()
local outFd
local function captured(f)
  if not outFd then
    local path = ffi.new("char[?]", 32, "/tmp/luasemXXXXXX")
    outFd = ffi.C.mkstemp(path)
    assert(outFd >= 0, "mkstemp failed")
    ffi.C.unlink(path)
  end
  ffi.C.fflush(nil)
  ffi.C.lseek(outFd, 0, 0)
  ffi.C.ftruncate(outFd, 0)
  local saved = ffi.C.dup(1)
  ffi.C.dup2(outFd, 1)
  local r = f()
  ffi.C.fflush(nil)
  ffi.C.dup2(saved, 1)
  ffi.C.close(saved)
  local n = tonumber(ffi.C.lseek(outFd, 0, 1))
  ffi.C.lseek(outFd, 0, 0)
  local buf = ffi.new("char[?]", n + 1)
  assert(ffi.C.read(outFd, buf, n) == n, "reading stdout back failed")
  return r, ffi.string(buf, n)
end

-- src's results under LuaJIT, as text, and what it wrote to stdout
function M.run(src)
  local f, err = loadstring(src, "=c")
  if not f then return "parse error: " .. err end
  local r, out = captured(function() return M.outcome(pcall(f)) end)
  return #out > 0 and r .. " stdout:" .. str(out) or r
end

-- `^` is libm's pow, and the committed cases hold glibc's (DESIGN.md, the host's libm): off Linux a chunk with `^`
-- may give the Lean text with each number within 1e-12 of it (macOS's pow is 1 ulp off glibc's near a halfway case)
local function nearPow(src, got, want)
  if jit.os == "Linux" or not src:find("^", 1, true) then return false end
  local gs, ws = {}, {}
  local function skel(s, t)
    return (s:gsub("%-?%d[%d.]*e?[-+]?%d*", function(n) t[#t + 1] = tonumber(n) or n return "#" end))
  end
  if skel(got, gs) ~= skel(want, ws) then return false end
  for i, g in ipairs(gs) do
    local w = ws[i]
    if g ~= w and not (type(g) == "number" and type(w) == "number" and math.abs(g - w) <= 1e-12 * math.abs(w)) then
      return false
    end
  end
  return true
end

-- a cases file (LuaLean/Gen.lean's writeCases, gzipped or not): each chunk under LuaJIT must give the Lean
-- interpreter's results for M.target (`single`, where given, else `out`); errors with the first differences.
-- `any`: errors may be most of them (`lua-lean check`'s random arguments)
function M.check(file, any)
  local h = assert(io.popen((file:match("%.gz$") and "gzip -dc '" or "cat '") .. file .. "'"))
  local cases = assert(loadstring(h:read("*a"), "=" .. file))()
  h:close()
  assert(cases and (any or #cases > 0), "no cases in " .. file)
  local bad, errs = {}, 0
  for i, k in ipairs(cases) do
    local got, want = M.run(k.src), M.target == "single" and k.single or k.out
    if got ~= want and not nearPow(k.src, got, want) then
      bad[#bad + 1] = ("case %d:\n%s\n  LuaJIT: %s\n  Lean:   %s"):format(i, k.src, got, want)
    end
    if k.out:match("^error:") then errs = errs + 1 end
  end
  if #bad > 0 then
    error(("%d of %d cases differ; the first:\n%s"):format(#bad, #cases, table.concat(bad, "\n", 1, math.min(3, #bad))), 0)
  end
  -- the cases must mostly run
  assert(any or errs < #cases / 4, ("%d of %d cases end in an error"):format(errs, #cases))
  return #cases
end

-- luajit luasem.lua <file.lua>...: each chunk's results; luajit luasem.lua --cases <file>: M.check
if arg and arg[0] and arg[0]:match("luasem%.lua$") then
  if arg[1] == "--cases" then
    local n = M.check(arg[2], arg[3] == "--any")
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
