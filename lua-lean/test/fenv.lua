-- Function environments: a template's function run in a sandbox that falls back on _G (setfenv), a config chunk
-- loaded into a table of its own (load's environment), and a function that switches its own globals (level 1)
local getfenv = getfenv

local function sandbox(f, vars)
  return setfenv(f, setmetatable(vars, {__index = _G}))
end

local function render(name)
  return "hello, " .. name .. " (" .. tostring(count) .. ")"
end

local function config(src)
  local t = {}
  assert(load(src, "=config", "t", t))()
  return t
end

local function counter()
  setfenv(1, {n = 0})
  n = n + 1
  return n, getfenv(1).n
end

local r = sandbox(render, {count = 3})
local c = config("width = 80 height = width / 2")
return r("ann"), c.width, c.height, counter(), getfenv(render).count, rawget(_G, "width"), getfenv(1) == _G
