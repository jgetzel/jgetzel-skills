-- coroutines: a generator through wrap, a producer and consumer through create and resume, a yield across pcall
local function range(n, step)
  return coroutine.wrap(function()
    for i = 1, n, step do coroutine.yield(i) end
  end)
end

local function sum(gen)
  local s = 0
  for v in gen do s = s + v end
  return s
end

local function producer(items)
  return coroutine.create(function(first)
    local got = {first}
    for _, x in ipairs(items) do
      local ok, back = pcall(coroutine.yield, x)
      got[#got + 1] = ok and back or "err"
    end
    return got
  end)
end

local function drain(co)
  local out, k = {}, 0
  while coroutine.status(co) ~= "dead" do
    k = k + 1
    local ok, v = coroutine.resume(co, k)
    if not ok then return nil, v end
    out[#out + 1] = v
  end
  return out, coroutine.resume(co)
end

return sum(range(10, 3)), drain(producer({"a", "b"}))
