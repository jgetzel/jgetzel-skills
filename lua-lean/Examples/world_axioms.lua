-- Examples/WorldSpec.lean's axioms about the world, each tested by its name against LuaJIT on this machine.

-- takes_writes: io.write answers (true, where the write succeeds)
assert(io.write("") == true, "takes_writes")

-- clock_answers: os.time() answers a time_t, an integer
local t = os.time()
assert(type(t) == "number" and t == math.floor(t), "clock_answers")

-- clock_mono: no reading is earlier than one before it
local last = os.time()
for _ = 1, 100000 do
  local now = os.time()
  assert(now >= last, "clock_mono")
  last = now
end

print("world_axioms: takes_writes, clock_answers, clock_mono hold")
