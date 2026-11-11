-- The world through effects (DESIGN.md, Effects): greet writes one line to the default output, readings reads the
-- clock twice. examples/WorldSpec.lean proves what each adds to the trace of effects, under named axioms about the
-- world: that it takes a write, and that its clock answers and never goes back.
local function greet(name)
  io.write("hello, ", name, "\n")
end

local function readings()
  local t0 = os.time()
  local t1 = os.time()
  return t0, t1
end

return greet, readings
