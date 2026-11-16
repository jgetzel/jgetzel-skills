/-! What `claim` needs of the world, as a record: `Main.lean` fills it with `IO`, swarm from its `Proc`/`Sys`/`Clock`/`Env`
classes. -/

namespace Claims

/-- The world. `run`: an argv's exit code and stdout, none when it did not start. -/
structure Host (m : Type → Type) where
  run : List String → m (Option (Int × String))
  /-- Sleeps `ms` milliseconds. -/
  sleep : Nat → m Unit
  /-- A line to stderr. -/
  err : String → m Unit
  /-- A line to stdout. -/
  out : String → m Unit
  /-- Epoch seconds. -/
  now : m Int

end Claims
