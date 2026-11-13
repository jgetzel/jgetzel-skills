import SwarmLean.Args
import SwarmLean.World

/-! What a command group gives the dispatcher. One file per group under Cmd/, listed once in Dispatch.lean. -/

namespace SwarmLean

/-- A command group: the top-level commands it ports, each with its argparse parser and what runs it. -/
structure Group (m : Type → Type) where
  /-- each command word with its parser, as main.lua's `parser()` declares it -/
  specs : List (String × Args.Spec)
  /-- runs a parsed command line (the command word under `cmd`); returns the exit code -/
  run : Args.Parsed → m UInt32

/-- The `cmd` value of a parse. -/
def Args.Parsed.cmd (p : Args.Parsed) : String := (p.str "cmd").getD ""

/-- The `act` (subcommand) value of a parse. -/
def Args.Parsed.act (p : Args.Parsed) : String := (p.str "act").getD ""

end SwarmLean
