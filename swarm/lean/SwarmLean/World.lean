import SwarmLean.Store

/-! The outside world the commands are written against, one class per part, as `Store` is. A command is generic in
its monad `m` and asks for the classes it uses; `Real.lean` gives the instances on IO. -/

namespace SwarmLean

/-- The time. -/
class Clock (m : Type → Type) where
  /-- Epoch seconds (util.now). -/
  now : m Int
  /-- The local `HH:MM` of an epoch second (util.hhmm). -/
  hhmm : Int → m String

/-- The process's environment, standard streams and working directory. -/
class Env (m : Type → Type) where
  /-- An environment variable as set, the empty string included. -/
  var : String → m (Option String)
  /-- Writes a line to stdout. -/
  out : String → m Unit
  /-- Writes a line to stderr. -/
  err : String → m Unit
  /-- All of stdin. -/
  stdin : m String
  /-- The working directory. -/
  cwd : m String

/-- Files. -/
class Fs (m : Type → Type) where
  /-- A file's text, none when it can't be read; `-` reads stdin (util.slurp). -/
  read : String → m (Option String)
  /-- The entries of a directory, none when it can't be listed. -/
  list : String → m (Option (List String))
  /-- Writes a file; false when it can't. -/
  write : String → String → m Bool

/-- What a finished subprocess left. -/
structure ProcOut where
  code : UInt32
  stdout : String
  stderr : String

/-- Subprocesses. -/
class Proc (m : Type → Type) where
  /-- Runs `argv` in `cwd` (none: here) with `env` added, waits, and returns what it printed; none if it can't start. -/
  output : List String → Option String → List (String × String) → m (Option ProcOut)
  /-- Replaces this process with `argv` (looked up on PATH), same environment; returns only on failure, with why. -/
  exec : List String → m String
  /-- The Lua CLI's launcher (swarm/swarm), for what is not ported yet; none when it can't be found. -/
  luaCli : m (Option String)

/-- git, which the commands run only through this (bases.lua). -/
class Git (m : Type → Type) where
  /-- `git <args>` in `cwd`: its stdout when it exits 0, else none (proc.git). -/
  git : List String → Option String → m (Option String)

/-- How a command ends early: its exit code, its message already written. -/
structure Exit where
  code : UInt32

/-- Runs an action and catches whatever ends it early, an `Exit` (as `exit N`) or an error of the world, as its message:
the pcall around each of watchd's passes. -/
class Guard (m : Type → Type) where
  guard {α : Type} : m α → m (Except String α)

/-- An environment variable, none when unset or empty (agents.env). -/
def env [Monad m] [Env m] (k : String) : m (Option String) := return py (← Env.var k)

/-- Writes `swarm: msg` to stderr and exits 1 (util.die). -/
def die [Monad m] [Env m] [MonadExceptOf Exit m] (msg : String) : m α := do
  Env.err s!"swarm: {msg}"
  throw (Exit.mk 1)

/-- The agent this process runs as, or die (agents.me). -/
def me [Monad m] [Env m] [MonadExceptOf Exit m] : m String := do
  match ← env "SWARM_NAME" with
  | some n => pure n
  | none => die "SWARM_NAME is unset (run as a swarm agent, or export SWARM_NAME)"

/-- The value of an `Except` from a pure step, or die with its message. -/
def orDie [Monad m] [Env m] [MonadExceptOf Exit m] : Except String α → m α
  | .ok a => pure a
  | .error e => die e

end SwarmLean
