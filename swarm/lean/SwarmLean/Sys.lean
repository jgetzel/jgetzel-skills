import SwarmLean.World

/-! The process and file calls beyond `Env`, `Fs` and `Proc` (luaposix's and lfs's), one class shared by the ported
modules; `RealSys.lean` gives the instance on IO. -/

namespace SwarmLean

/-- What is at a path (lfs's mode): nothing, a file, a directory, a symlink (only when not following), or else. -/
inductive Kind
  | none | file | dir | link | other
  deriving DecidableEq, Repr, Inhabited

/-- proc.exec's options: `env` is set on top of ours (none unsets), `merge` sends stderr to stdout, `stdoutFile` both. -/
structure RunOpts where
  cwd : Option String := none
  input : Option String := none
  env : List (String × Option String) := []
  merge : Bool := false
  stdoutFile : Option String := none

/-- The rest of the OS. -/
class Sys (m : Type → Type) where
  getpid : m Int
  getppid : m Int
  /-- posix.signal.kill(pid, 0) == 0 -/
  pidAlive : Int → m Bool
  /-- Sleeps `ms` milliseconds. -/
  sleep : Nat → m Unit
  /-- Epoch seconds with the fraction. -/
  nowF : m Float
  /-- os.date(fmt, t), local time. -/
  date : String → Int → m String
  /-- uname().nodename -/
  hostname : m String
  /-- The whole environment. -/
  environ : m (List (String × String))
  setenv : String → String → m Unit
  realpath : String → m (Option String)
  /-- A symlink's target, none when it is not one. -/
  readlink : String → m (Option String)
  /-- What is at a path, following a symlink (lfs.attributes) or not (lfs.symlinkattributes). -/
  kind : String → (follow : Bool) → m Kind
  /-- Modification time, epoch seconds. -/
  mtime : String → m (Option Int)
  /-- mkdir -p; false when it fails. -/
  mkdirp : String → m Bool
  /-- A hard link to the first path at the second; false when it fails. -/
  link : String → String → m Bool
  /-- Removes a file; false when it fails. -/
  remove : String → m Bool
  /-- proc.exec: runs argv to its end, waiting; code 127 when it can't start, 128+N when killed by signal N. -/
  exec : List String → RunOpts → m ProcOut

end SwarmLean
