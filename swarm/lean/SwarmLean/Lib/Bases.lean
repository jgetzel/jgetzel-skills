import SwarmLean.World
import SwarmLean.Lib.Json

/-! bases.lua: the branch a task's work lands on and the refs git compares against. -/

namespace SwarmLean.Bases

variable {m : Type → Type} [Monad m] [Git m] [Fs m]

/-- Distinct, in first-seen order. -/
def uniq (l : List String) : List String := l.foldl (fun r x => if r.contains x then r else r ++ [x]) []

/-- `.claude/swarm.json`'s base at the repo's top, else main (bases.default). -/
def default (cwd : Option String) : m String := do
  let some top := (← Git.git ["rev-parse", "--show-toplevel"] cwd).map strip | return "main"
  let txt := (← Fs.read s!"{top}/.claude/swarm.json").getD ""
  return ((Json.decode txt).bind (Json.fstr · "base")).filter (· ≠ "") |>.getD "main"

/-- A task's base: its own, else the default (bases.base_for). -/
def baseFor (base : Option String) (cwd : Option String) : m String := do
  match base with
  | some b => if b != "" then return b else default cwd
  | none => default cwd

/-- `origin/<b>` when origin has it (bases.remote_ref). -/
def remoteRef (b : String) (cwd : Option String) : m (Option String) := do
  return (← Git.git ["rev-parse", "--verify", "-q", s!"refs/remotes/origin/{b}"] cwd).map fun _ => s!"origin/{b}"

/-- The ref git compares against: `origin/<b>` when origin has it, else `<b>` (bases.ref). -/
def ref (b : String) (cwd : Option String) : m String := return (← remoteRef b cwd).getD b

/-- Brings origin's `<b>` up to date; a base with no remote branch fails quietly (bases.fetch). -/
def fetch [Proc m] (b : String) (cwd : Option String) : m Unit := do
  if strip ((← Git.git ["remote", "get-url", "origin"] cwd).getD "") != "" then
    discard <| Proc.output ["git", "fetch", "-q", "origin", b] cwd []

/-- The bases an agent's work must be on: those of the tasks it owns, else the default (bases.of_agent). -/
def ofAgent (owned : List (Option String)) (cwd : Option String) : m (List String) := do
  if owned.isEmpty then return [← default cwd]
  return uniq (← owned.mapM (baseFor · cwd))

/-- What the sweep protects: main, the default and every base a task names (bases.protected). -/
def protectedBases (named : List String) (cwd : Option String) : m (List String) := do
  return uniq (["main", ← default cwd] ++ (← named.mapM fun b => baseFor (some b) cwd))

/-- The refs of bases (bases.refs). -/
def refs (names : List String) (cwd : Option String) : m (List String) := do
  return uniq (← names.mapM (ref · cwd))

end SwarmLean.Bases
