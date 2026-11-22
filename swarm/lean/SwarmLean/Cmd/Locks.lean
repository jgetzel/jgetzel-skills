import SwarmLean.Cmd
import SwarmLean.Db.Locks
import SwarmLean.Lib.Workspaces
import SwarmLean.Sys

/-! `swarm lock` and `swarm unlock` (locks.lua's cmd_lock, cmd_unlock) on a path in its repo, and repo_rel, which the
edit hook uses too. -/

namespace SwarmLean.Cmd.Locks
open Args

/-- os.path.join of two parts (util.join). -/
def join (a b : String) : String :=
  if b.startsWith "/" || a == "" then b else if a.endsWith "/" then a ++ b else a ++ "/" ++ b

/-- The directory part of a path (util.dirname): `""` without a slash, `/` for a top-level name. -/
def dirname (p : String) : String :=
  match (p.splitOn "/").dropLast with
  | [] => ""
  | ps => let x := "/".intercalate ps; if x == "" then "/" else x

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Sys m] [Git m]

/-- os.path.realpath, non-strict: `..` folded first, then the longest existing prefix resolved and the rest appended
(locks.lua's realpath). -/
def realpathLoose (p : String) : m String := do
  let parts := (p.splitOn "/").filter (· != "") |>.foldl (init := #[]) fun acc x =>
    if x == ".." then acc.pop else if x == "." then acc else acc.push x
  let mut parts := parts
  let mut tail : List String := []
  for _ in [0:parts.size + 1] do
    if let some r ← Sys.realpath ("/" ++ "/".intercalate parts.toList) then
      return if tail.isEmpty then r else join r ("/".intercalate tail)
    tail := parts.back! :: tail
    parts := parts.pop
  return p

/-- The toplevel of the worktree an absolute or `cwd`-relative path is in, and the path in its repo (the repo keyed by
its main worktree, as a lock is); none outside a repo (locks.repo_rel). -/
def repoRel (path : String) (cwd : Option String) : m (Option (String × Locks.InRepo)) := do
  let here := (← Sys.realpath (← Env.cwd)).getD "/"
  let p ← realpathLoose (join (join here (cwd.getD ".")) path)
  let mut dir := dirname p
  for _ in [0:p.length] do
    if dir == "/" || (← Sys.kind dir true) == .dir then break
    dir := dirname dir
  let some top ← Git.git ["rev-parse", "--show-toplevel"] (some dir) | return none
  let top := strip top
  if top == "" then return none
  let top ← realpathLoose top
  let pre := if top == "/" then "/" else top ++ "/"
  let rel := if p == top then some "." else if p.startsWith pre then some (p.drop pre.length).toString else none
  let some rel := rel | return none
  return some (top, { repo := (← Workspaces.main (some top)).getD top, rel })

/-- A lock path as typed made relative to its repo, a trailing slash kept; outside a repo as typed, in the folder's
repo (locks.norm). -/
def norm (path : String) : m Locks.InRepo := do
  match ← repoRel path none with
  | none => return { repo := (← Workspaces.main none).getD "", rel := path }
  | some (_, p) => return { p with rel := p.rel ++ (if path.endsWith "/" && p.rel != "." then "/" else "") }

/-- `swarm lock -h`. -/
def helpLock : String :=
  "Usage: swarm lock [-h] [--reason <reason>] [--lease <lease>] <path>\n\nArguments:\n   path\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --reason <reason>     default: \n   --lease <lease>       default: 2h"

/-- `swarm unlock -h`. -/
def helpUnlock : String :=
  "Usage: swarm unlock [-h] <path>\n\nArguments:\n   path\n\nOptions:\n   -h, --help            Show this help message and exit."

/-- The `lock` parser. -/
def lockSpec : Spec := .mk "lock" helpLock [{ name := "path" }] [opt "--reason" (some ""), opt "--lease" (some "2h")] [] [] none

/-- The `unlock` parser. -/
def unlockSpec : Spec := .mk "unlock" helpUnlock [{ name := "path" }] [] [] [] none

/-- `swarm lock` / `swarm unlock`. -/
def run (a : Parsed) : m UInt32 := do
  let n ← me
  let p ← norm ((a.str "path").getD "")
  let now ← Clock.now
  if a.cmd == "lock" then
    let c : Tasks.Ctx := { me := n, now, here := ← env "HC_TERMINAL_ID" }
    orDie (← Store.run (Locks.lockTxn c p ((a.str "reason").getD "") ((a.str "lease").getD "2h")))
    Env.out s!"locked {p.rel}"
  else
    Store.run (Locks.unlockTxn n p now)
    Env.out s!"unlocked {p.rel}"
  return 0

/-- The group: lock and unlock. -/
def group : Group m where
  specs := [("lock", lockSpec), ("unlock", unlockSpec)]
  run := run

end SwarmLean.Cmd.Locks
