import SwarmLean.Cmd
import SwarmLean.Db.Locks
import SwarmLean.Sys

/-! `swarm lock` and `swarm unlock` (locks.lua's cmd_lock, cmd_unlock), and repo_rel, which the edit hook uses too. -/

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

/-- The repo's toplevel and the path relative to it, for an absolute or `cwd`-relative path; none outside a repo
(locks.repo_rel). -/
def repoRel (path : String) (cwd : Option String) : m (Option (String × String)) := do
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
  if p == top then return some (top, ".")
  let pre := if top == "/" then "/" else top ++ "/"
  if p.startsWith pre then return some (top, (p.drop pre.length).toString)
  return none

/-- A lock path as typed made repo-relative, a trailing slash kept; as typed outside a repo (locks.norm). -/
def norm (path : String) : m String := do
  match ← repoRel path none with
  | none => return path
  | some (_, rel) => return rel ++ (if path.endsWith "/" && rel != "." then "/" else "")

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
  let path ← norm ((a.str "path").getD "")
  let now ← Clock.now
  if a.cmd == "lock" then
    let c : Tasks.Ctx := { me := n, now, here := ← env "HC_TERMINAL_ID" }
    orDie (← Store.txn [.agent, .lock, .event, .cursor] (Locks.lock c path ((a.str "reason").getD "") ((a.str "lease").getD "2h")))
    Env.out s!"locked {path}"
  else
    Store.txn [.lock] fun db => (Locks.unlock n path now db, ())
    Env.out s!"unlocked {path}"
  return 0

/-- The group: lock and unlock. -/
def group : Group m where
  specs := [("lock", lockSpec), ("unlock", unlockSpec)]
  run := run

end SwarmLean.Cmd.Locks
