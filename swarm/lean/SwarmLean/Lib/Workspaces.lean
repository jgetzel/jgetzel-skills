import SwarmLean.Lib.Bases
import SwarmLean.Lib.Re
import SwarmLean.Sys
import SwarmLean.Db.Agents

/-! workspaces.lua: the worktrees swarm makes for a task, recorded as workspace rows (ro=0 the agent's own, ro=1 a
read-only attachment); and conflict.lua's worktree list, owned worktrees and agent-to-worktree map. -/

namespace SwarmLean.Workspaces

variable {m : Type → Type} [Monad m]

/-- A path resolved, or as given when it can't be (workspaces' `real`). -/
def real [Sys m] (p : String) : m String := return (← Sys.realpath p).getD p

/-- The main checkout: the first worktree git lists from `cwd` (workspaces.main). -/
def main [Git m] [Sys m] (cwd : Option String) : m (Option String) := do
  let some out ← Git.git ["worktree", "list", "--porcelain"] cwd | return none
  if !out.startsWith "worktree " then return none
  return some (← real (String.ofList ((out.drop 9).toString.toList.takeWhile (· ≠ '\n'))))

/-- Every worktree with a branch checked out, as (resolved path, branch) (conflict.worktrees). -/
def worktrees [Git m] [Sys m] : m (List (String × String)) := do
  let mut cur : Option String := none
  let mut out := []
  for l in splitlines ((← Git.git ["worktree", "list", "--porcelain"] none).getD "") do
    if l.startsWith "worktree " then
      let p := (l.drop 9).toString
      cur := some (← real p)
    else if l.startsWith "branch refs/heads/" then
      if let some c := cur then out := out ++ [(c, (l.drop 18).toString)]
  return out

/-- The worktrees `name` owns that still exist; none when none was ever recorded for it (workspaces.owned). -/
def owned (db : Db) (name : String) (wts : List (String × String)) : Option (List String) :=
  let rows := db.workspaces.filter fun w => w.agent == name && w.ro == some 0
  if rows.isEmpty then none else some ((rows.map (·.path)).filter fun p => wts.any (·.1 == p))

/-- Every worktree `name` owns: recorded ones when `db` has any, else by name (branch `<name>/…`, directory ending in
`-<name>` or holding `-<name>-`) (conflict.owned_wts). -/
def ownedWts (name : String) (wts : List (String × String)) (db : Option Db := none) : List String :=
  match db.bind (owned · name wts) with
  | some rec => rec
  | none => (wts.filter fun (p, b) =>
      let base := basename p
      b.startsWith (name ++ "/") || base.endsWith ("-" ++ name) || hasSub base ("-" ++ name ++ "-")).map (·.1)

/-- Each live agent's worktree: agent.wt, else its recorded one, else the one whose branch is `<name>/…`
(conflict.wt_map, given the worktrees). -/
def wtMapOf (db : Db) (wts : List (String × String)) : List (String × String) :=
  (Agents.live db).filterMap fun a =>
    let w := match py a.wt with
      | some w => some w
      | none => match ((owned db a.name wts).getD []).head? with
        | some w => some w
        | none => (wts.find? fun (x : String × String) => x.2.startsWith (a.name ++ "/")).map Prod.fst
    w.map (a.name, ·)

/-- Each live agent's worktree (conflict.wt_map); `db` holds the agent and workspace tables. -/
def wtMap [Git m] [Sys m] (db : Db) : m (List (String × String)) := return wtMapOf db (← worktrees)

/-- `db` with a workspace row put in place of one with its path and agent (insert or replace). -/
def upsert (db : Db) (w : Workspace) : Db :=
  { db with workspaces := db.workspaces.filter (fun x => !(x.path == w.path && x.agent == w.agent)) ++ [w] }

variable [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- `git worktree add ../<repo>-<agent> -b <agent>/<task> <base ref>`, recorded: path, branch, base
(workspaces.create). -/
def create (name : String) (task : Task) (cwd : Option String) : m (String × String × String) := do
  let some main ← main cwd | die "not in a git repo: no worktree to make"
  let base ← Bases.baseFor task.base (some main)
  Bases.fetch base (some main)
  let mut path := joinPath (dirname main) (basename main ++ "-" ++ name)
  if (← Sys.kind path true) != .none then path := path ++ "-" ++ d task.id  -- a predecessor's worktree is still there
  let mut branch := s!"{name}/{task.id}"
  if (← Git.git ["rev-parse", "--verify", "-q", "refs/heads/" ++ branch] (some main)).isSome then
    branch := branch ++ "-" ++ d (← Clock.now)
  let o ← Proc.output ["git", "-C", main, "worktree", "add", "-q", path, "-b", branch, ← Bases.ref base (some main)] none []
  match o with
  | some o => if o.code != 0 then die ("git worktree add failed: " ++ strip o.stderr)
  | none => die "git worktree add failed: "
  let rp ← real path
  Store.txn [.workspace] fun db => (upsert db { path := rp, branch, base, agent := name, ro := some 0 }, ())
  return (rp, branch, base)

/-- A launch that failed leaves nothing: the workspace row, and the fresh worktree and its branch when `created`
(workspaces.discard). -/
def discardWs (name path branch : String) (created : Bool) : m Unit := do
  Store.txn [.workspace] fun db => ({ db with workspaces := db.workspaces.filter fun w => !(w.agent == name && w.path == path) }, ())
  if created then
    if let some main ← main (some path) then
      discard <| Proc.output ["git", "-C", main, "worktree", "remove", "--force", path] none []
      discard <| Proc.output ["git", "-C", main, "branch", "-D", branch] none []

/-- Links `name` read-only to a recorded workspace: path, branch, base (workspaces.attach). -/
def attach (name path : String) : m (String × Option String × Option String) := do
  let path ← real path
  let w ← Store.txn [.workspace] fun db =>
    match db.workspaces.find? fun w => w.path == path && w.ro == some 0 with
    | some w => (upsert db { path, branch := w.branch, base := w.base, agent := name, ro := some 1 }, some w)
    | none => (db, none)
  let some w := w | die s!"{path} is not a swarm workspace"
  return (path, w.branch, w.base)

/-- The protected bases (bases.protected): main, the default and every base a task names; `db` holds the tasks. -/
def protectedOf (db : Db) (cwd : Option String) : m (List String) :=
  Bases.protectedBases ((db.tasks.filterMap (·.base)).eraseDups) cwd

/-- The base branch `cmd` would check out in an agent's workspace (`git checkout main`), if any
(workspaces.base_checkout); `db` holds the workspace and task tables. -/
def baseCheckout (db : Db) (name cmd : String) (cwd : Option String) : m (Option String) := do
  if !db.workspaces.any (·.agent == name) then return none
  let some mt := (Re.search "\\bgit\\s+(?:checkout|switch)\\s+(?:-[qf]\\s+)*([^\\s;&|-][^\\s;&|]*)\\s*(?:$|[;&|])" cmd).toOption.join
    | return none
  let g := mt.group 1
  return (← protectedOf db cwd).find? fun b => g == some b || g == some ("origin/" ++ b)

/-- Agents' workspaces with a base checked out, as (agent, path, base) (workspaces.base_out). -/
def baseOut (db : Db) (wts : List (String × String)) : m (List (String × String × String)) := do
  let prot ← protectedOf db (← main none)
  return (db.workspaces.filter (·.ro == some 0)).flatMap fun w =>
    (wts.filter fun (p, b) => p == w.path && prot.contains b).map fun (_, b) => (w.agent, w.path, b)

end SwarmLean.Workspaces
