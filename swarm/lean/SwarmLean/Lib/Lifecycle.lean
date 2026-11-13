import SwarmLean.Lib.Agents
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Workspaces

/-! watchd.lua's parts that `swarm end` and `swarm endable` run: whether an agent's work landed (landed_ref, landed,
unlanded, unclean_list), what keeps it (end_why, endable_reasons, over fate's reads of one agent), and the end itself
(end_agent). -/

namespace SwarmLean.Lifecycle
open Agents

variable {m : Type → Type} [Monad m]

/-- A command's exit code, 127 when it can't start. -/
def code [Proc m] (argv : List String) (cwd : Option String := none) : m UInt32 := do
  return ((← Proc.output argv cwd []).map (·.code)).getD 127

/-- A command's stdout when it exits 0 (proc.run). -/
def run [Proc m] (argv : List String) (cwd : Option String := none) : m (Option String) := do
  return (← Proc.output argv cwd []).bind fun o => if o.code == 0 then some o.stdout else none

/-- The commits of `ref` (checked from `cwd`) are in `b`: an ancestor, the same content under other commits, or a PR
merged at this commit (watchd.landed_ref). -/
def landedRef1 [Proc m] (cwd ref b : String) : m Bool := do
  if (← code ["git", "-C", cwd, "merge-base", "--is-ancestor", ref, b]) == 0 then return true
  let mb := py ((← run ["git", "-C", cwd, "merge-base", b, ref]).map strip)
  let files ← match mb with
    | some mb => do
      let out := (← run ["git", "-C", cwd, "diff", "--name-only", "-z", mb, ref]).getD ""
      pure ((out.splitOn "\x00").filter (· ≠ ""))
    | none => pure []
  if !files.isEmpty then  -- squash or rebase merge: same content under other commits
    if (← code (["git", "-C", cwd, "diff", "--quiet", ref, b, "--"] ++ files)) == 0 then return true
  let br := py ((← run ["git", "-C", cwd, "rev-parse", "--abbrev-ref", ref]).map strip)
  let head := py ((← run ["git", "-C", cwd, "rev-parse", ref]).map strip)
  let (some br, some head) := (br, head) | return false
  let some prs ← run ["gh", "pr", "list", "--head", br, "--state", "merged", "--json", "number,headRefOid"] (some cwd)
    | return false
  match Lean.Json.parse prs with
  | .ok (.arr a) => return a.any fun pr => (pr.getObjValAs? String "headRefOid").toOption == some head
  | _ => return false

/-- `ref` landed on any of the refs `bs` (watchd.landed_ref with a list). -/
def landedRef [Proc m] (cwd ref : String) (bs : List String) : m Bool := do
  for b in bs do if ← landedRef1 cwd ref b then return true
  return false

/-- Nothing in worktree `wt` is unlanded relative to any of the refs `bs` (watchd.landed). -/
def landed [Proc m] [Sys m] (wt : String) (bs : List String) (main : Option String) : m Bool := do
  if (← Sys.kind wt true) == .none then  -- nothing uncommitted can be lost; judge by its branch if git still knows it
    let mut inwt := false
    let mut br : Option String := none
    for l in splitlines ((← run ["git", "-C", main.getD "", "worktree", "list", "--porcelain"]).getD "") do
      if l.startsWith "worktree " then inwt := (l.drop 9).toString == wt
      else if inwt && l.startsWith "branch refs/heads/" then br := some (l.drop 18).toString; break
    match br with
    | none => return true
    | some b => return ← landedRef (main.getD "") b bs
  let some st ← run ["git", "-C", wt, "status", "--porcelain"] | return false
  if strip st != "" then return false
  return some wt == main || (← landedRef wt "HEAD" bs)

variable [Git m] [Fs m] [Proc m] [Sys m]

/-- A worktree `n` owns that holds work not on its tasks' bases, with those refs (watchd.unlanded); `wts` the live
agents' worktrees, `all` every worktree, `db` the agent, task and workspace tables. -/
def unlanded (db : Db) (n : String) (main : Option String) (wts all : List (String × String)) :
    m (Option (String × List String)) := do
  let names ← Bases.ofAgent ((db.tasks.filter (·.owner == some n)).map (·.base)) main
  let own := (wts.lookup n).toList ++ Workspaces.ownedWts n all (some db) ++ Workspaces.ownedWts n all
  for w in own.eraseDups do
    let mut bs ← Bases.refs names main
    if let some b := ((db.workspaces.find? fun x => x.path == w && x.agent == n && x.ro == some 0).bind (·.base)) then
      bs := bs ++ [← Bases.ref b main]
    if !(← landed w bs main) then return some (w, bs)
  return none

/-- What keeps worktree `wt` from landing on ref `b`: git status lines and `commit …` lines (watchd.unclean_list). -/
def uncleanList (wt b : String) : m String := do
  if (← Sys.kind wt true) == .none then return s!"{wt} is gone; its branch holds commits not on {b}"
  let st := (splitlines ((← run ["git", "-C", wt, "status", "--porcelain"]).getD "")).filter (· ≠ "")
  let lg := (splitlines ((← run ["git", "-C", wt, "log", "--oneline", b ++ "..HEAD"]).getD "")).filter (· ≠ "")
  return "\n".intercalate (st ++ lg.map ("commit " ++ ·))

/-- Job process `p` is just waiting: no descendant but sleep and shells, and little CPU (watchd.sleep_loop). -/
def sleepLoop (p : Machine.Ps) (ps : List Machine.Ps) : Bool :=
  let light := ["sleep", "bash", "sh", "zsh"]
  -- each level goes one process down; the tree is at most as deep as there are processes
  let rec walk : Nat → Int → Bool
    | 0, _ => true
    | n + 1, pid => ps.all fun q => q.ppid != pid || (light.contains q.comm && q.cpu_s ≤ 30 && walk n q.pid)
  p.cpu_s ≤ 30 && walk ps.length p.pid

/-- Fate's reads of one agent, each made only when asked (watchd.reads(…).f(n)). -/
structure Reads (m : Type → Type) where
  /-- it owns a claimed or blocked task -/
  claims : Bool
  /-- it holds a lock -/
  locks : Bool
  /-- its background job: a Bash-tool shell under its claude process -/
  job : m (Option Machine.Ps)
  /-- a worktree of its with work not on its bases, and those refs -/
  unlanded : m (Option (String × List String))

/-- The reads of agent `n` on `db` (agent, task, lock and workspace tables). -/
def reads (db : Db) (main : Option String) (wts all : List (String × String)) (n : String) : Reads m where
  claims := db.tasks.any fun t => t.owner == some n && (t.state = .claimed || t.state = .blocked)
  locks := db.locks.any (·.agent == some n)
  job := do return (Machine.bgAgents db.agents (← Machine.procs)).lookup n
  unlanded := unlanded db n main wts all

/-- The reads of agent `n` now: the db, the main worktree, the agents' and every worktree. -/
def readsNow [Store m] (n : String) : m (Db × Reads m) := do
  let db ← Store.txn [.agent, .task, .lock, .workspace] fun db => (db, db)
  return (db, reads db (← Workspaces.main none) (← Workspaces.wtMap db) (← Workspaces.worktrees) n)

/-- Why `swarm end` without `--force` refuses live agent row `a`, or none (watchd.end_why). -/
def endWhy (a : Agent) (f : Reads m) : m (Option String) := do
  if a.status != some "idle" then return some s!"is {a.status.getD "nil"}"
  if let some s := py a.stay then return some s!"stays for: {s}"
  if f.claims then return some "owns a claimed task"
  if f.locks then return some "holds a lock"
  if (← f.job).isSome then return some "has a background job running"
  if let some (held, _) ← f.unlanded then return some s!"has work not on its base in {held}"
  return none

/-- One thing that keeps an agent from being ended: its key, text, and whether it is declared (a stay, a blocked
task, its own job, a pushed branch). -/
structure Reason where
  key : String
  text : String
  declared : Bool

/-- Everything that keeps live agent row `a` from being ended (watchd.endable_reasons), for `swarm endable` and the
Stop hook. -/
def endableReasons [Clock m] (db : Db) (a : Agent) (f : Reads m) : m (List Reason) := do
  let n := a.name
  let mut out : List Reason := []
  if let some s := py a.stay then out := out ++ [⟨"stay", "stay: " ++ s, true⟩]
  for r in db.tasks.filter fun t => t.owner == some n && (t.state = .claimed || t.state = .blocked) do
    out := out ++ [⟨"claim", s!"claim held (#{r.id}{if r.state = .blocked then ", blocked on a question" else ""})", r.state = .blocked⟩]
  for l in db.locks.filter (·.agent == some n) do out := out ++ [⟨"lock", "lock held: " ++ l.path, false⟩]
  if let some p ← f.job then
    let cmd := Machine.jobCmd p.args
    let now ← Clock.now
    let head := s!"background job (pid {p.pid}, age {ago now (now - p.age)}): {cut cmd 200}"
    if sleepLoop p (← Machine.procs) then
      out := out ++ [⟨"idle-job", head ++ "\n  this poll loop is idle (only sleep runs, no CPU): it is not a wait" ++
        (if hasSub cmd "pgrep -f" then "; `pgrep -f` watches a name, not a pid, and matches peers' runs of the same script: wait on your job's completion notification or its PID" else ""), false⟩]
    else
      out := out ++ [⟨"job", head ++ s!"\n  a child of your own session (pid {p.pid}): stop it (TaskStop/KillShell) or wait for it", true⟩]
  if let some (held, bs) ← f.unlanded then
    let ls := (splitlines (← uncleanList held (bs.headD "main"))).filter (· ≠ "")
    let commits := ls.filter (·.startsWith "commit ")
    let dirty := ls.filter (!·.startsWith "commit ")
    if !dirty.isEmpty then out := out ++ [⟨"dirty", s!"dirty worktree {held}:\n  " ++ "\n  ".intercalate (dirty.take 20), false⟩]
    if !commits.isEmpty then
      -- shortcut: "pushed" = HEAD is on some origin branch, no task note required; upgrade if WIP gets lost
      let pushed := (py (← run ["git", "-C", held, "branch", "-r", "--contains", "HEAD"])).isSome
      out := out ++ [⟨"unlanded", s!"commits not on {bs.headD "nil"}{if pushed then " (branch pushed)" else ""}:\n  " ++
        "\n  ".intercalate (commits.take 10), pushed⟩]
  return out

/-- Agent GC: re-checks that `a` is still idle on the same terminal with no claim, lock or stay (unless `force`),
releases and ends it, then kills its terminal and what it left in its cgroup scope; false when it changed
(watchd.end_agent). `by_`: who ended it by hand. -/
def endAgent [Store m] [Clock m] [Env m] (a : Agent) (force : Bool) (by_ : Option String) : m Bool := do
  let n := a.name
  let now ← Clock.now
  let ok ← Store.txn [.agent, .task, .lock, .conflict, .pairkey] fun db =>
    let row := (live db).find? (·.name == n)
    let fine := match row with
      | none => false
      | some r => force || (r.status == some "idle" && r.hc == a.hc && r.stay.isNone &&
          !db.tasks.any (fun t => t.owner == some n && (t.state = .claimed || t.state = .blocked)) &&
          !db.locks.any (·.agent == some n))
    if !fine then (db, false) else
    let db := (release db n).setAgent n ({ · with ended := some now, status := some "ended" })
    (db.log now (some n) "end" none (some ((if force then "forced" else "landed") ++ (match by_ with | some b => " by " ++ b | none => ""))), true)
  if !ok then return false
  let cg ← match a.claude_pid with  -- read while claude lives
    | some p => Machine.cgroup p
    | none => pure none
  if let some h := py a.hc then
    discard <| Proc.output ["hc", "kill", h] none []
    discard <| Proc.output ["hc", "rm", h] none []
  if let some c := cg then discard <| Fs.write (c.dir ++ "/cgroup.kill") "1"  -- whatever the agent left in its scope
  return true

end SwarmLean.Lifecycle
