import SwarmLean.Lib.Lifecycle
import SwarmLean.Lib.Run
import SwarmLean.Lib.Cost
import SwarmLean.Lib.Spawn
import SwarmModel.Decide

/-! watchd.lua's passes: reap (keeps), the worktree sweep, the lifecycle (fate's verdicts acted on, digests,
auto-spawn), and the notices of an unclean, quiet, hung or blocking agent, and the machine tick. The tick and the
loop around them are `Cmd/Watchd.lean`. -/

namespace SwarmLean.Watchd
open Agents

/-- The question an hc-blocked task carries (watchd.HC_Q). -/
def HC_Q : String := "a prompt needs the human"

/-- Seconds after its spawn a terminal with no hc status counts as hc-blocked: Claude never started (a folder-trust
dialog; watchd.START_WAIT). -/
def START_WAIT : Int := 120
/-- An idle agent kept only by its unclean worktree this long (s) is told what holds it. -/
def UNCLEAN_IDLE : Int := 1800
/-- A stayer idle this long (s) is asked if it still stays. -/
def LIVENESS_IDLE : Int := 50 * 60
/-- A free-text stay (no `--until`) is asked what it waits for this idle long (s) after it was set, then each LIVENESS_IDLE. -/
def LIVENESS_FREE : Int := 15 * 60
/-- ...and is hung if its last_active has not moved this long (s) after. -/
def LIVENESS_WAIT : Int := 5 * 60
/-- A finished agent idle this long (s), held only by a sleep-loop job, is nudged once. -/
def JOB_IDLE : Int := 10 * 60
/-- ...and ended this long (s) after the nudge if still idle. -/
def JOB_GRACE : Int := 10 * 60
/-- A finished agent's job whose process tree used no CPU second, started or ended no process this long (s) is hung, as
a sleep loop is idle (board #125: a `lake env lean X | head` that sat 5 h at 0% CPU). A build burns CPU every tick. -/
def JOB_HUNG : Int := 20 * 60
/-- Failed launches in a row before auto-spawn gives up on a task. -/
def SPAWN_FAILS : Nat := 5

/-- The owner row's columns `Decide.keepsL` reads: a NULL status is no status ("" is not "idle"). -/
def keepRow (a : Agent) : Swarm.Decide.ARow := { ended := a.ended.map Int.toNat, status := a.status.getD "", hc := a.hc }

/-- Whether owner row `o` keeps a claim past its lease for the work it is doing (watchd.keeps): the model's
`Decide.keepsL`, proved to be its `keeps` (`keeps_lifted`). Live, and working, prompt-blocked, running a background
job (`bg`) or in a compaction the swarm asked for (`compacting`), unless hc no longer lists its bound terminal (`live`:
the live addresses, none when hc can't tell). -/
def keeps (o : Option Agent) (bg compacting : Bool) (live : Option (List String)) : Bool :=
  Swarm.Decide.keepsL (o.map keepRow) bg compacting live

/-- Agent `a` is flagged hung: a `stay-hung` event since its last_active (it did not answer a liveness check). -/
def hungNow (evs : List Event) (a : Agent) : Bool :=
  evs.any fun e => e.agent == some a.name && e.kind == some "stay-hung" && e.ts.any (· ≥ a.last_active.getD 0)

/-- Whether owner row `o` keeps a claim past its lease for being live (board #193), idle or not: not ended, bound to a
terminal hc still lists (or hc can't tell), and not flagged hung. An unbound row (a spawn that never launched) does not. -/
def lives (o : Option Agent) (hung : Bool) (live : Option (List String)) : Bool :=
  match o with
  | none => false
  | some a => a.ended.isNone && (py a.hc).isSome && !hung && live.all fun up => up.contains (a.hc.getD "")

/-- `p` is `wt` or under it (watchd.inside). -/
def inside (p wt : String) : Bool := p == wt || p.startsWith (wt ++ "/")

/-- Open tasks waiting, directly or through other open tasks, on any of `ids` (watchd.dependants). -/
def dependants (db : Db) (ids : List Int) : Nat := Id.run do
  let mut seen : List Int := []
  let mut q := ids
  -- each round adds at least one task to `seen` or ends; there are no more rounds than tasks
  for _ in [0:db.tasks.length + 1] do
    if q.isEmpty then break
    let mut nq := []
    for i in q do
      for r in Tasks.waiters db i do
        if !seen.contains (r.id : Int) then seen := seen ++ [(r.id : Int)]; nq := nq ++ [(r.id : Int)]
    q := nq
  return seen.length

/-- The latest event of one of `kinds` (watchd.last_event). -/
def lastEvent (db : Db) (kinds : List String) : Option String :=
  ((db.events.filter fun e => e.kind.any kinds.contains).getLast?).bind (·.kind)

/-- Posts as `swarm` (msgs.post from watchd). -/
def say (db : Db) (now : Int) (dest : Msgs.Dest) (body : String) (urgent : Bool) (kind : String) : Db :=
  (Msgs.post db now .system dest body urgent (some kind)).1

-- ---------- a pass's shape (sw-architecture-review §4 B1) ----------

/-- What a tick read of the machine before deciding, no db rows: the clock, once, and hc's terminals. -/
structure TickIn where
  now : Int
  terms : Option (List Term) := none
  away : Bool := false

/-- The order of a send and its mark: `atMost` marks, then sends (a failed send is not retried); `atLeast` sends,
then marks once it went (a crash between resends). -/
inductive Once | atMost | atLeast
  deriving BEq, Inhabited

/-- A non-db effect a pass asks for; `runActs` (Cmd/Watchd.lean) runs it. -/
inductive Act
  /-- `text` to agent `agent` at terminal `hc`, its `mark` run around the send as `once` says -/
  | send (agent hc text : String) (mark : List Stmt) (once : Once)
  /-- the agent ended (`Lifecycle.endAgent`) -/
  | endAgent (a : Agent)
  /-- hc terminal `hc` killed and removed -/
  | kill (hc : String)
  /-- a line to stderr -/
  | err (line : String)

/-- The `lease-late` event of task `id` with `data` (`holder`: its owner told; `comms`: the communicator) in the last
LEASE before `t`. -/
def leaseLateEv (db : Db) (id : Nat) (data : String) (t : Int) : Option Event :=
  (db.events.filter fun e => e.kind == some "lease-late" && e.path == some (d id) && e.data == some data &&
    e.ts.any (· > t - Tasks.LEASE)).getLast?

/-- Reap's notices of lapsed claim `r` its live owner `o` keeps (board #193), each once per LEASE: the owner first (a
message that wakes it, urgent when it is idle so a cold one wakes too; `hhmm` the lease's end); then the communicator, if the owner has been active since it was told
and is idle again without a renew (`quiet`: not while it compacts). -/
def leaseLate (r : Task) (o : Option Agent) (t : Int) (hhmm : String) (comms : Option String) (quiet : Bool) (db : Db) :
    Db :=
  let own := r.owner.getD "nil"
  match leaseLateEv db r.id "holder" t with
  | none =>
    let db := db.log t r.owner "lease-late" (some (d r.id)) (some "holder")
    match r.owner with
    | none => db
    | some own => say db t (.agent own) (s!"Your lease on #{d r.id} ended at {hhmm}; `swarm task renew {d r.id}` (it is kept while you are " ++
        "live, but renew on long work).") (o.any (·.status == some "idle")) "system"
  | some h =>
    match comms, o with
    | some c, some a =>
      if !quiet && a.status == some "idle" && a.last_active.any (· > h.ts.getD 0) &&
          (leaseLateEv db r.id "comms" t).isNone then
        let db := db.log t r.owner "lease-late" (some (d r.id)) (some "comms")
        say db t (.agent c) (s!"{own} has held #{d r.id} past its lease (idle {ago t (a.last_active.getD 0)}) and did not renew " ++
          "it when told.") false "notice"
      else db
    | _, _ => db

-- ---------- reap ----------

/-- Reap's reopen of lapsed claim `r` (read before): only if the task is still claimed by the same owner with its lease
before `t` (a renew or re-claim since the read keeps it); the owner is told; true when it reopened it. -/
def reapTask (r : Task) (t now : Int) (db : Db) : Db × Bool :=
  match db.find r.id with
  | some x =>
    if x.owner == r.owner && x.owner.isSome && x.state = .claimed && x.lease_until.any (· < t) then
      let db := db.set r.id fun x => { x with state := .open, owner := none, lease_until := none }
      let db := match r.owner with
        | none => db
        | some own => say db now (.agent own) (s!"released #{d r.id} ({r.title.getD "nil"}): its lease ended and watchd did not see you " ++
            s!"live (ended, no terminal, or no answer to the liveness check). `swarm task claim {d r.id}` to take it back.")
            false "system"
      (db.log now r.owner "reap" none (some s!"task #{d r.id} lease expired"), true)
    else (db, false)
  | none => (db, false)

/-- Reap's drop of expired lock `l` (read before): only if that agent's lock on the path is still expired at `t` (a
fresh lock on the path since the read stays); true when it dropped it. -/
def reapLock (l : Lock) (t now : Int) (db : Db) : Db × Bool :=
  if db.locks.any fun x => x.path == l.path && x.agent == l.agent && x.lease_until.any (· < t) then
    let db := { db with locks := db.locks.filter fun x => !(x.path == l.path && x.agent == l.agent) }
    (db.log now l.agent "reap" (some l.path) (some "lock expired"), true)
  else (db, false)

/-- Reap of agent `n` whose terminal `h` hc no longer lists: only if the row is still live and bound to `h`; it ends,
what it held is released, everyone is told; true when it ended it. -/
def reapGone (n h : String) (t : Int) (db : Db) : Db × Bool :=
  if (db.agent n).any fun x => x.hc == some h && x.ended.isNone then
    let db := endRow db n t
    let db := say db t (.all db.swarm) s!"{n} is gone; its tasks and locks are released." false "system"
    (db.log t (some n) "reap" none (some "agent gone"), true)
  else (db, false)

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- git's stdout stripped, none when it fails (proc.git). -/
def git (args : List String) (cwd : Option String := none) : m (Option String) := return (← Git.git args cwd).map strip

/-- A path's realpath, the path itself when it has none. -/
def real (p : String) : m String := Workspaces.real p

/-- The events `keeps` and `lives` read of an owner: its compactions (`Compact.compacting`) and liveness flags (`hungNow`). -/
def KEEP_KINDS : List String := ["compact-asked", "ctx-compact", "ctx-continue", "compact", "stay-hung"]

/-- Owner `n`'s events of `KEEP_KINDS`. -/
def keepSel (n : String) : Sel :=
  { table := .event, cond := .and (.eq "agent" (.text n)) (.oneOf "kind" (KEEP_KINDS.map .text)) }

/-- What `reapClaim` reads of lapsed claim `r`: the task, its `lease-late` events, its owner's row and `keepSel`. -/
def claimSels (r : Task) : List Sel :=
  [Sels.task (r.id : Int), { table := .event, cond := .and (.eq "kind" (.text "lease-late")) (.eq "path" (.text (d r.id))) }] ++
    match r.owner with
    | some n => [Sels.agent n, keepSel n]
    | none => []

/-- Reap's step on lapsed claim `r` (read before), on the rows read now: its owner keeps it for its work or lives
(`keeps`, `lives`; `bg` the agents running a background job, `live` hc's live terminals): told (`leaseLate`, `hhmm` the
lease's end); else reopened (`reapTask`), and a hung owner's reopen told to the communicator. True when it reopened it. -/
def reapClaim (r : Task) (t : Int) (hhmm : String) (comms : Option String) (bg : List String)
    (live : Option (List String)) (db : Db) : Db × Bool :=
  let o := r.owner.bind db.agent
  let comp := o.any fun a => Compact.compacting db.events a.name (a.last_active.getD 0) t
  let hung := o.any (hungNow db.events)
  if keeps o (o.any fun a => bg.contains a.name) comp live || lives o hung live then
    -- its owner is live (working, blocked, waiting on a job, compacting, or idle and not hung): keep it, tell them
    (leaseLate r o t hhmm comms comp db, false)
  else
    let (db, done) := reapTask r t t db
    match done && hung, comms with
    | true, some c =>
      let own := r.owner.getD "nil"
      (say db t (.agent c) (s!"#{d r.id} reopened: {own} is hung (no answer to the liveness " ++
        s!"check). `swarm nudge {own}`, or end it.") false "system", true)
    | _, _ => (db, done)

/-- The lock row `l` by its key. -/
def lockSel (l : Lock) : Sel :=
  { table := .lock, cond := .and (.eq "repo" (.text l.repo)) (.eq "path" (.text l.path)) }

/-- Reopens expired task leases whose owner neither keeps them for its work nor lives (`reapClaim`): a kept one is told
to its owner, then maybe the communicator (`leaseLate`); a hung owner's reopened one is told to the communicator. A
claim of an agent of another swarm (`foreign`) is left to that swarm's reap. Drops expired locks of `repo`, ends the
agents whose bound terminal hc no longer lists and asks for the kill of the terminal of an ended row hc still lists
(`live`: none skips both) (watchd.reap). One read of the scope, then one transaction per task, lock and agent, each
deciding on the rows it reads; `t` stamps the writes. What it did, and the kills for `runActs`. -/
def reap (live : Option (List String)) (t : Int) (comms : Option String) (foreign : List String := [])
    (repo : String := "") : m (List String × List Act) := do
  let db ← Store.view [Sels.all .agent, { table := .task, cond := .eq "state" (.text "claimed") },
    { table := .lock, cond := .eq "repo" (.text repo) }] id
  let lapsed := db.tasks.filter fun r => r.state = .claimed && r.lease_until.any (· < t) &&
    !((r.owner.bind db.agent).isNone && r.owner.any foreign.contains)
  -- the process table only when an idle live owner may be waiting on a background job
  let idle := lapsed.any fun r => (r.owner.bind db.agent).any fun a => a.ended.isNone && a.status == some "idle"
  let bg ← if idle then do pure ((Machine.bgAgents db.agents (← Machine.procs)).map (·.1)) else pure []
  let mut out := []
  for r in lapsed do
    let hm ← Clock.hhmm (r.lease_until.getD t)
    if ← Store.run (Txn.update (claimSels r) [.msg] (reapClaim r t hm comms bg live)) then out := out ++ [s!"task #{d r.id}"]
  for l in db.locks.filter (·.lease_until.any (· < t)) do
    if ← Store.run (Txn.update [lockSel l] [] (reapLock l t t)) then out := out ++ [s!"lock {l.path}"]
  let some up := live | return (out, [])
  for a in Agents.live db do
    let some h := py a.hc | continue
    if up.contains h then continue
    if ← Store.run (Txn.update (Sels.release a.name) [.msg] (reapGone a.name h t)) then out := out ++ [s!"agent {a.name}"]
  -- an ended row whose terminal hc still lists and no live row is bound to: its end stopped before the kill
  let mut acts : List Act := []
  for a in db.agents do
    let some h := py a.hc | continue
    if a.ended.isNone || !up.contains h || (Agents.live db).any (py ·.hc == some h) then continue
    acts := acts ++ [Act.kill h]
    out := out ++ [s!"terminal {a.name}"]
  return (out, acts)

-- ---------- sweep ----------

/-- The worktree rows an agent made (not a read-only one): what `madeHere`, `Workspaces.usedOf` and `owned` read. -/
def madeSel : Sel := { table := .workspace, cond := .eq "ro" (.int 0) }

/-- The tasks with a base: what `Workspaces.protectedOf` reads. -/
def basesSel : Sel := { table := .task, cond := .notNull "base" }

/-- What the sweep and `keepReasons` read: the live agents, the made worktrees and the tasks' bases. -/
def sweepSels : List Sel := [Sels.live, madeSel, basesSel]

/-- Deletes the local branch of a removed worktree: never a prot one, never master; `branch -d` when git agrees it
is merged, else `update-ref -d` guarded by the tip the sweep checked (watchd.delete_branch). -/
def deleteBranch (main : String) (br tip : Option String) (prot : List String) : m Unit := do
  let (some br, some tip) := (br, tip) | return
  if prot.contains br || br == "master" then return
  if (← Lifecycle.code ["git", "-C", main, "branch", "-d", br]) != 0 then
    discard <| Lifecycle.code ["git", "-C", main, "update-ref", "-d", "refs/heads/" ++ br, tip]

/-- The (path, branch) of each worktree `git worktree list --porcelain` lines list, the path as printed. -/
def wtLines (ls : List String) : List (String × Option String) :=
  (ls.foldl (fun (wts : Array (String × Option String)) l =>
    if l.startsWith "worktree " then wts.push ((l.drop 9).toString, none)
    else if l.startsWith "branch refs/heads/" && !wts.isEmpty then
      wts.modify (wts.size - 1) fun (p, _) => (p, some (l.drop 18).toString)
    else wts) #[]).toList

/-- Workspace GC: removes clean, landed worktrees (and their local branch) that no live agent or process uses; `dry`
only lists them. The worktrees and swept sizes (MB), and the "not landed" cache (worktree, HEAD and the bases' shas)
grown (watchd.sweep_worktrees, NOT_LANDED). With `dir` (a realpath), only the worktrees inside it are looked at; with
`made`, only those (realpaths: the worktrees a `workspace` row made, sw-global §4). -/
def sweep (comms : Option String) (dry : Bool) (notLanded : List String) (dir : Option String := none)
    (made : Option (List String) := none) : m (List (String × Option String × Int) × List String) := do
  let lines := splitlines ((← Lifecycle.run ["git", "worktree", "list", "--porcelain"]).getD "")
  let some first := lines.head? | return ([], notLanded)
  let main ← real (first.drop 9).toString
  let db ← Store.view sweepSels id
  let prot ← Workspaces.protectedOf db (some main)
  let bs ← Bases.refs prot (some main)
  let wts ← (wtLines lines.tail).mapM fun (p, br) => return (← real p, br)
  let used := (← (((Agents.live db).flatMap fun a => [a.wt.getD "", a.cwd.getD ""]).filter (· != "")).mapM real) ++
    Workspaces.usedOf db (← Workspaces.worktrees)
  let some cw ← Machine.cwds | return ([], notLanded)  -- which worktrees a process sits in is unknown: sweep none
  let pcwd ← cw.mapM fun (_, l) => real l
  let t ← Clock.now
  let mut out := []
  let mut freed : Int := 0
  let mut cache := notLanded
  for (wt, br) in wts do
    if wt == main || (← Sys.kind wt true) != .dir || used.any (inside · wt) || pcwd.any (inside · wt) ||
        (!(dir.all (inside wt)) || !(made.all (·.contains wt))) then continue
    let gd ← git ["-C", wt, "rev-parse", "--absolute-git-dir"]
    let last := max (max 0 ((← Sys.mtime wt).getD 0)) ((← Sys.mtime (joinPath (joinPath ((py gd).getD wt) "logs") "HEAD")).getD 0)
    -- no index.lock: an agent committing in wt meanwhile must not fail (#127)
    let st ← Lifecycle.run ["git", "--no-optional-locks", "-C", wt, "status", "--porcelain"]
    if t - last < SWEEP_IDLE || st.isNone || strip (st.getD "") != "" then continue  -- dirty or unreadable: never landed
    let shas ← bs.mapM fun b => return (← git ["-C", main, "rev-parse", b]).getD ""
    -- read before `landed`: the branch delete's guard is the HEAD landed then judged, not a later commit
    let head := py (← git ["-C", wt, "rev-parse", "HEAD"])
    let key := "\x00".intercalate [wt, head.getD "", ",".intercalate shas]
    if cache.contains key then continue
    if !(← Lifecycle.landed wt bs (some main)) then cache := cache ++ [key]; continue
    let du := (← Lifecycle.run ["du", "-sk", wt]).getD "0"
    let mb := fdiv ((String.ofList ((du.toList.dropWhile (!·.isDigit)).takeWhile Char.isDigit)).toNat?.getD 0) 1024
    let mut removed := true
    if !dry then
      if (← Lifecycle.code ["git", "-C", main, "worktree", "remove", wt]) != 0 then removed := false
      else
        Run.cleanRemote wt
        deleteBranch main br head prot
        Store.run (Txn.exec [logStmt t none "sweep" (some wt) (some s!"{br.getD "None"} {mb}MB")])
    if removed then
      out := out ++ [(wt, br, mb)]
      freed := freed + mb
  if !out.isEmpty && !dry then
    if let some c := comms then
      Store.run (Txn.update [] [.msg] fun db =>
        (say db t (.agent c) s!"swept {out.length} landed worktree(s), {freed} MB freed." false "notice", ()))
  return (out, cache)

/-- Why the sweep keeps each worktree of the repo that lies inside `dir` (a realpath), as it reads them now; "landed" for one
it would remove. Reads only; what `sweep` does is its own checks. -/
def keepReasons (dir : String) : m (List (String × Option String × String)) := do
  let lines := splitlines ((← Lifecycle.run ["git", "worktree", "list", "--porcelain"]).getD "")
  let some first := lines.head? | return []
  let main ← real (first.drop 9).toString
  let db ← Store.view sweepSels id
  let prot ← Workspaces.protectedOf db (some main)
  let bs ← Bases.refs prot (some main)
  let used := (← (((Agents.live db).flatMap fun a => [a.wt.getD "", a.cwd.getD ""]).filter (· != "")).mapM real) ++
    Workspaces.usedOf db (← Workspaces.worktrees)
  let pcwd ← (← Machine.cwds).getD [] |>.mapM fun (_, l) => real l
  let t ← Clock.now
  let mut out := []
  for (p, br) in wtLines lines.tail do
    let wt ← real p
    if wt == main || !inside wt dir then continue
    let why ← do
      if (← Sys.kind wt true) != .dir then pure "not a directory"
      else if used.any (inside · wt) then pure "a live agent's"
      else if pcwd.any (inside · wt) then pure "a process is in it"
      else
        let gd ← git ["-C", wt, "rev-parse", "--absolute-git-dir"]
        let last := max (max 0 ((← Sys.mtime wt).getD 0)) ((← Sys.mtime (joinPath (joinPath ((py gd).getD wt) "logs") "HEAD")).getD 0)
        let st ← Lifecycle.run ["git", "--no-optional-locks", "-C", wt, "status", "--porcelain"]
        if st.isNone then pure "status unreadable"
        else if strip (st.getD "") != "" then pure "dirty"
        else if t - last < SWEEP_IDLE then pure "touched recently"
        else if (← Lifecycle.landed wt bs (some main)) then pure "landed" else pure "work not in the base"
    out := out ++ [(wt, br, why)]
  return out

/-- A branch the sweep leaves to `sweepBranches`: an ended agent's (`<name>/…`), not a protected base nor master. -/
def leftBranch (ended prot : List String) (b : String) : Bool :=
  !prot.contains b && b != "master" && ended.any fun n => b.startsWith (n ++ "/")

/-- The branch of a worktree the sweep removed but stopped before deleting: each ended agent's branch gets
`branch -d`, which git refuses for one not merged into HEAD or checked out somewhere (a squash-landed one stays). -/
def sweepBranches (main : String) (ended prot : List String) : m Unit := do
  let out := (← Lifecycle.run ["git", "-C", main, "for-each-ref", "--format=%(refname:short)", "refs/heads/"]).getD ""
  for b in (splitlines out).filter (leftBranch ended prot) do
    discard <| Lifecycle.code ["git", "-C", main, "branch", "-d", b]

-- ---------- lifecycle's notices ----------

/-- Agent `a` is idle and kept only by its unclean worktree `wt`: once per idle stretch and per list, wake it with the
list; if it is idle again with the same list, or has no live waiter, tell comms (watchd.unclean). -/
def unclean (a : Agent) (wt b : String) (t : Int) (comms : String) : m Unit := do
  let n := a.name
  let since := a.last_active.getD 0
  if t - since < UNCLEAN_IDLE then return
  let db ← Store.txn [.event] fun db => (db, db)
  let last := (db.events.filter fun e => e.agent == some n &&
    (e.kind == some "unclean-nudge" || e.kind == some "unclean-notice")).getLast?
  if last.any (·.ts.getD 0 ≥ since) then return  -- already handled this idle stretch
  let list ← Lifecycle.uncleanList wt b
  let same := last.any (·.data == some list)
  if same && last.any (·.kind == some "unclean-notice") then return
  let ls := splitlines list
  let shown := "\n".intercalate (ls.take 20) ++ (if ls.length > 20 then s!"\n+{ls.length - 20} more" else "")
  let mins := fdiv (t - since) 60
  let waits ← match a.waiter with | some w => Sys.pidAlive w | none => pure false
  let now ← Clock.now
  if !same && waits then
    Store.txn [] fun db =>
      let db := db.log now (some n) "unclean-nudge" (some wt) (some list)
      (say db now (.agent n) (s!"You are idle {mins} min with no claim or lock; watchd keeps you only because worktree {wt} holds:\n{shown}\n" ++
        "If your work is done: land what is real, delete or ignore build outputs and scratch, then stop, and watchd ends you. " ++
        s!"If not, tell the communicator ({comms}) what you are waiting on.") true "system", ())
  else
    Store.txn [] fun db =>
      let db := db.log now (some n) "unclean-notice" (some wt) (some list)
      (say db now (.agent comms) (s!"{n} is idle {mins} min, kept only by its unclean worktree {wt} " ++
        s!"({if same then "nudged once, idle again and still unclean" else "no live waiter, so not nudged"}):\n{shown}") false "system", ())

/-- Task `r` is held by an agent of the swarm whose agents `db` read (board #135): its owner or its lander is one. Tasks
are the machine's, so a per-swarm pass acts only on these. -/
def ofSwarm (db : Db) (r : Task) : Bool :=
  let ns := db.agents.map (·.name)
  r.owner.any ns.contains || r.lander.any ns.contains

/-- On the edge into quiet (no task of the swarm open, claimed, blocked or landing, only stayers and comms live;
re-armed by a task add or claim): each wakeable stayer is asked once whether its stay is over, and comms gets one
notice (watchd.quiet). A task is the swarm's as its board lists it (`Swarms.mine`) or when its agent lands it
(`ofSwarm`, board #135); without a swarm every task is. -/
def quiet (t : Int) (comms : String) : m Unit := do
  let db ← Store.txn [.task, .event, .agent, .«meta»] fun db => (db, db)
  let mine ← match py (← env "SWARM") with
    | some s => some <$> Swarms.mineIds s
    | none => pure none
  if db.tasks.any fun x => (x.state = .open || x.state = .claimed || x.state = .blocked || x.state = .landing) &&
      (mine.all (·.contains (x.id : Int)) || ofSwarm db x) then return
  let q := ((db.events.filter (·.kind == some "quiet")).getLast?.map (·.id)).getD 0
  if !db.events.any fun e => (e.kind == some "task-add" || e.kind == some "claim") && e.id > q then return
  let envComms ← env "SWARM_COMMS"
  let mut stayers := []
  for a in Agents.live db do
    if a.name != comms && !isComms db envComms (some a.name) then
      if (py a.stay).isNone then return  -- someone is still working
      stayers := stayers ++ [a]
  let now ← Clock.now
  Store.txn [] fun db => (db.log now none "quiet" none (some (toString stayers.length)), ())
  let mut l := []
  let mut seen : Seen := []
  for a in stayers do
    let waits ← match a.waiter with | some w => Sys.pidAlive w | none => pure false
    let woken ← if waits then do
        let (cr, s) ← coldReason seen a t
        seen := s
        pure cr.isNone
      else pure false
    let stay := a.stay.getD ""
    if woken then
      let now ← Clock.now
      Store.txn [] fun db => (say db now (.agent a.name) (s!"The board is empty and nobody is working. You stay for: '{stay}'. If that is over, " ++
        "`swarm stay --end` and stop; if not, carry on.") false "system", ())
    l := l ++ [s!"{a.name}{match py a.role with | some r => " " ++ r | none => ""} stays for '{stay}' " ++
      s!"({if woken then "asked if that is over" else if waits then "cold, not woken" else "no live waiter, not woken"})"]
  let now ← Clock.now
  Store.txn [] fun db => (say db now (.agent comms) ("The swarm is quiet: no task is open, claimed or blocked and nobody else is working. " ++
    (if l.isEmpty then "No stayers." else "Stayers:\n" ++ "\n".intercalate l) ++ "\nIf the work is done, tell the user.") false "system", ())

/-- An agent idle `blockerIdle` min while its claim blocks open tasks: asked once per idle stretch what it waits on,
and comms told (watchd.blockers). -/
def blockersStep (t : Int) (comms : String) (blockerIdle : Float) (db0 : Db) : Db :=
  let lim := blockerIdle * 60
  (Agents.live db0).foldl (fun db a =>
    let n := a.name
    let last := a.last_active.getD 0
    if n == comms || a.status != some "idle" || Float.ofInt (t - last) < lim then db
    else if db.events.any (fun e => e.agent == some n && e.kind == some "blocker-nudge" && e.ts.any (· ≥ last)) then db
    else
      let ids : List Int := (db.tasks.filter fun x => x.state = .claimed && x.owner == some n).map (·.id)
      let w := dependants db ids
      if w > 0 then
        let db := db.log t (some n) "blocker-nudge" none (some (toString w))
        let db := say db t (.agent n) "What are you waiting on? Can you continue without it/land without it?" true "system"
        say db t (.agent comms) s!"{n} is idle {fdiv (t - last) 60} min holding #{",#".intercalate (ids.map d)}, which {w} open task(s) wait on (nudged)." false "system"
      else db) db0

/-- What `blockersStep` reads: the live agents, every task (`dependants` follows the deps), the `blocker-nudge` events. -/
def blockerSels : List Sel :=
  [Sels.live, Sels.all .task, { table := .event, cond := .eq "kind" (.text "blocker-nudge") }]

/-- The blockers pass in one transaction. -/
def blockers (t : Int) (comms : String) (blockerIdle : Float) : m Unit :=
  Store.run (Txn.update blockerSels [.msg] fun d => (blockersStep t comms blockerIdle d, ()))

/-- How long a landing task waits for its lander before the communicator is told (board #200). -/
def LANDING_LATE : Int := 7200

/-- Landing task `r` (read before) handed over LANDING_LATE before `t` and still landing at the same commit: the
communicator told, once per task and commit (a `landing-late` event marks it). -/
def landingLate1 (r : Task) (t : Int) (comms : String) (db : Db) : Db :=
  match db.find r.id with
  | some x =>
    if x.state = .landing && x.land_sha == r.land_sha && x.landing_at.any (· ≤ t - LANDING_LATE) &&
        !db.events.any (fun e => e.kind == some "landing-late" && e.path == some (d r.id) && e.data == x.land_sha) then
      let db := db.log t x.owner "landing-late" (some (d r.id)) x.land_sha
      say db t (.agent comms) (s!"{Tasks.landingText r.id x} has waited {fdiv (t - x.landing_at.getD t) 60} min with no " ++
        s!"`task done` or `task unland`{match py x.owner with | some o => " (" ++ o ++ " handed it over)" | none => ""}.") false "notice"
    else db
  | none => db

/-- The landing tasks of the swarm (`ofSwarm`: its agent handed it over or lands it) no lander closed within
LANDING_LATE, each told to the communicator once (`landingLate1`). -/
def landingLateStep (t : Int) (comms : String) (db : Db) : Db :=
  (db.tasks.filter fun x => x.state = .landing && x.landing_at.any (· ≤ t - LANDING_LATE) && ofSwarm db x).foldl
    (fun db r => landingLate1 r t comms db) db

/-- What `landingLateStep` reads: the landing tasks, the swarm's agents and the `landing-late` events. -/
def landingSels : List Sel :=
  [{ table := .task, cond := .eq "state" (.text "landing") }, Sels.all .agent,
   { table := .event, cond := .eq "kind" (.text "landing-late") }]

/-- The landing-late pass in one transaction. -/
def landingLate (t : Int) (comms : String) : m Unit :=
  Store.run (Txn.update landingSels [.msg] fun d => (landingLateStep t comms d, ()))

/-- Ends `n`'s stay if its `--until` condition holds (board #195): the stay cleared, its claimed tasks' leases renewed
2 h, and "Your wait is over: <cond> (<detail>)" sent. Whether it woke. -/
def wakeStay (n : String) (t : Int) : m Bool := do
  let now ← Clock.now
  Store.txn [.agent, .task, .event, .msg, .cursor, .«meta», .ci] fun db =>
    match (db.agent n).bind (·.stay) with
    | none => (db, false)
    | some s =>
      match stayCondOf db n with
      | (some c, since) =>
        match stayMet db Ci.ts n c since t with
        | none => (db, false)
        | some detail =>
          let db := db.setAgent n ({ · with stay := none })
          let db := db.log now (some n) "stay-end" (some n) (some s)
          let db := db.log now (some n) "stay-wake" (some c.text) (some detail)
          let db := db.tasks.foldl (fun db r =>
            if r.owner == some n && r.state == .claimed then db.set r.id ({ · with lease_until := some (now + 7200) }) else db) db
          (say db now (.agent n) s!"Your wait is over: {c} ({detail})" true "system", true)
      | _ => (db, false)

/-- Hung stayers: no live waiter, a waking message unread two ticks, and the liveness check and its answer; all state in
events newer than the stayer's last_active, so any wake re-arms it (watchd.hung). None while it compacts. -/
def hung (t : Int) (comms : String) (terms : Option (List Term)) (tick : Int) : m Unit := do
  let db ← Store.txn [.agent, .event, .msg, .cursor, .«meta», .task] fun db => (db, db)
  let envComms ← env "SWARM_COMMS"
  let mut seen : Seen := []
  for a in Agents.live db do
    let n := a.name
    let last := a.last_active.getD 0
    if n == comms || isComms db envComms (some n) || a.status != some "idle" then continue
    let evs := db.events.filter fun e => e.agent == some n && e.ts.any (· ≥ last)
    let ev (kind : String) (data : Option String := none) : Option Event :=
      (evs.filter fun e => e.kind == some kind && (data.isNone || e.data == data)).getLast?
    if Compact.compacting db.events n last t then continue  -- compactPass wakes it once the compaction ends
    -- a holder told its lease ended (`leaseLate`, urgent when idle), idle since and still holding the lapsed claim
    -- LIVENESS_WAIT later with no background job, did not answer: hung, and reap reopens the claim and tells comms
    -- (board #193)
    let told := db.tasks.filter fun r => r.owner == some n && r.state = .claimed && r.lease_until.any (· < t) &&
      evs.any fun e => e.kind == some "lease-late" && e.data == some "holder" && e.path == some (d r.id) &&
        e.ts.any fun s => s > last && t - s ≥ LIVENESS_WAIT
    if let some r := told.head? then
      if (ev "stay-hung").isNone && ((Machine.bgAgents db.agents (← Machine.procs)).lookup n).isNone then
        let now ← Clock.now
        Store.txn [] fun db => (db.log now (some n) "stay-hung" none (some s!"#{d r.id}"), ())
        continue
    let some stay := py a.stay | continue
    let waits ← match a.waiter with | some w => Sys.pidAlive w | none => pure false
    if !waits then
      if (ev "stay-nowaiter").isNone then
        let now ← Clock.now
        Store.txn [] fun db =>
          let db := db.log now (some n) "stay-nowaiter" none none
          (say db now (.agent comms) s!"{n} stays for '{stay}' but has no waiter and can't be woken." false "system", ())
      continue
    if (py a.stay).isSome && (← wakeStay n t) then continue
    for msg in Msgs.unread db n do
      if msg.dest == some n && msg.kind != some "notice" && msg.ts.getD 0 ≤ t - 2 * tick &&
          !(msg.body.getD "").startsWith "Liveness check:" && (ev "stay-unwoken" (some (d msg.id))).isNone then
        let now ← Clock.now
        Store.txn [] fun db =>
          let db := db.log now (some n) "stay-unwoken" none (some (d msg.id))
          (say db now (.agent comms) s!"{n} did not wake on a message (#{d msg.id} from {msg.frm.getD "nil"}, {t - msg.ts.getD 0} s ago)." false "system", ())
    if (ev "stay-hung").isSome then continue  -- no more checks until it is active again
    if let some chk := ev "stay-check" then
      if t - chk.ts.getD 0 ≥ LIVENESS_WAIT then
        let x := (terms.getD []).find? (·.address == a.hc)
        let now ← Clock.now
        Store.txn [] fun db =>
          let db := db.log now (some n) "stay-hung" none none
          (say db now (.agent comms) (s!"{n} stays for '{stay}' and did not answer the liveness check (terminal {a.hc.getD "?"}, hc status " ++
            s!"{(x.bind (·.status)).getD "unknown"}). Unstick it with `swarm nudge {n}`, or end it.") true "system", ())
    else if t - last ≥ (match stayCondOf db n with
        | (some _, _) => LIVENESS_IDLE
        | (none, since) => if (db.events.any fun e => e.agent == some n && e.kind == some "stay-check" && e.ts.any (· ≥ since))
            then LIVENESS_IDLE else LIVENESS_FREE) then
      let (cr, s) ← coldReason seen a t  -- a cold wake resends the whole context
      seen := s
      if cr.isNone then
        let now ← Clock.now
        Store.txn [] fun db =>
          let db := db.log now (some n) "stay-check" none none
          (say db now (.agent n) (s!"Liveness check: you have stayed {fdiv (t - last) 60} min for '{stay}'. What exactly are you waiting for? " ++
            "If you can take any step now, take it and `swarm stay --end`. If you are blocked, set the stay again with the " ++
            "condition (`swarm stay \"<why>\" --until <cond>`); that re-arms the check.") false "system", ())

/-- Whether agent `n`'s job tree `sig` (`Lifecycle.jobTree`) is hung at `t`, and whether to log `sig` as its new
`job-cpu` checkpoint: the first tree seen, or a changed one once the last is JOB_HUNG old. So at most one event per
JOB_HUNG, and a stall shows between JOB_HUNG and twice that after it began. -/
def hungStep (db : Db) (n sig : String) (t : Int) : Bool × Bool :=
  match (db.events.filter fun e => e.agent == some n && e.kind == some "job-cpu").getLast? with
  | none => (false, true)
  | some e => let old := t - e.ts.getD 0 ≥ JOB_HUNG; if e.data == some sig then (old, false) else (false, old)

/-- An agent fate kept only for its background job `p`, a sleep loop or hung (`hungStep`): once idle JOB_IDLE, one
nudge naming the pid; JOB_GRACE later, ended and comms told the job's command line. A real run (CPU time, a process
started or ended, a known waiter) is left alone (watchd.idle_job). -/
def idleJob (a : Agent) (f : Lifecycle.Reads m) (p : Machine.Ps) (procs : List Machine.Ps) (t : Int) (comms : String)
    (x : Option Term) (hasTerms : Bool) : m Unit := do
  let last := a.last_active.getD 0
  if t - last < JOB_IDLE then return
  let v ← Lifecycle.fate a t x hasTerms { f with job := pure none }
  if v != some "end" && v != some "reuse" then return
  let db ← Store.txn [.event] fun db => (db, db)
  let loop := Lifecycle.sleepLoop p procs
  if !loop then
    let some sig := Lifecycle.jobTree p procs | return
    let (hung, cp) := hungStep db a.name sig t
    if cp then
      let now ← Clock.now
      Store.txn [] fun db => (db.log now (some a.name) "job-cpu" (some (d p.pid)) (some sig), ())
    if !hung then return
  let why := if loop then "is a sleep-only loop" else s!"has used no CPU for {JOB_HUNG / 60} min"
  let nudge := (db.events.filter fun e => e.agent == some a.name && e.kind == some "job-nudge" && e.ts.any (· ≥ last)).getLast?
  match nudge with
  | none =>
    let now ← Clock.now
    Store.txn [] fun db =>
      let db := db.log now (some a.name) "job-nudge" none none
      (say db now (.agent a.name) (s!"Your task is done and your background job (pid {p.pid}) {why}: {cut (Machine.jobCmd p.args) 120}. " ++
        s!"Kill it, or say why you stay (`swarm stay \"<what>\"`); else watchd ends you in {JOB_GRACE / 60} min.") false "system", ())
  | some e =>
    if t - e.ts.getD 0 ≥ JOB_GRACE then
      if ← Lifecycle.endAgent a false none then
        let now ← Clock.now
        Store.txn [] fun db => (say db now (.agent comms) s!"ended {a.name}: idle with only a background job left, which {why}: {cut p.args 120}" false "notice", ())

-- ---------- auto-spawn ----------

/-- What auto-spawn is given: watchd's flags and the communicator's hold. -/
structure Opts where
  minFreeGib : Float := 4
  model : Option String := none
  effort : Option String := none
  interval : Int := 30
  once : Bool := false
  blockerIdle : Float := 25
  /-- why no communicator can be launched (ensure_comms), which holds auto-spawn -/
  commsHold : Option String := none

/-- The tasks this swarm staffs (sw-global §2): those of its repos; one of no repo only by a claim or `spawn --task`. -/
def mineOf : m (List Int) := do
  match ← env "SWARM" with
  | some s => Swarms.staffable s
  | none => pure []

/-- `name` is `prefix` and digits: the number (re.fullmatch(prefix .. "(\\d+)")). -/
def numbered (pre name : String) : Option Nat :=
  if name.startsWith pre then
    let rest := (name.drop pre.length).toString
    if !rest.isEmpty && rest.all Char.isDigit then rest.toNat? else none
  else none

/-- Staffs startable tasks of the swarm's repos up to the auto-spawn number, but none under an outstanding offer
(`offered`); the board's "auto-spawn holding" line when a limit stops it (watchd.auto_spawn). -/
def autoSpawn (comms : String) (opts : Opts) (offered : List Int := []) : m (Option String) := do
  let envComms ← env "SWARM_COMMS"
  let db ← Store.txn [.agent, .«meta», .task] fun db => (db, db)
  let (_, mn, mx) := limits db envComms
  let some mn := mn | return none
  if let some h := opts.commsHold then return some ("auto-spawn holding: " ++ h)
  let mut members := ((Agents.live db).filter (·.name != comms)).length
  let pre := if comms.endsWith "comms" then String.ofList (comms.toList.take (comms.length - 5)) else comms ++ "-"
  let mut top := (db.agents.filterMap (numbered pre ·.name)).foldl max 0
  -- "until,delay,name" after a failed launch
  let (boUntil, boDelay, boName) : Int × Int × Option String := match (db.getMeta "spawn_backoff").bind (·.v) with
    | some v => match v.splitOn "," with
      | u :: dl :: rest =>
        let digits (x : String) : Bool := !x.isEmpty && x.all Char.isDigit
        if digits u && digits dl then ((parseInt u).getD 0, (parseInt dl).getD 0, some (",".intercalate rest)) else (0, 0, none)
      | _ => (0, 0, none)
    | none => (0, 0, none)
  let mut boName := boName
  let mut boDelay := boDelay
  if (← Clock.now) < boUntil then return none
  let mut halt := (db.getMeta "spawn_halt").bind (·.v)  -- a task auto-spawn gave up on
  if let some h := halt then
    if !(Tasks.pool db).any (d ·.id == h) then  -- claimed, done or dropped: lifted
      Store.txn [.«meta»] fun db => (delMeta db "spawn_halt", ())
      halt := none
  let haltOf := halt
  -- only tasks of this swarm's repos (sw-global §2): one of no repo is staffed by a claim or `spawn --task` alone
  let mine ← mineOf
  let skip (x : Task) : Bool := haltOf == some (d x.id) || offered.contains x.id || !mine.contains (x.id : Int)
  let mut lost := 0
  repeat
    -- read again before each launch (model Staff.lean, `freshPool`): a task freed meanwhile must not wait (board #91)
    let pool ← Store.txn [.task, .«meta»] fun db => (db, Queue.staffing db)
    let rest := pool.dropWhile skip
    let some task := rest.head? | break
    let startable := (rest.filter (!skip ·)).length
    if (members : Int) ≥ mn then
      return some s!"auto-spawn holding: {members} live, the auto-spawn number is {mn}; {startable} task(s) startable{match mx with | some x => s!"; max {x}" | none => ""}"
    let free := match ← Machine.mem with | some (kb, _, _) => Float.ofInt kb / 1048576 | none => 1.0 / 0.0
    if free < opts.minFreeGib then
      return some s!"auto-spawn holding: {fixed free 1}G free, wants {fmtG opts.minFreeGib}G; {startable} task(s) startable"
    let name ← match boName with
      | some n => if n != "" then pure n else do top := top + 1; pure (pre ++ toString top)
      | none => do top := top + 1; pure (pre ++ toString top)
    let model := Reuse.modelOf ((py opts.model).getD "sonnet") task
    let sa : Spawn.Args := { name := name, model := model, effort := (py task.effort).orElse (fun _ => py opts.effort),
                             taskId := some (task.id : Int), top := some (Queue.staffHead skip) }
    let now ← Clock.now
    -- a bad ref in swarm.json: one event per value, not one per spawn
    for (k, v) in ← Bases.badConfig none do
      Store.txn [.event] fun db =>
        if db.events.any fun e => e.kind == some "config-base" && e.path == some v then (db, ())
        else (db.log now none "config-base" (some v) (some (Bases.badConfigText k v)), ())
    let r ← tryCatchThe Exit (do return some (← Spawn.spawnE sa)) fun _ => pure none
    let now ← Clock.now
    match r with
    | some (.ok none) =>
      Store.txn [.«meta»] fun db =>
        let db := delMeta (delMeta db "spawn_backoff") "spawn_fails"
        (db.log now (some name) "spawn" none (some s!"auto #{d task.id}"), ())
      members := members + 1
      boName := none; boDelay := 0  -- the retry took the name: later tasks this tick get fresh ones
    | some (.error (.lost _)) =>  -- a peer claimed it, or a task freed outranks it, between pool() and now
      lost := lost + 1
      if lost > pool.length then break  -- a pool that keeps changing: the next tick goes on
    | some (.error (.refused msg)) =>  -- an agent spawned between limits() and now: the max holds
      return some s!"auto-spawn holding: {String.ofList (msg.toList.takeWhile (· != '.'))}; {startable} task(s) startable"
    | _ =>  -- the launch failed (a die included); spawn already reopened the task
      if let some (.error (.die msg)) := r then Env.err s!"swarm: {msg}"
      let err := match r with | some (.ok (some e)) => e | _ => "launch error"
      let delay := if boDelay == 0 then 300 else min (boDelay * 2) 3600  -- 5 min, doubling, capped at 1 h
      let first := boDelay == 0
      Store.txn [.«meta»] fun db =>
        let db := db.setMeta "spawn_backoff" (some s!"{now + delay},{delay},{name}")
        let db := if first then  -- one notice per failure streak
            say db now (.agent comms) s!"auto-spawn of {name} for #{d task.id} failed: {err}. Auto-spawn pauses {fdiv delay 60} min and retries, doubling." false "notice"
          else db
        let fails : Int := match ((db.getMeta "spawn_fails").bind (·.v)).map (·.splitOn ",") with
          | some [ft, fn] => if ft == d task.id then (parseInt fn).getD 0 else 0
          | _ => 0
        let fn := fails + 1
        let db := db.setMeta "spawn_fails" (some s!"{d task.id},{fn}")
        if fn ≥ (SPAWN_FAILS : Int) then
          let db := delMeta (delMeta (db.setMeta "spawn_halt" (some (d task.id))) "spawn_backoff") "spawn_fails"
          (say db now (.agent comms) (s!"auto-spawn for #{d task.id} failed {fn} times in a row (last: {err}). " ++
            "Auto-spawn stops for it until it is claimed or changes; spawn it by hand.") true "system", ())
        else (db, ())
      break
  return none

-- ---------- lifecycle ----------

/-- The worktrees of the scope's repo a `workspace` row made (realpaths): the only ones the sweep removes (sw-global §4). -/
def madeHere : m (List String) := do
  (← Store.view [madeSel] fun db => (db.workspaces.filter (·.ro == some 0)).map (·.path)).mapM real

/-- The repo's own upkeep (sw-global §4, per repo, in its folder and scope): its bases fetched, the sweep of the
worktrees a `workspace` row made and the branches ended agents left; the "not landed" cache before and after. -/
def repoSweep (comms : Option String) (notLanded : List String) : m (List String) := do
  let db0 ← Store.view [{ table := .agent, cond := .notNull "ended" }, basesSel] id
  let main ← Workspaces.main none
  let prot ← Workspaces.protectedOf db0 main
  for b in prot do Bases.fetch b main
  let (_, notLanded) ← sweep comms false notLanded none (some (← madeHere))
  if let some mn := main then sweepBranches mn ((db0.agents.filter (·.ended.isSome)).map (·.name)) prot
  return notLanded

/-- Repo lock `l` dropped if its holder is no live agent of any swarm and the lock is still its (read before); true when
it dropped it. -/
def reapHolderGone (l : Lock) (t : Int) (db : Db) : Db × Bool :=
  if (Agents.live db).any (some ·.name == l.agent) || !db.locks.any (fun x => x.path == l.path && x.agent == l.agent) then (db, false)
  else
    let db := { db with locks := db.locks.filter fun x => !(x.path == l.path && x.agent == l.agent) }
    (db.log t l.agent "reap" (some l.path) (some "holder gone"), true)

/-- The repo's locks (sw-global §4, per repo, every swarm's agents in view): an expired one dropped (`reapLock`), and
one whose holder is no live agent of any swarm (`reapHolderGone`; its end released the locks of its own repo only).
One read, then one transaction per lock on its row (and its holder's); `t` stamps the writes. -/
def reapLocks (repo : String) (t : Int) : m (List String) := do
  let db ← Store.view [{ table := .lock, cond := .eq "repo" (.text repo) }, Sels.live] id
  let live := (Agents.live db).map (·.name)
  let mut out := []
  for l in db.locks do
    if l.lease_until.any (· < t) then
      if ← Store.run (Txn.update [lockSel l] [] (reapLock l t t)) then out := out ++ [s!"lock {l.path}"]
    else if l.agent.all (!live.contains ·) then
      let holder := match l.agent with | some n => [Sels.agent n] | none => []
      if ← Store.run (Txn.update ([lockSel l] ++ holder) [] (reapHolderGone l t)) then out := out ++ [s!"lock {l.path}"]
  return out

/-- Ends finished agents, offers reusable ones related tasks (board #186), staffs the startable tasks not under an
offer (watchd.lifecycle). -/
def lifecycle (t : Int) (comms : String) (terms : Option (List Term)) (opts : Opts) : m Unit := do
  let all ← Workspaces.worktrees
  let every ← Workspaces.every
  let main ← Workspaces.main none
  let db ← Store.txn [.agent, .task, .workspace, .event] fun db => (db, db)
  for (n, path, base) in ← Workspaces.baseOut db all do  -- a base checked out in an agent's worktree: once per agent and base
    let now ← Clock.now
    Store.txn [.event] fun db =>
      if db.events.any fun e => e.kind == some "base-out" && e.agent == some n && e.path == some base then (db, ()) else
      let db := db.log now (some n) "base-out" (some base) (some path)
      let db := say db now (.agent n) (s!"Your worktree {path} has {base} checked out: that blocks `git push . HEAD:{base}` for everyone. " ++
        "Switch back to your own branch.") false "notice"
      (say db now (.agent comms) s!"{n}'s worktree {path} has base {base} checked out." false "notice", ())
  let by_ (h : String) : Option Term := (terms.getD []).find? (·.address == some h)
  let db ← Store.txn [.agent, .task, .lock, .workspace, .event, .msg, .cursor, .«meta»] fun db => (db, db)
  let wts := Workspaces.wtMapOf db all
  let mine ← mineOf
  -- offers and the reuse fate count only what auto-spawn would staff here
  let pool := (Queue.staffing db).filter fun x => mine.contains (x.id : Int)
  let procs ← Machine.procs  -- machine.bg_agents, read once
  let mut reusable := []
  let dflt := (py opts.model).getD "sonnet"
  for a in Agents.live db do
    let offer := Reuse.candidates db a.name a.model dflt pool
    let f0 : Lifecycle.Reads m := Lifecycle.reads db main wts every a.name offer
    -- an offer unanswered OFFER_TTL counts as declined
    let f := { f0 with job := pure ((Machine.bgAgents db.agents procs).lookup a.name),
                       passedOver := f0.passedOver || Reuse.expired db a.name (offer.map (·.id : Task → Int)) t }
    let x := if terms.isSome then (py a.hc).bind by_ else none
    let (v, h) ← Lifecycle.fateHeard a t x terms.isSome f
    match v, h.proc with
    | none, some p => idleJob a f p procs t comms x terms.isSome
    | some "unclean", _ => if let some (w, bs) := h.held then unclean a w (bs.headD "nil") t comms
    | some "reuse", _ => reusable := reusable ++ [(a, offer)]
    | some "end", _ => discard <| Lifecycle.endAgent a false none
    | _, _ => pure ()
  for (a, offer) in reusable do  -- edge-triggered: only when the offer holds an id this agent was never offered
    let ids := offer.map (·.id : Task → Int)
    let now ← Clock.now
    Store.txn [.event] fun db =>
      let told := Lifecycle.toldOf db a.name
      if ids.all told.contains then (db, ()) else
      -- the event marks it told: never without its message
      let db := db.log now (some a.name) "digest" none (some (",".intercalate (ids.map d)))
      (say db now (.agent a.name) (Reuse.text offer) false "system", ())
  let offered ← if pool.isEmpty then pure [] else do
    let now ← Clock.now
    Store.txn [.agent, .task, .event] fun db => (db, Reuse.offered db now)
  let held ← if !pool.isEmpty then autoSpawn comms opts offered else pure none
  let now ← Clock.now
  Store.txn [.«meta»] fun db =>
    let old := db.getMeta "spawn_held"
    match held with
    | some h =>
      let db := db.setMeta "spawn_held" (some h)
      (if old.isNone then db.log now (some "swarm") "spawn-held" none (some h) else db, ())  -- one per edge
    | none => (if old.isSome then delMeta db "spawn_held" else db, ())

-- ---------- machine ----------

/-- Whether `scope` (a cgroup path) is the swarm-agent or swarm-job scope of agent `name` (`Machine.ownsScope`). -/
def ownsScope (name scope : String) : Bool := Machine.ownsScope name scope

/-- The processes to end: those in the scope of an ended agent that no live agent runs in, whatever their parent
(`systemd --user`, a subreaper, adopts orphans before init does). `scope p` is the swarm-agent or swarm-job scope `p` runs in. A process in no agent's scope is never one, whatever its cwd. -/
def orphanVictims (procs : List Machine.Ps) (scope : Machine.Ps → Option String) (agents : List Agent) : List Machine.Ps :=
  procs.filter fun p => match scope p with
    | none => false
    | some s => agents.any (fun a => a.ended.isSome && ownsScope a.name s) &&
        !agents.any (fun a => a.ended.isNone && ownsScope a.name s)

/-- Edge-triggered pressure notice, oom bias for the processes in agents' trees, orphan kills, and the cmd-cost tick
(watchd.machine_tick); the cost tick's memory before and after. -/
def machineTick [Guard m] (cost : Cost.TickMem) : m Cost.TickMem := do
  let some (avail, total, psi) ← Machine.mem | return cost
  let procs ← Machine.procs
  let cost ← match ← Guard.guard (Cost.tick cost procs (← Clock.now)) with  -- the history never stops the tick
    | .ok c => pure c
    | .error e => do Env.err s!"cost: {e}"; pure cost
  let db ← Store.txn [.agent, .event] fun db => (db, db)
  let hs := Machine.holders db.agents procs
  let root ← Machine.procRoot
  if (← Machine.osName) == "Linux" then  -- the OOM killer picks agents' processes before the dev db and Claude
    for h in hs do
      if h.agent == "other session" then continue
      for p in h.procs do
        let f := s!"{root}/{d p.pid}/oom_score_adj"
        if let some v := (← Fs.read f).bind (parseInt ∘ strip) then
          if v < 500 then discard <| Fs.write f "500"
  let high := Machine.pressureHigh avail total psi
  let was := lastEvent db ["pressure", "pressure-end"] == some "pressure"
  if high && !was then
    let ps := procs.mergeSort fun x y => x.rss_kb > y.rss_kb || (x.rss_kb == y.rss_kb && x.pid ≤ y.pid)
    let top := (ps.take 3).map fun p => s!"{p.comm}({d p.pid}) {fixed (Float.ofInt p.rss_kb / 1048576) 1}G"
    let line := Machine.line avail total psi
    let mut who : List String := []
    for h in hs do  -- the three agents holding the most memory, then every stayer
      if h.agent != "other session" && !who.contains h.agent && who.length < 3 then who := who ++ [h.agent]
    for s in Agents.live db do
      if s.stay.isSome && !who.contains s.name then who := who ++ [s.name]
    let now ← Clock.now
    let whoS := who.mergeSort (· ≤ ·)
    Store.txn [] fun db =>
      let db := db.log now none "pressure" none (some line)
      (whoS.foldl (fun db w => say db now (.agent w) s!"memory pressure: {line}. Top holders: {", ".intercalate top}. Prefer other work or ask the agent holding the most." false "notice") db, ())
  else if was && !high then
    let now ← Clock.now
    Store.txn [] fun db => (db.log now none "pressure-end" none none, ())
  -- orphans: what is left in an ended agent's scope, whoever adopted it (macOS has no scopes: orphans of init are only noted)
  if (← Machine.osName) == "Linux" then
    let mut sc : List (Int × String) := []
    for h in procs do
      if let some s := Machine.scopeOf ((← Fs.read s!"{root}/{d h.pid}/cgroup").getD "") then sc := sc ++ [(h.pid, s)]
    for h in orphanVictims procs (fun p => sc.lookup p.pid) db.agents do
      discard <| Proc.output ["kill", "-TERM", d h.pid] none []  -- kill-site: the orphan sweep, victims only; SIGTERM through kill(1), Sys has no signal call
      let who := (sc.lookup h.pid).bind fun s => (db.agents.find? fun a => a.ended.isSome && ownsScope a.name s).map (·.name)
      let now ← Clock.now
      Store.txn [] fun db => (db.log now who "orphan-kill" none (some s!"{d h.pid} {cut (Machine.procCmd h) 60} {fdiv h.rss_kb 1024}M"), ())
  else
    let ended := (db.agents.filter fun a => a.ended.isSome).filterMap (·.cwd)
    let live := (db.agents.filter fun a => a.ended.isNone).filterMap (·.cwd)
    let seen := db.events.filterMap fun e => if e.kind == some "orphan-seen" then e.data else none
    let mut cw : Option (List (Int × String)) := none
    for h in procs do
      if h.ppid != 1 then continue
      if cw.isNone then cw := some ((← Machine.cwds).getD [])
      let some l := (cw.getD []).lookup h.pid | continue
      let cwd ← real l
      if !ended.any (inside cwd) || live.any (inside cwd) then continue
      let what := s!"{d h.pid} {cut (Machine.procCmd h) 60} {fdiv h.rss_kb 1024}M"
      if seen.contains what then continue
      let now ← Clock.now
      Store.txn [] fun db => (db.log now none "orphan-seen" none (some what), ())
  return cost

end SwarmLean.Watchd
