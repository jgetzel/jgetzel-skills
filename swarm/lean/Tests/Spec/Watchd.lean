import Tests.Cli.Fixture
import SwarmLean.Cmd.Watchd

/-! watchd_spec.lua: watchd races (a peer writes between a read and the write that depends on it, and the write must
not clobber it), end_agent's re-checks and cgroup kill, auto-spawn's lost race, board #91's pool re-read, board #84's
per-pass guard and the loop's guard.

The Lua patched c.all (racing), tasks.pool, proc.run, launch_agent, hc_terminals, reap and ci_poll. Here the passes run
in `TM`, App with a hook before and after each `Store.txn` (the peer's write lands between transactions, through its
own connection, `t.q_`), a hook on `Proc.output` and `Git.git`, hc always failing (hc_terminals nil, proc.run nil for
hc kill), and the SWARM_/HC_ variables only as the test sets them. -/

namespace SwarmLean.Tests.Spec.Watchd
open SwarmLean.Tests.Cli
open SwarmLean
open Lean (Json toJson)

/-- What the test monad hooks. -/
structure Hooks where
  /-- the SWARM_* and HC_* variables the passes see (others are the process's) -/
  vars : List (String × String)
  /-- runs before each transaction, with the tables it loads; may throw -/
  before : IO.Ref (List Table → IO Unit)
  /-- runs after each transaction commits: the peer -/
  after : IO.Ref (List Table → IO Unit)
  /-- a fake for a subprocess: some answer, or none to run it -/
  proc : IO.Ref (List String → IO (Option (Option ProcOut)))
  /-- runs before each git call (args, cwd); may throw -/
  git : IO.Ref (List String → Option String → IO Unit)

abbrev TM := ReaderT Hooks App

instance : Store TM where
  txn ts f := do
    let h ← read
    (← h.before.get) ts
    let a ← (Store.txn ts f : App _)
    (← h.after.get) ts
    pure a

instance : Clock TM where
  now := (Clock.now : App _)
  hhmm t := (Clock.hhmm t : App _)

instance : Env TM where
  var k := do
    if k.startsWith "SWARM_" || k.startsWith "HC_" then return (← read).vars.lookup k
    (Env.var k : App _)
  out s := (Env.out s : App _)
  err s := (Env.err s : App _)
  stdin := (Env.stdin : App _)
  cwd := (Env.cwd : App _)

instance : Fs TM where
  read p := (Fs.read p : App _)
  list p := (Fs.list p : App _)
  write p s := (Fs.write p s : App _)

instance : Proc TM where
  output argv cwd env := do
    if argv.head? == some "hc" then return none
    match ← (← (← read).proc.get) argv with
    | some r => pure r
    | none => (Proc.output argv cwd env : App _)
  exec argv := (Proc.exec argv : App _)
  launcherDir := (Proc.launcherDir : App _)

instance : Git TM where
  git args cwd := do
    (← (← read).git.get) args cwd
    (Git.git args cwd : App _)

instance : Sys TM where
  getpid := (Sys.getpid : App _)
  getppid := (Sys.getppid : App _)
  pidAlive p := (Sys.pidAlive p : App _)
  sleep ms := (Sys.sleep ms : App _)
  nowF := (Sys.nowF : App _)
  date f t := (Sys.date f t : App _)
  hostname := (Sys.hostname : App _)
  environ := (Sys.environ : App _)
  setenv k v := (Sys.setenv k v : App _)
  realpath p := (Sys.realpath p : App _)
  readlink p := (Sys.readlink p : App _)
  kind p f := (Sys.kind p f : App _)
  mtime p := (Sys.mtime p : App _)
  mkdirp p := (Sys.mkdirp p : App _)
  link a b := (Sys.link a b : App _)
  remove p := (Sys.remove p : App _)
  exec argv o := (Sys.exec argv o : App _)
  sqlAt p s stmts ro := (Sys.sqlAt p s stmts ro : App _)

instance : Guard TM where
  guard x := do let h ← read; (Guard.guard (x.run h) : App _)

/-- Hooks that do nothing, with SWARM_DB and SWARM_NAME=a, and `vars`. -/
def hooks (t : T) (vars : List (String × String) := []) : IO Hooks := do
  return { vars := vars ++ [("SWARM_DB", t.db), ("SWARM_NAME", "a")]
           before := ← IO.mkRef fun _ => pure ()
           after := ← IO.mkRef fun _ => pure ()
           proc := ← IO.mkRef fun _ => pure none
           git := ← IO.mkRef fun _ _ => pure () }

/-- Runs an action of the test monad on its own connection; an exit fails the test. -/
def run (h : Hooks) (act : TM α) : IO α := do
  match ← (act.run h).run.run { conn := ← IO.mkRef none } with
  | .ok a => pure a
  | .error e => fail s!"exited {e.code}"

/-- The Lua's setup: the db, and the cwd in the repo. -/
def setup (t : T) : IO Unit := do
  Shim.setenv "SWARM_DB" t.db
  IO.Process.setCurrentDir t.repo

def now : IO Int := return (← Sqlite.now).toNat

/-- `fn` once, right after the first transaction whose tables pass `p` (racing: a peer acting in between); the check
that it ran. -/
def racing (h : Hooks) (p : List Table → Bool) (fn : IO Unit) : IO (IO Unit) := do
  let armed ← IO.mkRef true
  h.after.set fun ts => do
    if (← armed.get) && p ts then armed.set false; fn
  return do if ← armed.get then fail "the peer never ran"

/-- `fn` once, right after auto_spawn's own read of the pool: the first task-only transaction after its read of the
agents, meta and tasks (the Lua's second tasks.pool call); the check that it ran. -/
def afterSpawnRead (h : Hooks) (fn : IO Unit) : IO (IO Unit) := do
  let st ← IO.mkRef 0
  h.after.set fun ts => do
    match ← st.get with
    | 0 => if ts == [.agent, .«meta», .task] then st.set 1
    | 1 => if ts == [.task] then st.set 2; fn
    | _ => pure ()
  return do if (← st.get) != 2 then fail "the peer never ran"

/-- What `swarm join` then `task add` + `task claim` leave. -/
def claim (t : T) (name title : String) : IO Unit := do
  let n ← now
  t.q_ "insert or ignore into agent(name,cwd,status,last_active,started,hc) values(?,?,'idle',?,?,?)"
    [.text name, .text t.repo, .int n, .int n, .null]
  t.q_ "insert into task(title,state,owner,lease_until) values(?,'claimed',?,?)" [.text title, .text name, .int (n + 7200)]

def task1 (t : T) : IO Json := t.q1 "select state, owner from task where id=1"

/-- A row exists (the Lua's truthy peer:one). -/
def exists_ (t : T) (sql : String) : IO Unit := do
  if (← t.q sql).isEmpty then fail s!"no row: {sql}"

/-- An agent row as the pass reads it. -/
def agentRow (h : Hooks) (n : String) : IO Agent := do
  let some a ← run h (Store.txn [.agent] fun db => (db, db.agent n)) | fail s!"no agent {n}"
  return a

/-- watchd_tick(c, "t-comms", nil, { min_free_gib = 0 }): its error, none when every pass ran clean. -/
def tick (h : Hooks) : IO (Option String) :=
  return (← run h (Cmd.Watchd.tick (some "t-comms") none { minFreeGib := 0 } {})).2

-- reap judged a dead from hc ls (bound to t1, only t2 live), but a takeover rebound it to t2 since: spared
def reap_spares_a_rebound_terminal (t : T) : IO Unit := do
  setup t
  let h ← hooks t
  claim t "a" "t"
  t.q_ "update agent set hc='t1'"
  -- reap's read of the live agents is its agent-only transaction
  let ran ← racing h (· == [.agent]) (t.q_ "update agent set hc='t2' where name='a'")
  let out ← run h (Watchd.reap (some ["t2"]) (← now) none)
  ran
  eq out.length 0 (",".intercalate out)
  let a ← t.q1 "select hc, ended from agent"
  eq (a.f "hc") "t2"; eq (a.f "ended") Json.null
  eq ((← task1 t).f "state") "claimed"

-- a renew after reap's select of expired leases keeps the task; a fresh lock after its lock select keeps the lock
def reap_keeps_a_renewed_lease_and_a_fresh_lock (t : T) : IO Unit := do
  setup t
  let h ← hooks t
  claim t "a" "t1"
  t.q_ "insert into lock(path,agent,since,lease_until) values('a.txt','a',1,?)" [.int ((← now) + 3600)]
  t.q_ "update task set lease_until=1"
  t.q_ "update agent set ended=1"
  let ran ← racing h (·.contains .task) do t.q_ "update task set lease_until=? where id=1" [.int ((← now) + 3600)]
  let out ← run h (Watchd.reap none (← now) none)
  ran
  eq out.length 0 (",".intercalate out)
  eq ((← task1 t).f "state") "claimed"
  t.q_ "update lock set lease_until=1"
  let ran ← racing h (· == [.lock]) do t.q_ "update lock set lease_until=?" [.int ((← now) + 3600)]
  let out ← run h (Watchd.reap none (← now) none)
  ran
  eq out.length 0 (",".intercalate out)
  eq (← t.q "select * from lock").size 1

-- done/renew/block/release by a after its task was reaped and reclaimed by b: refused, b keeps it
-- (each is one transaction in Lean: no peer gets between its read and its write, so b's re-claim comes first)
def done_renew_block_release_by_a_reaped_owner_are_refused (t : T) : IO Unit := do
  setup t
  claim t "a" "t1"
  let acts := [("done", ["--evidence", "e"]), ("renew", ["--lease", "1h"]), ("block", ["q"]), ("release", [])]
  for (act, more) in acts do
    t.q_ "update task set owner='b' where id=1"
    let r ← t.sw "a" (["task", act, "1"] ++ more) { ok := false }
    unless r.code ≠ 0 do fail s!"{act}: not refused"
    let x ← task1 t
    eq (x.f "state") "claimed" act; eq (x.f "owner") "b" act
    t.q_ "update task set owner='a'"

-- end_agent re-checks what lifecycle judged: e claimed a task since, so it is neither ended nor cleaned
def end_agent_rechecks_a_claim_since (t : T) : IO Unit := do
  setup t
  let h ← hooks t
  t.q_ "insert into agent(name,cwd,status,last_active,started) values('e',?,'idle',1,1)" [.text t.repo]
  let row ← agentRow h "e"
  t.q_ "insert into task(title,state,owner,lease_until) values('t','claimed','e',?)" [.int ((← now) + 3600)]
  discard <| run h (Lifecycle.endAgent row false none)
  eq ((← t.q1 "select ended from agent where name='e'").f "ended") Json.null
  eq ((← task1 t).f "owner") "e"

-- end_agent re-checks stay: e ran `swarm stay` between lifecycle's judgment and the end, so it is kept
def end_agent_rechecks_stay (t : T) : IO Unit := do
  setup t
  let h ← hooks t
  t.q_ "insert into agent(name,cwd,status,last_active,started) values('e',?,'idle',1,1)" [.text t.repo]
  let row ← agentRow h "e"
  t.q_ "update agent set stay='reviews' where name='e'"
  discard <| run h (Lifecycle.endAgent row false none)
  eq ((← t.q1 "select ended from agent where name='e'").f "ended") Json.null

-- end_agent kills what the agent left in its cgroup scope (machine.PROC and CGROUP: SWARM_PROC and SWARM_CGROUP)
def end_agent_kills_its_cgroup_scope (t : T) : IO Unit := do
  setup t
  let h ← hooks t [("SWARM_PROC", t.d ++ "/proc"), ("SWARM_CGROUP", t.d ++ "/cg")]
  let scope := t.d ++ "/cg/u/swarm-agent-e-1.scope"
  IO.FS.createDirAll (t.d ++ "/proc/77"); IO.FS.createDirAll scope
  put (t.d ++ "/proc/77/cgroup") "0::/u/swarm-agent-e-1.scope\n"
  put (scope ++ "/memory.peak") "1048576\n"
  t.q_ "insert into agent(name,cwd,status,last_active,started,claude_pid) values('e',?,'idle',1,1,77)" [.text t.repo]
  let row ← agentRow h "e"
  discard <| run h (Lifecycle.endAgent row false none)
  unless (← t.q1 "select ended from agent where name='e'").f "ended" != Json.null do fail "e not ended"
  eq (← slurp (scope ++ "/cgroup.kill")) "1"

/-- The launch script (SWARM_LAUNCH) faked: each call's argv logged, `onLaunch n` run on the nth, stdout `hc<n>`. -/
def fakeLaunch (h : Hooks) (launch : String) (onLaunch : Nat → IO Unit := fun _ => pure ()) :
    IO (IO.Ref (Array (List String))) := do
  let launched ← IO.mkRef #[]
  h.proc.set fun argv => do
    if argv.head? != some launch then return none
    launched.modify (·.push argv)
    let n := (← launched.get).size
    onLaunch n
    return some (some { code := 0, stdout := s!"hc{n}", stderr := "" })
  return launched

/-- Hooks with the launch script and the swarm/ dir (brief.md, settings.template.json) set. -/
def spawnHooks (t : T) : IO Hooks := do
  hooks t [("SWARM_LAUNCH", t.d ++ "/launch"), ("SWARM_HERE", ← swarmDir)]

-- auto-spawn: a peer claims the task between pool() and the reserve; nothing launches, the peer keeps it
def auto_spawn_loses_the_race_for_a_task (t : T) : IO Unit := do
  setup t
  let h ← spawnHooks t
  t.q_ "insert into agent(name,cwd,status,last_active,started) values('t-comms',?,'working',1,1)" [.text t.repo]
  t.q_ "insert into task(title) values('do it')"
  let launched ← fakeLaunch h (t.d ++ "/launch")
  -- after auto_spawn's own read (the reserve's check runs in its write transaction: no peer gets in)
  let ran ← afterSpawnRead h do
    t.q_ "insert into agent(name,cwd,status,last_active,started) values('t-1',?,'working',1,1)" [.text t.repo]
    t.q_ "update task set state='claimed', owner='t-1' where id=1"
  -- cap 2: with t-1 live there is room for t-2, so the spawn is tried and its reserve loses (cap 1 would stop before it)
  t.q_ "insert or replace into meta(k,v) values('agent_min','2')"
  eq (← tick h) Json.null
  ran
  eq (← launched.get).size 0
  eq ((← task1 t).f "owner") "t-1"
  eq (← t.q "select 1 from agent where name='t-2'").size 0
  eq (← t.q "select 1 from msg where dest='t-comms'").size 0  -- a lost race is no launch failure

-- board #91: a task freed while auto-spawn launches (its last dependency done) is staffed before lower-priority ones
-- of the pool lifecycle read. X (#1) is claimed, L1 (#2) and L2 (#3) are open at P2, H (#4, P0) waits on X; X goes
-- done during L1's launch. Room for two: they go to L1 and H, not L1 and L2.
def board91_a_task_freed_during_a_launch_is_staffed_first (t : T) : IO Unit := do
  setup t
  let h ← spawnHooks t
  t.q_ "insert into agent(name,cwd,status,last_active,started) values('t-comms',?,'working',1,1)" [.text t.repo]
  t.q_ "insert into agent(name,cwd,status,last_active,started) values('t-1',?,'working',1,1)" [.text t.repo]
  t.q_ "insert into task(title,state,owner,lease_until) values('X','claimed','t-1',?)" [.int ((← now) + 7200)]
  t.q_ "insert into task(title) values('L1')"
  t.q_ "insert into task(title) values('L2')"
  t.q_ "insert into task(title,deps,priority) values('H','1',0)"
  t.q_ "insert or replace into meta(k,v) values('agent_min','3')"
  let launched ← fakeLaunch h (t.d ++ "/launch") fun n => do
    if n == 1 then t.q_ "update task set state='done' where id=1"
  eq (← tick h) Json.null
  let st := (← t.q "select id, state from task order by id").map fun r => (r.f "id", r.f "state")
  let state (i : Int) : Json := ((st.find? (·.1 == toJson i)).map (·.2)).getD .null
  eq (← launched.get).size 2 (repr (toJson st.toList))
  eq (state 2) "claimed"; eq (state 4) "claimed"; eq (state 3) "open"

-- board #91, and in the claim's own transaction: X done after auto_spawn's read of the pool, before the reserve
def board91_a_task_freed_before_the_reserve_is_staffed_first (t : T) : IO Unit := do
  setup t
  let h ← spawnHooks t
  t.q_ "insert into agent(name,cwd,status,last_active,started) values('t-comms',?,'working',1,1)" [.text t.repo]
  t.q_ "insert into agent(name,cwd,status,last_active,started) values('t-1',?,'working',1,1)" [.text t.repo]
  t.q_ "insert into task(title,state,owner,lease_until) values('X','claimed','t-1',?)" [.int ((← now) + 7200)]
  t.q_ "insert into task(title) values('L')"
  t.q_ "insert into task(title,deps,priority) values('H','1',0)"
  t.q_ "insert or replace into meta(k,v) values('agent_min','2')"
  discard <| fakeLaunch h (t.d ++ "/launch")
  let ran ← afterSpawnRead h (t.q_ "update task set state='done' where id=1")  -- right after auto_spawn's read
  eq (← tick h) Json.null
  ran
  eq ((← t.q1 "select state from task where id=3").f "state") "claimed"
  eq ((← t.q1 "select state from task where id=2").f "state") "open"

-- board #84: each pass under its own pcall: reap failing ends reap alone; the notices still run, and the tick raises it
-- (reap fails at its first transaction, the closest seam to the Lua's patched reap; the tick returns its errors)
def board84_reap_failing_ends_reap_alone (t : T) : IO Unit := do
  setup t
  let h ← hooks t
  t.q_ "insert into task(title,state,owner,question) values('q','blocked','x','which way?')"
  let armed ← IO.mkRef true
  h.before.set fun ts => do
    if (← armed.get) && ts == [.task, .agent] then armed.set false; throw (IO.userError "boom")
  let err ← tick h
  has (err.getD "") "reap: boom"
  exists_ t "select 1 from msg where dest='t-comms' and body like '%is blocked on #1%'"
  exists_ t "select 1 from event where kind='task-blocked' and path='1'"

-- the whole iteration is under pcall: an error in a pass that was not wrapped (ci_poll) used to end watchd, and so did
-- one in the loop's own read of the record
-- (the tick error's memory is the loop's St, so the two failing ticks run in one loop, the second taking the record
-- away so it ends; Lean's loop returns only why, so up is read as meta watchd_up)
def the_whole_iteration_is_under_pcall (t : T) : IO Unit := do
  setup t
  let h ← hooks t
  t.q_ "insert or replace into meta(k,v) values('watchd','me')"
  -- ci_poll raises: its first call, the repo's git, is the seam
  let booms ← IO.mkRef 0
  h.git.set fun _ cwd => do
    if cwd == some "/nonexistent" then
      booms.modify (· + 1)
      if (← booms.get) == 2 then t.q_ "delete from meta where k='watchd'"
      throw (IO.userError "boom")
  let opts : SwarmLean.Watchd.Opts := { minFreeGib := 0, once := false, interval := 0 }
  eq (← run h (Cmd.Watchd.loop "me" (some "t-comms") (some "/nonexistent") opts)) ": its record is gone"
  eq (← booms.get) 2
  eq (← t.q1 "select v from meta where k='watchd_up'") Json.null  -- up false
  eq (← t.q "select 1 from event where kind='watchd-tick-error'").size 1  -- once per distinct message
  h.git.set fun _ _ => pure ()
  t.q_ "insert or replace into meta(k,v) values('watchd','me')"
  eq (← run h (Cmd.Watchd.loop "me" (some "t-comms") none { opts with once := true })) Json.null
  eq ((← t.q1 "select v from meta where k='watchd_up'").f "v") "me"
  h.before.set fun _ => throw (IO.userError "database is locked")
  eq (← run h (Cmd.Watchd.loop "me" (some "t-comms") none { opts with once := true })) Json.null

def tests : List Case := [
  ("reap_spares_a_rebound_terminal", reap_spares_a_rebound_terminal),
  ("reap_keeps_a_renewed_lease_and_a_fresh_lock", reap_keeps_a_renewed_lease_and_a_fresh_lock),
  ("done_renew_block_release_by_a_reaped_owner_are_refused", done_renew_block_release_by_a_reaped_owner_are_refused),
  ("end_agent_rechecks_a_claim_since", end_agent_rechecks_a_claim_since),
  ("end_agent_rechecks_stay", end_agent_rechecks_stay),
  ("end_agent_kills_its_cgroup_scope", end_agent_kills_its_cgroup_scope),
  ("auto_spawn_loses_the_race_for_a_task", auto_spawn_loses_the_race_for_a_task),
  ("board91_a_task_freed_during_a_launch_is_staffed_first", board91_a_task_freed_during_a_launch_is_staffed_first),
  ("board91_a_task_freed_before_the_reserve_is_staffed_first", board91_a_task_freed_before_the_reserve_is_staffed_first),
  ("board84_reap_failing_ends_reap_alone", board84_reap_failing_ends_reap_alone),
  ("the_whole_iteration_is_under_pcall", the_whole_iteration_is_under_pcall)]

end SwarmLean.Tests.Spec.Watchd
