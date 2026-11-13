import SwarmLean.Cmd.Agents
import SwarmLean.Cmd.Hook
import SwarmLean.Cmd.Msgs
import SwarmLean.Lib.Watchd
import SwarmLean.Lib.Ci
import SwarmLean.Lib.Conflict

/-! `swarm watchd` (watchd.cmd_watchd): the record and its takeover, the loop of ticks under the tick lease, each pass
of a tick under its own guard, `--restart` and `--dry-run`. The passes are `Lib/Watchd.lean`. -/

namespace SwarmLean.Cmd.Watchd
open Args _root_.SwarmLean.Agents _root_.SwarmLean.Watchd

/-- `swarm watchd -h`. -/
def helpWatchd : String :=
  "Usage: swarm watchd [-h] [--comms <comms>] [--interval <interval>]\n       [--once] [--ci] [--takeover] [--restart] [--dry-run]\n       [--max-agents <max_agents>] [--min-free-mem <min_free_mem>]\n       [--blocker-idle <blocker_idle>] [--model <model>]\n       [--effort {low,medium,high,xhigh,max}]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --comms <comms>\n   --interval <interval>\n   --once\n   --ci                  also watch main CI with gh\n   --takeover            replace a live watchd; it exits on its next tick\n   --restart             start the same watchd (its recorded flags) in a hidden hc terminal, taking over\n   --dry-run             only list the worktrees the sweep would remove, then exit\n   --max-agents <max_agents>\n                         set the auto-spawn number (`swarm limits --min`; default: live agents when first started)\n   --min-free-mem <min_free_mem>\n                         GiB of MemAvailable needed to auto-spawn\n   --blocker-idle <blocker_idle>\n                         minutes an agent may sit idle holding a claim other tasks wait on before it is nudged and comms told\n   --model <model>       model for auto-spawned agents (default: sonnet; a task's own --model wins)\n   --effort {low,medium,high,xhigh,max}\n                         effort for auto-spawned agents (default: their settings)"

/-- The parser, as main.lua declares it. -/
def watchdSpec : Spec :=
  .mk "watchd" helpWatchd []
    [opt "--comms", opt "--interval" none (some int), flag "--once", flag "--ci", flag "--takeover", flag "--restart",
     flag "--dry-run", opt "--max-agents" none (some int), opt "--min-free-mem" none (some Cmd.Msgs.num),
     opt "--blocker-idle" none (some Cmd.Msgs.num), opt "--model",
     { opt "--effort" with choices := ["low", "medium", "high", "xhigh", "max"] }] [] [] none

/-- What watchd keeps between ticks: the sweep's "not landed" cache, the last tick error told, the cost tick's memory. -/
structure St where
  notLanded : List String := []
  lastErr : Option String := none
  cost : Cost.TickMem := {}

/-- A `--…` number as Lua's tostring prints it (`4`, `4.5`). -/
def numText (s : String) : String := fmtG ((parseFloat (strip s)).getD 0)

/-- The flags watchd ran with, as argv for `--restart`: comms resolved, --max-agents left out (watchd.flags). -/
def flags (a : Parsed) (comms : Option String) : List String :=
  ["--interval", d ((a.int "interval").getD 30), "--min-free-mem", numText ((a.str "min_free_mem").getD "4")] ++
  (match comms with | some c => ["--comms", c] | none => []) ++
  ["--blocker-idle", numText ((a.str "blocker_idle").getD "25")] ++
  (if a.flag "ci" then ["--ci"] else []) ++
  (match a.str "model" with | some x => ["--model", x] | none => []) ++
  (match a.str "effort" with | some x => ["--effort", x] | none => [])

/-- The flags given on this command line, as argv (what `--restart` amends the recorded flags with). -/
def given (a : Parsed) : List String :=
  [("comms", "--comms"), ("interval", "--interval"), ("min_free_mem", "--min-free-mem"), ("blocker_idle", "--blocker-idle"),
   ("model", "--model"), ("effort", "--effort"), ("max_agents", "--max-agents")].flatMap (fun (k, f) =>
    match a.str k with | some v => [f, v] | none => (match a.int k with | some v => [f, d v] | none => [])) ++
  (if a.flag "ci" then ["--ci"] else [])

/-- The recorded flags with those of `over` replacing same-named ones. -/
def amend (fl over : List String) : List String :=
  let rec go : List String → List String
    | f :: v :: r => if f.startsWith "--" && !v.startsWith "--" then (if over.contains f then go r else f :: v :: go r)
                     else if over.contains f then go (v :: r) else f :: go (v :: r)
    | [f] => if over.contains f then [] else [f]
    | [] => []
  go fl ++ over

/-- The first word of a watchd record, its pid. -/
def pidOf (rec : String) : Option Int := parseInt ((words rec).headD "")

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]
  [Guard m]

/-- The record's process lives (run.pid_alive of its first word). -/
def recAlive (rec : String) : m Bool := do
  match pidOf rec with
  | some p => Sys.pidAlive p
  | none => pure false

/-- A swarm with work always has its own communicator: its row bound to a live terminal in the swarm's space whose
session is this db's communicator; else one is launched there and bound. Why it can't, for the board's auto-spawn
line, or none (watchd.ensure_comms). -/
def ensureComms (comms : String) (terms : Option (List Term)) : m (Option String) := do
  let db ← Store.txn [.agent, .task, .«meta»] fun db => (db, db)
  let some sp := (db.getMeta "space").bind (·.v) | return none
  let some terms := terms | return none
  if !((Agents.live db).any (·.name != comms) || db.tasks.any (·.state = .open)) then return none
  let r := (Agents.live db).find? (·.name == comms)
  let dbp ← Spawn.dbPath
  for x in terms do
    if r.isSome && (r.bind (·.hc)) == x.address && x.state == some "live" then
      let (space, cm) ← Cmd.Agents.hcInfo (x.address.getD "")
      if space == some sp && cm == some dbp then return none
  if let some bo := (db.getMeta "comms_backoff").bind (·.v) then
    if (← Clock.now) < (parseInt bo).getD 0 then return some "no communicator can be launched (last launch failed)"
  let brief := s!"You are the communicator of this swarm (your name: {comms}), started by watchd because the swarm had work " ++
    "and no communicator in its Herdr space. Load the swarm skill, run `swarm board` and `swarm read`, and carry on as the communicator."
  let model := match db.agent comms with
    | some a => a.model.getD "opus"
    | none => "opus"
  let cwd ← Env.cwd
  let (out, err) ← Spawn.launchAgent comms brief model none (some cwd)
  let some out := out | do
    let now ← Clock.now
    Store.txn [.«meta»] fun db => (db.setMeta "comms_backoff" (some (d (now + 300))), ())
    return some ("no communicator can be launched: " ++ err)
  let addr := (splitlines (strip out)).getLastD ""
  Cmd.Agents.bindAgent comms (some cwd) (some addr) none true
  discard <| Proc.output ["hc", "label", addr, "swarm.comms=" ++ dbp] none []
  let now ← Clock.now
  Store.txn [.«meta»] fun db => ((delMeta db "comms_backoff").log now (some comms) "comms-launch" none (some addr), ())
  return none

/-- The user is away: a question waits for them. -/
def AWAY : String := " The user is away: answer it if it is yours to decide; else it waits for them."

/-- An hc terminal's prompt blocks its agent (blocked, the claim marked, comms told); gone, the claim given back. -/
def hcBlocked (terms : List Term) (t : Int) (comms : Option String) (away : Bool) : m Unit := do
  let db0 ← Store.txn [.agent, .event] fun db => (db, db)
  for a in Agents.live db0 do
    let some x := a.hc.bind (fun h => terms.find? (·.address == some h)) | continue
    let now ← Clock.now
    -- no agent in it yet, long after its spawn: a dialog before the session (folder trust)
    let spawned := (db0.events.filter fun e => e.kind == some "spawn" && e.data == some a.name).filterMap (·.ts)
    let nostart := x.status.isNone && spawned.foldl (fun acc s => acc || t - s >= START_WAIT) false
    if x.status != some "blocked" && !nostart then  -- the prompt is gone: give back the claim hc blocked
      let back (r : Task) : Task :=
        if r.owner == some a.name && r.state == .blocked && r.question == some HC_Q then
          { r with state := .claimed, question := none, lease_until := some (t + Tasks.LEASE) } else r
      -- the row this pass blocked follows the terminal again (board #135: a session started there later)
      let st := if x.status == some "working" then "working" else "idle"
      Store.txn [.task, .agent, .event] fun db =>
        let db := { db with tasks := db.tasks.map back }
        (if a.status == some "blocked" then (db.setAgent a.name ({ · with status := some st })).log now (some a.name) "status" none (some st) else db, ())
    else if a.status != some "blocked" then
      Store.txn [.agent, .task] fun db =>
        let db := (db.setAgent a.name ({ · with status := some "blocked" })).log now (some a.name) "blocked" none none
        let db := match ((db.tasks.filter fun r => r.owner == some a.name && r.state = .claimed).mergeSort (·.id ≤ ·.id)).head? with
          | some r =>  -- the agent notice below is the single notice; the task notice is marked sent
            (db.set r.id ({ · with state := .blocked, question := some HC_Q })).log now (some a.name) "task-blocked" (some (d r.id)) (some HC_Q)
          | none => db
        match comms with  -- while the user is away the question queues: not urgent
        | some c =>
          let hint := if nostart then
            s!" Its terminal {a.hc.getD ""} has no Claude session yet (a folder-trust prompt?): `hc read {a.hc.getD ""}`." else ""
          (say db now c (a.name ++ " is blocked (a prompt or question needs the human)." ++ hint ++ (if away then AWAY else "")) (!away) "system", ())
        | none => (db, ())

/-- Context compaction (board #136): each live agent holding work (a task, a stay, the communicator's role) gets
`Compact.step`'s act; the state is kept in meta `ctx:<name>` and only once the act is carried out. -/
def compactPass (terms : List Term) (comms : String) : m Unit := do
  let db ← Store.txn [.agent, .task, .event, .«meta»] fun db => (db, db)
  let (nAt, cAt, too) := (Compact.nudgeAt db, Compact.compactAt db, Compact.stayersToo db)
  for a in Agents.live db do
    let some h := py a.hc | continue
    let some x := terms.find? (·.address == some h) | continue
    let task := ((db.tasks.filter fun r => r.owner == some a.name && (r.state = .claimed || r.state = .blocked)).mergeSort
      (·.id ≤ ·.id)).head?
    let stays := a.name == comms || a.stay.isSome
    if !stays && task.isNone then continue  -- holds nothing: watchd ends it soon
    -- a compaction has ended (the hook logged "compact") and nothing woke the agent since: send it the stop hook's
    -- verdict as a prompt, once; a hook cannot start a turn itself
    let ev (kind : String) := (db.events.filter fun e => e.agent == some a.name && e.kind == some kind).getLast?.bind (·.ts)
    if Compact.Term.ofHc x.status == .idle then
      if let some t0 := ev "compact" then
        if (ev "ctx-continue").all (· < t0) then
          let now ← Clock.now
          Store.txn [.event] fun db => (db.log now (some a.name) "ctx-continue" none none, ())
          if let some why ← Hook.stopBlock a.name (Lean.Json.mkObj []) then
            if let some e ← Msgs.typeLine h ("Compaction done. " ++ why) then Env.err s!"continue {a.name}: hc send {h} failed: {e}"
          continue
    let k := a.ctx_tokens.getD 0
    let force := too || !stays
    let s0 := Compact.load db a.name
    let (act, s) := Compact.step k nAt cAt force (Compact.Term.ofHc x.status) s0
    let now ← Clock.now
    let done ← match act with
      | .nothing => pure true
      | .nudge =>
        Store.txn [.agent, .msg, .cursor, .event] fun db =>
          ((say db now a.name (Compact.nudgeText k cAt (task.map (·.id)) force) false "system").log now (some a.name)
            "ctx-nudge" none (some (d k)), true)
      | .compact =>
        match ← Msgs.typeLine h (← Msgs.compactLine db a none) with
        | some e => Env.err s!"compact {a.name}: hc send {h} failed: {e}"; pure false
        | none => Store.txn [.event] fun db => (db.log now (some a.name) "ctx-compact" none (some (d k)), true)
      | .failed =>
        Store.txn [.agent, .msg, .cursor, .event] fun db =>
          ((say db now comms (Compact.failedText a.name k cAt h) false "system").log now (some a.name)
            "ctx-compact-failed" none (some (d k)), true)
    if done && s != s0 then Store.txn [.«meta»] fun db => (Compact.save db a.name s, ())

/-- Each blocked task's question told to comms once per block: a task-blocked event after its latest `task block`. -/
def notices (comms : String) (away : Bool) : m Unit := do
  let db ← Store.txn [.task] fun db => (db, db)
  for r in db.tasks.filter (·.state = .blocked) do
    let now ← Clock.now
    Store.txn [.event] fun db =>
      -- the latest of the task's question events (model Model.lean, toldAfter): the same question asked again is new
      let e := (db.events.filter fun e =>
        (e.kind == some "block" && e.data.any fun x => x == "#" ++ d r.id || likePrefix x ("#" ++ d r.id ++ " ")) ||
        (e.kind == some "task-blocked" && e.path == some (d r.id))).getLast?
      if e.any (·.kind == some "task-blocked") then (db, ()) else
      -- the event marks it told: never without its message
      let db := db.log now r.owner "task-blocked" (some (d r.id)) r.question
      (say db now comms (s!"{r.owner.getD "None"} is blocked on #{d r.id} ({r.title.getD "nil"}): {r.question.getD "None"} " ++
        s!"Answer with `swarm task unblock {d r.id} --answer \"...\"`." ++ (if away then AWAY else "")) (!away) "system", ())

/-- One tick: each pass under its own guard, an error ending its pass alone; the errors joined, or none
(watchd.watchd_tick). -/
def tick (comms repo : Option String) (opts : Opts) (st : St) : m (St × Option String) := do
  let mut errs : List String := []
  let mut st := st
  let terms ← hcTerminals
  let live := terms.map fun ts => ts.filterMap fun x => if x.state == some "live" then x.address else none
  if let .error e ← Guard.guard (reap live (← Clock.now) comms) then errs := errs ++ ["reap: " ++ e]
  let mut opts := opts
  if let some c := comms then
    match ← Guard.guard (ensureComms c terms) with
    | .ok h => opts := { opts with commsHold := h }
    | .error e => errs := errs ++ ["comms: " ++ e]; opts := { opts with commsHold := none }
  let t ← Clock.now
  let away := (away (← Store.txn [.«meta»] fun db => (db, db))).isSome
  if let some ts := terms then
    if !ts.isEmpty then
      if let .error e ← Guard.guard (hcBlocked ts t comms away) then errs := errs ++ ["hc blocked: " ++ e]
  if let some c := comms then
    if let .error e ← Guard.guard (notices c away) then errs := errs ++ ["notices: " ++ e]
  let conflictPass : m Unit := do  -- a bad conflict pass never stops the tick
    let db ← Store.txn [.agent, .workspace] fun db => (db, db)
    Conflict.conflictTick (← Workspaces.wtMap db) (Bases.baseFor · none) t
  if let .error e ← Guard.guard conflictPass then Env.err s!"conflict: {e}"
  if let some c := comms then  -- ending reports to the communicator; without one, nobody hears what it did
    match ← Guard.guard (lifecycle t c terms opts st.notLanded) with
    | .ok nl => st := { st with notLanded := nl }
    | .error e => errs := errs ++ ["lifecycle: " ++ e]
    if let .error e ← Guard.guard (quiet t c) then errs := errs ++ ["quiet: " ++ e]
    if let .error e ← Guard.guard (hung t c terms opts.interval) then errs := errs ++ ["hung: " ++ e]
    if let .error e ← Guard.guard (blockers t c opts.blockerIdle) then errs := errs ++ ["blockers: " ++ e]
    if let some ts := terms then
      if let .error e ← Guard.guard (compactPass ts c) then errs := errs ++ ["compact: " ++ e]
  match ← Guard.guard (machineTick st.cost) with
  | .ok c => st := { st with cost := c }
  | .error e => errs := errs ++ ["machine: " ++ e]
  if let .error e ← Guard.guard (Run.remoteTick t) then errs := errs ++ ["remote: " ++ e]
  if let some r := repo then
    if let .error e ← Guard.guard (Ci.ciPoll (some r)) then errs := errs ++ ["ci_poll: " ++ e]
    if let .error e ← Guard.guard (Ci.ciCheck (some r) comms) then errs := errs ++ ["ci_check: " ++ e]
    if let .error e ← Guard.guard (Ci.prCi (some r)) then errs := errs ++ ["pr_ci: " ++ e]
    if let .error e ← Guard.guard (Ci.prWatch (some r)) then errs := errs ++ ["pr_watch: " ++ e]
  return (st, if errs.isEmpty then none else some ("; ".intercalate errs))

/-- An error out of a tick: to stderr, and logged and told to comms once per distinct message (watchd.tick_failed). -/
def tickFailed (comms : Option String) (msg : String) (st : St) : m St := do
  Env.err s!"watchd tick: {msg}"
  if st.lastErr == some msg then return st
  let now ← Clock.now
  Store.txn [] fun db =>
    let db := db.log now (some "swarm") "watchd-tick-error" none (some msg)
    (match comms with | some c => say db now c ("watchd tick failed (it carries on): " ++ msg) false "system" | none => db, ())
  return { st with lastErr := some msg }

/-- The tick lease (meta watchd_tick): the record still ours and no other live watchd mid-tick, in one transaction.
true: ours; false: the record isn't; none: another's tick (or the lease changed since its holder was checked). -/
def claimTick (mine : String) : m (Option Bool) := do
  let t0 ← Store.txn [.«meta»] fun db => (db, (db.getMeta "watchd_tick").bind (·.v))
  let busy ← match t0 with
    | some v => if v != mine then recAlive v else pure false
    | none => pure false
  Store.txn [.«meta»] fun db =>
    if (db.getMeta "watchd").bind (·.v) != some mine then (db, some false)
    else if (db.getMeta "watchd_tick").bind (·.v) != t0 || busy then (db, none)
    else (db.setMeta "watchd_tick" (some mine), some true)

/-- One pass of the loop: the record, then the tick; whether a tick has finished, why watchd exits if it should, and
the tick's error (watchd.watchd_pass). -/
def watchdPass (mine : String) (comms repo : Option String) (opts : Opts) (up : Bool) (st : St) :
    m (Bool × Option String × St × Option String) := do
  let db ← Store.txn [.«meta»] fun db => (db, db)
  let some cur := (db.getMeta "watchd").bind (·.v) | return (up, some ": its record is gone", st, none)
  if cur != mine then
    -- hand over only to a live watchd that has finished a tick; a replacement that died gets the record back
    let alive ← recAlive cur
    if (db.getMeta "watchd_up").bind (·.v) == some cur && alive then return (up, some s!" was replaced by {cur}", st, none)
    if !alive then
      let now ← Clock.now
      Store.txn [.«meta»] fun db =>  -- the record and its event together: a reader that sees one sees both
        if (db.getMeta "watchd").bind (·.v) == some cur then
          ((db.setMeta "watchd" (some mine)).log now (some "swarm") "watchd-back" none (some s!"{cur} died before its first tick; {mine} carries on"), ())
        else (db, ())
    return (up, none, st, none)
  let mut mid ← claimTick mine
  while mid.isNone do  -- not a whole interval: --restart waits for our first tick
    Sys.sleep 1000
    mid ← claimTick mine
  if mid != some true then return (up, none, st, none)
  let (st, err) ← match ← Guard.guard (tick comms repo opts st) with
    | .ok r => pure r
    | .error e => pure (st, some e)
  Store.txn [.«meta»] fun db =>
    let db := if err.isNone && !up then db.setMeta "watchd_up" (some mine) else db
    (if (db.getMeta "watchd_tick").bind (·.v) == some mine then delMeta db "watchd_tick" else db, ())
  match err with
  | some e => return (up, none, st, some e)
  | none => return (true, none, { st with lastErr := none }, none)

/-- watchd's loop: passes, a failed tick reported, the pause, until a pass says why watchd exits (or `--once`); why
(watchd.loop). -/
def loop (mine : String) (comms repo : Option String) (opts : Opts) : m (Option String) := do
  let mut up := false
  let mut st : St := {}
  repeat
    let (up', why, st', err) ← match ← Guard.guard (watchdPass mine comms repo opts up st) with
      | .ok r => pure r
      | .error e => pure (up, none, st, some e)
    up := up'; st := st'
    if let some e := err then
      match ← Guard.guard (tickFailed comms e st) with
      | .ok s => st := s
      | .error _ => pure ()
    if why.isSome then return why
    if opts.once then return none
    Sys.sleep (opts.interval.toNat * 1000)
  return none

/-- `swarm watchd --restart`: the same watchd (recorded flags and cwd) in a hidden hc terminal, taking over; success
only once it has finished a tick (watchd.restart). -/
def restart (over : List String := []) : m UInt32 := do
  let db ← Store.txn [.«meta»] fun db => (db, db)
  let rec_ := ((db.getMeta "watchd_run").bind (·.v)).bind Json.decode
  let some (fl, cwd) := rec_.bind (fun j => match Json.field j "flags", Json.fstr j "cwd" with
      | some f, some c => some ((Json.items f).filterMap Json.str?, c)
      | some f, none => some ((Json.items f).filterMap Json.str?, "")
      | _, _ => none)
    | die "no recorded watchd flags (it predates them); start it by hand once"
  let old := (db.getMeta "watchd").bind (·.v)
  let here := (← Spawn.swarmHere).getD "."
  let argv := ["hc", "run", "--json", "--bg", "--no-parent", "--no-notify", "--cwd", cwd, "--", joinPath here "swarm", "watchd", "--takeover"] ++ amend fl over
  let o ← Sys.exec argv { env := [("SWARM_DB", some (← Spawn.dbPath))] }
  let fail (why : String) : m Unit := do
    let still ← match old with | some o => recAlive o | none => pure false
    die s!"watchd restart failed: {why}; {if still then s!"the old watchd (pid {(words (old.getD "")).headD ""}) still runs" else "NO watchd runs: start one by hand"}"
  if o.code != 0 then fail s!"`hc run` exited {o.code}: {strip o.stderr}"
  let wait := ((← env "SWARM_WATCHD_UP_WAIT").bind (parseFloat ∘ strip)).getD 90
  let t0 ← Clock.now
  let mut seen : Option String := none  -- the record of the watchd that took over (it may already have given it back)
  while Float.ofInt ((← Clock.now) - t0) < wait do
    let db ← Store.txn [.«meta»] fun db => (db, db)
    let r := (db.getMeta "watchd").bind (·.v)
    if r.isSome && r != old then seen := r
    if let some s := seen then
      if !(← recAlive s) then break
      if r == some s && (db.getMeta "watchd_up").bind (·.v) == some s then
        let ws := words s
        Env.out s!"watchd restarted: pid {ws.headD ""}, terminal {(ws[1]?).getD "-"}"
        return 0
    Sys.sleep 200
  if let some s := seen then  -- it took the record but never ticked: stop it and give the record back
    let alive ← recAlive s
    -- shortcut: SIGTERM through kill(1); Sys has no signal call
    if alive then discard <| Proc.output ["kill", "-TERM", (words s).headD ""] none []
    if let some o := old then
      Store.txn [.«meta»] fun db => (if (db.getMeta "watchd").bind (·.v) == some s then db.setMeta "watchd" (some o) else db, ())
    fail s!"the new watchd ({s}) {if alive then "did not finish a tick" else "died before its first tick"}"
  fail s!"no new watchd took over within {(Float.floor wait).toInt64.toInt} s"
  return 1

/-- `swarm watchd [...]` (watchd.cmd_watchd). -/
def watchd (a : Parsed) : m UInt32 := do
  if a.flag "dry_run" then
    for (wt, br, mb) in (← sweep none true []).1 do Env.out s!"{wt}\t{br.getD "None"}\t{mb} MB"
    return 0
  if a.flag "restart" then return ← restart (given a)
  let repo ← if a.flag "ci" then git ["rev-parse", "--show-toplevel"] else pure none
  let comms ← match py (a.str "comms") with | some c => pure (some c) | none => env "SWARM_COMMS"
  let mine := s!"{← Sys.getpid} {(← env "HC_TERMINAL_ID").getD "-"}"  -- the watchd record
  let old := ((← Store.txn [.«meta»] fun db => (db, db)).getMeta "watchd").bind (·.v)
  let oldAlive ← match old with | some o => recAlive o | none => pure false
  let once := a.flag "once"
  let run := Json.encode (Lean.Json.mkObj [("cwd", .str (← Env.cwd)),
    ("flags", .arr (flags a comms |>.map Lean.Json.str |>.toArray)), ("started", Json.int (← Clock.now))])
  let now ← Clock.now
  let refused ← Store.txn [.«meta», .agent] fun db =>
    let o := (db.getMeta "watchd").bind (·.v)
    -- the pid was checked outside: a record changed since counts as alive
    if o.isSome && o != some mine && (o != old || oldAlive) && !a.flag "takeover" then (db, o) else
    let db := db.setMeta "watchd" (some mine)
    let db := if once then db else db.setMeta "watchd_run" (some run)  -- what --restart starts again
    match comms with  -- the communicator is a stayer; meta.comms is only where watchd sends what needs the human
    | some c =>
      let db := db.setMeta "comms" (some c)
      if (db.agent c).any fun x => x.ended.isNone && x.stay.isNone then
        ((db.setAgent c ({ · with stay := some "the user's channel" })).log now (some c) "stay" none (some "the user's channel"), none)
      else (db, none)
    | none => (db, none)
  if let some o := refused then
    let ws := words o
    die s!"watchd already runs (pid {ws.headD ""}, terminal {(ws[1]?).getD ""}); `swarm watchd --takeover` replaces it."
  -- the auto-spawn number: --max-agents writes it; else the first watchd sets it to the roster the human launched
  let envComms ← env "SWARM_COMMS"
  Store.txn [.agent, .«meta»] fun db =>
    let (n, mn, _) := limits db envComms
    match a.int "max_agents", mn with
    | some x, _ => (db.setMeta "agent_min" (some (d x)), ())
    | none, none => (db.setMeta "agent_min" (some (toString n)), ())
    | none, some _ => (db, ())
  let num (k dflt : String) : Float := (parseFloat (strip ((a.str k).getD dflt))).getD 0
  let opts : Opts := { minFreeGib := num "min_free_mem" "4", model := a.str "model", effort := a.str "effort",
                       interval := (a.int "interval").getD 30, once, blockerIdle := num "blocker_idle" "25" }
  if let some why ← loop mine comms repo opts then die s!"watchd (pid {← Sys.getpid}){why}; exiting"
  return 0

/-- The group. -/
def group : Group m where
  specs := [("watchd", watchdSpec)]
  run a := watchd a

end SwarmLean.Cmd.Watchd
