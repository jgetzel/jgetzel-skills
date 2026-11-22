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
  "Usage: swarm watchd [-h] [--comms <comms>] [--interval <interval>]\n       [--once] [--ci] [--takeover] [--restart] [--dry-run]\n       [--max-agents <max_agents>] [--min-free-mem <min_free_mem>]\n       [--blocker-idle <blocker_idle>] [--model <model>]\n       [--effort {low,medium,high,xhigh,max}]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --comms <comms>       set the communicator of the swarm this acts on\n   --interval <interval>\n   --once\n   --ci                  turn on the swarm's `ci` knob: watch its repos' base CI and PRs with gh\n   --takeover            replace a live watchd; it exits on its next tick\n   --restart             start the same watchd (its recorded flags) in a hidden hc terminal, taking over\n   --dry-run             only list the worktrees the sweep would remove in the folder's repo, then exit\n   --max-agents <max_agents>\n                         set the swarm's auto-spawn number (`swarm limits --min`; default: its live agents when unset)\n   --min-free-mem <min_free_mem>\n                         GiB of MemAvailable needed to auto-spawn\n   --blocker-idle <blocker_idle>\n                         minutes an agent may sit idle holding a claim other tasks wait on before it is nudged and comms told\n   --model <model>       set the swarm's model for auto-spawned agents (`spawn_model`; default: sonnet; a task's own --model wins)\n   --effort {low,medium,high,xhigh,max}\n                         set the swarm's effort for auto-spawned agents (`spawn_effort`; default: their settings)\n\nOne watchd runs per machine: each tick it runs every live swarm's agent and swarm passes, every repo's conflict,\nlock, sweep and (a staffing swarm's `ci` knob on) CI passes, then the machine's, and hourly copies the db to\nswarm.db.bak beside it. --comms, --max-agents, --ci, --model and --effort set knobs of the swarm this command acts\non (`--swarm`, $SWARM, ...); the others are the machine's.\n\nThe communicator needs no waiter: with none alive, each tick sends its unread messages (as `swarm\nread` prints them, once the oldest is 20 s old, at most 40 lines) and marks them read once sent; only while hc shows\nthe terminal idle or working, never blocked or compacting, and while no other agent lives only for an urgent one.\n\nwatchd sends to an agent (these messages, the continue line after a compaction or an API error) as a Claude Code\ncross-session message, posted to the inbox socket its `swarm` commands recorded; with none recorded, or once a\npost fails (the communicator is told once), it types the line with hc send. A /compact is always typed."

/-- The parser, as main.lua declares it. -/
def watchdSpec : Spec :=
  .mk "watchd" helpWatchd []
    [opt "--comms", opt "--interval" none (some int), flag "--once", flag "--ci", flag "--takeover", flag "--restart",
     flag "--dry-run", opt "--max-agents" none (some int), opt "--min-free-mem" none (some Cmd.Msgs.num),
     opt "--blocker-idle" none (some Cmd.Msgs.num), opt "--model",
     { opt "--effort" with choices := ["low", "medium", "high", "xhigh", "max"] }] [] [] none

/-- `swarm worktrees -h`. -/
def helpWorktrees : String :=
  "Usage: swarm worktrees [-h] <command> ...\n\nOptions:\n   -h, --help            Show this help message and exit.\n\nCommands:\n   prune"

/-- `swarm worktrees prune -h`. -/
def helpWorktreesPrune : String :=
  "Usage: swarm worktrees prune [-h] [--apply] [--dir <dir>]\n\nOptions:\n   -h, --help            Show this help message and exit.\n   --apply               remove them (default: only list what would go)\n   --dir <dir>           the worktrees under it (default: .worktrees of the main checkout)\n\nRemoves the worktrees whose work is in a base: the sweep's gate and removal, agent-owned or not."

/-- The `worktrees` parser. -/
def worktreesSpec : Spec :=
  .mk "worktrees" helpWorktrees [] [] [] (cmdTarget := some "act") (cmds :=
    [.mk "prune" helpWorktreesPrune [] [flag "--apply", opt "--dir"] [] [] none])

/-- What watchd keeps between ticks: the sweep's "not landed" cache, the last tick error told, the cost tick's memory. -/
structure St where
  notLanded : List String := []
  lastErr : Option String := none
  cost : Cost.TickMem := {}

/-- A `--…` number as Lua's tostring prints it (`4`, `4.5`). -/
def numText (s : String) : String := fmtG ((parseFloat (strip s)).getD 0)

/-- The machine's flags watchd ran with, as argv for `--restart` (watchd.flags); a swarm's knobs are its meta. -/
def flags (a : Parsed) : List String :=
  ["--interval", d ((a.int "interval").getD 30), "--min-free-mem", numText ((a.str "min_free_mem").getD "4"),
   "--blocker-idle", numText ((a.str "blocker_idle").getD "25")]

/-- The machine's flags given on this command line, as argv (what `--restart` amends the recorded flags with). -/
def given (a : Parsed) : List String :=
  [("interval", "--interval"), ("min_free_mem", "--min-free-mem"), ("blocker_idle", "--blocker-idle")].flatMap (fun (k, f) =>
    match a.str k with | some v => [f, v] | none => (match a.int k with | some v => [f, d v] | none => []))

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
  [Guard m] [Scoped m]

/-- The record's process lives (run.pid_alive of its first word). -/
def recAlive (rec : String) : m Bool := do
  match pidOf rec with
  | some p => Sys.pidAlive p
  | none => pure false

/-- A swarm's communicator is present (sw-global §4): its live row bound to a terminal hc lists live. No space, label or
folder enters it. -/
def commsPresent (r : Option Agent) (terms : List Term) : Bool :=
  r.any fun a => a.ended.isNone && (py a.hc).any fun h => terms.any fun x => x.address == some h && x.state == some "live"

/-- A swarm whose communicator joined from a Herdr terminal gets one launched and bound when its bound terminal is gone
(not `commsPresent`) and the swarm has work it can start (`Queue.staffing` of its repos: a held task is none, board
#67). A live
binding is never moved: only `swarm join --takeover` moves one. Why it can't, for the board's auto-spawn line, or none
(watchd.ensure_comms). -/
def ensureComms (comms : String) (terms : Option (List Term)) : m (Option String) := do
  let db ← Store.txn [.agent, .task, .«meta»] fun db => (db, db)
  -- only a swarm whose communicator joined from a Herdr terminal (`join` records it) gets one launched
  if ((db.getMeta "comms_hc").bind (·.v)).isNone then return none
  let some sw ← env "SWARM" | return none
  let some terms := terms | return none
  if commsPresent (db.agent comms) terms then return none
  let mine ← Swarms.staffable sw  -- work of its repos (sw-global §2), as auto-spawn staffs it
  if !(Queue.staffing db).any (mine.contains ·.id) then return none
  if let some bo := (db.getMeta "comms_backoff").bind (·.v) then
    if (← Clock.now) < (parseInt bo).getD 0 then return some "no communicator can be launched (last launch failed)"
  let brief := s!"You are the communicator of swarm {sw} (your name: {comms}), started by watchd because the swarm had " ++
    "work it could start and its communicator's terminal was gone. Load the swarm skill, run `swarm board` and `swarm read`, and carry on as the communicator."
  let model := match db.agent comms with
    | some a => a.model.getD "opus"
    | none => "opus"
  let cwd ← Env.cwd
  let (out, err) ← Spawn.launchAgent comms brief model none (some cwd) true
  let some out := out | do
    let now ← Clock.now
    Store.txn [.«meta»] fun db => (db.setMeta "comms_backoff" (some (d (now + 300))), ())
    return some ("no communicator can be launched: " ++ err)
  let addr := (splitlines (strip out)).getLastD ""
  -- a `join` while it launched bound the row to a live terminal: that binding stays
  let db ← Store.txn [.agent] fun db => (db, db)
  if commsPresent (db.agent comms) ((← hcTerminals).getD []) then return none
  Cmd.Agents.bindAgent comms (some cwd) (some addr) none false
  discard <| Proc.output ["hc", "label", addr, "swarm=" ++ sw] none []
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

/-- How long a continue line may go unanswered (no turn) before it is sent once more. -/
def RESUME_WAIT : Int := 5 * 60

/-- Context compaction (board #136): each live agent holding work (a task, a stay, the communicator's role) gets
`Compact.step`'s act; the state is kept in meta `ctx:<name>` and only once the act is carried out. -/
def compactPass (terms : List Term) (comms : String) : m Unit := do
  let db ← Store.txn [.agent, .task, .event, .«meta», .workspace] fun db => (db, db)
  let (nAt, cAt, too) := (Compact.nudgeAt db, Compact.compactAt db, Compact.stayersToo db)
  for a in Agents.live db do
    let some h := py a.hc | continue
    let some x := terms.find? (·.address == some h) | continue
    let task := ((db.tasks.filter fun r => r.owner == some a.name && (r.state = .claimed || r.state = .blocked)).mergeSort
      (·.id ≤ ·.id)).head?
    let stays := a.name == comms || a.stay.isSome
    let ev (kind : String) := (db.events.filter fun e => e.agent == some a.name && e.kind == some kind).getLast?.bind (·.ts)
    let evId (kind : String) := (db.events.filter fun e => e.agent == some a.name && e.kind == some kind).getLast?.map (·.id)
    let idle := Compact.Term.ofHc x.status == .idle
    -- a continue line nobody answered in RESUME_WAIT (no turn since): sent once more and the communicator told, once
    if idle then
      if let (some cid, some ct) := (evId "ctx-continue", ev "ctx-continue") then
        let now ← Clock.now
        if now - ct ≥ RESUME_WAIT && a.last_active.getD 0 ≤ ct && (evId "ctx-resent").all (· < cid) then
          Store.txn [.agent, .msg, .cursor, .event] fun db =>
            ((say db now comms s!"{a.name} did not resume after its compaction (terminal {h})." false "system").log now (some a.name)
              "ctx-resent" none none, ())
          let why := (← Hook.stopBlock a.name (Lean.Json.mkObj [])).getD "Carry on with what your keep note says is next."
          if let some e ← Msgs.deliverTo a.name h ("Compaction done. " ++ why) then Env.err s!"continue {a.name}: hc send {h} failed: {e}"
    -- a compaction ended (the hook's `compact` event, then the continue line or the agent's first turn) and the stay
    -- was set before it: the stay ends
    let mut stayNote := ""
    if let (some s, some cid) := (a.stay, evId "compact") then
      let ended := (db.events.any fun e => e.agent == some a.name && e.id > cid && (e.kind == some "stay" || e.kind == some "stay-end"))
      let t0 := (ev "compact").getD 0
      let willSend := idle && (evId "ctx-continue").all (· < cid) && a.last_active.getD 0 ≤ t0
      let done := (evId "ctx-continue").any (· > cid) || a.last_active.getD 0 > t0 || willSend
      if !ended && done then
        let now ← Clock.now
        Store.txn [.agent, .event] fun db =>
          ((db.setAgent a.name ({ · with stay := none })).log now (some a.name) "stay-end" (some s) (some "compaction"), ())
        stayNote := s!" Your stay '{s}' ended with the compaction; `swarm stay \"<why>\"` again if it still holds."
        if !willSend then
          Store.txn [.agent, .msg, .cursor] fun db => (say db now a.name stayNote.trimAscii.toString false "system", ())
    if !stays && task.isNone then continue  -- holds nothing: watchd ends it soon
    -- a compaction has ended (the hook logged "compact") and nothing woke the agent since: send it the stop hook's
    -- verdict as a prompt, once; a hook cannot start a turn itself
    if idle then
      if let some t0 := ev "compact" then
        if (ev "ctx-continue").all (· < t0) && a.last_active.getD 0 ≤ t0 then
          let now ← Clock.now
          Store.txn [.event] fun db => (db.log now (some a.name) "ctx-continue" none none, ())
          -- a stayer or the communicator has no verdict (a declared wait): still tell it to carry on
          let why := (← Hook.stopBlock a.name (Lean.Json.mkObj [])).getD "Carry on with what your keep note says is next."
          if let some e ← Msgs.deliverTo a.name h ("Compaction done. " ++ why ++ stayNote) then Env.err s!"continue {a.name}: hc send {h} failed: {e}"
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

/-- A terminal idle this long with the agent's hooks silent and its transcript ending on an API error: the stop hook never ran. -/
def APIERR_IDLE : Int := 2 * 60

/-- How long a continue line after an API error may go unanswered before the communicator is told. -/
def APIERR_WAIT : Int := 5 * 60

/-- A turn that ended on an API error (board #194). The StopFailure hook logs `api-error`; failing that, a row still
"working" whose terminal hc shows idle/done, silent APIERR_IDLE, with a transcript ending on one gets it logged here and
its status set idle. Per `api-error` event, once: the agent gets a continue line typed into its terminal (the
communicator is only told); no turn APIERR_WAIT later, the communicator is told, once. A later turn re-arms it. -/
def apiErrorPass (terms : List Term) (comms : String) : m Unit := do
  let db ← Store.txn [.agent, .task, .event, .«meta»] fun db => (db, db)
  for a in Agents.live db do
    let some h := py a.hc | continue
    let some x := terms.find? (·.address == some h) | continue
    let idle := Compact.Term.ofHc x.status == .idle
    let now ← Clock.now
    let la := a.last_active.getD 0
    if a.status == some "working" && idle && now - la ≥ APIERR_IDLE then
      let tr := (db.getMeta ("tr:" ++ a.name)).bind (·.v)
      if let some txt ← SwarmLean.Hook.errorText tr then
        Store.txn [.agent, .event] fun db =>
          ((db.setAgent a.name ({ · with status := some "idle" })).log now (some a.name) "api-error" none (some txt), ())
    let db ← Store.txn [.agent, .task, .event, .«meta»] fun db => (db, db)
    let evs (kind : String) := db.events.filter fun e => e.agent == some a.name && e.kind == some kind
    let la := ((db.agent a.name).bind (·.last_active)).getD 0
    let some err := (evs "api-error").getLast? | continue
    let et := err.ts.getD 0
    if la > et then continue  -- a turn since: re-armed
    if !idle then continue
    let sent := (evs "api-resume").getLast?.filter (·.id > err.id)
    match sent with
    | none =>
      let task := ((db.tasks.filter fun r => r.owner == some a.name && (r.state = .claimed || r.state = .blocked)).mergeSort
        (·.id ≤ ·.id)).head?
      let txt := err.data.getD ""
      if a.name == comms then
        Store.txn [.agent, .msg, .cursor, .event] fun db =>
          ((say db now comms s!"Your last turn ended on an API error ({txt}); nothing woke it. Go on from where you were." false "system").log now
            (some a.name) "api-resume" none none, ())
      else
        let line := s!"Your last turn ended on an API error ({txt}). Go on from where you were" ++
          (match task with | some r => s!": task #{r.id}." | none => ".")
        Store.txn [.event] fun db => (db.log now (some a.name) "api-resume" none none, ())
        if let some e ← Msgs.deliverTo a.name h line then Env.err s!"api-error {a.name}: hc send {h} failed: {e}"
    | some s =>
      if now - s.ts.getD 0 ≥ APIERR_WAIT && a.name != comms && (evs "api-noresume").all (·.id < err.id) then
        Store.txn [.agent, .msg, .cursor, .event] fun db =>
          ((say db now comms s!"{a.name} did not resume after an API error (terminal {h})." false "system").log now
            (some a.name) "api-noresume" none none, ())

/-- How old the communicator's oldest waking unread message is before watchd types its inbox in (`commsInbox`): a
burst within it goes in one block. -/
def COMMS_SETTLE : Int := 20

/-- The communicator's inbox (board #210). It has no hooks, so with no live waiter watchd sends its unread messages
(`Msgs.deliverTo`: its inbox socket, else typed into its terminal, board #215): `swarm read`'s lines under the peer
head, at most `Msgs.TYPE_LINES` (then "N more"), once a waking one (not a plain notice) is COMMS_SETTLE old. They are
marked read only once sent (event `comms-deliver`, data the last id). Only while hc shows the terminal idle or working (Claude Code queues it to the turn's end): never
into a prompt, which it could answer (hc send refuses a blocked one too). None while it compacts (compactPass sends
its continue line); while no other agent lives, only for an urgent message: the terminal may hold a session doing
other work. A live waiter delivers itself. -/
def commsInbox (t : Int) (comms : String) (terms : Option (List Term)) : m Unit := do
  let db ← Store.txn [.agent, .event, .msg, .cursor] fun db => (db, db)
  let some a := db.agent comms | return
  if a.ended.isSome then return
  let some h := py a.hc | return
  let some x := terms.bind (·.find? fun x => x.address == some h && x.state == some "live") | return
  let st := Compact.Term.ofHc x.status
  if !(st == .idle || st == .working) then return
  if Compact.compacting db.events comms (a.last_active.getD 0) t then return
  if ← (match a.waiter with | some w => Sys.pidAlive w | none => pure false) then return
  let rows := Msgs.unread db comms
  let urg (r : Msg) : Bool := r.urgent.getD 0 != 0
  let wake := rows.filter fun r => r.kind != some "notice" || urg r
  let some oldest := wake.head? | return
  if (Agents.live db).all (·.name == comms) && !wake.any urg then return
  if t - oldest.ts.getD t < COMMS_SETTLE then return
  let fit := Msgs.linesFit Msgs.TYPE_LINES rows
  let some last := fit.getLast? | return
  let now ← Clock.now
  let hh ← fit.mapM fun r => Clock.hhmm (r.ts.getD now)
  match ← Msgs.deliverTo comms h (Msgs.typedNote hh fit (rows.length - fit.length)) with
  | some e => Env.err s!"comms inbox: hc send {h} failed: {e}"
  | none =>
    let now ← Clock.now
    Store.txn [.msg, .cursor, .event] fun db =>
      ((Msgs.typedStep comms last.id db).1.log now (some comms) "comms-deliver" none (some (d last.id)), ())

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

/-- A pass under its guard: its error, prefixed, added to `errs`. -/
def pass (errs : List String) (what : String) (x : m Unit) : m (List String) := do
  match ← Guard.guard x with
  | .ok _ => pure errs
  | .error e => pure (errs ++ [what ++ e])

/-- The repo of folder `dir`: its main worktree, resolved; `''` outside one or when it is gone. -/
def repoOf (dir : String) : m String := do
  if dir == "" || (← Sys.kind dir true) != .dir then return ""
  return (← Workspaces.main (some dir)).getD ""

/-- What one tick covers (sw-global §4), read at its start: the live swarms, each live agent's (name, swarm, repo: of
its worktree, else its folder), the repos (every one the db names or a live agent works in), and for each live swarm's
repo (repo, swarm, its communicator, its `ci` knob). -/
structure Plan where
  swarms : List Swarms.Row := []
  agents : List (String × String × String) := []
  repos : List String := []
  staff : List (String × String × Option String × Bool) := []

/-- The plan of a tick, from the machine's db. -/
def plan : m Plan := do
  let swarms := (← Swarms.list).filter (·.ended.isNone)
  let rs ← Sys.sqlAt (← Swarms.dbPath) "" [
    ("select a.name, coalesce(a.swarm, ''), coalesce(nullif(a.wt, ''), a.cwd, ''), (select w.repo from workspace w " ++
      "where w.agent = a.name and w.path = a.wt and w.repo <> '') from agent a where a.ended is null order by a.name", []),
    ("select path from repo union select repo from swarm_repo union select repo from workspace where repo <> '' " ++
      "union select repo from lock where repo <> ''", []),
    ("select sr.repo, sr.swarm, s.comms, (select v from meta m where m.scope = sr.swarm and m.k = 'ci') from swarm_repo sr " ++
      "join swarm s on s.name = sr.swarm where s.ended is null order by sr.swarm, sr.repo", [])] true
  let txt := Swarms.txt
  let mut agents := []
  let mut seen : List (String × String) := []  -- each folder asked of git once
  for r in (rs.getD 0 #[]).toList do
    let dir := (txt r[2]?).getD ""
    let repo ← match txt r[3]?, seen.lookup dir with
      | some w, _ => pure w
      | none, some x => pure x
      | none, none => do let x ← repoOf dir; seen := (dir, x) :: seen; pure x
    agents := agents ++ [((txt r[0]?).getD "", (txt r[1]?).getD "", repo)]
  let mut repos := []
  for r in ((rs.getD 1 #[]).toList.filterMap (txt ·[0]?)) ++ agents.map (·.2.2) do
    if r != "" && !repos.contains r && (← Sys.kind r true) == .dir then repos := repos ++ [r]
  let staff := (rs.getD 2 #[]).toList.filterMap fun r => match txt r[0]?, txt r[1]? with
    | some p, some sw => some (p, sw, txt r[2]?, (txt r[3]?).any (· != ""))
    | _, _ => none
  return { swarms, agents, repos, staff }

/-- A swarm's home repo, where its own passes and auto-spawn run: its first repo, else its communicator's, else its
first agent's; `''` with none. -/
def Plan.home (p : Plan) (sw : Swarms.Row) : String :=
  let mine := p.agents.filter (·.2.1 == sw.name)
  match sw.repos.head? with
  | some r => r
  | none => match (mine.find? fun a => some a.1 == sw.comms).map (·.2.2) with
    | some r => if r != "" then r else ((mine.map (·.2.2)).find? (· != "")).getD ""
    | none => ((mine.map (·.2.2)).find? (· != "")).getD ""

/-- A swarm's knobs for auto-spawn: its `spawn_model` and `spawn_effort` over watchd's flags. -/
def knobs (opts : Opts) : m Opts := do
  let db ← Store.txn [.«meta»] fun db => (db, db)
  let k (key : String) : Option String := py ((db.getMeta key).bind (·.v))
  return { opts with model := (k "spawn_model").orElse fun _ => opts.model, effort := (k "spawn_effort").orElse fun _ => opts.effort }

/-- One swarm's passes (sw-global §4, per agent and per swarm), in the swarm's scope and its home repo: reap, its
communicator, hc's prompts, the blocked notices, the lifecycle (ends, offers, auto-spawn: an agent working in another
repo is judged as the lifecycle judges a foreign worktree), then the quiet, hung, inbox, blocker, landing, compaction
and API-error passes. Without a communicator only reap and hc's prompts run: nobody would hear the rest. The errors. -/
def swarmTick (p : Plan) (sw : Swarms.Row) (terms : Option (List Term)) (opts : Opts) (t : Int) : m (List String) := do
  let home := p.home sw
  let pre := s!"{sw.name}: "
  let live := terms.map fun ts => ts.filterMap fun x => if x.state == some "live" then x.address else none
  let hs : Scope := { swarm := sw.name, repo := home }
  let comms := sw.comms
  let foreign := (p.agents.filter (·.2.1 != sw.name)).map (·.1)
  let (errs, opts) ← Scoped.within hs do
    let mut errs : List String := []
    errs ← pass errs (pre ++ "reap: ") (discard <| reap live (← Clock.now) comms foreign)
    let mut opts ← match ← Guard.guard (knobs opts) with
      | .ok o => pure o
      | .error e => errs := errs ++ [pre ++ "knobs: " ++ e]; pure opts
    if let some c := comms then
      match ← Guard.guard (ensureComms c terms) with
      | .ok h => opts := { opts with commsHold := h }
      | .error e => errs := errs ++ [pre ++ "comms: " ++ e]; opts := { opts with commsHold := none }
    let away := (away (← Store.txn [.«meta»] fun db => (db, db))).isSome
    if let some ts := terms then
      if !ts.isEmpty then errs ← pass errs (pre ++ "hc blocked: ") (hcBlocked ts t comms away)
    if let some c := comms then errs ← pass errs (pre ++ "notices: ") (notices c away)
    return (errs, opts)
  let some c := comms | return errs
  Scoped.within hs do
    let mut errs := errs
    errs ← pass errs (pre ++ "lifecycle: ") (lifecycle t c terms opts)
    errs ← pass errs (pre ++ "quiet: ") (quiet t c)
    errs ← pass errs (pre ++ "hung: ") (hung t c terms opts.interval)
    errs ← pass errs (pre ++ "comms inbox: ") (commsInbox t c terms)
    errs ← pass errs (pre ++ "blockers: ") (blockers t c opts.blockerIdle)
    errs ← pass errs (pre ++ "landing-late: ") (landingLate t c)
    if let some ts := terms then
      errs ← pass errs (pre ++ "compact: ") (compactPass ts c)
      errs ← pass errs (pre ++ "api-error: ") (apiErrorPass ts c)
    return errs

/-- One repo's passes (sw-global §4, per repo), in its folder and its own scope with every swarm's agents in view: the
trial-merge conflicts among the agents with a worktree here, its locks, the sweep, and with a swarm's `ci` knob on CI
and PR polling for its base. What it says goes to the communicator of the first swarm staffing from it. The sweep's
"not landed" cache before and after, and the errors. -/
def repoTick (p : Plan) (r : String) (notLanded : List String) (t : Int) : m (List String × List String) := do
  let staff := p.staff.filter (·.1 == r)
  let comms := (staff.filterMap (·.2.2.1)).head?.orElse fun _ =>
    (p.agents.filter (·.2.2 == r)).findSome? fun a => (p.swarms.find? (·.name == a.2.1)).bind (·.comms)
  let pre := s!"{r}: "
  Scoped.within { swarm := "", repo := r, every := true } do
    let conflictPass : m Unit := do  -- a bad conflict pass never stops the tick
      let db ← Store.txn [.agent, .workspace] fun db => (db, db)
      let all ← Workspaces.worktrees
      let rs ← (Workspaces.wtMapOf db all).mapM fun (n, w) => do pure (n, w, ← real w)
      let here := (rs.filter fun (_, _, r) => all.any (·.1 == r)).map fun (n, w, _) => (n, w)
      Conflict.conflictTick r here (Bases.baseFor · none) t
    if let .error e ← Guard.guard conflictPass then Env.err s!"conflict: {e}"
    let mut errs : List String := []
    errs ← pass errs (pre ++ "locks: ") (discard <| reapLocks t)
    let mut nl := notLanded
    match ← Guard.guard (repoSweep comms notLanded) with
    | .ok x => nl := x
    | .error e => errs := errs ++ [pre ++ "sweep: " ++ e]
    if staff.any (·.2.2.2) then
      errs ← pass errs (pre ++ "ci_poll: ") (Ci.ciPoll (some r))
      errs ← pass errs (pre ++ "ci_check: ") (Ci.ciCheck (some r) comms)
      errs ← pass errs (pre ++ "pr_ci: ") (Ci.prCi (some r))
      errs ← pass errs (pre ++ "pr_watch: ") (Ci.prWatch (some r))
    return (nl, errs)

/-- How old `swarm.db.bak` may get before watchd makes it again (s). -/
def BACKUP_EVERY : Int := 3600

/-- The backup (sw-global §4): once `swarm.db.bak` is BACKUP_EVERY old, `VACUUM INTO` `swarm.db.tmp` beside the db,
renamed over it. One copy. -/
def backup (t : Int) : m Unit := do
  let db ← Swarms.dbPath
  let bak := db ++ ".bak"
  if let some mt ← Sys.mtime bak then if t - mt < BACKUP_EVERY then return
  let tmp := db ++ ".tmp"
  discard <| Sys.remove tmp
  discard <| Sys.sqlAt db "" [("vacuum into ?", [.text tmp])] true
  match ← Proc.output ["mv", "-f", tmp, bak] none [] with
  | some o => if o.code != 0 then die s!"backup: mv: {strip o.stderr}"
  | none => die "backup: mv did not start"

/-- The machine's scope: its own meta keys and events (and every swarm's job events), every swarm's agents. -/
def machineScope : Scope := { swarm := "", repo := "", every := true }

/-- One tick (sw-global §4): each live swarm's passes, each repo's, then the machine's (pressure, oom bias, orphans,
remote machines and jobs, the backup); each pass under its own guard, an error ending its pass alone; the errors
joined, or none (watchd.watchd_tick). -/
def tick (opts : Opts) (st : St) : m (St × Option String) := do
  let mut errs : List String := []
  let mut st := st
  let terms ← hcTerminals
  let t ← Clock.now
  let p ← match ← Guard.guard plan with
    | .ok p => pure p
    | .error e => errs := errs ++ ["plan: " ++ e]; pure {}
  for sw in p.swarms do
    match ← Guard.guard (swarmTick p sw terms opts t) with
    | .ok e => errs := errs ++ e
    | .error e => errs := errs ++ [s!"{sw.name}: {e}"]
  for r in p.repos do
    match ← Guard.guard (repoTick p r st.notLanded t) with
    | .ok (nl, e) => st := { st with notLanded := nl }; errs := errs ++ e
    | .error e => errs := errs ++ [s!"{r}: {e}"]
  Scoped.within machineScope do
    let mut errs := errs
    let mut st := st
    match ← Guard.guard (machineTick st.cost) with
    | .ok c => st := { st with cost := c }
    | .error e => errs := errs ++ ["machine: " ++ e]
    errs ← pass errs "remote: " (Run.remoteTick t)
    errs ← pass errs "gone: " (Run.goneTick t none (t % 300 < opts.interval))
    errs ← pass errs "detached: " (Run.detachedTick t)
    errs ← pass errs "backup: " (backup t)
    return (st, if errs.isEmpty then none else some ("; ".intercalate errs))

/-- An error out of a tick: to stderr, and logged and told to every live swarm's communicator once per distinct message
(watchd.tick_failed). -/
def tickFailed (msg : String) (st : St) : m St := do
  Env.err s!"watchd tick: {msg}"
  if st.lastErr == some msg then return st
  let cs := (← Swarms.list).filterMap fun sw => if sw.ended.isNone then sw.comms else none
  let now ← Clock.now
  Store.txn [] fun db =>
    let db := db.log now (some "swarm") "watchd-tick-error" none (some msg)
    (cs.foldl (fun db c => say db now c ("watchd tick failed (it carries on): " ++ msg) false "system") db, ())
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
def watchdPass (mine : String) (opts : Opts) (up : Bool) (st : St) :
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
  let (st, err) ← match ← Guard.guard (tick opts st) with
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
def loop (mine : String) (opts : Opts) : m (Option String) := do
  let mut up := false
  let mut st : St := {}
  repeat
    let (up', why, st', err) ← match ← Guard.guard (watchdPass mine opts up st) with
      | .ok r => pure r
      | .error e => pure (up, none, st, some e)
    up := up'; st := st'
    if let some e := err then
      match ← Guard.guard (tickFailed e st) with
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
  let o ← Sys.exec argv { env := [("SWARM_DB", some (← Spawn.dbPath)), ("SWARM", none), ("SWARM_NAME", none)] }
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
    if alive then discard <| Proc.output ["kill", "-TERM", (words s).headD ""] none []  -- kill-site: the watchd it displaced
    if let some o := old then
      Store.txn [.«meta»] fun db => (if (db.getMeta "watchd").bind (·.v) == some s then db.setMeta "watchd" (some o) else db, ())
    fail s!"the new watchd ({s}) {if alive then "did not finish a tick" else "died before its first tick"}"
  fail s!"no new watchd took over within {(Float.floor wait).toInt64.toInt} s"
  return 1

/-- The swarm knobs given on the command line, set on the swarm this process acts on (it must resolve one): `--comms`
(the communicator, a stayer), `--max-agents` (`agent_min`, else the live roster when it has none), `--ci` (meta `ci`),
`--model` and `--effort` (meta `spawn_model`, `spawn_effort`). Nothing when none is given. -/
def setKnobs (a : Parsed) : m Unit := do
  let comms := py (a.str "comms")
  if comms.isNone && (a.int "max_agents").isNone && !a.flag "ci" && (a.str "model").isNone && (a.str "effort").isNone then
    return
  let now ← Clock.now
  let envComms ← env "SWARM_COMMS"
  Store.txn [.«meta», .agent] fun db =>
    let db := match comms with  -- the communicator is a stayer; meta.comms is only where watchd sends what needs the human
      | some c =>
        let db := db.setMeta "comms" (some c)
        if (db.agent c).any fun x => x.ended.isNone && x.stay.isNone then
          (db.setAgent c ({ · with stay := some "the user's channel" })).log now (some c) "stay" none (some "the user's channel")
        else db
      | none => db
    let (n, mn, _) := limits db envComms
    let db := match a.int "max_agents", mn with
      | some x, _ => db.setMeta "agent_min" (some (d x))
      | none, none => db.setMeta "agent_min" (some (toString n))
      | none, some _ => db
    let db := if a.flag "ci" then db.setMeta "ci" (some "on") else db
    let db := match a.str "model" with | some x => db.setMeta "spawn_model" (some x) | none => db
    (match a.str "effort" with | some x => db.setMeta "spawn_effort" (some x) | none => db, ())

/-- The repo scope of the working directory, every swarm's agents in view (the sweep's and `worktrees prune`'s). -/
def repoScope : m Scope := return { swarm := "", repo := (← Workspaces.main none).getD "", every := true }

/-- The machine's one watchd (sw-global §4), its record in meta scope `''`: refused while another lives (unless
`--takeover`), then the loop. -/
def serve (a : Parsed) : m UInt32 := do
  let mine := s!"{← Sys.getpid} {(← env "HC_TERMINAL_ID").getD "-"}"  -- the watchd record
  let old := ((← Store.txn [.«meta»] fun db => (db, db)).getMeta "watchd").bind (·.v)
  let oldAlive ← match old with | some o => recAlive o | none => pure false
  let once := a.flag "once"
  let run := Json.encode (Lean.Json.mkObj [("cwd", .str (← Env.cwd)),
    ("flags", .arr (flags a |>.map Lean.Json.str |>.toArray)), ("started", Json.int (← Clock.now))])
  let refused ← Store.txn [.«meta»] fun db =>
    let o := (db.getMeta "watchd").bind (·.v)
    -- the pid was checked outside: a record changed since counts as alive
    if o.isSome && o != some mine && (o != old || oldAlive) && !a.flag "takeover" then (db, o) else
    let db := db.setMeta "watchd" (some mine)
    (if once then db else db.setMeta "watchd_run" (some run), none)  -- what --restart starts again
  if let some o := refused then
    let ws := words o
    die s!"watchd already runs (pid {ws.headD ""}, terminal {(ws[1]?).getD ""}); `swarm watchd --takeover` replaces it."
  Sock.checkAll  -- a recorded inbox socket that no longer connects falls back to hc send, comms told
  let num (k dflt : String) : Float := (parseFloat (strip ((a.str k).getD dflt))).getD 0
  let opts : Opts := { minFreeGib := num "min_free_mem" "4", interval := (a.int "interval").getD 30, once,
                       blockerIdle := num "blocker_idle" "25" }
  let pid ← Sys.getpid
  let why ← loop mine opts
  if let some why := why then die s!"watchd (pid {pid}){why}; exiting"
  return 0

/-- `swarm watchd [...]` (watchd.cmd_watchd). -/
def watchd (a : Parsed) : m UInt32 := do
  if a.flag "dry_run" then
    let (out, _) ← Scoped.within (← repoScope) do sweep none true [] none (some (← madeHere))
    for (wt, br, mb) in out do Env.out s!"{wt}\t{br.getD "None"}\t{mb} MB"
    return 0
  setKnobs a
  if a.flag "restart" then return ← Scoped.within machineScope (restart (given a))
  Scoped.within machineScope (serve a)

/-- `swarm worktrees prune [--apply] [--dir <dir>]`: the sweep's gate and removal on every worktree under `dir`
(default `.worktrees` of the main checkout), whether or not an agent owns it; a dry run unless `--apply`. -/
def prune (a : Parsed) : m UInt32 := do
  let some main ← Workspaces.main none | die "not in a git repository"
  let dir ← real ((a.str "dir").getD (main ++ "/.worktrees"))
  let go := a.flag "apply"
  let (reasons, gone) ← Scoped.within (← repoScope) do
    let reasons ← keepReasons dir
    let (gone, _) ← sweep none (!go) [] (some dir)
    return (reasons, gone)
  for (wt, br, why) in reasons do
    let b := br.getD "None"
    if gone.any (·.1 == wt) then Env.out s!"{if go then "removed" else "would remove"}: {wt} [{b}]"
    else Env.out s!"keep ({if why == "landed" then "git would not remove it" else why}): {wt} [{b}]"
  return 0

/-- The group. -/
def group : Group m where
  specs := [("watchd", watchdSpec), ("worktrees", worktreesSpec)]
  run a := if a.cmd == "worktrees" then prune a else watchd a

end SwarmLean.Cmd.Watchd
