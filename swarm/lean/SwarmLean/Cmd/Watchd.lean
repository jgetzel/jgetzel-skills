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

/-- What `ensureComms` reads: its knobs, the communicator's row, and what `Queue.staffing` reads. -/
def ensureCommsReads (comms : String) : Txn Db := do
  let ps ← TaskTxn.poolSels
  Txn.slice (ps ++ [Sels.agent comms, Sels.metas ["comms_hc", "comms_backoff", "queue_only"]])

/-- A swarm whose communicator joined from a Herdr terminal gets one launched and bound when its bound terminal is gone
(not `commsPresent`) and the swarm has work it can start (`Queue.staffing` of its repos: a held task is none, board
#67). A live
binding is never moved: only `swarm join --takeover` moves one. Why it can't, for the board's auto-spawn line, or none
(watchd.ensure_comms). `t` is the tick's. -/
def ensureComms (comms : String) (terms : Option (List Term)) (t : Int) : m (Option String) := do
  let db ← Store.run (ensureCommsReads comms)
  -- only a swarm whose communicator joined from a Herdr terminal (`join` records it) gets one launched
  if ((db.getMeta "comms_hc").bind (·.v)).isNone then return none
  let some sw ← env "SWARM" | return none
  let some terms := terms | return none
  if commsPresent (db.agent comms) terms then return none
  let mine ← Swarms.staffable sw  -- work of its repos (sw-global §2), as auto-spawn staffs it
  if !(Queue.staffing db).any (mine.contains ·.id) then return none
  if let some bo := (db.getMeta "comms_backoff").bind (·.v) then
    if t < (parseInt bo).getD 0 then return some "no communicator can be launched (last launch failed)"
  let brief := s!"You are the communicator of swarm {sw} (your name: {comms}), started by watchd because the swarm had " ++
    "work it could start and its communicator's terminal was gone. Load the swarm skill, run `swarm board` and `swarm read`, and carry on as the communicator."
  let model := match db.agent comms with
    | some a => a.model.getD "opus"
    | none => "opus"
  let cwd ← Env.cwd
  let (out, err) ← Spawn.launchAgent comms brief model none (some cwd) true
  let some out := out | do
    Store.run (Txn.update [Sels.metas ["comms_backoff"]] [] fun db => (db.setMeta "comms_backoff" (some (d (t + 300))), ()))
    return some ("no communicator can be launched: " ++ err)
  let addr := (splitlines (strip out)).getLastD ""
  -- a `join` while it launched bound the row to a live terminal: that binding stays
  let r ← Store.view [Sels.agent comms] (·.agent comms)
  if commsPresent r ((← hcTerminals).getD []) then return none
  Cmd.Agents.bindAgent comms (some cwd) (some addr) none false
  discard <| Proc.output ["hc", "label", addr, "swarm=" ++ sw] none []
  Store.run (Txn.update [Sels.metas ["comms_backoff"]] [] fun db =>
    ((delMeta db "comms_backoff").log t (some comms) "comms-launch" none (some addr), ()))
  return none

/-- The user is away: a question waits for them. -/
def AWAY : String := " The user is away: answer it if it is yours to decide; else it waits for them."

/-- Runs a pass's acts in order: the only place a pass sends or kills a terminal (sw-architecture-review §4 B1). -/
def runActs (acts : List Act) : m Unit := do
  let go (n h : String) (mark : Txn Unit) (once : Once) (send : m (Option String)) : m Unit := do
    if once == Once.atMost then Store.run mark
    match ← send with
    | some e => Env.err s!"{n}: hc send {h} failed: {e}"
    | none => if once == Once.atLeast then Store.run mark
  for x in acts do
    match x with
    | .send n h text mark once => go n h mark once (Msgs.deliverTo n h text)
    | .type n h text mark once => go n h mark once (Msgs.typeLine h text)
    | .endAgent a after => if ← Lifecycle.endAgent a false none then Store.run after
    | .kill h =>
      discard <| Proc.output ["hc", "kill", h] none []
      discard <| Proc.output ["hc", "rm", h] none []
    | .err line => Env.err line

/-- The names of the scope's live agents, read once before a per-agent pass. -/
def liveNames : m (List String) := Store.view [Sels.live] fun db => (Agents.live db).map (·.name)

/-- Agent `n`'s spawn events. -/
def spawnSel (n : String) : Sel := { table := .event, cond := .and (.eq "kind" (.text "spawn")) (.eq "data" (.text n)) }

/-- What `hcBlockedStep` reads of agent `n`: its row, its tasks and its spawn events. -/
def hcBlockedSels (n : String) : List Sel := [Sels.agent n, Sels.owned n, spawnSel n]

/-- `hcBlocked` on live agent `n`'s rows, its terminal found in `terms`: a prompt there (or no session long after its
spawn) blocks the row, its first claimed task (on HC_Q) and tells comms; the prompt gone, the task HC_Q blocked is
given back and a row this pass blocked follows the terminal again. -/
def hcBlockedStep (terms : List Term) (t : Int) (comms : Option String) (away : Bool) (n : String) (db : Db) : Db :=
  Id.run do
  let some a := db.agent n | return db
  if a.ended.isSome then return db
  let some x := a.hc.bind (fun h => terms.find? (·.address == some h)) | return db
  -- no agent in it yet, long after its spawn: a dialog before the session (folder trust)
  let spawned := (db.events.filter fun e => e.kind == some "spawn" && e.data == some n).filterMap (·.ts)
  let nostart := x.status.isNone && spawned.any (t - · >= START_WAIT)
  if x.status != some "blocked" && !nostart then  -- the prompt is gone: give back the claim hc blocked
    let back (r : Task) : Task :=
      if r.owner == some n && r.status == .blocked && r.question == some HC_Q then
        { r with state := r.state.unblock (t + Tasks.LEASE) } else r
    -- the row this pass blocked follows the terminal again (board #135: a session started there later)
    let st : AgentStatus := if x.status == some "working" then .working else .idle
    let db := { db with tasks := db.tasks.map back }
    return if a.status == some .blocked then (db.setAgent n ({ · with status := some st })).log t (some n) "status" none (some st.text) else db
  if a.status == some .blocked then return db
  let db := (db.setAgent n ({ · with status := some .blocked })).log t (some n) "blocked" none none
  let db := match ((db.tasks.filter fun r => r.owner == some n && r.status = .claimed).mergeSort (·.id ≤ ·.id)).head? with
    | some r =>  -- the agent notice below is the single notice; the task notice is marked sent
      (db.set r.id fun x => { x with state := x.state.block HC_Q }).log t (some n) "task-blocked" (some (d r.id)) (some HC_Q)
    | none => db
  match comms with  -- while the user is away the question queues: not urgent
  | some c =>
    let hint := if nostart then
      s!" Its terminal {a.hc.getD ""} has no Claude session yet (a folder-trust prompt?): `hc read {a.hc.getD ""}`." else ""
    say db t (.agent c) (n ++ " is blocked (a prompt or question needs the human)." ++ hint ++ (if away then AWAY else "")) (!away) "system"
  | none => db

/-- An hc terminal's prompt blocks its agent (blocked, the claim marked, comms told); gone, the claim given back. One
transaction per live agent bound to one of `terms`. -/
def hcBlocked (terms : List Term) (t : Int) (comms : Option String) (away : Bool) : m Unit := do
  for n in ← liveNames do
    Store.run (Txn.update (hcBlockedSels n) [.msg] fun db => (hcBlockedStep terms t comms away n db, ()))

/-- How long a continue line may go unanswered (no turn) before it is sent once more. -/
def RESUME_WAIT : Int := 5 * 60

/-- A continue line's text when the stop hook has no verdict (a stayer, the communicator: a declared wait). -/
def CARRY_ON : String := "Carry on with what your keep note says is next."

/-- Agent `n`'s last event of kind `k`. -/
def lastOf (db : Db) (n k : String) : Option Event :=
  (db.events.filter fun e => e.agent == some n && e.kind == some k).getLast?

/-- What `compactStep` reads of agent `n`: its row, tasks and worktrees (its `/compact` line), the thresholds and its
state, and its last event of each kind it decides on. -/
def compactSels (n : String) : List Sel :=
  [Sels.agent n, Sels.owned n, Sels.workspaces n,
   Sels.metas ["ctx_nudge", "ctx_compact", "compact_stayers", Compact.key n]] ++
  (["ctx-continue", "ctx-resent", "compact", "stay", "stay-end"].map (Sels.lastEv n ·))

/-- What watchd read before `compactStep`'s transaction: the stop hook's verdict for a continue line
(`Hook.stopBlock`), the `/compact` line (`Msgs.compactLine`); each only when the step on a first read wanted it. -/
structure CompactIn where
  why : Option String := none
  line : Option String := none

/-- The `ctx-compact` mark of a `/compact` typed at context `k`: logged, and `n`'s state `s` saved. -/
def compactMark (t : Int) (n : String) (k : Int) (s : Compact.St) : Txn Unit :=
  Txn.update [Sels.metas [Compact.key n]] [] fun db =>
    (Compact.save (db.log t (some n) "ctx-compact" none (some (d k))) n s, ())

/-- `compactPass` on live agent `n`'s rows (`compactSels`), its terminal found in `terms`: a continue line unanswered
RESUME_WAIT sent again (comms told), a stay set before a compaction ended with it, the continue line once a
compaction ended, then `Compact.step`'s act. The sends, each after its mark (at most once) but the `/compact`, marked
once typed. -/
def compactStep (t : Int) (comms : String) (terms : List Term) (g : CompactIn) (n : String) (db0 : Db) :
    Db × List Act := Id.run do
  let some a := db0.agent n | return (db0, [])
  if a.ended.isSome then return (db0, [])
  let some h := py a.hc | return (db0, [])
  let some x := terms.find? (·.address == some h) | return (db0, [])
  let task := ((db0.tasks.filter fun r => r.owner == some n && (r.status = .claimed || r.status = .blocked)).mergeSort
    (·.id ≤ ·.id)).head?
  let stays := n == comms || a.stay.isSome
  let ev (k : String) := (lastOf db0 n k).bind (·.ts)
  let evId (k : String) := (lastOf db0 n k).map (·.id)
  let la := a.last_active.getD 0
  let idle := Compact.Term.ofHc x.status == .idle
  let cont := "Compaction done. " ++ g.why.getD CARRY_ON
  let mut db := db0
  let mut acts : List Act := []
  -- a continue line nobody answered in RESUME_WAIT (no turn since): sent once more and the communicator told, once
  if idle then
    if let (some cid, some ct) := (evId "ctx-continue", ev "ctx-continue") then
      if t - ct ≥ RESUME_WAIT && la ≤ ct && (evId "ctx-resent").all (· < cid) then
        db := (say db t (.agent comms) s!"{n} did not resume after its compaction (terminal {h})." false "system").log t
          (some n) "ctx-resent" none none
        acts := acts ++ [Act.marked n h cont]
  -- a compaction ended (the hook's `compact` event, then the continue line or the agent's first turn) and the stay
  -- was set before it: the stay ends
  let mut stayNote := ""
  if let (some s, some cid) := (a.stay, evId "compact") then
    let ended := db0.events.any fun e => e.agent == some n && e.id > cid && (e.kind == some "stay" || e.kind == some "stay-end")
    let t0 := (ev "compact").getD 0
    let willSend := idle && (evId "ctx-continue").all (· < cid) && la ≤ t0
    let done := (evId "ctx-continue").any (· > cid) || la > t0 || willSend
    if !ended && done then
      db := (db.setAgent n ({ · with stay := none })).log t (some n) "stay-end" (some s) (some "compaction")
      stayNote := s!" Your stay '{s}' ended with the compaction; `swarm stay \"<why>\"` again if it still holds."
      if !willSend then db := say db t (.agent n) stayNote.trimAscii.toString false "system"
  if !stays && task.isNone then return (db, acts)  -- holds nothing: watchd ends it soon
  -- a compaction has ended (the hook logged "compact") and nothing woke the agent since: send it the stop hook's
  -- verdict as a prompt, once; a hook cannot start a turn itself
  if idle then
    if let some t0 := ev "compact" then
      if (ev "ctx-continue").all (· < t0) && la ≤ t0 then
        return (db.log t (some n) "ctx-continue" none none, acts ++ [Act.marked n h (cont ++ stayNote)])
  let k := a.ctx_tokens.getD 0
  let cAt := Compact.compactAt db0
  let force := Compact.stayersToo db0 || !stays
  let s0 := Compact.load db0 n
  let (act, s) := Compact.step k (Compact.nudgeAt db0) cAt force (Compact.Term.ofHc x.status) s0
  let save (db : Db) : Db := if s != s0 then Compact.save db n s else db
  match act with
  | .nothing => return (save db, acts)
  | .nudge =>
    return (save ((say db t (.agent n) (Compact.nudgeText k cAt (task.map (·.id)) force) false "system").log t (some n)
      "ctx-nudge" none (some (d k))), acts)
  | .compact =>  -- the state saved only once it is typed: a failed send compacts again next tick
    match g.line with
    | some l => return (db, acts ++ [.type n h l (compactMark t n k s) .atLeast])
    | none => return (db, acts)
  | .failed =>
    return (save ((say db t (.agent comms) (Compact.failedText n k cAt h) false "system").log t (some n)
      "ctx-compact-failed" none (some (d k))), acts)

/-- Context compaction (board #136): each live agent holding work (a task, a stay, the communicator's role) gets
`Compact.step`'s act; the state is kept in meta `ctx:<name>` and only once the act is carried out. Per agent: a first
read says what the step will send, the stop hook's verdict and the `/compact` line are read for that alone, then the
step runs in one transaction on the rows read again. -/
def compactPass (t : Int) (terms : List Term) (comms : String) : m Unit := do
  for n in ← liveNames do
    let db ← Store.view (compactSels n) id
    let some a := db.agent n | continue
    let (_, want) := compactStep t comms terms { line := some "" } n db
    let why ← if want.any (fun | .send .. => true | _ => false) then Hook.stopBlock n (Lean.Json.mkObj []) else pure none
    let line ← if want.any (fun | .type .. => true | _ => false) then some <$> Msgs.compactLine db a none else pure none
    runActs (← Store.run (Txn.update (compactSels n) [.msg] fun db => compactStep t comms terms { why, line } n db))

/-- A terminal idle this long with the agent's hooks silent and its transcript ending on an API error: the stop hook never ran. -/
def APIERR_IDLE : Int := 2 * 60

/-- How long a continue line after an API error may go unanswered before the communicator is told. -/
def APIERR_WAIT : Int := 5 * 60

/-- What `apiErrorStep` reads of agent `n`: its row, its tasks, its last `api-error`, `api-resume` and `api-noresume`. -/
def apiErrorSels (n : String) : List Sel :=
  [Sels.agent n, Sels.owned n] ++ (["api-error", "api-resume", "api-noresume"].map (Sels.lastEv n ·))

/-- Whether agent row `a`'s turn may have ended on an API error the hooks missed: "working", its terminal `x` idle,
silent APIERR_IDLE. -/
def apiSilent (t : Int) (a : Agent) (x : Term) : Bool :=
  a.status == some .working && Compact.Term.ofHc x.status == .idle && t - a.last_active.getD 0 ≥ APIERR_IDLE

/-- `apiErrorPass` on live agent `n`'s rows (`apiErrorSels`), its terminal found in `terms`; `err`: the API error its
transcript ends on, read when it was `apiSilent`. -/
def apiErrorStep (t : Int) (comms : String) (terms : List Term) (err : Option String) (n : String) (db0 : Db) :
    Db × List Act := Id.run do
  let some a := db0.agent n | return (db0, [])
  if a.ended.isSome then return (db0, [])
  let some h := py a.hc | return (db0, [])
  let some x := terms.find? (·.address == some h) | return (db0, [])
  let db := match err with
    | some txt => if apiSilent t a x then
        (db0.setAgent n ({ · with status := some .idle })).log t (some n) "api-error" none (some txt) else db0
    | none => db0
  let some e := lastOf db n "api-error" | return (db, [])
  if a.last_active.getD 0 > e.ts.getD 0 then return (db, [])  -- a turn since: re-armed
  if Compact.Term.ofHc x.status != .idle then return (db, [])
  match (lastOf db n "api-resume").filter (·.id > e.id) with
  | none =>
    let txt := e.data.getD ""
    if n == comms then
      return ((say db t (.agent comms) s!"Your last turn ended on an API error ({txt}); nothing woke it. Go on from where you were." false "system").log t
        (some n) "api-resume" none none, [])
    let task := ((db.tasks.filter fun r => r.owner == some n && (r.status = .claimed || r.status = .blocked)).mergeSort
      (·.id ≤ ·.id)).head?
    let line := s!"Your last turn ended on an API error ({txt}). Go on from where you were" ++
      (match task with | some r => s!": task #{r.id}." | none => ".")
    return (db.log t (some n) "api-resume" none none, [Act.marked n h line])
  | some s =>
    if t - s.ts.getD 0 ≥ APIERR_WAIT && n != comms && (lastOf db n "api-noresume").all (·.id < e.id) then
      return ((say db t (.agent comms) s!"{n} did not resume after an API error (terminal {h})." false "system").log t
        (some n) "api-noresume" none none, [])
    return (db, [])

/-- A turn that ended on an API error (board #194). The StopFailure hook logs `api-error`; failing that, a row still
"working" whose terminal hc shows idle/done, silent APIERR_IDLE, with a transcript ending on one gets it logged here and
its status set idle. Per `api-error` event, once: the agent gets a continue line typed into its terminal (the
communicator is only told); no turn APIERR_WAIT later, the communicator is told, once. A later turn re-arms it. The
transcripts are read first, then one transaction per agent. -/
def apiErrorPass (t : Int) (terms : List Term) (comms : String) : m Unit := do
  let rows ← Store.view [Sels.live, Sels.metaPre "tr:"] fun db =>
    (Agents.live db).map fun a => (a, (db.getMeta ("tr:" ++ a.name)).bind (·.v))
  for (a, tr) in rows do
    let some h := py a.hc | continue
    let some x := terms.find? (·.address == some h) | continue
    let err ← if apiSilent t a x then SwarmLean.Hook.errorText tr else pure none
    -- the next event id: the step reads the id of an `api-error` it logs
    runActs (← Store.run (Txn.update (apiErrorSels a.name) [.msg, .event] (apiErrorStep t comms terms err a.name)))

/-- How old the communicator's oldest waking unread message is before watchd types its inbox in (`commsInbox`): a
burst within it goes in one block. -/
def COMMS_SETTLE : Int := 20

/-- What `commsInboxStep` reads besides the communicator's inbox: its row, the live agents, its compaction events. -/
def commsSels (comms : String) : List Sel :=
  let kinds : Cond := .oneOf "kind" [.text "compact-asked", .text "ctx-compact", .text "ctx-continue", .text "compact"]
  [Sels.agent comms, Sels.live, { table := .event, cond := .and (.eq "agent" (.text comms)) kinds }]

/-- What `commsInbox` sends: its terminal, the unread rows that fit and how many more stay unread. -/
structure InboxSend where
  hc : String
  fit : List Msg
  more : Nat

/-- `commsInbox`'s decision on the communicator's rows (`commsSels` and its inbox); `waiter`: the waiter pid read
before and whether it lived (a waiter since then counts as alive). -/
def commsInboxStep (t : Int) (comms : String) (terms : Option (List Term)) (waiter : Option Int × Bool) (db : Db) :
    Option InboxSend := do
  let a ← db.agent comms
  guard a.ended.isNone
  let h ← py a.hc
  let x ← terms.bind (·.find? fun x => x.address == some h && x.state == some "live")
  let st := Compact.Term.ofHc x.status
  guard (st == .idle || st == .working)
  guard !(Compact.compacting db.events comms (a.last_active.getD 0) t)
  guard !(a.waiter.isSome && (a.waiter != waiter.1 || waiter.2))  -- a live waiter delivers itself
  let rows := Msgs.unread db comms
  let urg (r : Msg) : Bool := r.urgent.getD 0 != 0
  let wake := rows.filter fun r => r.kind != some "notice" || urg r
  let oldest ← wake.head?
  guard !((Agents.live db).all (·.name == comms) && !wake.any urg)
  guard (t - oldest.ts.getD t ≥ COMMS_SETTLE)
  let fit := Msgs.linesFit Msgs.TYPE_LINES rows
  guard !fit.isEmpty
  pure { hc := h, fit, more := rows.length - fit.length }

/-- `commsInboxStep` on the communicator's inbox and `commsSels`, read in one transaction. -/
def commsInboxTxn (t : Int) (comms : String) (terms : Option (List Term)) (waiter : Option Int × Bool) :
    Txn (Option InboxSend) := do
  let db ← Msgs.inboxTxn comms (commsSels comms)
  pure (commsInboxStep t comms terms waiter db)

/-- The mark once `commsInbox` sent through id `last`: those rows read (none a `swarm read` since passed), and the
`comms-deliver` event. -/
def commsMark (t : Int) (comms : String) (last : Nat) : Txn Unit := do
  discard <| Msgs.takeTxn comms (Msgs.upTo last)
  Txn.exec [logStmt t (some comms) "comms-deliver" none (some (d last))]

/-- The communicator's inbox (board #210). It has no hooks, so with no live waiter watchd sends its unread messages
(`Msgs.deliverTo`: its inbox socket, else typed into its terminal, board #215): `swarm read`'s lines under the peer
head, at most `Msgs.TYPE_LINES` (then "N more"), once a waking one (not a plain notice) is COMMS_SETTLE old. They are
marked read only once sent (event `comms-deliver`, data the last id). Only while hc shows the terminal idle or working (Claude Code queues it to the turn's end): never
into a prompt, which it could answer (hc send refuses a blocked one too). None while it compacts (compactPass sends
its continue line); while no other agent lives, only for an urgent message: the terminal may hold a session doing
other work. A live waiter delivers itself. The waiter's pid is asked first, then one transaction decides. -/
def commsInbox (t : Int) (comms : String) (terms : Option (List Term)) : m Unit := do
  let w ← Store.view [Sels.agent comms] fun db => (db.agent comms).bind (·.waiter)
  let alive ← match w with | some p => Sys.pidAlive p | none => pure false
  let some s ← Store.run (commsInboxTxn t comms terms (w, alive)) | return
  let some last := s.fit.getLast? | return
  let hh ← s.fit.mapM fun r => Clock.hhmm (r.ts.getD t)
  runActs [.send comms s.hc (Msgs.typedNote hh s.fit s.more) (commsMark t comms last.id) .atLeast]

/-- Each blocked task of the swarm's agents (`ofSwarm`, board #135) has its question told to comms once per block: a
task-blocked event after its latest `task block`. -/
def noticesStep (t : Int) (comms : String) (away : Bool) (db0 : Db) : Db :=
  (db0.tasks.filter fun r => r.status = .blocked && ofSwarm db0 r).foldl (fun db r =>
    -- the latest of the task's question events (model Model.lean, toldAfter): the same question asked again is new
    let e := (db.events.filter fun e =>
      (e.kind == some "block" && e.data.any fun x => x == "#" ++ d r.id || likePrefix x ("#" ++ d r.id ++ " ")) ||
      (e.kind == some "task-blocked" && e.path == some (d r.id))).getLast?
    if e.any (·.kind == some "task-blocked") then db else
    -- the event marks it told: never without its message
    let db := db.log t r.owner "task-blocked" (some (d r.id)) r.question
    say db t (.agent comms) (s!"{r.owner.getD "None"} is blocked on #{d r.id} ({r.title.getD "nil"}): {r.question.getD "None"} " ++
      s!"Answer with `swarm task unblock {d r.id} --answer \"...\"`." ++ (if away then AWAY else "")) (!away) "system") db0

/-- What `noticesStep` reads: the blocked tasks, the swarm's agents and the `block` and `task-blocked` events. -/
def noticeSels : List Sel :=
  [{ table := .task, cond := .eq "state" (.text "blocked") }, Sels.all .agent,
   { table := .event, cond := .oneOf "kind" [.text "block", .text "task-blocked"] }]

/-- The blocked notices in one transaction. -/
def notices (t : Int) (comms : String) (away : Bool) : m Unit :=
  Store.run (Txn.update noticeSels [.msg] fun d => (noticesStep t comms away d, ()))

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
def knobs (opts : Opts) : m Opts :=
  Store.view [Sels.metas ["spawn_model", "spawn_effort"]] fun db =>
    let k (key : String) : Option String := py ((db.getMeta key).bind (·.v))
    { opts with model := (k "spawn_model").orElse fun _ => opts.model, effort := (k "spawn_effort").orElse fun _ => opts.effort }

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
    errs ← pass errs (pre ++ "reap: ") (do runActs (← reap live t comms foreign home).2)
    let mut opts ← match ← Guard.guard (knobs opts) with
      | .ok o => pure o
      | .error e => errs := errs ++ [pre ++ "knobs: " ++ e]; pure opts
    if let some c := comms then
      match ← Guard.guard (ensureComms c terms t) with
      | .ok h => opts := { opts with commsHold := h }
      | .error e => errs := errs ++ [pre ++ "comms: " ++ e]; opts := { opts with commsHold := none }
    let away ← Store.view [Sels.metas ["away"]] fun db => (away db).isSome
    if let some ts := terms then
      if !ts.isEmpty then errs ← pass errs (pre ++ "hc blocked: ") (hcBlocked ts t comms away)
    if let some c := comms then errs ← pass errs (pre ++ "notices: ") (notices t c away)
    return (errs, opts)
  let some c := comms | return errs
  Scoped.within hs do
    let mut errs := errs
    errs ← pass errs (pre ++ "lifecycle: ") (lifecycle t c terms opts runActs)
    errs ← pass errs (pre ++ "quiet: ") (quiet t c)
    errs ← pass errs (pre ++ "hung: ") (hung t c terms opts.interval)
    errs ← pass errs (pre ++ "comms inbox: ") (commsInbox t c terms)
    errs ← pass errs (pre ++ "blockers: ") (blockers t c opts.blockerIdle)
    errs ← pass errs (pre ++ "landing-late: ") (landingLate t c)
    if let some ts := terms then
      errs ← pass errs (pre ++ "compact: ") (compactPass t ts c)
      errs ← pass errs (pre ++ "api-error: ") (apiErrorPass t ts c)
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
      let db ← Store.view [Sels.live, Sels.all .workspace] id
      let all ← Workspaces.worktrees
      let rs ← (Workspaces.wtMapOf db all).mapM fun (n, w) => do pure (n, w, ← real w)
      let here := (rs.filter fun (_, _, r) => all.any (·.1 == r)).map fun (n, w, _) => (n, w)
      Conflict.conflictTick r here (Bases.baseFor · none) t
    if let .error e ← Guard.guard conflictPass then Env.err s!"conflict: {e}"
    let mut errs : List String := []
    errs ← pass errs (pre ++ "locks: ") (discard <| reapLocks r t)
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
  Store.run (Txn.update [] [.msg] fun db =>
    let db := db.log now (some "swarm") "watchd-tick-error" none (some msg)
    (cs.foldl (fun db c => say db now (.agent c) ("watchd tick failed (it carries on): " ++ msg) false "system") db, ()))
  return { st with lastErr := some msg }

/-- The tick lease (meta watchd_tick): the record still ours and no other live watchd mid-tick, in one transaction.
true: ours; false: the record isn't; none: another's tick (or the lease changed since its holder was checked). -/
def claimTick (mine : String) : m (Option Bool) := do
  let t0 ← Store.view [Sels.metas ["watchd_tick"]] fun db => (db.getMeta "watchd_tick").bind (·.v)
  let busy ← match t0 with
    | some v => if v != mine then recAlive v else pure false
    | none => pure false
  Store.run (Txn.update [Sels.metas ["watchd", "watchd_tick"]] [] fun db =>
    if (db.getMeta "watchd").bind (·.v) != some mine then (db, some false)
    else if (db.getMeta "watchd_tick").bind (·.v) != t0 || busy then (db, none)
    else (db.setMeta "watchd_tick" (some mine), some true))

/-- One pass of the loop: the record, then the tick; whether a tick has finished, why watchd exits if it should, and
the tick's error (watchd.watchd_pass). -/
def watchdPass (mine : String) (opts : Opts) (up : Bool) (st : St) :
    m (Bool × Option String × St × Option String) := do
  let db ← Store.view [Sels.metas ["watchd", "watchd_up"]] id
  let some cur := (db.getMeta "watchd").bind (·.v) | return (up, some ": its record is gone", st, none)
  if cur != mine then
    -- hand over only to a live watchd that has finished a tick; a replacement that died gets the record back
    let alive ← recAlive cur
    if (db.getMeta "watchd_up").bind (·.v) == some cur && alive then return (up, some s!" was replaced by {cur}", st, none)
    if !alive then
      let now ← Clock.now
      -- the record and its event together: a reader that sees one sees both
      Store.run (Txn.update [Sels.metas ["watchd"]] [] fun db =>
        if (db.getMeta "watchd").bind (·.v) == some cur then
          ((db.setMeta "watchd" (some mine)).log now (some "swarm") "watchd-back" none (some s!"{cur} died before its first tick; {mine} carries on"), ())
        else (db, ()))
    return (up, none, st, none)
  let mut mid ← claimTick mine
  while mid.isNone do  -- not a whole interval: --restart waits for our first tick
    Sys.sleep 1000
    mid ← claimTick mine
  if mid != some true then return (up, none, st, none)
  let (st, err) ← match ← Guard.guard (tick opts st) with
    | .ok r => pure r
    | .error e => pure (st, some e)
  Store.run (Txn.update [Sels.metas ["watchd_up", "watchd_tick"]] [] fun db =>
    let db := if err.isNone && !up then db.setMeta "watchd_up" (some mine) else db
    (if (db.getMeta "watchd_tick").bind (·.v) == some mine then delMeta db "watchd_tick" else db, ()))
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
  let db ← Store.view [Sels.metas ["watchd_run", "watchd"]] id
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
    let db ← Store.view [Sels.metas ["watchd", "watchd_up"]] id
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
      Store.run (Txn.update [Sels.metas ["watchd"]] [] fun db =>
        (if (db.getMeta "watchd").bind (·.v) == some s then db.setMeta "watchd" (some o) else db, ()))
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
  let ss := Sels.limits ++ [Sels.metas ["ci", "spawn_model", "spawn_effort"]] ++ (comms.map Sels.agent).toList
  Store.run <| Txn.update ss [] fun db =>
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
  let old ← Store.view [Sels.metas ["watchd"]] fun db => (db.getMeta "watchd").bind (·.v)
  let oldAlive ← match old with | some o => recAlive o | none => pure false
  let once := a.flag "once"
  let run := Json.encode (Lean.Json.mkObj [("cwd", .str (← Env.cwd)),
    ("flags", .arr (flags a |>.map Lean.Json.str |>.toArray)), ("started", Json.int (← Clock.now))])
  let refused ← Store.run <| Txn.update [Sels.metas ["watchd", "watchd_run"]] [] fun db =>
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
