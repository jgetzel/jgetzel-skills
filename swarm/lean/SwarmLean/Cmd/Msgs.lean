import SwarmLean.Cmd
import SwarmLean.Cmd.MsgsHelp
import SwarmLean.Lib.Msgs
import SwarmLean.Lib.Agents
import SwarmLean.Sys
import SwarmLean.Db.Compact
import SwarmLean.Lib.Spawn
import SwarmLean.Db.Notes
import SwarmLean.Lib.Sock
import SwarmLean.Lib.Swarms

/-! `swarm post`, `read`, `wait` (msgs.lua's cmd_post, cmd_read, cmd_wait), `swarm nudge` (agents.cmd_nudge) and
`swarm compact` (board #136). -/

namespace SwarmLean.Cmd.Msgs
open Args _root_.SwarmLean.Msgs Agents

/-- Lua's `tonumber` for `--poll`, kept as text: a decimal, else argparse's "malformed argument". -/
def num : Conv := fun s => match parseFloat (strip s) with
  | some _ => .ok (.s s)
  | none => .error none

/-- The `post` parser. -/
def postSpec : Spec := .mk "post" helpPost [{ name := "to" }, { name := "text", maxArgs := 1000000 }] [flag "--urgent"] [] [] none
/-- The `read` parser. -/
def readSpec : Spec := .mk "read" helpRead [] [] [] [] none
/-- The `wait` parser. -/
def waitSpec : Spec :=
  .mk "wait" helpWait [] [opt "--me", opt "--timeout" (some "21000") (some int), opt "--poll" (some "1") (some num)] [] [] none
/-- The `nudge` parser. -/
def nudgeSpec : Spec := .mk "nudge" helpNudge [{ name := "agent" }] [] [] [] none

/-- The `compact` parser. -/
def compactSpec : Spec := .mk "compact" helpCompact [] [opt "--keep"] [] [] none

/-- The fixed line `swarm nudge` types (agents.NUDGE). -/
def NUDGE : String := "read your messages and continue, or say what you wait for"

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- The delivery groups `post` reports, in order. -/
def KEYS : List String :=
  ["drains at its next tool round", "wakes", "held, cold (reads it when it next wakes)", "no live waiter",
    "compacting (watchd wakes it when that ends)"]

/-- `swarm post '#N' <text>… [--urgent]` (board #202): a note on task N, sent to its live owner, held for its next
owner, or for a done task to whoever did it, else the communicator; the poster is told which. -/
def postTask (frm : String) (id : Int) (body : String) (urgent : Bool) : m UInt32 := do
  let owner := ((← Store.view [Sels.task id] (·.find id)).bind (·.owner)).toList
  let rows ← Store.view (owner.map fun o => { Sels.agent o with inScope := false }) (·.agents)  -- of any swarm
  let here := (← splitAgents { agents := rows }).1.map (·.name)
  let envComms ← env "SWARM_COMMS"
  let now ← Clock.now
  let to ← orDie (← Store.run (Txn.update [Sels.task id, Sels.metas ["comms"]] [.msg] fun db =>
    Notes.post db now frm id body urgent (here.contains ·) (commsOf db envComms)))
  Env.out s!"posted to #{d id}: {to.text id}"
  return 0

/-- The agents a post to `dest` reaches: the agent of that name in any swarm, or the agents of swarm `s` (`sw`: the
view's). -/
def reachSel (sw : String) : Dest → Sel
  | .all s => if s == sw then { table := .agent } else { table := .agent, cond := .eq "swarm" (.text s), inScope := false }
  | dest => { Sels.agent dest.text with inScope := false }

/-- `post`'s transaction: the message from `frm` to `to` (`Dest.ofText`: `@all` the sender's swarm), and the slice it
read: the agents it reaches and who the communicator is. None when `to` names no agent and no swarm of `swarms`. -/
def postTxn (now : Int) (frm to body : String) (urgent : Bool) (swarms : List String) : Txn (Option (Dest × Db)) := do
  let d ← Txn.slice []
  let some dest := Dest.ofText d.swarm to | return none
  match dest with
  | .task _ => return none
  | .all s => if s != d.swarm && !swarms.contains s then return none
  | .agent _ => pure ()
  let d ← Txn.slice [reachSel d.swarm dest, Sels.metas ["comms"]] [.msg]
  if let .agent n := dest then
    if (d.agent n).isNone then return none
  let (d', _) := _root_.SwarmLean.Msgs.post d now (Who.ofText frm) dest body urgent
  Txn.exec (slicePlan d d')
  return some (dest, d)

/-- What `Compact.compacting` reads of agent `n`: its compaction events, in any swarm. -/
def compactEvs (n : String) : Sel :=
  { table := .event, inScope := false, cond := .and (.eq "agent" (.text n))
      (.oneOf "kind" [.text "compact-asked", .text "ctx-compact", .text "ctx-continue", .text "compact"]) }

/-- `swarm post <to> <text>… [--urgent]` (msgs.cmd_post): `to` an agent of any swarm, `@all` (the sender's swarm) or
`@<swarm>` (its live agents); `#N` or `task:N` is a note to a task (`postTask`). -/
def post (a : Parsed) : m UInt32 := do
  let frm ← me
  let to := (a.str "to").getD ""
  let urgent := a.flag "urgent"
  let body := clean (" ".intercalate (a.strs "text"))
  if let some id := Notes.target? to then return ← postTask frm id body urgent
  let sws ← Swarms.list
  let now ← Clock.now
  let some (dest, db) ← Store.run (postTxn now frm to body urgent ((sws.filter (·.ended.isNone)).map (·.name)))
    | die s!"unknown agent or swarm '{to}'; `swarm who` lists the agents, `swarm swarms` the swarms"
  let (here, gone) ← splitAgents db
  let toIt (x : Agent) : Bool := x.name != frm && (match dest with | .agent n => x.name == n | _ => true)
  let envComms ← env "SWARM_COMMS"
  let isC (n : String) : Bool := isComms db envComms (some n) || sws.any (·.comms == some n)
  let mut g0 : List String := []
  let mut g1 : List String := []
  let mut g2 : List String := []
  let mut g3 : List String := []
  let mut g4 : List String := []
  let mut seen : Seen := []
  for x in here.filter toIt do
    let mut k := 0
    if x.status != some "working" then
      let (cr, s) ← coldReason seen x (← Clock.now)
      seen := s
      let up ← match x.waiter with | some w => Sys.pidAlive w | none => pure false
      -- a communicator with no waiter is not held cold: watchd types it in (board #210)
      k := if cr.isSome && !urgent && (up || !isC x.name) then 2 else if up then 1 else 3
      if k == 3 then  -- the events only for a recipient no waiter wakes
        let e ← Store.view [compactEvs x.name] (·.events)
        if Compact.compacting e x.name (x.last_active.getD 0) (← Clock.now) then k := 4
    match k with
    | 1 => g1 := g1 ++ [x.name]
    | 2 => g2 := g2 ++ [x.name]
    | 3 => g3 := g3 ++ [x.name]
    | 4 => g4 := g4 ++ [x.name]
    | _ => g0 := g0 ++ [x.name]
  let mut parts := (KEYS.zip [g0, g1, g2, g3, g4]).filterMap fun (k, ns) => if ns.isEmpty then none else some (", ".intercalate ns ++ ": " ++ k)
  let dead := (gone.filter toIt).map (·.name)
  if !dead.isEmpty then
    parts := parts ++ [", ".intercalate dead ++ ": no terminal; can't be delivered now (stored; read after `swarm join --takeover`)"]
  Env.out ("posted. " ++ "; ".intercalate parts)
  let (held, idle) := g3.partition isC
  if !held.isEmpty then
    Env.out (", ".intercalate held ++ ": no waiter; watchd sends it to the communicator within a tick (while no other agent lives, only an urgent one)")
  if !idle.isEmpty then
    Env.out ("nudge by SendMessage (one line, `swarm read`): " ++ ", ".intercalate idle)
  return 0

/-- `swarm read` (msgs.cmd_read). -/
def read : m UInt32 := do
  let n ← me
  let (_, rows) ← Store.run (takeTxn n)
  Env.out (← if rows.isEmpty then pure "no unread messages" else fmtMsgs rows)
  return 0

/-- `x`, tried again a second later while the db is busy ("database is locked": busy_timeout ran out), for about an
hour: a waiter that exits on a busy db is read as broken (board #137). -/
def retryBusy [Guard m] (x : m α) : m α := do
  for _ in [0:300] do
    match ← Guard.guard x with
    | .ok a => return a
    | .error e => if !hasSub e "database is locked" then die e
    Sys.sleep 1000
  x

/-- `Store.run t` under `retryBusy`. -/
def runBusy [Guard m] (t : Txn α) : m α := retryBusy (Store.run t)

/-- `swarm wait [--me N] [--timeout S] [--poll S]` (msgs.cmd_wait): 2 after a delivery to stderr, 3 when fenced, 0 on
a timeout or when superseded or working, with one stderr line saying which (and, on a timeout, what is unread). -/
def wait [Guard m] (a : Parsed) : m UInt32 := do
  let n ← me
  let here ← env "HC_TERMINAL_ID"
  let now ← Clock.now
  -- the Stop hook set last_active; the cold rule needs it untouched
  if let some f ← runBusy (Sels.onAgent n (touchWith · n none here now true ({ · with status := some "idle" }))) then
    -- fenced: this waiter can never wake; 3 so it isn't read as a timeout (0) or messages (2)
    Env.err (← fenceText n f)
    throw (Exit.mk 3)
  let pid ← Sys.getpid  -- every Stop starts a waiter and none is killed: the newest owns the inbox
  runBusy (Txn.update [Sels.agent n] [] fun db => (db.setAgent n ({ · with waiter := some pid }), ()))
  let deadline := (← Clock.now) + (a.int "timeout").getD 21000
  let pollMs := ((parseFloat (strip ((a.str "poll").getD "1"))).getD 1 * 1000).toUInt64.toNat
  let mut seen : Seen := []
  let mut left : List Msg := []  -- the last poll's unread rows
  let mut held : Option String := none  -- why they were held as cold
  while (← Clock.now) < deadline do
    let (ag, rows) ← runBusy do let db ← inboxTxn n [Sels.agent n]; pure (db.agent n, unread db n)
    let some ag := ag | Env.err s!"swarm wait: {n} has no agent row; `swarm join`"; return 0
    if ag.waiter != some pid then
      Env.err s!"swarm wait: superseded: a newer waiter (pid {(ag.waiter.map toString).getD "none"}) owns {n}'s inbox"
      return 0
    if ag.status == some "working" then
      Env.err s!"swarm wait: {n} is working; its hooks deliver"
      return 0
    let urg (r : Msg) : Bool := r.urgent.getD 0 != 0
    let wake := rows.filter fun r => r.kind != some "notice" || urg r
    let urgent := wake.any urg
    let mut cold := false
    if !wake.isEmpty && !urgent then
      let (cr, s) ← coldReason seen ag (← Clock.now)
      seen := s
      cold := cr.isSome
      held := cr
    if (← wakes rows (pure cold : m Bool)).isSome then
      let t ← Clock.now
      runBusy (Txn.exec [logStmt t (some n) "wake" none (some s!"{wake.length} msg{if urgent then " urgent" else ""}")])
      Env.err (← retryBusy (deliver n))  -- a failed delivery rolls back: nothing is marked read
      throw (Exit.mk 2)
    left := rows
    Sys.sleep pollMs
  let notes := (left.filter (·.kind == some "notice")).length
  let msgs := left.length - notes
  let what := if left.isEmpty then "nothing unread"
    else ", ".intercalate ((if msgs > 0 then [s!"{msgs} message(s) held, cold: {held.getD "?"} `swarm read` takes them"] else []) ++
      (if notes > 0 then [s!"{notes} notice(s) (notices don't wake)"] else []))
  Env.err s!"swarm wait: timed out after {(a.int "timeout").getD 21000}s; {what}"
  return 0

/-- `swarm nudge <agent>`: types one fixed line into a live agent's terminal (hc send) and logs it (agents.cmd_nudge). -/
def nudge (a : Parsed) : m UInt32 := do
  let me := (← env "SWARM_NAME").getD HUMAN
  let ag := (a.str "agent").getD ""
  let some r ← Store.view [Sels.agent ag] (·.agent ag) | die s!"{ag} is not an agent"
  if r.ended.isSome then die s!"{ag} has ended; nothing to nudge"
  let some hc := py r.hc | die s!"{ag} has no terminal"
  let err := match ← Proc.output ["hc", "send", hc, NUDGE] none [] with
    | some o => if o.code == 0 then none else some o.stderr
    | none => some ""
  if let some e := err then die s!"hc send {hc} failed: {strip e}"
  let now ← Clock.now
  Store.run (Txn.exec [logStmt now (some me) "nudge" (some ag) none])
  Env.out s!"nudged {ag} ({hc})"
  return 0

/-- Types `text` into terminal `hc` as if at its keyboard: hc wraps text sent from an agent's terminal in `<hc from>`,
and a wrapped `/compact` is no command. Its error, or none. -/
def typeLine (hc text : String) : m (Option String) := do
  let o ← Sys.exec ["hc", "send", hc, text] { env := [("HC_TERMINAL_ID", none)] }
  return if o.code == 0 then none else some (strip (o.stderr ++ o.stdout))

/-- Delivers `text` to agent `name` in terminal `hc`: as a cross-session message by its Claude Code inbox socket when
one is recorded (board #215), else, or when that fails, typed with hc send (`typeLine`). hc send's error, or none. -/
def deliverTo (name hc text : String) : m (Option String) := do
  if (← Sock.post name text).isNone then return none
  typeLine hc text

/-- The `/compact` line for agent row `a`: its claimed or blocked task, worktree and branch, and `extra` (board #136); `db` holds the
agent's row, its tasks and its worktrees. -/
def compactLine (db : Db) (a : Agent) (extra : Option String) : m String := do
  let task := ((db.tasks.filter fun r => r.owner == some a.name && (r.state = .claimed || r.state = .blocked)).mergeSort
    (·.id ≤ ·.id)).head?
  -- an agent's cwd is the checkout it was spawned from; its worktree is what it must find again
  let dir := ((← Workspaces.wtMap db).lookup a.name).orElse fun _ => a.cwd
  let br ← match dir with
    | some c => pure ((← Git.out ["-C", c, "branch", "--show-current"] none).bind fun o =>
        if o.code == 0 then some (strip o.stdout) else none)
    | none => pure none
  -- Claude Code turns a long paste (over ~800 chars) into an attachment, so a long keep note goes by file
  let extra ← match extra with
    | some e =>
      if e.length ≤ Compact.maxKeep then pure (some e) else do
        let sd := joinPath (dirname (← Spawn.dbPath)) "agents"
        let f := joinPath sd (a.name ++ ".keep.txt")
        discard <| Sys.mkdirp sd
        pure (some (if ← Fs.write f e then s!"Keep: read {f} first." else (e.take Compact.maxKeep).toString))
    | none => pure none
  return Compact.line a.name (task.map fun r => ((r.id : Int), r.title.getD "")) dir br extra

/-- `swarm compact [--keep <text>]`: types `/compact <what to keep>` into the agent's own terminal; Claude Code runs it
when the turn ends (board #136). -/
def compact (a : Parsed) : m UInt32 := do
  let some me ← env "SWARM_NAME" | die "swarm compact: SWARM_NAME is not set"
  let (row, db) ← Store.view [Sels.agent me, Sels.owned me, Sels.workspaces me] fun db => (db.agent me, db)
  let some r := row.filter (·.ended.isNone) | die s!"{me} is not a live agent"
  let some hc := py r.hc | die s!"{me} has no terminal"
  if let some e ← typeLine hc (← compactLine db r (a.str "keep")) then die s!"hc send {hc} failed: {e}"
  let now ← Clock.now
  Store.run (Txn.exec [logStmt now (some me) "compact-asked" none none])
  Env.out s!"/compact queued in {hc}: it runs when this turn ends."
  return 0

/-- The group: post, read, wait, nudge and compact. -/
def group [Guard m] : Group m where
  specs := [("post", postSpec), ("read", readSpec), ("wait", waitSpec), ("nudge", nudgeSpec), ("compact", compactSpec)]
  run a := match a.cmd with
    | "post" => post a
    | "read" => read
    | "wait" => wait a
    | "compact" => compact a
    | _ => nudge a

end SwarmLean.Cmd.Msgs
