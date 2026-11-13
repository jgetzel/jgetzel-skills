import SwarmLean.Cmd
import SwarmLean.Cmd.MsgsHelp
import SwarmLean.Lib.Msgs
import SwarmLean.Lib.Agents
import SwarmLean.Sys
import SwarmLean.Db.Compact

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

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Proc m] [Sys m]

/-- The delivery groups `post` reports, in order. -/
def KEYS : List String :=
  ["drains at its next tool round", "wakes", "held, cold (reads it when it next wakes)", "no live waiter"]

/-- `swarm post <to> <text>… [--urgent]` (msgs.cmd_post). -/
def post (a : Parsed) : m UInt32 := do
  let frm ← me
  let to := (a.str "to").getD ""
  let urgent := a.flag "urgent"
  let body := " ".intercalate (a.strs "text")
  let now ← Clock.now
  let some db ← Store.txn [.agent, .«meta»] (fun db =>
      if to != "@all" && (db.agent to).isNone then (db, none) else let db := (_root_.SwarmLean.Msgs.post db now frm to body urgent).1; (db, some db))
    | die s!"unknown agent '{to}'; `swarm who` lists them"
  let (here, gone) ← splitAgents db
  let toIt (x : Agent) : Bool := x.name != frm && (to == "@all" || x.name == to)
  let mut g : Array (List String) := #[[], [], [], []]
  let mut seen : Seen := []
  for x in here.filter toIt do
    let mut k := 0
    if x.status != some "working" then
      let (cr, s) ← coldReason seen x (← Clock.now)
      seen := s
      let up ← match x.waiter with | some w => Sys.pidAlive w | none => pure false
      k := if cr.isSome && !urgent then 2 else if up then 1 else 3
    g := g.modify k (· ++ [x.name])
  let mut parts := (KEYS.zip g.toList).filterMap fun (k, ns) => if ns.isEmpty then none else some (", ".intercalate ns ++ ": " ++ k)
  let dead := (gone.filter toIt).map (·.name)
  if !dead.isEmpty then
    parts := parts ++ [", ".intercalate dead ++ ": no terminal; can't be delivered now (stored; read after `swarm join --takeover`)"]
  Env.out ("posted. " ++ "; ".intercalate parts)
  let envComms ← env "SWARM_COMMS"
  let (held, idle) := g[3]!.partition fun n => isComms db envComms (some n)
  if !held.isEmpty then
    Env.out (", ".intercalate held ++ ": held; the communicator reads it when its inbox is next armed (no SendMessage nudge)")
  if !idle.isEmpty then
    Env.out ("nudge by SendMessage (one line, `swarm read`): " ++ ", ".intercalate idle)
  return 0

/-- `swarm read` (msgs.cmd_read). -/
def read : m UInt32 := do
  let n ← me
  let rows ← Store.txn [.msg, .cursor] fun db => let (db, _, fit) := take n id db; (db, fit)
  Env.out (← if rows.isEmpty then pure "no unread messages" else fmtMsgs rows)
  return 0

/-- `Store.txn ts f`, tried again a second later while the db is busy ("database is locked": busy_timeout ran out),
for about an hour: a waiter that exits on a busy db is read as broken (board #137). -/
def txnBusy [Guard m] (ts : List Table) (f : Db → Db × α) : m α := do
  for _ in [0:300] do
    match ← Guard.guard (Store.txn ts f) with
    | .ok a => return a
    | .error e => if !hasSub e "database is locked" then die e
    Sys.sleep 1000
  Store.txn ts f

/-- `swarm wait [--me N] [--timeout S] [--poll S]` (msgs.cmd_wait): 2 after a delivery to stderr, 3 when fenced, 0 on
a timeout or when superseded or working. -/
def wait [Guard m] (a : Parsed) : m UInt32 := do
  let n ← me
  let here ← env "HC_TERMINAL_ID"
  let now ← Clock.now
  -- the Stop hook set last_active; the cold rule needs it untouched
  if let some f ← txnBusy [.agent, .event, .cursor] (touchWith · n none here now true ({ · with status := some "idle" })) then
    -- fenced: this waiter can never wake; 3 so it isn't read as a timeout (0) or messages (2)
    Env.err (← fenceText n f)
    throw (Exit.mk 3)
  let pid ← Sys.getpid  -- every Stop starts a waiter and none is killed: the newest owns the inbox
  txnBusy [.agent] fun db => (db.setAgent n ({ · with waiter := some pid }), ())
  let deadline := (← Clock.now) + (a.int "timeout").getD 21000
  let pollMs := ((parseFloat (strip ((a.str "poll").getD "1"))).getD 1 * 1000).toUInt64.toNat
  let mut seen : Seen := []
  while (← Clock.now) < deadline do
    let (ag, rows) ← txnBusy [.agent, .msg, .cursor] fun db => (db, (db.agent n, unread db n))
    let some ag := ag | return 0
    if ag.waiter != some pid || ag.status == some "working" then return 0  -- superseded, or its hooks deliver
    let urg (r : Msg) : Bool := r.urgent.getD 0 != 0
    let wake := rows.filter fun r => r.kind != some "notice" || urg r
    let urgent := wake.any urg
    let mut cold := false
    if !wake.isEmpty && !urgent then
      let (cr, s) ← coldReason seen ag (← Clock.now)
      seen := s
      cold := cr.isSome
    if (← wakes rows (pure cold : m Bool)).isSome then
      let t ← Clock.now
      txnBusy [] fun db => (db.log t (some n) "wake" none (some s!"{wake.length} msg{if urgent then " urgent" else ""}"), ())
      Env.err (← deliver n)
      throw (Exit.mk 2)
    Sys.sleep pollMs
  return 0

/-- `swarm nudge <agent>`: types one fixed line into a live agent's terminal (hc send) and logs it (agents.cmd_nudge). -/
def nudge (a : Parsed) : m UInt32 := do
  let me := (← env "SWARM_NAME").getD HUMAN
  let ag := (a.str "agent").getD ""
  let some r ← Store.txn [.agent] fun db => (db, db.agent ag) | die s!"{ag} is not an agent"
  if r.ended.isSome then die s!"{ag} has ended; nothing to nudge"
  let some hc := py r.hc | die s!"{ag} has no terminal"
  let err := match ← Proc.output ["hc", "send", hc, NUDGE] none [] with
    | some o => if o.code == 0 then none else some o.stderr
    | none => some ""
  if let some e := err then die s!"hc send {hc} failed: {strip e}"
  let now ← Clock.now
  Store.txn [] fun db => (db.log now (some me) "nudge" (some ag) none, ())
  Env.out s!"nudged {ag} ({hc})"
  return 0

/-- Types `text` into terminal `hc` as if at its keyboard: hc wraps text sent from an agent's terminal in `<hc from>`,
and a wrapped `/compact` is no command. Its error, or none. -/
def typeLine (hc text : String) : m (Option String) := do
  let o ← Sys.exec ["hc", "send", hc, text] { env := [("HC_TERMINAL_ID", none)] }
  return if o.code == 0 then none else some (strip (o.stderr ++ o.stdout))

/-- The `/compact` line for agent row `a`: its claimed or blocked task, worktree and branch, and `extra` (board #136). -/
def compactLine (db : Db) (a : Agent) (extra : Option String) : m String := do
  let task := ((db.tasks.filter fun r => r.owner == some a.name && (r.state = .claimed || r.state = .blocked)).mergeSort
    (·.id ≤ ·.id)).head?
  let br ← match a.cwd with
    | some c => pure ((← Proc.output ["git", "-C", c, "branch", "--show-current"] none []).bind fun o =>
        if o.code == 0 then some (strip o.stdout) else none)
    | none => pure none
  return Compact.line a.name (task.map fun r => ((r.id : Int), r.title.getD "")) a.cwd br extra

/-- `swarm compact [--keep <text>]`: types `/compact <what to keep>` into the agent's own terminal; Claude Code runs it
when the turn ends (board #136). -/
def compact (a : Parsed) : m UInt32 := do
  let some me ← env "SWARM_NAME" | die "swarm compact: SWARM_NAME is not set"
  let (row, db) ← Store.txn [.agent, .task] fun db => (db, (db.agent me, db))
  let some r := row.filter (·.ended.isNone) | die s!"{me} is not a live agent"
  let some hc := py r.hc | die s!"{me} has no terminal"
  if let some e ← typeLine hc (← compactLine db r (a.str "keep")) then die s!"hc send {hc} failed: {e}"
  let now ← Clock.now
  Store.txn [] fun db => (db.log now (some me) "compact-asked" none none, ())
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
