import SwarmLean.Db.Agents
import SwarmLean.World
import Lean.Data.Json

/-! agents.lua's world-facing helpers: hc's terminals, the live/gone split, the cold-cache rule, touch with fields and
the fence's text. -/

namespace SwarmLean.Agents

variable {m : Type → Type}

/-- A prompt cache counts as warm this long after the last turn (agents.COLD_IDLE). -/
def COLD_IDLE : Int := 55 * 60

/-- A terminal as `hc ls --json` lists it. -/
structure Term where
  state : Option String
  address : Option String

/-- `hc ls --json`'s terminals; none when hc fails or prints no list (agents.hc_terminals). -/
def hcTerminals [Monad m] [Proc m] : m (Option (List Term)) := do
  let some o ← Proc.output ["hc", "ls", "--json"] none [] | return none
  if o.code != 0 then return none
  let some j := (Lean.Json.parse o.stdout).toOption | return none
  let str (x : Lean.Json) (k : String) : Option String := (x.getObjValAs? String k).toOption
  match j.getObjVal? "terminals" with
  | .ok (.arr ts) => return some (ts.toList.map fun x => { state := str x "state", address := str x "address" })
  | .ok (.obj _) => return some []
  | _ => return none

/-- Live rows split by the terminal now (hc ls): present, gone. No hc, or an unbound row, can't show a terminal gone
(agents.split_agents). -/
def splitAgents [Monad m] [Proc m] (db : Db) : m (List Agent × List Agent) := do
  let terms ← hcTerminals
  let up := (terms.getD []).filterMap fun x => if x.state == some "live" then x.address else none
  let gone (x : Agent) : Bool := terms.isSome && match x.hc with
    | some h => h != "" && !up.contains h
    | none => false
  return ((live db).filter (!gone ·), (live db).filter gone)

/-- What `hc get` said of each terminal: when it was asked and the session's last status change (agents.term_seen). -/
abbrev Seen := List (String × Int × Int)

/-- A JSON number or numeric text, in thousandths, floored (`math.floor(tonumber(x) / 1000)`); 0 otherwise. -/
def kilo : Except String Lean.Json → Int
  | .ok (.num n) => Int.fdiv n.mantissa (10 ^ n.exponent * 1000)
  | .ok (.str t) => fdiv ((parseInt t).getD 0) 1000
  | _ => 0

/-- The later of last_active and the hc session's last status change, asked of hc at most every 30 s
(agents.session_active). -/
def sessionActive [Monad m] [Proc m] (seen : Seen) (a : Agent) (t : Int) : m (Int × Seen) := do
  let last := a.last_active.getD 0
  let some hc := a.hc | return (last, seen)
  if hc == "" || t - last < COLD_IDLE then return (last, seen)
  let s ← match seen.lookup hc with
    | some (at_, s) => if t - at_ > 30 then pure none else pure (some s)
    | none => pure none
  match s with
  | some s => return (max last s, seen)
  | none =>
    let out ← Proc.output ["hc", "get", hc, "--json"] none []
    let txt := match out with | some o => if o.code == 0 then o.stdout else "{}" | none => "{}"
    let s := match Lean.Json.parse txt with | .ok j => kilo (j.getObjVal? "status_ms") | .error _ => 0
    return (max last s, (hc, t, s) :: seen.filter (·.1 != hc))

/-- None if waking agent row `a` is cheap at `t`, else why it is a cold wake (agents.cold_reason). -/
def coldReason [Monad m] [Proc m] (seen : Seen) (a : Agent) (t : Int) : m (Option String × Seen) := do
  let ctx := a.ctx_tokens.getD 0
  if a.status == some "working" || ctx < SMALL_CTX then return (none, seen)
  let (last, seen) ← sessionActive seen a t
  if a.compacted_at.getD 0 ≥ last || t - last < COLD_IDLE then return (none, seen)
  let k := fdiv ctx 1000
  return (some s!"{a.name} is idle {fdiv (t - last) 60} min with ~{k}k context and no compaction; a wake costs ~{k}k uncached tokens.", seen)

/-- agents.touch with fields: creates `name`'s row if it has none (bound to `here`), with `bind` binds an unbound row
to `here`, then applies `f` to the row unless it is ended or another terminal's. Nothing for the user; a fenced name
gets its fence back. -/
def touchWith (db : Db) (name : String) (cwd here : Option String) (now : Int) (bind : Bool) (f : Agent → Agent) :
    Db × Option Fence :=
  if name == HUMAN then (db, none) else
  match fence db name here with
  | some w => (db, some w)
  | none =>
    let db := touch db name cwd here now
    let db := if bind && here.isSome then db.setAgent name fun a => if a.hc.isNone then { a with hc := here } else a else db
    (db.setAgent name fun a => if a.ended.isNone && (a.hc.isNone || a.hc == here) then f a else a, none)

/-- The fence's message (agents.fence). -/
def fenceText [Monad m] [Clock m] (name : String) : Fence → m String
  | .ended t why =>
    let tail := match why with | some w => if w != "" then s!" ({w})" else "" | none => ""
    return s!"{name} was ended at {← Clock.hhmm (t.getD 0)}{tail}; `swarm join` to return."
  | .bound hc here =>
    return s!"{name} is bound to {hc}; this terminal is {here.getD "outside Herdr"}. `swarm join --takeover` moves it here."

end SwarmLean.Agents
