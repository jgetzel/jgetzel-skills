import SwarmLean.Db.Msgs
import Lean.Data.Json

/-! agents.lua's pure steps: who is in charge, the staffing numbers, the away flag, the fence, touch, binding, release,
role, stay, limits and away. -/

namespace SwarmLean.Agents

/-- The user's name (agents.HUMAN). -/
def HUMAN : String := "human"
/-- A context this small is cheap to wake (agents.SMALL_CTX). -/
def SMALL_CTX : Int := 40000

/-- The communicator's name: meta comms, else $SWARM_COMMS (agents.comms check in is_comms). -/
def commsOf (db : Db) (envComms : Option String) : Option String :=
  match db.getMeta "comms" with
  | some { v := some v, .. } => some v
  | _ => envComms

/-- `name` is the communicator (agents.is_comms). -/
def isComms (db : Db) (envComms : Option String) (name : Option String) : Bool :=
  match name with
  | none | some "" => false
  | some n => some n == commsOf db envComms

/-- `n` has the communicator's rights: it, or the user (agents.in_charge). -/
def inCharge (db : Db) (envComms : Option String) (n : String) : Bool := n == HUMAN || isComms db envComms (some n)

/-- Live agent rows, by name (agents.live_agents). -/
def live (db : Db) : List Agent := (db.agents.filter (·.ended.isNone)).mergeSort (·.name ≤ ·.name)

/-- A meta value as Lua's `tonumber` reads it (an integer here), or none. -/
def metaNum (db : Db) (k : String) : Option Int := (db.getMeta k).bind (·.v) |>.bind parseInt

/-- Live agents but the communicator, and the auto-spawn number and max (agents.limits). -/
def limits (db : Db) (envComms : Option String) : Nat × Option Int × Option Int :=
  ((live db).filter (fun a => !isComms db envComms (some a.name)) |>.length, metaNum db "agent_min", metaNum db "agent_max")

/-- `agents: N live, …` (agents.limits_line). -/
def limitsLine (db : Db) (envComms : Option String) : String :=
  let (n, mn, mx) := limits db envComms
  s!"agents: {n} live, {match mn with | some x => s!"auto-spawn to {x}" | none => "no auto-spawn number"}, {match mx with | some x => s!"max {x}" | none => "no max set"}{if ((db.getMeta "queue_only").bind (·.v)) == some "on" then ", queue-only" else ""}"

/-- The user's away flag: since (none when the text has no leading number) and note (agents.away). -/
def away (db : Db) : Option (Option Int × Option String) :=
  match db.getMeta "away" with
  | none => none
  | some m =>
    let v := m.v.getD ""
    let ds := String.ofList (v.toList.takeWhile Char.isDigit)
    let since := if ds.isEmpty then none else ds.toNat?.map (Int.ofNat ·)
    let rest := (v.drop ds.length).toString
    let note := if !ds.isEmpty && rest.startsWith " " && rest.length > 1 then some (rest.drop 1).toString else none
    some (since, note)

/-- What the agent waits for (agents.stay_of). -/
def stayOf (db : Db) (n : String) : Option String := (db.agent n).bind (·.stay)

/-- Why this terminal may not write as `name` (agents.fence), before the time is formatted. -/
inductive Fence
  /-- the row ended at `t`; `why` is the data of its last reap, leave or end event -/
  | ended (t : Option Int) (why : Option String)
  /-- the row is bound to terminal `hc`; this one is `here` -/
  | bound (hc : String) (here : Option String)

/-- The fence on `name` from terminal `here` (HC_TERMINAL_ID), if any. -/
def fence (db : Db) (name : String) (here : Option String) : Option Fence :=
  match db.agent name with
  | none => none
  | some r =>
    if r.ended.isSome then
      let why := (db.events.filter fun e => e.agent == some name && [some "reap", some "leave", some "end"].contains e.kind)
        |>.getLast? |>.bind (·.data)
      some (.ended r.ended why)
    else match r.hc with
      | some h => if h != "" && some h != here then some (.bound h here) else none
      | none => none

/-- A new agent's cursor starts after the messages there are (agents.new_inbox); one already there stays. -/
def newInbox (db : Db) (n : String) : Db :=
  if db.cursors.any (·.agent == n) then db
  else { db with cursors := db.cursors ++ [{ agent := n, last_msg_id := some (db.msgNext - 1 : Nat) }] }

/-- Creates `name`'s row if it has none, bound to `here` (agents.touch with no fields); nothing for the user or a
fenced name. -/
def touch (db : Db) (name : String) (cwd : Option String) (here : Option String) (now : Int) : Db :=
  if name == HUMAN || (fence db name here).isSome then db
  else if db.agents.any (·.name == name) then db
  else newInbox { db with agents := db.agents ++ [{ name, cwd, status := some "idle", last_active := some now,
                                                    started := some now, hc := here }] } name

/-- `name` is the user's, which no agent takes (agents.not_human). -/
def notHuman (name : String) : Except String Unit :=
  if name == HUMAN then .error "'human' is the user's name (the panel acts as it); an agent can't take it" else .ok ()

/-- A row's binding as bind reads it before its transaction: its terminal and when it ended. -/
abbrev Binding := Option (Option String × Option Int)

/-- The binding of `name` now. -/
def binding (db : Db) (name : String) : Binding := (db.agent name).map fun r => (r.hc, r.ended)

/-- The live terminal a row read as `r` is bound to, which a bind elsewhere must take over (bind's `old`). -/
def boundTo (r : Binding) : Option String :=
  match r with
  | some (some h, none) => if h != "" then some h else none
  | _ => none

/-- Binds `name` to terminal `hc` (agents.bind's transaction), given the row as read before (`r`): refuses if it
changed since, logs a takeover from another terminal. -/
def bind (db : Db) (name : String) (cwd hc model : Option String) (r : Binding) (now : Int) : Db × Except String Unit :=
  if binding db name != r then (db, .error s!"{name}'s binding changed under you; run it again") else
  let db := if db.agents.any (·.name == name) then db else
    { db with agents := db.agents ++ [{ name, cwd, status := some "idle", last_active := some now, started := some now }] }
  let db := if r.isNone then newInbox db name else db
  let db := db.setAgent name fun a => { a with hc, ended := none, model := model.orElse fun _ => a.model,
                                                status := if a.ended.isNone then a.status else some "idle" }
  let db := match boundTo r with
    | some old => if some old != hc then db.log now (some name) "takeover" none (some s!"{old} -> {hc.getD "outside Herdr"}") else db
    | none => db
  (db, .ok ())

/-- What an agent holds goes when it ends: its stay, claims, locks, conflicts and pair keys (agents._release). -/
def release (db : Db) (name : String) : Db :=
  let db := db.setAgent name ({ · with stay := none })
  { db with
    tasks := db.tasks.map fun t =>
      if t.owner == some name && (t.state = .claimed || t.state = .blocked) then
        { t with state := .open, owner := none, lease_until := none, question := none } else t
    locks := db.locks.filter (·.agent != some name)
    conflicts := db.conflicts.filter fun c => c.a != name && c.b != name
    pairkeys := db.pairkeys.filter fun p => p.a != name && p.b != name }

/-- `swarm leave`: the row ends, what it held is released (agents.cmd_leave). -/
def leave (db : Db) (name : String) (now : Int) : Db :=
  let db := db.setAgent name ({ · with ended := some now, status := some "ended" })
  (release db name).log now (some name) "leave" none none

/-- Runs of whitespace as one space, stripped, cut at 80 characters: a field peers read (agents.one_line). -/
def oneLine (s : String) : String :=
  let squeezed := s.toList.foldl (fun (acc : List Char) c =>
    if isSpace c then (if acc.head? == some ' ' then acc else ' ' :: acc) else c :: acc) []
  cut (strip (String.ofList squeezed.reverse)) 80

/-- SQLite's `lower`: ASCII letters only. -/
def lowerA (s : String) : String := String.map (fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c) s

/-- Sets `name`'s role and logs it; the live peers declaring the same text (agents.set_role). -/
def setRole (db : Db) (name text : String) (now : Int) : Db × List String :=
  let text := oneLine text
  let db := db.setAgent name ({ · with role := if text != "" then some text else none })
  let db := db.log now (some name) "role" none (some text)
  if text == "" then (db, []) else
  (db, ((live db).filter fun r => r.name != name && (r.role.map lowerA) == some (lowerA text)).map
    fun r => s!"{r.name} also declares '{text}'")

/-- touch, then `f` if `name` is not fenced from terminal `here`; the fence otherwise (a fenced self-write). -/
def fenced (db : Db) (name : String) (cwd here : Option String) (now : Int) (f : Db → Db × α) : Db × Except Fence α :=
  if name == HUMAN then let (db, a) := f db; (db, .ok a) else
  match fence db name here with
  | some w => (db, .error w)
  | none => let (db, a) := f (touch db name cwd here now); (db, .ok a)

/-- `swarm role <text>`: touch and set the role (agents.cmd_role's transaction). -/
def role (db : Db) (name : String) (cwd here : Option String) (text : String) (now : Int) : Db × Except Fence (List String) :=
  fenced db name cwd here now fun db => setRole db name text now

/-- `swarm stay [<what>] | --end`: sets or clears the agent's own stay (agents.cmd_stay's transaction). -/
def stay (db : Db) (name : String) (here : Option String) (v : Option String) (now : Int) : Db × Except Fence Unit :=
  fenced db name none here now fun db =>
    let db := db.setAgent name ({ · with stay := v })
    (db.log now (some name) (if v.isSome then "stay" else "stay-end") none v, ())

/-- `swarm stay --end NAME` by `me` (in charge): clears a live agent's stay (agents.end_stay's transaction). -/
def endStay (db : Db) (me n : String) (now : Int) : Db × Except String Unit :=
  match (live db).find? (·.name == n) with
  | none => (db, .error s!"{n} is not a live agent")
  | some r => match r.stay with
    | none => (db, .error s!"{n} stays for nothing")
    | some s =>
      let db := db.setAgent n ({ · with stay := none })
      (db.log now (some me) "stay-end" (some n) (some s), .ok ())

/-- Lua's `tostring` of an optional integer. -/
def tostr : Option Int → String
  | some i => toString i
  | none => "nil"

/-- `swarm limits --min` or `--max` by `me`: sets the staffing numbers (agents.cmd_limits's transaction). -/
def setLimits (db : Db) (envComms : Option String) (me : String) (mn mx : Option Int) (now : Int) : Db × Except String Unit :=
  let (_, mn0, mx0) := limits db envComms
  let mn' := mn.orElse fun _ => mn0
  let mx' := mx.orElse fun _ => mx0
  match mn', mx' with
  | some a, some b => if a > b then (db, .error s!"the auto-spawn number {a} is above the max {b}") else go mn' mx'
  | _, _ => go mn' mx'
where
  go (mn' mx' : Option Int) : Db × Except String Unit :=
    let db := match mn with | some a => db.setMeta "agent_min" (some (toString a)) | none => db
    let db := match mx with | some b => db.setMeta "agent_max" (some (toString b)) | none => db
    (db.log now (some me) "limits" none (some s!"min {tostr mn'} max {tostr mx'}"), .ok ())

/-- `swarm limits --queue-only on|off` by `me` (board #128): on, auto-spawn staffs only the queue and main red tasks. -/
def setQueueOnly (db : Db) (me : String) (on : Bool) (now : Int) : Db :=
  (db.setMeta "queue_only" (some (if on then "on" else "off"))).log now (some me) "limits" none
    (some s!"queue-only {if on then "on" else "off"}")

/-- A question waiting in the away digest: a blocked task and since when. -/
structure Question where
  id : Nat
  title : Option String
  owner : Option String
  question : Option String
  since : Option Int

/-- What happened while the user was away (agents.digest). -/
structure Digest where
  since : Option Int
  back : Int
  note : Option String
  questions : List Question
  done : List Task
  merged : List Task
  ci : Option Ci
  /-- each ended agent: name, when, why -/
  ended : List (String × Option Int × Option String)
  hung : List String

/-- An event's data names task `id`: `#id` or `#id …` (SQL `data='#'||id or data like '#'||id||' %'`). -/
def namesTask (data : Option String) (id : Nat) : Bool :=
  data == some s!"#{id}" || likePrefix (data.getD "") s!"#{id} "

/-- What happened since away: `since` its second, `from` its event's id (agents.digest). -/
def digest (db : Db) (since : Option Int) (note : Option String) («from» : Nat) (now : Int) : Digest :=
  let qs := (db.tasks.filter (·.state = .blocked)).map fun r =>
    let es := db.events.filter fun e => (e.kind == some "block" && namesTask e.data r.id) ||
      (e.kind == some "task-blocked" && e.path == some (d r.id))
    let ts := es.foldl (fun m e => match m, e.ts with | some a, some b => some (max a b) | none, b => b | a, none => a) none
    let ev := (es.map (·.id)).max?.getD «from»
    (ev, ({ id := r.id, title := r.title, owner := r.owner, question := r.question,
            since := ts.orElse fun _ => since } : Question))
  let qs := (qs.mergeSort fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.id ≤ y.2.id)).map (·.2)
  let ended := ((db.agents.filter (·.ended.isSome)).mergeSort fun a b => a.ended.getD 0 ≤ b.ended.getD 0).filterMap fun r =>
    (db.events.filter fun e => e.agent == some r.name && e.id > «from» &&
      [some "reap", some "leave", some "end"].contains e.kind).getLast?.map fun e => (r.name, r.ended, e.data)
  let hung := ((db.events.filter fun e => e.kind == some "stay-hung" && e.id > «from» &&
      (e.agent.bind fun n => (db.agent n).filter (·.ended.isNone)).isSome).filterMap (·.agent)).eraseDups.mergeSort (· ≤ ·)
  let done := (db.tasks.filter fun t => t.state = .done && db.events.any fun e =>
      e.kind == some "done" && e.id > «from» && namesTask e.data t.id).mergeSort fun a b => a.done_at.getD 0 ≤ b.done_at.getD 0
  let merged := match since with
    | some s => (db.tasks.filter fun t => t.merged_at.any (· ≥ s)).mergeSort fun a b => a.merged_at.getD 0 ≤ b.merged_at.getD 0
    | none => []
  let ci := (db.cis.mergeSort fun a b => a.created.getD "" ≥ b.created.getD "").head?
  { since, back := now, note, questions := qs, done, merged, ci, ended, hung }

/-- A JSON object of the fields that are set (a row as cjson encodes it: NULL columns absent). -/
def jobj (l : List (String × Option Lean.Json)) : Lean.Json := Lean.Json.mkObj (l.filterMap fun (k, v) => v.map (k, ·))

/-- The digest as `swarm away --back` stores it in meta away_digest (for state --json's `back`). -/
def Digest.json (g : Digest) : Lean.Json :=
  let i (x : Option Int) : Option Lean.Json := x.map Lean.toJson
  let s (x : Option String) : Option Lean.Json := x.map Lean.toJson
  let n (x : Nat) : Option Lean.Json := some (Lean.toJson x)
  let orNull (x : Option Lean.Json) : Lean.Json := x.getD .null
  jobj [("since", i g.since), ("back", i (some g.back)), ("note", some (orNull (s g.note))),
    ("questions", some (.arr (g.questions.map fun q => jobj [("id", n q.id), ("title", s q.title), ("owner", s q.owner),
      ("question", s q.question), ("since", i q.since)]).toArray)),
    ("done", some (.arr (g.done.map fun t => jobj [("id", n t.id), ("title", s t.title), ("owner", s t.owner),
      ("evidence", s t.evidence), ("done_at", i t.done_at)]).toArray)),
    ("merged", some (.arr (g.merged.map fun t => jobj [("id", n t.id), ("title", s t.title), ("pr", i t.pr),
      ("merged_at", i t.merged_at)]).toArray)),
    ("ci", some (orNull (g.ci.map fun c => jobj [("sha", s c.sha), ("status", s c.status), ("conclusion", s c.conclusion),
      ("url", s c.url)]))),
    ("ended", some (.arr (g.ended.map fun (nm, at_, why) => jobj [("name", s (some nm)), ("at", i at_),
      ("why", some (orNull (s why)))]).toArray)),
    ("hung", some (.arr (g.hung.map Lean.toJson).toArray))]

/-- `db` without meta `k`. -/
def delMeta (db : Db) (k : String) : Db := { db with metas := db.metas.filter (·.k != k) }

/-- `swarm away [note]` by `me`: sets the flag and tells the communicator `line`, unless already away (the flag
returned) (agents.cmd_away's transaction). -/
def goAway (db : Db) (me : String) (comms : Option String) (note line : String) (now : Int) :
    Db × Option (Option Int × Option String) :=
  match away db with
  | some aw => (db, some aw)
  | none =>
    let db := (delMeta db "away_digest").setMeta "away" (some (strip s!"{now} {note}"))
    let db := db.log now (some me) "away" none (some note)
    match comms with
    | some c => ((Msgs.post db now me c line false (some "system")).1, none)
    | none => (db, none)

/-- `swarm away --back` by `me`: clears the flag, keeps the digest and tells the communicator; none when the user was
not away (agents.cmd_away's back transaction). -/
def goBack (db : Db) (me : String) (comms : Option String) (now : Int) : Db × Option Digest :=
  match away db with
  | none => (db, none)
  | some (since, note) =>
    let «from» := ((db.events.filter (·.kind == some "away")).map (·.id)).max?.getD 0
    let g := digest db since note «from» now
    let db := (delMeta db "away").setMeta "away_digest" (some g.json.compress)
    let db := db.log now (some me) "back" none none
    match comms with
    | some c =>
      let ids := g.questions.map fun q => s!"#{q.id}"
      let body := s!"the user is back: {ids.length} question{if ids.length == 1 then "" else "s"} wait{if ids.isEmpty then "" else " (" ++ ", ".intercalate ids ++ ")"}"
      ((Msgs.post db now me c body true (some "system")).1, some g)
    | none => (db, some g)

end SwarmLean.Agents
