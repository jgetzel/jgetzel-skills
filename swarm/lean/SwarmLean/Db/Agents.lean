import SwarmLean.Db

/-! agents.lua's pure parts that the board needs: who is in charge, the staffing numbers, the away flag, the fence and
touch. The rest of agents.lua (join, leave, who, role, stay, limits, away) is board task #100's. -/

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
  s!"agents: {n} live, {match mn with | some x => s!"auto-spawn to {x}" | none => "no auto-spawn number"}, {match mx with | some x => s!"max {x}" | none => "no max set"}"

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

end SwarmLean.Agents
