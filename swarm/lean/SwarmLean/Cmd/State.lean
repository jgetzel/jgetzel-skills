import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Db.Agents
import SwarmLean.Sys

/-! `swarm state --json` (one read-only snapshot for UIs) and `swarm watch` (state.lua). -/

namespace SwarmLean.Cmd.State
open Args

/-- The panel views (state.VIEWS' keys, sorted). -/
def VIEWS : List String := ["activity", "agents", "board", "overview", "system"]

/-- The `watch` parser. -/
def watchSpec : Spec := .mk "watch" helpWatch [] [opt "--tail" (some "20") (some int), flag "--once"] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Sys m]

/-- An event's line: time, the agent in a colour of its name, kind, path and data. -/
def eventLine (e : Event) : m String := do
  let ag := e.agent.getD ""
  let sum := ag.toUTF8.foldl (fun s b => s + b.toNat) 0
  let col := ["31", "32", "33", "34", "35", "36"][sum % 6]!
  let t ← match e.ts with | some t => pure t | none => Clock.now
  return s!"{← Sys.date "%H:%M:%S" t} \x1b[{col}m{padRight (e.agent.getD "-") 12}\x1b[0m {padRight (e.kind.getD "nil") 9} {e.path.getD ""} {e.data.getD ""}"

/-- `swarm watch` (state.cmd_watch): the events as they come, and the live agents every 30 s. -/
def watch (a : Parsed) : m UInt32 := do
  -- shortcut: each second loads the event table whole (Store has no query); fine for a human's terminal
  let mx ← Store.txn [.event] fun db => (db, db.events.foldl (fun x e => max x e.id) 0)
  let mut last : Int := max 0 (mx - (a.int "tail").getD 20)
  let mut tick : Nat := 0
  repeat
    let db ← Store.txn [.event, .agent] fun db => (db, db)
    for e in db.events do
      if (e.id : Int) > last then
        last := e.id
        Env.out (← eventLine e)
    if tick % 30 == 0 then
      Env.out s!"\x1b[2m-- {" | ".intercalate ((Agents.live db).map fun x => x.name ++ ":" ++ x.status.getD "nil")} --\x1b[0m"
    tick := tick + 1
    if a.flag "once" then break
    Sys.sleep 1000
  return 0

/-- The group: state and watch. -/
def group : Group m where
  specs := [("watch", watchSpec)]
  run a := watch a

end SwarmLean.Cmd.State
