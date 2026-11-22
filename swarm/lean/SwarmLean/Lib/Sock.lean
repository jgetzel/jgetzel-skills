import SwarmLean.Db.Agents
import SwarmLean.Db.Sels
import SwarmLean.World
import SwarmLean.Sys

/-! Claude Code's inbox socket (board #215): each session listens on a unix socket, `$CLAUDE_CODE_MESSAGING_SOCKET`,
and a JSON line written there arrives as a cross-session message. An internal of Claude Code (2.1.325), not a
documented interface: the socket gives no ack, so a format it stops reading fails unseen. -/

namespace SwarmLean.Sock
open Lean (Json)

/-- The meta key of `name`'s socket record: `<mtime> <path>`. -/
def key (name : String) : String := "sock:" ++ name

/-- The meta key of `name`'s last record a send or check failed on: it is not taken again, and comms is told once. -/
def badKey (name : String) : String := "sockbad:" ++ name

/-- A record's mtime and path. -/
def parse (v : String) : Option (Int × String) :=
  match v.splitOn " " with
  | t :: p@(_ :: _) => t.toInt?.map (·, " ".intercalate p)
  | _ => none

/-- The line the inbox takes as a message from "swarm watchd"; `text` can't close the envelope. -/
def frame (text : String) : String :=
  let body := text.replace "cross-session-message" "cross-session message"
  (Json.mkObj [("type", "user"), ("message", Json.mkObj [("role", "user"),
    ("content", s!"<cross-session-message from-name=\"swarm watchd\">\n{body}\n</cross-session-message>")])]).compress ++ "\n"

/-- `db` after a send or check on record `v` of `name` failed with `e`: the record dropped, the event
`sock-fallback`, and the communicator told, once per record. -/
def failed (db : Db) (now : Int) (name v e : String) (comms : Option String) : Db :=
  let db := (if ((db.getMeta (key name)).bind (·.v)) == some v then db.setMeta (key name) none else db).log now (some name)
    "sock-fallback" (some v) (some e)
  if ((db.getMeta (badKey name)).bind (·.v)) == some v then db else
  let db := db.setMeta (badKey name) (some v)
  match comms with
  | some c => (Msgs.post db now "swarm" c (s!"watchd can't post to {name}'s Claude Code inbox socket ({(parse v).map (·.2) |>.getD v}): {e}. " ++
      "It types to that terminal with hc send until the session restarts.") false (some "system")).1
  | none => db

variable {m : Type → Type} [Monad m] [Store m] [Clock m] [Env m] [Sys m]

/-- Writes `data` to the socket at `path` (`$SWARM_SOCK_SEND path data` instead when set, exit 0 for sent); the error,
none when it went. -/
def send (path data : String) : m (Option String) := do
  match ← env "SWARM_SOCK_SEND" with
  | some cmd =>
    let o ← Sys.exec [cmd, path, data] {}
    let e := strip (o.stderr ++ o.stdout)
    return if o.code == 0 then none else some (if e == "" then s!"exit {o.code}" else e)
  | none => Sys.udsSend path data

/-- Sends `text` to `name`'s recorded socket when it is still the one recorded (same mtime: a reused pid's socket is
another); none when sent. Without a record, `some ""`; on a failure the error, the record dropped (`failed`). -/
def post (name text : String) : m (Option String) := do
  let some v ← Store.txn [.«meta»] fun db => (db, (db.getMeta (key name)).bind (·.v)) | return some ""
  let err ← match parse v with
    | none => pure (some "unreadable record")
    | some (mt, path) => if (← Sys.mtime path) != some mt then pure (some "socket gone or replaced") else send path (frame text)
  let some e := err | return none
  let envComms ← env "SWARM_COMMS"
  let now ← Clock.now
  Store.txn [.«meta», .event, .agent, .msg, .cursor] fun db => (failed db now name v e (Agents.commsOf db envComms), ())
  return some e

/-- Records the calling session's socket for `name` when this terminal holds its live row (an inherited variable in
another terminal records nothing): only a new record, checked first by connecting and writing the auth line; a record
that failed before is not retried. -/
def record (name : String) : m Unit := do
  let some path ← env "CLAUDE_CODE_MESSAGING_SOCKET" | return
  let here ← env "HC_TERMINAL_ID"
  let some mt ← Sys.mtime path | return
  let v := s!"{mt} {path}"
  let new ← Store.view [Sels.agent name, Sels.metas [key name, badKey name]] fun db =>
    here.isSome && (db.agent name).any (fun r => r.ended.isNone && r.hc == here) &&
    ((db.getMeta (key name)).bind (·.v)) != some v && ((db.getMeta (badKey name)).bind (·.v)) != some v
  if !new then return
  let auth := match ← env "CLAUDE_CODE_MESSAGING_TOKEN" with
    | some t => (Json.mkObj [("type", "auth"), ("token", t)]).compress ++ "\n"
    | none => ""
  let err ← send path auth
  let envComms ← env "SWARM_COMMS"
  let now ← Clock.now
  -- every hook runs this: keyed reads, the event and a message inserted (`failed` reads its records and comms)
  Store.run (Txn.update [Sels.metas [key name, badKey name, "comms"]] [.msg] fun db => (match err with
    | none => (db.setMeta (key name) (some v)).log now (some name) "sock" (some v) none
    | some e => failed db now name v e (Agents.commsOf db envComms), ()))

/-- watchd's start: each recorded socket of a live agent still there and connecting (nothing written), else dropped
(`failed`). -/
def checkAll : m Unit := do
  let recs ← Store.txn [.agent, .«meta»] fun db => (db, db.agents.filterMap fun a =>
    if a.ended.isSome then none else ((db.getMeta (key a.name)).bind (·.v)).map (a.name, ·))
  for (name, v) in recs do
    let err ← match parse v with
      | none => pure (some "unreadable record")
      | some (mt, path) => if (← Sys.mtime path) != some mt then pure (some "socket gone or replaced") else send path ""
    if let some e := err then
      let envComms ← env "SWARM_COMMS"
      let now ← Clock.now
      Store.txn [.«meta», .event, .agent, .msg, .cursor] fun db => (failed db now name v e (Agents.commsOf db envComms), ())

end SwarmLean.Sock
