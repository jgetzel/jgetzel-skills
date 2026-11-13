import SwarmLean.Cmd
import SwarmLean.Cmd.AgentsHelp
import SwarmLean.Lib.Agents
import SwarmLean.Lib.Hook
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Spawn
import SwarmLean.Lib.Lifecycle

/-! `swarm join`, `leave`, `role`, `stay`, `limits`, `away`, `who` and `machine` (agents.lua's commands and
machine.cmd_machine). -/

namespace SwarmLean.Cmd.Agents
open Args _root_.SwarmLean.Agents

/-- A `*` positional. -/
def many (name : String) : Pos := { name, minArgs := 0, maxArgs := 1000000 }

/-- A `?` positional. -/
def maybe (name : String) : Pos := { name, minArgs := 0 }

/-- The parsers, as main.lua declares them. -/
def joinSpec : Spec := .mk "join" helpJoin [maybe "name"] [opt "--model", flag "--takeover"] [] [] none
/-- `swarm leave`'s parser. -/
def leaveSpec : Spec := .mk "leave" helpLeave [maybe "name"] [] [] [] none
/-- `swarm role`'s parser. -/
def roleSpec : Spec := .mk "role" helpRole [many "text"] [] [] [] none
/-- `swarm stay`'s parser. -/
def staySpec : Spec := .mk "stay" helpStay [many "text"] [flag "--end"] [] [] none
/-- `swarm limits`'s parser. -/
def limitsSpec : Spec := .mk "limits" helpLimits []
  [opt "--min" none (some int), opt "--max" none (some int), { opt "--queue-only" with choices := ["on", "off"] },
   opt "--ctx-nudge" none (some int), opt "--ctx-compact" none (some int),
   { opt "--compact-stayers" with choices := ["on", "off"] }] [] [] none
/-- `swarm away`'s parser. -/
def awaySpec : Spec := .mk "away" helpAway [many "note"] [flag "--back"] [] [] none
/-- `swarm spawn`'s parser. -/
def spawnSpec : Spec :=
  .mk "spawn" helpSpawn [{ name := "name" }, many "task"]
    [opt "--model" (some "sonnet"), { opt "--effort" with choices := ["low", "medium", "high", "xhigh", "max"] }, opt "--stay",
     { opt "--task" none (some int) with target := "task_id" }, opt "--role", opt "--attach"] [] [] none
/-- `swarm end`'s parser. -/
def endSpec : Spec := .mk "end" helpEnd [{ name := "agent" }] [flag "--force"] [] [] none
/-- `swarm endable`'s parser. -/
def endableSpec : Spec := .mk "endable" helpEndable [maybe "agent"] [flag "--why"] [] [] none
/-- `swarm who`'s parser. -/
def whoSpec : Spec := .mk "who" helpWho [] [] [] [] none
/-- `swarm machine`'s parser. -/
def machineSpec : Spec := .mk "machine" helpMachine [] [] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- A fenced step's value, or die with the fence. -/
def unfence (name : String) : Except Fence α → m α
  | .ok a => pure a
  | .error f => do die (← fenceText name f)

/-- The labels hc keeps on a terminal: its Herdr space and the db it is the communicator of (agents.hc_info). -/
def hcInfo (addr : String) : m (Option String × Option String) := do
  let o ← Proc.output ["hc", "get", addr] none []
  let j := match o with | some o => if o.code == 0 then (Lean.Json.parse o.stdout).toOption else none | none => none
  let l := (j.bind fun j => (j.getObjVal? "labels").toOption).getD .null
  return ((l.getObjValAs? String "herdr.space").toOption, (l.getObjValAs? String "swarm.comms").toOption)

/-- Binds `name` to terminal `hc` (agents.bind): a live binding elsewhere moves only with `takeover`. -/
def bindAgent (name : String) (cwd hc model : Option String) (takeover : Bool) : m Unit := do
  orDie (notHuman name)
  let r ← Store.txn [.agent] fun db => (db, binding db name)
  if let some old := boundTo r then
    if some old != hc && !takeover then
      let live := match ← hcTerminals with
        | none => true
        | some ts => ts.any fun x => x.state == some "live" && x.address == some old
      if live then
        die s!"{name} is bound to {old}; this terminal is {hc.getD "outside Herdr"}. `swarm join --takeover` moves it here."
  let now ← Clock.now
  orDie (← Store.txn [.agent, .cursor] (bind · name cwd hc model r now))

/-- `swarm join [name] [--model M] [--takeover]` (agents.cmd_join). -/
def join (a : Parsed) : m UInt32 := do
  let n ← match a.str "name" with | some n => pure n | none => me
  let here ← env "HC_TERMINAL_ID"
  let envComms ← env "SWARM_COMMS"
  let isC ← match here with
    | some _ => Store.txn [.«meta»] fun db => (db, isComms db envComms (some n))
    | none => pure false
  if let (true, some h) := (isC, here) then
    let (space, comms) ← hcInfo h
    let sp ← Store.txn [.«meta»] fun db => (db, (db.getMeta "space").bind (·.v))
    if let (some sp, some i) := (sp, space) then
      if i != sp then die s!"{n} is the communicator of a swarm in space {sp}; this terminal is in space {i}."
    if let some c := comms then
      if c != (← Spawn.dbPath) && !a.flag "takeover" then
        die s!"this terminal is the communicator of another swarm ({c}). `swarm join --takeover` takes it for this one."
  bindAgent n (some (← Env.cwd)) here (a.str "model") (a.flag "takeover")
  let mut space := none
  if let (true, some h) := (isC, here) then
    discard <| Proc.output ["hc", "label", h, "swarm.comms=" ++ (← Spawn.dbPath)] none []
    space := (← hcInfo h).1
  let now ← Clock.now
  Store.txn [.«meta»] fun db =>
    let db := match space with
      | some sp => if (db.getMeta "space").isSome then db else db.setMeta "space" (some sp)
      | none => db
    (db.log now (some n) "join" none none, ())
  return 0

/-- `swarm leave [name]` (agents.cmd_leave). -/
def leaveCmd (a : Parsed) : m UInt32 := do
  let n ← match a.str "name" with | some n => pure n | none => me
  let now ← Clock.now
  Store.txn [.agent, .task, .lock, .conflict, .pairkey] fun db => (leave db n now, ())
  return 0

/-- `swarm role [text…]` (agents.cmd_role). -/
def roleCmd (a : Parsed) : m UInt32 := do
  let n ← me
  let text := a.strs "text"
  if text.isEmpty then
    let r ← Store.txn [.agent] fun db => (db, (db.agent n).bind (·.role))
    Env.out (r.getD "(none)")
    return 0
  let cwd ← Env.cwd
  let here ← env "HC_TERMINAL_ID"
  let now ← Clock.now
  let same ← unfence n (← Store.txn [.agent, .cursor, .event] (role · n (some cwd) here (" ".intercalate text) now))
  for s in same do Env.out s
  return 0

/-- `swarm stay --end NAME`: the user or the communicator clears another agent's stay (agents.end_stay). -/
def endStayCmd (n : String) : m UInt32 := do
  let me := (← env "SWARM_NAME").getD HUMAN
  let envComms ← env "SWARM_COMMS"
  if !(← Store.txn [.«meta»] fun db => (db, inCharge db envComms me)) then
    die "only human or the communicator ends another agent's stay"
  let now ← Clock.now
  orDie (← Store.txn [.agent] (endStay · me n now))
  Env.out s!"{n}'s stay ended: watchd ends it once it is idle, holds nothing and its work is on its base."
  return 0

/-- `swarm stay [text…] [--end]` (agents.cmd_stay). -/
def stayCmd (a : Parsed) : m UInt32 := do
  let text := a.strs "text"
  let isEnd := a.flag "end"
  if isEnd && !text.isEmpty then return ← endStayCmd text.head!
  let n ← me
  if text.isEmpty && !isEnd then
    let s ← Store.txn [.agent] fun db => (db, stayOf db n)
    Env.out (match s with
      | some s => s!"you stay for '{s}'"
      | none => "you stay for nothing: watchd ends you once idle, holding nothing, work landed")
    return 0
  let v := if isEnd then none else some (oneLine (" ".intercalate text))
  if v == some "" then die "say what you wait for: swarm stay \"<what>\""
  let here ← env "HC_TERMINAL_ID"
  let now ← Clock.now
  unfence n (← Store.txn [.agent, .cursor, .event] (stay · n here v now))
  Env.out (match v with
    | some v => s!"you stay for '{v}'; watchd won't end you. `swarm stay --end` when it is over."
    | none => "stay ended: watchd ends you once you are idle, hold nothing and your work is on your task's base.")
  return 0

/-- `swarm limits [--min N] [--max M]` (agents.cmd_limits). -/
def limitsCmd (a : Parsed) : m UInt32 := do
  let envComms ← env "SWARM_COMMS"
  let mn := a.int "min"
  let mx := a.int "max"
  if mn.isSome || mx.isSome then
    let me := (← env "SWARM_NAME").getD HUMAN
    let now ← Clock.now
    orDie (← Store.txn [.agent, .«meta»] (setLimits · envComms me mn mx now))
  if let some q := a.str "queue_only" then
    let me := (← env "SWARM_NAME").getD HUMAN
    let now ← Clock.now
    Store.txn [.«meta»] fun db => (setQueueOnly db me (q == "on") now, ())
  let cn := a.int "ctx_nudge"
  let cc := a.int "ctx_compact"
  let cs := (a.str "compact_stayers").map (· == "on")
  if cn.any (· < 0) || cc.any (· < 0) then die "a context threshold is tokens, 0 for off"
  if cn.isSome || cc.isSome || cs.isSome then
    let me := (← env "SWARM_NAME").getD HUMAN
    let now ← Clock.now
    Store.txn [.«meta», .event] fun db => (Compact.setLimits db me cn cc cs now, ())
  Env.out (← Store.txn [.agent, .«meta»] fun db => (db, limitsLine db envComms ++ "\n" ++ Compact.limitsLine db))
  return 0

/-- The communicator's name: meta comms when set and not empty, else $SWARM_COMMS (agents.comms_name). -/
def commsName (db : Db) (envComms : Option String) : Option String :=
  match db.getMeta "comms" with
  | some { v := some v, .. } => if v != "" then some v else envComms
  | _ => envComms

/-- The digest as `swarm away --back` prints it (agents.digest_text). -/
def digestText (g : Digest) : m String := do
  let now ← Clock.now
  let since ← Clock.hhmm (g.since.getD now)
  let mut l := [s!"back: away since {since}{match g.note with | some n => s!" ({n})" | none => ""}, {ago now (g.since.getD 0)}"]
  let nq := g.questions.length
  l := l ++ [if nq == 0 then "no questions wait" else s!"{nq} question{if nq == 1 then "" else "s"} wait, oldest first:"]
  for q in g.questions do
    l := l ++ [s!"  #{q.id} {q.owner.getD "-"} ({← Clock.hhmm (q.since.getD now)}): {q.question.getD "?"}  [{q.title.getD ""}]"]
  let list (head : String) (xs : List String) : List String := if xs.isEmpty then [] else [head ++ ", ".intercalate xs]
  l := l ++ list "finished: " (g.done.map fun r => s!"#{r.id} {r.title.getD ""}")
  l := l ++ list "merged: " (g.merged.map fun r => s!"PR #{(r.pr.map d).getD "?"} (#{r.id})")
  l := l ++ ["main CI: " ++ match g.ci with
    | some c => s!"{(c.conclusion.orElse fun _ => c.status).getD "?"} {String.ofList ((c.sha.getD "").toList.take 7)}"
    | none => "no run seen"]
  l := l ++ list "ended: " (g.ended.map fun (n, _, why) => n ++ match why with | some w => s!" ({w})" | none => "")
  l := l ++ list "hung: " g.hung
  return "\n".intercalate l

/-- `swarm away [note…] | --back` (agents.cmd_away). -/
def awayCmd (a : Parsed) : m UInt32 := do
  let me := (← env "SWARM_NAME").getD HUMAN
  let envComms ← env "SWARM_COMMS"
  let now ← Clock.now
  if a.flag "back" then
    let g ← Store.txn [.«meta», .event, .task, .agent, .ci] fun db => goBack db me (commsName db envComms) now
    Env.out (← match g with | some g => digestText g | none => pure "you were not away")
    return 0
  let note := strip (" ".intercalate (a.strs "note"))
  let line ← Hook.awayLine (some now, if note == "" then none else some note)
  let was ← Store.txn [.«meta»] fun db => goAway db me (commsName db envComms) note line now
  match was with
  | some (since, _) => Env.out s!"already away since {← Clock.hhmm (since.getD now)}"
  | none => Env.out s!"away{if note != "" then ": " ++ note else ""}; questions wait for you, work goes on"
  return 0

/-- Something is at `p` (lfs.attributes). -/
def exists_ (p : String) : m Bool := return (← Sys.kind p true) != .none

/-- A notice when install.sh's Herdr copies predate this checkout's herdr-mods (agents.herdr_stale). -/
def herdrStale : m (Option String) := do
  let home := (← Env.var "HERDR_APP_HOME").getD (((← Env.var "HOME").getD "") ++ "/.config/herdr-app")
  let some here ← Spawn.swarmHere | return none
  if !((← exists_ (home ++ "/mods/jgetzel-tabs")) || (← exists_ (home ++ "/mods/swarm-tabs"))) then return none
  let stamp := strip ((← Fs.read (home ++ "/jgetzel-install.stamp")).getD "")
  let o ← Proc.output ["sh", "-c", herdrStampCmd]
    (some (here ++ "/../herdr-mods")) []
  match o with
  | some o => if o.code == 0 && String.ofList ((strip o.stdout).toList.take 64) != stamp then
      return some "herdr panel: out of date: run install.sh" else return none
  | none => return none

/-- `swarm who` (agents.cmd_who). -/
def who : m UInt32 := do
  let t ← Clock.now
  let db ← Store.txn [.agent, .«meta», .lock, .workspace] fun db => (db, db)
  let wts ← Workspaces.wtMap db
  Env.out (limitsLine db (← env "SWARM_COMMS"))
  if let some (avail, total, psi) ← Machine.mem then Env.out (Machine.line avail total psi)
  if let some s ← herdrStale then Env.out s
  let (here, gone) ← splitAgents db
  for x in gone do Env.out s!"{x.name} gone: no terminal; swarm join --takeover {x.name}"
  let mut seen : Seen := []
  for x in here do
    let k := fdiv (x.ctx_tokens.getD 0) 1000
    let (last, s1) ← sessionActive seen x t
    let (cold, s2) ← coldReason s1 x t
    seen := s2
    let snap := match x.snap with
      | some sn => if sn.startsWith "{" then (Lean.Json.parse sn).toOption else none
      | none => none
    let fs := match snap.map (·.getObjVal? "files") with
      | some (.ok (.arr a)) => a.toList.filterMap fun (j : Lean.Json) => j.getStr?.toOption
      | _ => []
    let lk := (db.locks.filter (·.agent == some x.name)).map (·.path)
    let mut l := s!"{x.name} {x.status.getD "nil"}{match x.role with | some r => " role=" ++ r | none => ""}{match x.stay with | some s => s!" stays: \"{s}\"" | none => ""} ctx={k}k idle={ago t last} cache={if t - last < COLD_IDLE then "warm" else "cold"}"
    l := l ++ (if cold.isSome then " COLD-GUARDED" else "") ++ " wt: " ++ ((wts.lookup x.name).map basename).getD "?"
    if !fs.isEmpty then
      l := l ++ " files: " ++ ", ".intercalate (fs.take 5) ++ (if fs.length > 5 then s!" +{fs.length - 5} more" else "")
    if !lk.isEmpty then l := l ++ " locks: " ++ ", ".intercalate lk
    Env.out l
  return 0

/-- `swarm spawn <name> [options] [-- <task>…]` (watchd.cmd_spawn). -/
def spawnCmd (a : Parsed) : m UInt32 := do
  let task := a.strs "task"
  Spawn.spawn { name := (a.str "name").getD "", model := (a.str "model").getD "sonnet", effort := a.str "effort",
                stay := a.str "stay", taskId := a.int "task_id", role := a.str "role", attach := a.str "attach",
                task := if task.head? == some "--" then task.tail else task }
  return 0

/-- `swarm endable [agent] [--why]`: exit 0 when nothing keeps the agent from being ended, else 1 (watchd.cmd_endable). -/
def endableCmd (a : Parsed) : m UInt32 := do
  let n ← match a.str "agent" with | some n => pure n | none => me
  let (db, f) ← Lifecycle.readsNow n
  let some row := (live db).find? (·.name == n) | die s!"{n} is not a live agent"
  let rs ← Lifecycle.endableReasons db row f
  if a.flag "why" then for r in rs do Env.out r.text
  return if rs.isEmpty then 0 else 1

/-- `swarm end <agent> [--force]`: the communicator's manual agent GC (watchd.cmd_end). -/
def endCmd (a : Parsed) : m UInt32 := do
  let me ← me
  let envComms ← env "SWARM_COMMS"
  if !(← Store.txn [.«meta»] fun db => (db, inCharge db envComms me)) then
    die "only the communicator or the user (`human`) ends agents"
  let n := (a.str "agent").getD ""
  let (db, f) ← Lifecycle.readsNow n
  let some row := (live db).find? (·.name == n) | die s!"{n} is not a live agent"
  let force := a.flag "force"
  if !force then
    if let some why ← Lifecycle.endWhy row f then die s!"{n} {why}; `swarm end {n} --force` ends it anyway."
  if !(← Lifecycle.endAgent row force (some me)) then die s!"{n} changed state; try again"
  Env.out s!"{n} ended"
  return 0

/-- `swarm machine` (machine.cmd_machine). -/
def machineCmd : m UInt32 := do
  Env.out (← Machine.note)
  return 0

/-- The group. -/
def group : Group m where
  specs := [("spawn", spawnSpec), ("join", joinSpec), ("end", endSpec), ("endable", endableSpec), ("leave", leaveSpec), ("role", roleSpec), ("stay", staySpec), ("limits", limitsSpec),
    ("away", awaySpec), ("who", whoSpec), ("machine", machineSpec)]
  run a := match a.cmd with
    | "spawn" => spawnCmd a
    | "join" => join a
    | "end" => endCmd a
    | "endable" => endableCmd a
    | "leave" => leaveCmd a
    | "role" => roleCmd a
    | "stay" => stayCmd a
    | "limits" => limitsCmd a
    | "away" => awayCmd a
    | "who" => who
    | _ => machineCmd

end SwarmLean.Cmd.Agents
