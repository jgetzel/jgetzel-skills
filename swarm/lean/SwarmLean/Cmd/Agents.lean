import SwarmLean.Cmd
import SwarmLean.Cmd.AgentsHelp
import SwarmLean.Lib.Agents
import SwarmLean.Lib.Hook
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Spawn
import SwarmLean.Lib.Lifecycle
import SwarmLean.Lib.Swarms

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
def staySpec : Spec := .mk "stay" helpStay [many "text"] [flag "--end", opt "--until"] [] [] none
/-- `swarm limits`'s parser. -/
def limitsSpec : Spec := .mk "limits" helpLimits []
  [opt "--min" none (some int), opt "--max" none (some int), { opt "--queue-only" with choices := ["on", "off"] },
   opt "--ctx-nudge" none (some int), opt "--ctx-compact" none (some int),
   { opt "--compact-stayers" with choices := ["on", "off"] }, opt "--reuse-below" none (some int)] [] [] none
/-- `swarm away`'s parser. -/
def awaySpec : Spec := .mk "away" helpAway [many "note"] [flag "--back"] [] [] none
/-- `swarm spawn`'s parser. -/
def spawnSpec : Spec :=
  .mk "spawn" helpSpawn [{ name := "name" }, many "task"]
    [opt "--model" (some "sonnet"), { opt "--effort" with choices := ["low", "medium", "high", "xhigh", "max"] }, opt "--stay",
     { opt "--task" none (some int) with target := "task_id" }, opt "--role", opt "--attach", opt "--base", flag "--full"] [] [] none
/-- `swarm end`'s parser. -/
def endSpec : Spec := .mk "end" helpEnd [{ name := "agent" }] [flag "--force"] [] [] none
/-- `swarm endable`'s parser. -/
def endableSpec : Spec := .mk "endable" helpEndable [maybe "agent"] [flag "--why"] [] [] none
/-- `swarm new`'s parser. -/
def newSpec : Spec := .mk "new" helpNew [{ name := "name" }] [{ opt "--repo" with maxCount := 1000000 }, opt "--comms"] [] [] none
/-- `swarm swarms`'s parser. -/
def swarmsSpec : Spec := .mk "swarms" helpSwarms [] [] [] [] none
/-- `swarm who`'s parser. -/
def whoSpec : Spec := .mk "who" helpWho [] [] [] [] none
/-- `swarm machine`'s parser. -/
def machineSpec : Spec := .mk "machine" helpMachine [] [] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- A fenced step's value, or die with the fence. -/
def unfence (name : String) : Except Fence α → m α
  | .ok a => pure a
  | .error f => do die (← fenceText name f)

/-- The swarm a terminal's hc label `swarm` names, if any (`join` sets it). -/
def hcSwarm (addr : String) : m (Option String) := do
  let o ← Proc.output ["hc", "get", addr] none []
  let j := match o with | some o => if o.code == 0 then (Lean.Json.parse o.stdout).toOption else none | none => none
  let l := (j.bind fun j => (j.getObjVal? "labels").toOption).getD .null
  return (l.getObjValAs? String "swarm").toOption

/-- Binds `name` to terminal `hc` (agents.bind): a live binding elsewhere moves only with `takeover`. -/
def bindAgent (name : String) (cwd hc model : Option String) (takeover : Bool) : m Unit := do
  orDie (agentName name)
  let r ← Store.view [Sels.agent name] (binding · name)
  if let some old := boundTo r then
    if some old != hc && !takeover then
      let live := match ← hcTerminals with
        | none => true
        | some ts => ts.any fun x => x.state == some "live" && x.address == some old
      if live then
        die s!"{name} is bound to {old}; this terminal is {hc.getD "outside Herdr"}. `swarm join --takeover` moves it here."
  let now ← Clock.now
  orDie (← Store.run (Txn.update [Sels.agent name, Sels.cursor name] [.msg] (bind · name cwd hc model r now)))

/-- `swarm join [name] [--model M] [--takeover]` (agents.cmd_join): binds the agent to this terminal in the swarm this
process acts on (sw-global §2), its row moved there; a communicator `<x>-comms` with no `$SWARM`, row or label makes
(or joins) swarm `x`, even while another swarm is the only live one. Labels the terminal `swarm=<name>`. -/
def join (a : Parsed) : m UInt32 := do
  let n ← match a.str "name" with | some n => pure n | none => me
  orDie (agentName n)
  let here ← env "HC_TERMINAL_ID"
  -- a communicator `<x>-comms` with no swarm given, no row and no label naming one makes swarm `x`, or joins it,
  -- before the "only live swarm" fallback: another live swarm is not its own
  if let some x := Swarms.ofComms n then
    let sws ← Swarms.list
    let byLabel ← match here with
      | some h => pure ((← hcSwarm h).any fun s => sws.any (·.name == s))
      | none => pure false
    if (← env "SWARM").isNone && (← Swarms.ofAgent n).isNone && !byLabel then
      let some sx := SwarmName.parse? x | die s!"not a swarm name: '{x}' (from {n}; 1-32 of a-z 0-9 - _, not 'all')"
      let repo ← Workspaces.main none
      let base ← match repo with | some r => pure (some (← Bases.default (some r))) | none => pure none
      discard <| Swarms.create sx (some n) (repo.toList.map (·, base)) (← Clock.now)
      Sys.setenv "SWARM" x
  Store.view [] fun _ => ()  -- resolves the swarm (or refuses), which the store exports as $SWARM
  if let (some h, some cur) := (here, ← env "SWARM") then
    if let some s ← hcSwarm h then
      if s != cur && !a.flag "takeover" then
        die s!"this terminal is in swarm {s}. `swarm join --takeover` moves it to {cur}."
  bindAgent n (some (← Env.cwd)) here (a.str "model") (a.flag "takeover")
  let sw ← env "SWARM"  -- exported by the store once its first transaction resolved it
  if let (some h, some s) := (here, sw) then discard <| Proc.output ["hc", "label", h, "swarm=" ++ s] none []
  let now ← Clock.now
  let envComms ← env "SWARM_COMMS"
  Store.run (Txn.update [Sels.metas ["comms", "comms_hc"]] [] fun db =>
    -- the communicator in a Herdr terminal: watchd keeps one there (`ensureComms`)
    let db := match here with
      | some h => if isComms db envComms (some n) then db.setMeta "comms_hc" (some h) else db
      | none => db
    (db.log now (some n) "join" none none, ()))
  return 0

/-- `swarm leave [name]` (agents.cmd_leave). -/
def leaveCmd (a : Parsed) : m UInt32 := do
  let n ← match a.str "name" with | some n => pure n | none => me
  let now ← Clock.now
  Store.run (Txn.update (Sels.release n) [] fun db => (leave db n now, ()))
  return 0

/-- `swarm role [text…]` (agents.cmd_role). -/
def roleCmd (a : Parsed) : m UInt32 := do
  let n ← me
  let text := a.strs "text"
  if text.isEmpty then
    let r ← Store.view [Sels.agent n] fun db => (db.agent n).bind (·.role)
    Env.out (r.getD "(none)")
    return 0
  let cwd ← Env.cwd
  let here ← env "HC_TERMINAL_ID"
  let now ← Clock.now
  let same ← unfence n (← Store.run (Sels.onAgent n (role · n (some cwd) here (" ".intercalate text) now) [Sels.live]))
  for s in same do Env.out s
  return 0

/-- `swarm stay --end NAME`: the user or the communicator clears another agent's stay (agents.end_stay). -/
def endStayCmd (n : String) : m UInt32 := do
  let me := (← env "SWARM_NAME").getD HUMAN
  let envComms ← env "SWARM_COMMS"
  if !(← Store.view [Sels.metas ["comms"]] (inCharge · envComms me)) then
    die "only human or the communicator ends another agent's stay"
  let now ← Clock.now
  orDie (← Store.run (Txn.update [Sels.agent n] [] (endStay · me n now)))
  Env.out s!"{n}'s stay ended: watchd ends it once it is idle, holds nothing and its work is on its base."
  return 0

/-- `swarm stay [text…] [--end]` (agents.cmd_stay). -/
def stayCmd (a : Parsed) : m UInt32 := do
  let text := a.strs "text"
  let isEnd := a.flag "end"
  if isEnd then
    if let h :: _ := text then return ← endStayCmd h
  let n ← me
  if text.isEmpty && !isEnd then
    let s ← Store.view [Sels.agent n] (stayOf · n)
    Env.out (match s with
      | some s => s!"you stay for '{s}'"
      | none => "you stay for nothing: watchd ends you once idle, holding nothing, work landed")
    return 0
  let v := if isEnd then none else some (oneLine (" ".intercalate text))
  if v == some "" then die "say what you wait for: swarm stay \"<what>\""
  let cond ← match a.str "until" with
    | none => pure none
    | some u => match StayCond.parse? u with
      | some c => pure (some c)
      | none => die s!"bad --until '{u}': one of job:<id>, task:<id>, msg:<agent>, ci, time:<HH:MM> (UTC)"
  if isEnd && cond.isSome then die "--until goes with a stay, not --end"
  let here ← env "HC_TERMINAL_ID"
  let now ← Clock.now
  unfence n (← Store.run (Sels.onAgent n fun db =>
    let (db, r) := stay db n here v now
    match r, cond with
    | .ok _, some c => (db.log now (some n) "stay-until" (some c.text) v, r)
    | _, _ => (db, r)))
  Env.out (match v with
    | some v => match cond with
      | some c => s!"you stay for '{v}' until {c}; watchd wakes you then, and won't end you before. `swarm stay --end` if it is over sooner."
      | none => s!"you stay for '{v}'; watchd won't end you. Name the wait, not the plan: with a condition, `swarm stay \"<why>\" --until <job:<id>|task:<id>|msg:<agent>|ci|time:HH:MM>`. `swarm stay --end` when it is over."
    | none => "stay ended: watchd ends you once you are idle, hold nothing and your work is on your task's base.")
  return 0

/-- What `swarm limits` was asked to set. -/
structure LimitsReq where
  min : Option Int := none
  max : Option Int := none
  queueOnly : Option Bool := none
  nudge : Option Int := none
  compact : Option Int := none
  stayers : Option Bool := none
  reuse : Option Int := none

/-- `swarm limits`'s flags as one request, every one checked before anything is set. -/
def limitsReq (a : Parsed) : Except String LimitsReq := do
  let q : LimitsReq :=
    { min := a.int "min", max := a.int "max", queueOnly := (a.str "queue_only").map (· == "on")
      nudge := a.int "ctx_nudge", compact := a.int "ctx_compact", stayers := (a.str "compact_stayers").map (· == "on")
      reuse := a.int "reuse_below" }
  if q.nudge.any (· < 0) || q.compact.any (· < 0) || q.reuse.any (· < 0) then throw "a context threshold is tokens, 0 for off"
  pure q

/-- The meta keys `swarm limits` reads and sets. -/
def LIMITS_KEYS : List String := Sels.LIMIT_KEYS ++ ["ctx_nudge", "ctx_compact", "compact_stayers", "reuse_below"]

/-- `swarm limits` by `me` as one step: sets what `q` asks (all or nothing: an auto-spawn number above the max refuses
the whole request) and returns the three lines it prints. -/
def limitsStep (envComms : Option String) (me : String) (q : LimitsReq) (now : Int) (db : Db) : Db × Except String String :=
  let (db', r) := if q.min.isSome || q.max.isSome then setLimits db envComms me q.min q.max now else (db, .ok ())
  match r with
  | .error e => (db, .error e)
  | .ok () =>
    let db := db'
    let db := match q.queueOnly with | some b => setQueueOnly db me b now | none => db
    let db := if q.nudge.isSome || q.compact.isSome || q.stayers.isSome then
      Compact.setLimits db me q.nudge q.compact q.stayers now else db
    let db := match q.reuse with | some r => Reuse.setBelow db me r now | none => db
    (db, .ok (limitsLine db envComms ++ "\n" ++ Compact.limitsLine db ++ "\n" ++ Reuse.limitsLine db))

/-- `swarm limits [--min N] [--max M] [--queue-only on|off] [--ctx-nudge N] [--ctx-compact N] [--compact-stayers on|off]
[--reuse-below N]` (agents.cmd_limits): every flag checked, then one transaction. -/
def limitsCmd (a : Parsed) : m UInt32 := do
  let q ← orDie (limitsReq a)
  let envComms ← env "SWARM_COMMS"
  let me := (← env "SWARM_NAME").getD HUMAN
  let now ← Clock.now
  Env.out (← orDie (← Store.run (Txn.update [Sels.live, Sels.metas LIMITS_KEYS] [] (limitsStep envComms me q now))))
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
    l := l ++ [s!"  #{q.id} {q.owner.getD "-"} ({← Clock.hhmm (q.since.getD now)}): {cont (q.question.getD "?")}  [{cont (q.title.getD "")}]"]
  let list (head : String) (xs : List String) : List String := if xs.isEmpty then [] else [head ++ ", ".intercalate xs]
  l := l ++ list "finished: " (g.done.map fun r => s!"#{r.id} {cont (r.title.getD "")}")
  l := l ++ list "merged: " (g.merged.map fun r => s!"PR #{(r.pr.map d).getD "?"} (#{r.id})")
  l := l ++ ["main CI: " ++ match g.ci with
    | some c => s!"{(c.conclusion.orElse fun _ => c.status).getD "?"} {String.ofList ((c.sha.getD "").toList.take 7)}"
    | none => "no run seen"]
  l := l ++ list "ended: " (g.ended.map fun (n, _, why) => n ++ match why with | some w => s!" ({w})" | none => "")
  l := l ++ list "hung: " g.hung
  return "\n".intercalate l

/-- The task an event's data names: `#id` or `#id …` (`namesTask`). -/
def taskOf (data : Option String) : Option Nat :=
  match (data.getD "").toList with
  | '#' :: rest =>
    let ds := rest.takeWhile Char.isDigit
    let tail := rest.drop ds.length
    if ds.isEmpty || !(tail.isEmpty || tail.head? == some ' ') then none else (String.ofList ds).toNat?
  | _ => none

#guard taskOf (some "#12 title") == some 12
#guard taskOf (some "#12") == some 12
#guard taskOf (some "#12x") == none
#guard taskOf (some "12") == none

/-- `swarm away --back` by `me` (`goBack`): the flag and the away event first, then what the digest reads of what
happened since: the events after it and every block, the tasks they name or blocked or merged since, the agents they
name, and the CI runs. -/
def backTxn (envComms : Option String) (me : String) (now : Int) : Txn (Option Digest) := do
  let flag := [Sels.metas ["away", "away_digest", "comms"], { table := .event, cond := .eq "kind" (.text "away"), last := some 1 }]
  let d ← Txn.slice flag
  let some (since, _) := away d | pure none
  let «from» := (d.events.map (·.id)).max?.getD 0
  let evs : Sel := { table := .event, cond := .or (.gt "id" (.int «from»)) (.oneOf "kind" [.text "block", .text "task-blocked"]) }
  let later := (← Txn.slice [evs]).events.filter (·.id > «from»)
  let ids := (later.filter (·.kind == some "done")).filterMap (taskOf ·.data)
  let names := ((later.filter fun e => [some "reap", some "leave", some "end", some "stay-hung"].contains e.kind).filterMap (·.agent)).eraseDups
  let merged : Cond := match since with | some s => .gt "merged_at" (.int (s - 1)) | none => .oneOf "id" []
  let tasks : Cond := .or (.eq "state" (.text "blocked")) (.or (.oneOf "id" (ids.map fun i => .int (Int.ofNat i))) merged)
  Txn.update (flag ++ [evs, { table := .task, cond := tasks }, { table := .agent, cond := .oneOf "name" (names.map .text) },
      { table := .ci }]) [.msg]
    fun db => goBack db me (commsName db envComms) now

/-- `swarm away [note…] | --back` (agents.cmd_away). -/
def awayCmd (a : Parsed) : m UInt32 := do
  let me := (← env "SWARM_NAME").getD HUMAN
  let envComms ← env "SWARM_COMMS"
  let now ← Clock.now
  if a.flag "back" then
    let g ← Store.run (backTxn envComms me now)
    Env.out (← match g with | some g => digestText g | none => pure "you were not away")
    return 0
  let note := strip (" ".intercalate (a.strs "note"))
  let line ← Hook.awayLine (some now, if note == "" then none else some note)
  let was ← Store.run (Txn.update [Sels.metas ["away", "away_digest", "comms"]] [.msg] fun db =>
    goAway db me (commsName db envComms) note line now)
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
  -- the live agents, the staffing knobs, the worktrees, and the locks the live agents hold
  let db ← Store.run do
    let d0 ← Txn.slice [Sels.live]
    Txn.slice [Sels.live, Sels.metas Sels.LIMIT_KEYS, { table := .lock, cond := .oneOf "agent" (d0.agents.map fun x => .text x.name) },
      { table := .workspace }]
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
                stay := a.str "stay", taskId := a.int "task_id", role := a.str "role", attach := a.str "attach", base := a.str "base", full := a.flag "full",
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
  if !(← Store.view [Sels.metas ["comms"]] (inCharge · envComms me)) then
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

/-- `swarm new <name> [--repo P]… [--comms C]`: makes swarm `name` with the repos its auto-spawn staffs from (each a
path in a git repo: its main worktree). -/
def newCmd (a : Parsed) : m UInt32 := do
  let some n := a.str "name" | die "usage: swarm new <name> [--repo P]... [--comms C]"
  let some sn := SwarmName.parse? n | die s!"not a swarm name: '{n}' (1-32 of a-z 0-9 - _, not 'all')"
  if let some c := a.str "comms" then orDie (agentName c)
  let mut repos : List (String × Option String) := []
  for p in a.strs "repo" do
    let some r ← Workspaces.main (some p) | die s!"not in a git repo: {p}"
    repos := repos ++ [(r, some (← Bases.default (some r)))]
  if !(← Swarms.create sn (a.str "comms") repos (← Clock.now)) then die s!"swarm {n} exists"
  Env.out s!"swarm {n}{if repos.isEmpty then "" else " (" ++ ", ".intercalate (repos.map (·.1)) ++ ")"}"
  return 0

/-- `swarm swarms`: the machine's swarms, each with its communicator, repos and live agents. -/
def swarmsCmd : m UInt32 := do
  let l ← Swarms.list
  if l.isEmpty then Env.out "(no swarms: `swarm new <name>`)"
  for r in l do
    let st := if r.ended.isSome then " (ended)" else ""
    Env.out s!"{r.name}{st}  comms {r.comms.getD "-"}  {r.live.length} live{if r.live.isEmpty then "" else ": " ++ ", ".intercalate r.live}  repos: {if r.repos.isEmpty then "-" else ", ".intercalate r.repos}"
  return 0

/-- `swarm machine` (machine.cmd_machine). -/
def machineCmd : m UInt32 := do
  Env.out (← Machine.note)
  return 0

/-- The group. -/
def group : Group m where
  specs := [("spawn", spawnSpec), ("join", joinSpec), ("end", endSpec), ("endable", endableSpec), ("leave", leaveSpec), ("role", roleSpec), ("stay", staySpec), ("limits", limitsSpec),
    ("away", awaySpec), ("who", whoSpec), ("machine", machineSpec), ("new", newSpec), ("swarms", swarmsSpec)]
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
    | "new" => newCmd a
    | "swarms" => swarmsCmd
    | _ => machineCmd

end SwarmLean.Cmd.Agents
