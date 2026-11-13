import SwarmLean.Cmd
import SwarmLean.Cmd.TasksHelp
import SwarmLean.Db.Queue
import SwarmLean.Lib.Machine

/-! `swarm task …`, `swarm board` and `swarm rules` (tasks.lua's cmd_task, cmd_board, cmd_rules). -/

namespace SwarmLean.Cmd.Tasks
open Args _root_.SwarmLean.Tasks Agents

/-- argparse's effort choices (main.lua's EFFORTS). -/
def EFFORTS : List String := ["low", "medium", "high", "xhigh", "max"]

/-- An `<id>` argument. -/
def idArg : Pos := { name := "id", conv := some int }

/-- `--lease` with its default. -/
def leaseOpt : Opt := opt "--lease" (some "2h")

/-- The `task` parser and its subcommands, as main.lua declares them. -/
def taskSpec : Spec :=
  .mk "task" helpTask [] [] [] (cmdTarget := some "act") (cmds := [
    .mk "add" helpTaskAdd [{ name := "title" }]
      [opt "--body" (some ""), opt "--body-file", opt "--after" none (some idList), opt "--model",
       { opt "--effort" with choices := EFFORTS }, { aliases := ["-p", "--priority"], target := "priority", conv := some prio },
       opt "--base"] [["body", "body_file"]] [] none,
    .mk "priority" helpTaskPriority [idArg, { name := "priority", conv := some prio }] [] [] [] none,
    .mk "after" helpTaskAfter [idArg, { name := "deps", minArgs := 0, conv := some idList }] [] [] [] none,
    .mk "claim" helpTaskClaim [idArg] [leaseOpt, flag "--force"] [] [] none,
    .mk "renew" helpTaskRenew [idArg] [leaseOpt] [] [] none,
    .mk "show" helpTaskShow [idArg] [] [] [] none,
    .mk "done" helpTaskDone [idArg] [{ opt "--evidence" with minCount := 1 }] [] [] none,
    .mk "block" helpTaskBlock [idArg, { name := "question" }] [] [] [] none,
    .mk "unblock" helpTaskUnblock [idArg] [opt "--answer" (some "")] [] [] none,
    .mk "release" helpTaskRelease [idArg] [opt "--after" none (some idList)] [] [] none,
    .mk "edit" helpTaskEdit [idArg]
      [opt "--title", opt "--body", opt "--body-file", opt "--append", opt "--model",
       { opt "--effort" with choices := EFFORTS }, flag "--urgent"] [["body", "body_file", "append"]] [] none,
    .mk "drop" helpTaskDrop [idArg] [] [] [] none,
    .mk "hold" helpTaskHold [idArg] [{ opt "--why" with minCount := 1 }] [] [] none,
    .mk "unhold" helpTaskUnhold [idArg] [] [] [] none])

/-- The `queue` parser: its words are the action and the ids, read by `queue`. -/
def queueSpec : Spec := .mk "queue" helpQueue [{ name := "words", minArgs := 0, maxArgs := 1000000 }]
  [flag "--front", opt "--before" none (some int), opt "--after" none (some int)] [["front", "before", "after"]] [] none

/-- The `rules` parser. -/
def rulesSpec : Spec :=
  .mk "rules" helpRules [] [] [] (cmdTarget := some "act") (cmds :=
    [.mk "show" helpRulesShow [] [] [] [] none, .mk "set" helpRulesSet [{ name := "text", maxArgs := 1000000 }] [] [] [] none])

/-- The `board` parser. -/
def boardSpec : Spec := .mk "board" helpBoard [] [flag "--all"] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m]

/-- The command's world: the agent, the time, the terminal, the communicator by env. -/
def ctx : m Tasks.Ctx := do
  return { me := ← me, now := ← Clock.now, here := ← env "HC_TERMINAL_ID", comms := ← env "SWARM_COMMS" }

/-- Runs a task step in one transaction over `ts`, dying with its error. -/
def step (ts : List Table) (f : Db → Db × Except String α) : m α := do orDie (← Store.txn ts f)

/-- `task show`'s text (tasks.lua's show branch). -/
def showText (db : Db) (r : Task) : m String := do
  let now ← Clock.now
  let evs := taskEvents db r.id
  let tm := timing r evs now
  let f (x : Option Int) : String := match x with | some v => s!"{fdiv v 60}m" | none => "-"
  let mut s := s!"#{d r.id} {r.state.text} {(py r.owner).getD "-"}  {r.title.getD ""}\ntiming: queue {f tm.queue_wait_s}, work {f tm.work_s}, total {f tm.total_s}, blocked {f (some tm.blocked_s)}, claims {tm.claims}, releases {tm.releases}, held by {(py (some (", ".intercalate tm.holders))).getD "-"}"
  for e in evs do
    if e.kind == some "task-edit" then
      let data := e.data.getD ""
      let ds := (data.drop 1).toString.toList.takeWhile Char.isDigit
      let data := if data.startsWith "#" && !ds.isEmpty && ((data.drop (1 + ds.length)).startsWith " ") then
        (data.drop (2 + ds.length)).toString else data
      s := s ++ s!"\nedited {← Clock.hhmm (e.ts.getD 0)} by {e.agent.getD ""}: {data}"
  s := s ++ "\npriority: P" ++ d (r.priority.getD DEFAULT_PRIORITY)
  if let some b := py r.base then s := s ++ "\nbase: " ++ b
  if let some q := r.qpos then s := s ++ s!"\nqueue: {q}"
  if let some h := r.hold then s := s ++ "\nheld: " ++ h
  if let some k := pyI tm.claim_ctx then s := s ++ s!", ctx {fdiv k 1000}k at claim"
  if let some k := pyI tm.done_ctx then s := s ++ s!" -> {fdiv k 1000}k at done"
  if let some ma := pyI tm.merged_at then
    s := s ++ s!"\nPR #{(tm.pr.map d).getD "None"} merged {← Clock.hhmm ma}, main CI {(py tm.ci_conclusion).getD "pending"}"
    if let some g := tm.merge_to_green_s then s := s ++ s!", green {fdiv g 60}m after merge"
  return s ++ depLines db r ++ "\n" ++ (py r.body).getD "(no body)" ++
    (match py r.answer with | some a => "\nAnswer to the block: " ++ a | none => "")

/-- `swarm task …`. -/
def task (a : Parsed) : m UInt32 := do
  let c ← ctx
  let id := (a.int "id").getD 0
  let out := Env.out (m := m)
  match a.act with
  | "add" =>
    let body ← match a.str "body_file" with
      | some p => match ← Fs.read p with
        | some t => pure t
        | none => die s!"can't read {p}"
      | none => pure ((a.str "body").getD "")
    let n ← step [.task] (add c { title := (a.str "title").getD "", body, deps := (a.ids "after").getD [],
                                    model := a.str "model", effort := a.str "effort", base := a.str "base", priority := a.int "priority" })
    out s!"task #{d n}"
  | "claim" =>
    let r ← step [.task, .agent, .cursor, .event, .«meta»] (claim { c with force := a.flag "force" } id ((a.str "lease").getD "2h"))
    out s!"claimed #{d id} until {← Clock.hhmm r.«until»}"
    if let some (avail, total, psi) ← Machine.mem then
      if Machine.pressureHigh avail total psi then
        out (← Machine.note)
      else out (Machine.line avail total psi)
    out (r.body.getD "(no body)")
  | "show" =>
    let db ← Store.txn [.task, .event] fun db => (db, db)
    let some r := db.find id | die s!"no task #{d id}"
    out (← showText db r)
  | "after" =>
    let deps := (a.ids "deps").getD []
    step [.task] (after c id deps)
    out s!"#{d id} after {(py (some (idsText deps))).getD "nothing"}"
  | "priority" =>
    let p := (a.int "priority").getD DEFAULT_PRIORITY
    step [.task] (priority c id p)
    out s!"#{d id} P{d p}"
  | "renew" =>
    let u ← step [.task] (renew c id ((a.str "lease").getD "2h"))
    out s!"renewed #{d id} until {← Clock.hhmm u}"
  | "done" =>
    match ← step [.task, .agent, .cursor, .«meta»] (Queue.done c id ((a.str "evidence").getD "")) with
    | .red => out s!"#{d id} stays yours until a green run: watchd marks it done then, and you can go idle now."
    | .done k stay n =>
      out s!"done #{d id}"
      match stay with
      | some s => out s!"context ~{k}k: you stay for '{s}'. `swarm stay --end` when that is over."
      | none =>
        if k * 1000 < SMALL_CTX && n > 0 then out s!"context ~{k}k: take the next task (swarm board)."
        else out s!"context ~{k}k: go idle. watchd ends you once your work lands; a fresh agent takes new work."
  | "block" =>
    let away ← step [.task, .«meta»] (block c id ((a.str "question").getD ""))
    out s!"blocked #{d id}; {if away then "the user is away: park this and take work that doesn't need the answer." else "watchd tells the communicator."} It stays yours until `swarm task unblock`."
  | "unblock" =>
    let o ← step [.task, .agent, .«meta»] (unblock c id ((a.str "answer").getD ""))
    out s!"unblocked #{d id}; claimed by {o.getD "nil"}"
  | "release" =>
    let after := a.ids "after"
    let fromA ← step [.task, .«meta»] (release c id after)
    out s!"released #{d id}{match fromA with | some f => " from " ++ f | none => ""}; it is open again{match after with | some l@(_ :: _) => " after " ++ idsText l | _ => ""}"
  | "edit" =>
    let bodyFile ← match a.str "body_file" with
      | some p => pure (some (p, ← Fs.read p))
      | none => pure none
    let (fields, st) ← step [.task, .agent] (edit c id { title := a.str "title", body := a.str "body", bodyFile,
                                                           append := a.str "append", model := a.str "model", effort := a.str "effort", urgent := a.flag "urgent" })
    out s!"edited #{d id}: {", ".intercalate fields}"
    let fs := " ".intercalate fields
    if st = .claimed && (hasSub fs "model" || hasSub fs "effort") then
      out "model/effort change the row only: they apply at the next spawn/claim"
  | "drop" =>
    let ws ← step [.task, .«meta»] (Queue.drop c id)
    out s!"dropped #{d id}"
    for w in ws do out s!"#{d w.id} waits on #{d id}: drop it too, or `swarm task after {d w.id} …`"
  | "hold" =>
    step [.task] (Queue.hold c id ((a.str "why").getD ""))
    out s!"held #{d id}: neither auto-spawn nor an agent asking for work takes it until `swarm task unhold {d id}`"
  | "unhold" =>
    step [.task] (Queue.unhold c id)
    out s!"unheld #{d id}"
  | act => die s!"unknown task action {act}"
  return 0

/-- `swarm board` (tasks.cmd_board). -/
def board (a : Parsed) : m UInt32 := do
  let out := Env.out (m := m)
  if let some (avail, total, psi) ← Machine.mem then out (Machine.line avail total psi)
  let db ← Store.txn [.task, .agent, .«meta»] fun db => (db, db)
  let now ← Clock.now
  let all := a.flag "all"
  let role (o : Option String) : Option String :=
    o.bind fun n => (db.agents.find? fun x => x.name == n && x.ended.isNone).bind (·.role)
  let red (t : Task) : Nat := if redKey t == 1 && t.state ≠ .done then 1 else 0
  let rows := (db.tasks.filter fun t => all || t.state = .open || t.state = .claimed || t.state = .blocked).mergeSort
    (boardLe red)
  out (limitsLine db (← env "SWARM_COMMS"))
  if let some h := db.getMeta "spawn_held" then out (h.v.getD "nil")
  for r in rows do
    let who := (py r.owner).getD "-" ++ (match role r.owner with | some x => s!" ({x})" | none => "")
    let pr := s!"  [P{d (r.priority.getD DEFAULT_PRIORITY)}]"
    if r.state = .blocked then
      out s!"#{d r.id} blocked by {who}: {r.question.getD "None"}  {r.title.getD ""}{pr}"
    else
      let lease := if r.state = .claimed then
        let left := r.lease_until.getD 0 - now
        if left > 0 then s!" lease {fdiv left 60}m left" else " lease EXPIRED"
        else ""
      let u := undone db r
      let wait := if u.isEmpty then "" else
        " after " ++ ", ".intercalate (u.map fun x => "#" ++ d x.id ++ (if x.state = .dropped then " (dropped)" else ""))
      out (s!"#{d r.id} {padRight r.state.text 7} {who}{lease}{wait}  {r.title.getD ""}" ++ pr ++
        (match r.qpos with | some q => s!"  [queue {q}]" | none => "") ++
        (if (py r.body).isSome then "  [body: task show]" else "") ++
        (match r.hold with | some h => s!"  held: {h}" | none => "") ++
        (match py r.evidence with | some e => s!"  [evidence: {e}]" | none => ""))
  if all then out s!"({rows.length} tasks)"
  else out s!"({rows.length} shown, {(db.tasks.filter (·.state = .done)).length} done)"
  for x in (live db).filter (·.stay.isSome) do
    out s!"staying: {x.name}{match x.role with | some r => " " ++ r | none => ""}: {x.stay.getD ""}"
  return 0

/-- `swarm queue`, `queue add <id>… [--front | --before <id> | --after <id>]`, `queue rm <id>…` (board #128). -/
def queue (a : Parsed) : m UInt32 := do
  let out := Env.out (m := m)
  let usage := "usage: swarm queue [add <id>... [--front | --before <id> | --after <id>] | rm <id>...]"
  let ids (ws : List String) : m (List Int) := ws.mapM fun w => match parseInt (if w.startsWith "#" then (w.drop 1).toString else w) with
    | some i => pure i
    | none => die s!"not a task id: '{w}'"
  -- no SWARM_NAME: the user
  let c : Tasks.Ctx := { me := (← env "SWARM_NAME").getD HUMAN, now := ← Clock.now, comms := ← env "SWARM_COMMS" }
  match a.strs "words" with
  | [] =>
    let db ← Store.txn [.task, .«meta», .agent, .cursor] fun db => (db, db)
    let q := Queue.queued db
    if Queue.queueOnly db then out "queue-only: auto-spawn staffs only the queue (and main red tasks)"
    if q.isEmpty then out "(queue empty)"
    for t in q do
      let why := (Queue.whyNot db t).getD "startable"
      out s!"{(t.qpos.map d).getD "?"}. #{d t.id} {padRight t.state.text 7} {why}  {t.title.getD ""}  [P{d (t.priority.getD DEFAULT_PRIORITY)}]"
  | "add" :: ws@(_ :: _) =>
    let w : Queue.Place := match a.flag "front", a.int "before", a.int "after" with
      | true, _, _ => .front
      | _, some x, _ => .before x
      | _, _, some x => .after x
      | _, _, _ => .back
    let is ← ids ws
    step [.task, .agent, .«meta», .event] (Queue.add c is w)
    out s!"queued {idsText (Queue.dedup is)}"
  | "rm" :: ws@(_ :: _) =>
    if a.flag "front" || (a.int "before").isSome || (a.int "after").isSome then die usage
    let is ← ids ws
    step [.task, .agent, .«meta», .event] (Queue.rm c is)
    out s!"unqueued {idsText (Queue.dedup is)}"
  | _ => die usage
  return 0

/-- `swarm rules [show | set <text>…]` (tasks.cmd_rules). -/
def rules (a : Parsed) : m UInt32 := do
  let text := " ".intercalate (a.strs "text")
  let set := a.act == "set"
  let r ← Store.txn [.«meta»] fun db =>
    let db := if set then rulesSet text db else db
    (db, db.getMeta "rules")
  Env.out (match r with | some x => x.v.getD "None" | none => "(none)")
  return 0

/-- The group: task, rules and board. -/
def group : Group m where
  specs := [("task", taskSpec), ("rules", rulesSpec), ("board", boardSpec), ("queue", queueSpec)]
  run a := match a.cmd with
    | "task" => task a
    | "rules" => rules a
    | "queue" => queue a
    | _ => board a

end SwarmLean.Cmd.Tasks
