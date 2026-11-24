import SwarmLean.Cmd
import SwarmLean.Cmd.TasksHelp
import SwarmLean.Db.Queue
import SwarmLean.Db.Reuse
import SwarmLean.Lib.Bases
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Msgs
import SwarmLean.Db.Notes
import SwarmLean.Lib.Workspaces
import SwarmLean.Db.TaskTxn
import SwarmLean.Lib.Events

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
       opt "--base", opt "--label", { opt "--repo" with maxCount := 1000000 }, flag "--no-repo"]
      [["body", "body_file"], ["repo", "no_repo"]] [] none,
    .mk "priority" helpTaskPriority [idArg, { name := "priority", conv := some prio }] [] [] [] none,
    .mk "after" helpTaskAfter [idArg, { name := "deps", minArgs := 0, conv := some idList }] [] [] [] none,
    .mk "claim" helpTaskClaim [idArg] [leaseOpt, flag "--force"] [] [] none,
    .mk "renew" helpTaskRenew [idArg] [leaseOpt] [] [] none,
    .mk "show" helpTaskShow [idArg] [flag "--json"] [] [] none,
    .mk "done" helpTaskDone [idArg] [{ opt "--evidence" with minCount := 1 }] [] [] none,
    .mk "land" helpTaskLand [idArg] [{ opt "--sha" with minCount := 1 }, opt "--lander"] [] [] none,
    .mk "unland" helpTaskUnland [idArg] [{ opt "--why" with minCount := 1 }] [] [] none,
    .mk "block" helpTaskBlock [idArg, { name := "question" }] [] [] [] none,
    .mk "unblock" helpTaskUnblock [idArg] [opt "--answer" (some "")] [] [] none,
    .mk "release" helpTaskRelease [idArg] [opt "--after" none (some idList)] [] [] none,
    .mk "edit" helpTaskEdit [idArg]
      [opt "--title", opt "--body", opt "--body-file", opt "--append", opt "--model",
       { opt "--effort" with choices := EFFORTS }, flag "--urgent"] [["body", "body_file", "append"]] [] none,
    .mk "label" helpTaskLabel [idArg, { name := "labels", minArgs := 0, maxArgs := 1000000 }] [] [] [] none,
    .mk "drop" helpTaskDrop [idArg] [opt "--duplicate-of" none (some int), opt "--note"] [] [] none,
    .mk "backlog" helpTaskBacklog [idArg] [{ opt "--note" with minCount := 1 }] [] [] none,
    .mk "ready" helpTaskReady [idArg] [] [] [] none,
    .mk "assign" helpTaskAssign [idArg, { name := "who", minArgs := 0 }] [flag "--none"] [] [] none,
    -- the old verbs, out of the help: each fails naming its replacement (agents may still have the old SKILL.md)
    .mk "hold" helpTaskHold [idArg] [opt "--why"] [] [] none,
    .mk "unhold" helpTaskUnhold [idArg] [] [] [] none])

/-- The `queue` parser: its words are the action and the ids, read by `queue`. -/
def queueSpec : Spec := .mk "queue" helpQueue [{ name := "words", minArgs := 0, maxArgs := 1000000 }]
  [flag "--front", opt "--before" none (some int), opt "--after" none (some int)] [["front", "before", "after"]] [] none

/-- The `rules` parser. -/
def rulesSpec : Spec :=
  .mk "rules" helpRules [] [] [] (cmdTarget := some "act") (cmds :=
    [.mk "show" helpRulesShow [] [] [] [] none, .mk "set" helpRulesSet [{ name := "text", maxArgs := 1000000 }] [] [] [] none])

/-- The `board` parser. -/
def boardSpec : Spec := .mk "board" helpBoard [] [flag "--all", flag "--json"] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Fs m] [Proc m] [Git m] [Sys m]

/-- The command's world: the agent, the time, the terminal, the communicator by env. -/
def ctx : m Tasks.Ctx := do
  return { me := ← me, now := ← Clock.now, here := ← env "HC_TERMINAL_ID", comms := ← env "SWARM_COMMS" }

/-- Runs a task transaction, dying with its error. -/
def step (t : Txn (Except String α)) : m α := do orDie (← Store.run t)

/-- Evidence `e` (its first word) names a commit on base `b` of repo `cwd`: local or origin's, fetched first (board
#200). -/
def evidenceOnBaseIn (e b : String) (cwd : Option String) : m Bool := do
  let some w := (words e).head? | return false
  let some sha := (← Git.git ["rev-parse", "--verify", "-q", "--end-of-options", w ++ "^{commit}"] cwd).map strip
    | return false
  let anc (r : String) : m Bool := return (← Git.git ["merge-base", "--is-ancestor", sha, r] cwd).isSome
  if (GitRef.parse? b).isSome && (← anc b) then return true
  Bases.fetch b cwd
  match ← Bases.remoteRef b cwd with
  | some r => anc r
  | none => return false

/-- Evidence `e` names a commit on task `t`'s base in one of its repos (sw-global §2), or, for a task of no repo, on its
base in the folder's repo. -/
def evidenceOnBase (e : String) (t : Task) : m Bool := do
  let repos ← Swarms.taskRepos t.id
  if repos.isEmpty then
    let cwd := some (← Env.cwd)
    return ← evidenceOnBaseIn e (← Bases.baseFor t.base cwd) cwd
  for (r, _) in repos do
    if ← evidenceOnBaseIn e (← Bases.forTask t r) (some r) then return true
  return false

/-- A landing task's line: `#N landing <sha> by <lander> since HH:MM (from <owner>)`. -/
def landingLine (r : Task) : m String := do
  return s!"{landingText r.id r} since {← Clock.hhmm (r.landing_at.getD 0)}{match py r.owner with | some o => " (from " ++ o ++ ")" | none => ""}"

/-- `task show`'s text (tasks.lua's show branch); `repos` the repos it touches, with their own bases. -/
def showText (db : Db) (r : Task) (repos : List (String × Option String) := []) : m String := do
  let now ← Clock.now
  let evs := taskEvents db r.id
  let tm := timing r evs now
  let f (x : Option Int) : String := match x with | some v => s!"{fdiv v 60}m" | none => "-"
  let mut s := s!"#{d r.id} {r.status.name} {(py r.assignee).getD "-"}  {cont (r.title.getD "")}\ntiming: queue {f tm.queue_wait_s}, work {f tm.work_s}, total {f tm.total_s}, blocked {f (some tm.blocked_s)}, claims {tm.claims}, releases {tm.releases}, held by {(py (some (", ".intercalate tm.holders))).getD "-"}"
  for e in evs do
    if e.kind == some "task-edit" then
      let data := e.data.getD ""
      let ds := (data.drop 1).toString.toList.takeWhile Char.isDigit
      let data := if data.startsWith "#" && !ds.isEmpty && ((data.drop (1 + ds.length)).startsWith " ") then
        (data.drop (2 + ds.length)).toString else data
      s := s ++ s!"\nedited {← Clock.hhmm (e.ts.getD 0)} by {e.agent.getD ""}: {cont data}"
  if r.status = .inReview then s := s ++ "\n" ++ (← landingLine r)
  for n in Notes.notes db r.id do
    let to := match n.to with
      | some t => if n.held then " (held)" else if t == Notes.box r.id then " (given at claim)" else s!" (to {t})"
      | none => ""
    s := s ++ s!"\nnote {← Clock.hhmm n.ts} {n.frm}{to}: {((clean n.text).splitOn "\n").headD ""}"
  s := s ++ "\npriority: " ++ r.priority.name
  if let some o := r.dupOf then s := s ++ s!"\nduplicate of #{d o}"
  if let some b := py r.base then s := s ++ "\nbase: " ++ b
  if !repos.isEmpty then
    s := s ++ s!"\nrepo{if repos.length > 1 then "s" else ""}: " ++ ", ".intercalate (repos.map fun (p, b) =>
      p ++ (match b with | some b => s!" (base {b})" | none => ""))
  if let some q := Queue.place db r then s := s ++ s!"\n{if r.status = .backlog then "backlog" else "queue"}: {q}"
  if let some h := r.note then s := s ++ "\nnote: " ++ cont h
  if !(labelsOf r).isEmpty then s := s ++ "\nlabels: " ++ ", ".intercalate (labelsOf r)
  if !(parentsOf r).isEmpty then s := s ++ s!"\nfiled by {r.created_by.getD "-"} while holding {idsText (parentsOf r)}"
  if let some k := pyI tm.claim_ctx then s := s ++ s!", ctx {fdiv k 1000}k at claim"
  if let some k := pyI tm.done_ctx then s := s ++ s!" -> {fdiv k 1000}k at done"
  if let some ma := pyI tm.merged_at then
    s := s ++ s!"\nPR #{(tm.pr.map d).getD "None"} merged {← Clock.hhmm ma}, main CI {(py (tm.ci_conclusion.map Conclusion.text)).getD "pending"}"
    if let some g := tm.merge_to_green_s then s := s ++ s!", green {fdiv g 60}m after merge"
  return s ++ depLines db r ++ "\n" ++ ((py r.body).map contBlock).getD "(no body)" ++
    (match py r.answer with | some a => "\nAnswer to the block: " ++ cont a | none => "")

/-- `task show --json`: the row's fields and its notes, oldest first (board #202). -/
def showJson (db : Db) (r : Task) : Lean.Json :=
  let j {α} [Lean.ToJson α] (x : α) : Lean.Json := Lean.toJson x
  let note (n : Notes.Note) : Lean.Json := Lean.Json.mkObj [("ts", j n.ts), ("from", j n.frm), ("text", j n.text),
    ("to", j n.to), ("held", j n.held)]
  Lean.Json.mkObj [("id", j r.id), ("title", j r.title), ("state", j r.status.text), ("category", j r.category.text),
    ("assignee", j r.assignee), ("owner", j r.owner), ("priority", j r.priority.text), ("base", j r.base),
    ("labels", j (labelsOf r)), ("deps", j (depsOf r)), ("note", j r.note), ("dup_of", j r.dupOf),
    ("place", j (Queue.place db r)), ("evidence", j r.evidence), ("body", j (py r.body)),
    ("notes", Lean.Json.arr ((Notes.notes db r.id).map note).toArray)]

/-- `swarm task …`. -/
def task (a : Parsed) : m UInt32 := do
  let c ← ctx
  let id := (a.int "id").getD 0
  let out := Env.out (m := m)
  match a.act with
  | "add" =>
    let body ← match a.str "body_file" with
      | some p => match ← Fs.read p with
        | some t => pure (clean t)
        | none => die s!"can't read {p}"
      | none => pure (clean ((a.str "body").getD ""))
    -- the repos it touches (sw-global §2): each --repo's main worktree, else the folder's; none with --no-repo
    let mut repos : List String := []
    for p in a.strs "repo" do
      let some r ← Workspaces.main (some p) | die s!"--repo {p}: not in a git repo"
      if !repos.contains r then repos := repos ++ [r]
    if a.strs "repo" == [] && !a.flag "no_repo" then
      if let some r ← Workspaces.main (some (← Env.cwd)) then repos := [r]
    match a.str "base" with
    | some b => if b != "" && (GitRef.parse? b).isNone then die s!"--base {b}: not a valid git ref name"
    | none => for r in repos do Bases.warnBadConfig ["base"] (some r)
    let n ← step (TaskTxn.add c { title := clean ((a.str "title").getD ""), body, deps := (a.ids "after").getD [],
                                    model := a.str "model", effort := a.str "effort", base := a.str "base",
                                    priority := (a.str "priority").bind Priority.ofText,
                                    labels := a.str "label" })
    let rows ← repos.mapM fun r => do return (r, (a.str "base").filter (· ≠ ""), some (← Bases.default (some r)))
    Swarms.addTaskRepos n rows
    out s!"task #{d n}"
  | "claim" =>
    -- the claim and the take of its held notes in one transaction: a note posted after it goes to the new owner
    let (r, notes) ← step (TaskTxn.claimTxn { c with force := a.flag "force" } id ((a.str "lease").getD "2h"))
    out s!"claimed #{d id} until {← Clock.hhmm r.«until»}"
    if !notes.isEmpty then out s!"notes left on #{d id} for its next owner:\n{← Msgs.fmtMsgs notes}"
    if let some (avail, total, psi) ← Machine.mem then
      if Machine.pressureHigh avail total psi then
        out (← Machine.note)
      else out (Machine.line avail total psi)
    out (((py r.body).map contBlock).getD "(no body)")
  | "show" =>
    let db ← Store.run (TaskTxn.showTxn id)
    let some r := db.find id | die s!"no task #{d id}"
    let repos ← Swarms.taskRepos r.id
    if a.flag "json" then
      -- its activity for the swarm view's peek: every event about it, in any swarm, by key
      let evs ← Events.ofTask r.id
      out (((showJson db r).setObjVal! "repos" (Lean.toJson (repos.map (·.1)))).setObjVal! "events"
        (Lean.Json.arr (evs.map Events.taskJson).toArray)).compress
    else out (← showText db r repos)
  | "after" =>
    let deps := (a.ids "deps").getD []
    step (TaskTxn.after c id deps)
    out s!"#{d id} after {(py (some (idsText deps))).getD "nothing"}"
  | "priority" =>
    let p := ((a.str "priority").bind Priority.ofText).getD DEFAULT_PRIORITY
    step (TaskTxn.one id (priority c id p))
    out s!"#{d id} {p.name}"
  | "renew" =>
    let u ← step (TaskTxn.one id (renew c id ((a.str "lease").getD "2h")))
    out s!"renewed #{d id} until {← Clock.hhmm u}"
  | "done" =>
    let ev := (a.str "evidence").getD ""
    let r0 ← Store.view [TaskTxn.task id] (·.find id)
    let onBase ← match r0 with
      | some r => if r.status = .inReview then evidenceOnBase ev r else pure false
      | none => pure false
    match ← step (TaskTxn.done { c with onBase } id ev) with
    | .landed o => out s!"done #{d id}: landed{match py o with | some o => ", handed over by " ++ o | none => ""}"
    | .red => out s!"#{d id} released: your fix is recorded, the task is in Backlog until a green run closes it (a newer red run moves it back to Ready). Go idle."
    | .done k stay n =>
      out s!"done #{d id}"
      match stay with
      | some s => out s!"context ~{k}k: you stay for '{s}'. `swarm stay --end` when that is over."
      | none =>
        let below ← Store.view [Sels.metas ["reuse_below"]] Reuse.reuseBelow
        if k * 1000 < below && n > 0 then
          out s!"context ~{k}k: go idle. Once your work lands watchd offers you related startable tasks, if any; else it ends you."
        else out s!"context ~{k}k: go idle. watchd ends you once your work lands; a fresh agent takes new work."
  | "land" =>
    let given := (a.str "sha").getD ""
    let sha ← match (words given).head? with
      | some w => match ← Git.git ["rev-parse", "--verify", "-q", "--end-of-options", w ++ "^{commit}"] (some (← Env.cwd)) with
        | some s => pure (strip s)
        | none => die s!"--sha {given}: no such commit here"
      | none => pure ""
    step (TaskTxn.land c id sha (a.str "lander"))
    if let some r ← Store.view [TaskTxn.task id] (·.find id) then out (← landingLine r)
    out s!"it is no longer yours: take the next task or go idle. Its lander closes it: `swarm task done {d id} --evidence <sha on its base>`, or `swarm task unland {d id} --why \"…\"`."
  | "unland" =>
    let u ← step (TaskTxn.unland c id ((a.str "why").getD ""))
    out s!"unlanded #{d id}: Ready again, priority {u.priority.name}{match py u.owner with | some o => ", " ++ o ++ " and the communicator told" | none => ""}"
  | "block" =>
    let away ← step (TaskTxn.block c id (clean ((a.str "question").getD "")))
    out s!"#{d id} needs input; {if away then "the user is away: park this and take work that doesn't need the answer." else "watchd tells the communicator."} It stays yours until `swarm task unblock`."
  | "unblock" =>
    let o ← step (TaskTxn.unblock c id (clean ((a.str "answer").getD "")))
    out s!"#{d id} in progress again; assignee {o.getD "nil"}"
  | "release" =>
    let after := a.ids "after"
    let fromA ← step (TaskTxn.release c id after)
    out s!"released #{d id}{match fromA with | some f => " from " ++ f | none => ""}; it is Ready again{match after with | some l@(_ :: _) => " after " ++ idsText l | _ => ""}"
  | "edit" =>
    let bodyFile ← match a.str "body_file" with
      | some p => pure (some (p, (← Fs.read p).map clean))
      | none => pure none
    let (fields, st) ← step (TaskTxn.edit c id { title := (a.str "title").map clean, body := (a.str "body").map clean, bodyFile,
                                                           append := (a.str "append").map clean, model := a.str "model", effort := a.str "effort", urgent := a.flag "urgent" })
    out s!"edited #{d id}: {", ".intercalate fields}"
    let fs := " ".intercalate fields
    if st = .inProgress && (hasSub fs "model" || hasSub fs "effort") then
      out "model/effort change the row only: they apply at the next spawn/claim"
  | "label" =>
    discard <| step (TaskTxn.edit c id { labels := some (",".intercalate (a.strs "labels")) })
    let r ← Store.view [TaskTxn.task id] (·.find id)
    out s!"#{d id} labels: {match r.map labelsOf with | some l@(_ :: _) => ", ".intercalate l | _ => "none"}"
  | "drop" =>
    let dup := a.int "duplicate_of"
    let ws ← step (TaskTxn.drop c id dup (a.str "note"))
    out s!"#{d id} {match dup with | some o => s!"Duplicate of #{d o}" | none => "Cancelled"}"
    for w in ws do
      out s!"#{d w.id} waits on #{d id}: `swarm task drop {d w.id}` too, or remove the dependency: `swarm task after {d w.id} …`"
  | "backlog" =>
    step (TaskTxn.backlog c id ((a.str "note").getD ""))
    out s!"#{d id} Backlog: auto-spawn and agents asking for work skip it until `swarm task ready {d id}` (the communicator or the user)"
  | "ready" =>
    step (TaskTxn.ready c id)
    let r ← Store.view [TaskTxn.task id, TaskTxn.queuedSel] fun db => (db.find id).bind (Queue.place db)
    out s!"#{d id} Ready{match r with | some n => s!", queue {n}" | none => ""}"
  | "assign" =>
    let who := a.str "who"
    if a.flag "none" == who.isSome then die "usage: swarm task assign <id> <who>, or swarm task assign <id> --none"
    step (TaskTxn.assign c id who)
    out s!"#{d id} assignee: {who.getD "none"}"
  | "hold" => die s!"`task hold` is gone: `swarm task backlog {d id} --note \"…\"` moves a task to Backlog"
  | "unhold" => die s!"`task unhold` is gone: `swarm task ready {d id}` moves a Backlog task to Ready"
  | act => die s!"unknown task action {act}"
  return 0

/-- `swarm board` (tasks.cmd_board). -/
def board (a : Parsed) : m UInt32 := do
  let out := Env.out (m := m)
  if let some (avail, total, psi) ← Machine.mem then out (Machine.line avail total psi)
  let all := a.flag "all"
  -- the tasks not done (`--all`: every task); the done ones only counted
  let db ← Store.view (if all then TaskTxn.boardSels else TaskTxn.undoneSel :: TaskTxn.boardSels.filter (·.table != .task)) id
  let now ← Clock.now
  let role (o : Option String) : Option String :=
    o.bind fun n => (db.agents.find? fun x => x.name == n && x.ended.isNone).bind (·.role)
  let red (t : Task) : Nat := if redKey t == 1 && t.status ≠ .completed then 1 else 0
  let rows := (db.tasks.filter fun t => all || Queue.onBoard t).mergeSort
    (boardLe red)
  out (limitsLine db (← env "SWARM_COMMS"))
  if let some h := db.getMeta "spawn_held" then out (h.v.getD "nil")
  for r in rows do
    let who := (py r.assignee).getD "-" ++ (match role r.assignee with | some x => s!" ({x})" | none => "")
    let pr := s!"  [{r.priority.name}]"
    if r.status = .needsInput then
      out s!"#{d r.id} needs input from {who}: {cont (r.question.getD "None")}  {cont (r.title.getD "")}{pr}"
    else if r.status = .inReview then
      out s!"{← landingLine r}  {cont (r.title.getD "")}{pr}"
    else
      let lease := if r.status = .inProgress && r.owner != some Agents.HUMAN then
        let left := r.lease_until.getD 0 - now
        if left > 0 then s!" lease {fdiv left 60}m left" else " lease EXPIRED"
        else ""
      let u := undone db r
      let wait := if u.isEmpty then "" else
        " waiting on " ++ ", ".intercalate (u.map fun x => "#" ++ d x.id ++ (if x.category = .cancelled then " (cancelled)" else ""))
      out (s!"#{d r.id} {padRight r.status.name 11} {who}{lease}{wait}  {cont (r.title.getD "")}" ++ pr ++
        (match Queue.place db r with | some q => s!"  [{if r.status = .backlog then "backlog" else "queue"} {q}]" | none => "") ++
        (if (py r.body).isSome then "  [body: task show]" else "") ++
        (match r.note with | some h => s!"  note: {cont h}" | none => "") ++
        (match py r.evidence with | some e => s!"  [evidence: {e}]" | none => ""))
  if all then out s!"({rows.length} tasks)"
  else out s!"({rows.length} shown, {((← Swarms.taskStates).filter (·.2 == Status.completed.text)).length} completed)"
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
    let db ← Store.run TaskTxn.queueView
    let q := Queue.readyList db
    if q.isEmpty then out "(Ready empty)"
    for (t, i) in q.zipIdx do
      let why := (Queue.whyNot db t).getD "startable"
      out s!"{i + 1}. #{d t.id} {why}  {cont (t.title.getD "")}  [{t.priority.name}]"
    let b := Queue.backlogList db
    if !b.isEmpty then out s!"Backlog: {idsText (b.map (·.id))}"
  | "add" :: ws@(_ :: _) =>
    let w : Queue.Place := match a.flag "front", a.int "before", a.int "after" with
      | true, _, _ => .front
      | _, some x, _ => .before x
      | _, _, some x => .after x
      | _, _, _ => .back
    let is ← ids ws
    step (TaskTxn.qadd c is w)
    out s!"moved {idsText (Queue.dedup is)}"
  | "rm" :: ws@(_ :: _) =>
    if a.flag "front" || (a.int "before").isSome || (a.int "after").isSome then die usage
    let is ← ids ws
    step (TaskTxn.qrm c is)
    out s!"moved {idsText (Queue.dedup is)} to the end"
  | _ => die usage
  return 0

/-- `swarm rules [show | set <text>…]` (tasks.cmd_rules). -/
def rules (a : Parsed) : m UInt32 := do
  let text := " ".intercalate (a.strs "text")
  if a.act == "set" then step (TaskTxn.setRules (← ctx) text)
  let r ← Store.view [Sels.metas ["rules"]] (·.getMeta "rules")
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
