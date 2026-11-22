import SwarmLean.Lib.Bases
import SwarmLean.Lib.Workspaces
import SwarmLean.Db.Msgs
import SwarmLean.Db.Queue
import SwarmLean.Db.TaskTxn

/-! ci.lua: the flows of `.claude/swarm.json`, GitHub's time stamps and a PR's check verdict. -/

namespace SwarmLean.Ci
open Lean (Json)

variable {m : Type → Type} [Monad m]

/-- "2026-11-08T10:00:00Z" as epoch seconds (UTC), as Python's fromisoformat(...).timestamp() (ci.ts). -/
def ts (s : String) : Int :=
  let num (i n : Nat) : Int := ((s.drop i |>.take n).toString.toNat?.getD 0 : Nat)
  let (y, mo, dd) := (num 0 4, num 5 2, num 8 2)
  let y := if mo ≤ 2 then y - 1 else y
  let era := Int.fdiv y 400
  let mp := Int.emod (mo + 9) 12
  let yoe := y - era * 400
  let doe := yoe * 365 + Int.fdiv yoe 4 - Int.fdiv yoe 100 + Int.fdiv (153 * mp + 2) 5 + dd - 1
  (era * 146097 + doe - 719468) * 86400 + num 11 2 * 3600 + num 14 2 * 60 + num 17 2

/-- `.claude/swarm.json`'s `ci` object at the repo's top, or {} (ci_cfg). -/
def ciCfg [Git m] [Fs m] (repo : Option String) : m Json := do
  let top := (← Git.git ["rev-parse", "--show-toplevel"] repo).map strip
  let txt ← match top with
    | some t => pure ((← Fs.read s!"{t}/.claude/swarm.json").getD "")
    | none => pure ""
  match (Json.decode txt).bind (Json.field · "ci") with
  | some c@(.obj _) => return c
  | _ => return Json.mkObj []

/-- The flows `ci.flow` may name (ci.FLOWS). -/
def FLOWS : List String := ["none", "post-merge", "pr-gated", "promoted"]

/-- The spawn message's CI line for each flow (ci.FLOW_LINE). -/
def FLOW_LINE : String → Option String
  | "none" => some "CI here (`ci.flow` none): there is no CI; land on green local checks."
  | "post-merge" => some ("CI here (`ci.flow` post-merge, or unset): land on green local checks and don't wait for CI; a red run " ++
      "on the base becomes one `main red: …` task; `swarm task done` with your fix's sha releases you, watchd closes it on the next green run.")
  | "pr-gated" => some ("CI here (`ci.flow` pr-gated): the PR's checks gate the merge. `swarm stay \"CI on PR #N, then merge\"` and " ++
      "stop; watchd wakes you when they finish: merge on green, fix and push on red.")
  | "promoted" => some ("CI here (`ci.flow` promoted): land on the dev base your task names, as post-merge: green local checks, " ++
      "don't wait for CI.")
  | _ => none

/-- The repo's CI flow, none when unset or not one of FLOWS (ci.flow). -/
def flow [Git m] [Fs m] (repo : Option String) : m (Option String) := do
  return (Json.fstr (← ciCfg repo) "flow").filter FLOWS.contains

/-- A PR's checks from gh's statusCheckRollup: green, red or pending (ci.verdict). -/
def verdict (rollup : Option Json) : String := Id.run do
  let some (.arr xs) := rollup | return "pending"
  if xs.isEmpty then return "pending"
  let mut red := false
  for x in xs do
    let st := if Json.fstr x "__typename" == some "StatusContext" then Json.fstr x "state"
      else if Json.fstr x "status" == some "COMPLETED" then Json.fstr x "conclusion" else none
    match st with
    | none | some "" | some "PENDING" | some "EXPECTED" => return "pending"
    | some s => if s != "SUCCESS" && s != "NEUTRAL" && s != "SKIPPED" then red := true
  return if red then "red" else "green"

/-- The poll's decision on a claimed task's PR (ci.pr_act): done once merged; wake once its checks finished in a
pr-gated repo and the owner was not told. -/
def prAct (state verdict : String) (gated told : Bool) : Option String :=
  if state == "MERGED" then some "done"
  else if gated && state == "OPEN" && verdict != "pending" && !told then some "wake" else none


/-! watchd's side: the polls into the ci table and the task columns, each a pure step on the db with what gh said. -/

/-- True, and stamps the time, if meta `key` was stamped `every` seconds ago or never (ci.due). -/
def due (now : Int) (key : String) (every : Int) (db : Db) : Db × Bool :=
  match db.getMeta key with
  | some r => if now - ((r.v.bind parseInt).getD 0) < every then (db, false) else (db.setMeta key (some (d now)), true)
  | none => (db.setMeta key (some (d now)), true)

/-- The digits after the first `pat` in `s` and where that `pat` starts (`s:match(pat .. "(%d+)")`, `s:find(pat .. "%d")`). -/
def numAt (s pat : String) : Option (Nat × Int) :=
  let parts := s.splitOn pat
  let rec go (pre : Nat) : List String → Option (Nat × Int)
    | x :: y :: rest =>
      let ds := y.toList.takeWhile Char.isDigit
      if ds.isEmpty then go (pre + x.utf8ByteSize + pat.utf8ByteSize) (y :: rest)
      else some (pre + x.utf8ByteSize, (String.ofList ds).toNat!)
    | _ => none
  go 0 parts

/-- A run as pr_ci compares them. -/
structure Run where
  headSha : Option String
  conclusion : Option String
  status : Option String
  createdAt : Option String
  updatedAt : Option String

/-- Sel `s` cut to the tasks of ids `ids` (none: every task): a repo's CI passes act only on its own tasks (board #136). -/
def ofIds (ids : Option (List Int)) (s : Sel) : Sel :=
  match ids with
  | some xs => { s with cond := .and s.cond (.oneOf "id" (xs.map .int)) }
  | none => s

/-- Task `t` is one of `ids` (none: every task is). -/
def inIds (ids : Option (List Int)) (t : Task) : Bool := ids.all (·.contains (t.id : Int))

/-- The done tasks pr_ci still fills: no merge data or no green run yet, done in the last day. -/
def prCiTodo (now : Int) (db : Db) : List Task :=
  db.tasks.filter fun t => t.state = .done && (t.merged_at.isNone || t.ci_green_at.isNone) && t.done_at.getD 0 > now - 86400
    && t.done_at.isSome

/-- The tasks `prCiTodo` picks from: done in the last day with merge data or a green run missing. -/
def prCiSel (now : Int) : Sel :=
  { table := .task, cond := .and (.and (.eq "state" (.text "done")) (.gt "done_at" (.int (now - 86400))))
      (.or (.null "merged_at") (.null "ci_green_at")) }

/-- pr_ci's gate: something to fill and the PR list due (every 10 min, gh calls count against the API limit). -/
def prCiGate (now : Int) (db : Db) : Db × Bool :=
  if (prCiTodo now db).isEmpty then (db, false) else due now "pr_polled" 600 db

/-- pr_ci with gh's merged PRs: each done task's PR, merge time, its main run's conclusion and the first green after. -/
def prCiApply (now : Int) (prs : List Lean.Json) (db : Db) : Db :=
  let runs : List Run := (db.cis.mergeSort fun a b => a.created.getD "" ≤ b.created.getD "").map fun x =>
    { headSha := x.sha, conclusion := x.conclusion, status := x.status, createdAt := x.created, updatedAt := x.updated }
  let completed (f : Run → Bool) : Option Run := runs.find? fun x => x.status == some "completed" && f x
  (prCiTodo now db).foldl (fun db r =>
    let ev := r.evidence.getD ""
    let a := numAt ev "PR #"
    let b := numAt ev "pull/"
    let pick : Option Int := match a, b with
      | some (pa, na), some (pb, nb) => some (if pa < pb then na else nb)
      | some (_, na), none => some na
      | none, some (_, nb) => some nb
      | none, none => none
    let num := r.pr.orElse fun _ => pick
    let byNum := prs.find? fun x => num.isSome && Json.fint x "number" == num
    let pr := byNum.orElse fun _ => prs.foldl (fun (pr : Option Lean.Json) x =>
      let ma := (Json.fstr x "mergedAt").getD ""
      if ((Json.fstr x "headRefName").getD "").startsWith (r.owner.getD "nil" ++ "/") && ts ma ≥ r.first_claimed_at.getD 0
        && (pr.isNone || ma > ((pr.bind (Json.fstr · "mergedAt")).getD "")) then some x else pr) none
    match pr with
    | none => db
    | some pr =>
      let merged := ts ((Json.fstr pr "mergedAt").getD "")
      let oid := (Json.field pr "mergeCommit").bind (Json.fstr · "oid")
      let n := Json.fint pr "number"
      -- the task's activity: its PR once found, its main run's conclusion once known
      let db := match n with
        | some k => if r.pr != some k then db.log now none "task-pr" none (some s!"#{d r.id} {d k}") else db
        | none => db
      match completed (·.headSha == oid) with
      | none => db.set r.id fun t => { t with pr := n, merged_at := some merged }
      | some mine =>
        let green := if mine.conclusion == some "success" then some mine
          else completed fun x => x.createdAt.getD "" > mine.createdAt.getD "" && x.conclusion == some "success"
        let db := if r.ci_conclusion != mine.conclusion then
            db.log now none "task-ci" none (some s!"#{d r.id} {mine.conclusion.getD "-"} {String.ofList ((mine.headSha.getD "-").toList.take 7)}") else db
        db.set r.id fun t => { t with pr := n, merged_at := some merged, ci_conclusion := mine.conclusion,
                                      ci_green_at := green.map fun g => ts (g.updatedAt.getD "") }) db

/-- gh's output as a JSON list, none when it failed or is not one (or not a table, as Lua's `type(prs) ~= "table"`). -/
def ghList (out : Option ProcOut) (dflt : String) : Option (List Lean.Json) :=
  let txt := match out with | some o => if o.code == 0 then o.stdout else dflt | none => dflt
  match Json.decode txt with
  | some (.arr a) => some a.toList
  | some (.obj _) => some []
  | _ => none

variable [Store m] [Clock m] [Proc m] [Git m] [Fs m]

/-- Repo `repo`'s main worktree and the ids of its tasks (`Swarms.tasksOf`), none without a repo (every task). Tasks are
the machine's, but GitHub's run ids are global and PR numbers per repo, so each repo's CI passes read only its own
(board #136); a folder in no repo has none. -/
def repoTasks [Env m] [Sys m] (repo : Option String) : m (Option (String × List Int)) := do
  let some _ := repo | return none
  let some p ← Workspaces.main repo | return some ("", [])
  return some (p, ← Swarms.tasksOf p)

/-- ci.pr_ci: fill merge-to-green for the repo's done tasks. -/
def prCi [Env m] [Sys m] (repo : Option String) : m Unit := do
  let now ← Clock.now
  let ids := (← repoTasks repo).map (·.2)
  let sel := ofIds ids (prCiSel now)
  if !(← Store.run (Txn.update [sel, Sels.metas ["pr_polled"]] [] (prCiGate now))) then return
  let some prs := ghList (← Proc.output ["gh", "pr", "list", "--state", "merged", "--limit", "100", "--json",
    "number,mergedAt,mergeCommit,headRefName"] repo []) "[]" | return
  Store.run (Txn.update [sel, Sels.all .ci] [] fun db => (prCiApply now prs db, ()))

/-- A claimed task of a live owner (pr_watch's held). -/
structure Held where
  id : Nat
  owner : String
  base : Option String
  first_claimed_at : Option Int

/-- pr_watch's claims of live owners, by id. -/
def held (db : Db) : List Held :=
  db.tasks.filterMap fun t => match t.owner with
    | some o => if t.state = .claimed && (db.agent o).any (·.ended.isNone) then
        some { id := t.id, owner := o, base := t.base, first_claimed_at := t.first_claimed_at } else none
    | none => none

/-- The claimed and blocked tasks: `held` and the count `prWatchGate` makes of each owner's. -/
def heldSel : Sel := { table := .task, cond := .oneOf "state" [.text "claimed", .text "blocked"] }

/-- pr_watch's gate and its claims with the branches each may be on: `<owner>/<task>`, plus the owner's recorded
worktree branches when this is its one task. -/
def prWatchGate (now : Int) (db : Db) : Db × Option (List (Held × List String)) :=
  let hs := held db
  if hs.isEmpty then (db, none) else
  let (db, ok) := due now "pr_watched" 60 db
  if !ok then (db, none) else
  (db, some (hs.map fun t =>
    let n := (db.tasks.filter fun x => x.owner == some t.owner && (x.state = .claimed || x.state = .blocked)).length
    (t, s!"{t.owner}/{d t.id}" :: if n == 1 then (db.workspaces.filter (·.agent == t.owner)).filterMap (·.branch) else [])))

/-- `prWatchGate` on what it reads: the claims, the live agents, the stamp and the owners' worktrees; with repo `r` (its
main worktree and its tasks' ids, `repoTasks`) only its claims and the worktrees recorded in it (board #136). -/
def prWatchTxn (now : Int) (r : Option (String × List Int)) : Txn (Option (List (Held × List String))) := do
  let ss := [ofIds (r.map (·.2)) heldSel, Sels.live]
  let owners := ((held (← Txn.slice ss)).map (·.owner)).eraseDups
  if owners.isEmpty then return none
  let wts : Cond := .oneOf "agent" (owners.map .text)
  let wts := match r with
    | some (p, _) => .and wts (.oneOf "repo" [.text p, .text ""])
    | none => wts
  Txn.update (ss ++ [Sels.metas ["pr_watched"], { table := .workspace, cond := wts }]) [] (prWatchGate now)

/-- The rollup's checks that did not finish well, by name. -/
def failedChecks (rollup : List Lean.Json) : List String :=
  rollup.filterMap fun x =>
    let st := if Json.fstr x "__typename" == some "StatusContext" then Json.fstr x "state" else Json.fstr x "conclusion"
    if st == some "SUCCESS" || st == some "NEUTRAL" || st == some "SKIPPED" then none
    else some (((Json.fstr x "name").orElse fun _ => Json.fstr x "context").getD "?")

/-- `tostring(x):sub(1, 7)` of an optional text. -/
def short (x : Option String) : String := (x.getD "nil").take 7 |>.toString

/-- The data of a PR's `pr-wake` event: its number, head and verdict. -/
def wakeKey (pr : Lean.Json) : String :=
  s!"{d ((Json.fint pr "number").getD 0)} {(Json.fstr pr "headRefOid").getD "nil"} {verdict (Json.field pr "statusCheckRollup")}"

/-- pr_watch's act on one claim and its PR: a merged PR closes the task; a finished verdict wakes the owner once. -/
def prWatchApply (now : Int) (gated : Bool) (t : Held) (pr : Lean.Json) (db : Db) : Db :=
  let rollup := Json.field pr "statusCheckRollup"
  let v := verdict rollup
  let num := (Json.fint pr "number").getD 0
  let head := Json.fstr pr "headRefOid"
  let key := wakeKey pr
  let told := db.events.any fun e => e.kind == some "pr-wake" && e.agent == some t.owner && e.data == some key
  match prAct ((Json.fstr pr "state").getD "") v gated told with
  | some "done" =>
    let ev := s!"PR #{d num} merged as {short (((Json.field pr "mergeCommit").bind (Json.fstr · "oid")).orElse fun _ => some "?")}"
    if (db.find t.id).any (·.state = .claimed) then
      let db := if (db.find t.id).any (·.pr != some num) then db.log now none "task-pr" none (some s!"#{d t.id} {d num}") else db
      let db := db.set t.id fun x => { x with state := .done, evidence := some ev, lease_until := none, done_at := some now, pr := some num, merged_at := some (ts ((Json.fstr pr "mergedAt").getD "")) }
      let db := Queue.tidy (db.log now (some "swarm") "done" none (some s!"#{d t.id} {ev}"))
      (Msgs.post db now .system (.agent t.owner) s!"{ev}: watchd marked #{d t.id} done, so no `task done` is needed. If you stay for it, `swarm stay --end`." true (some "system")).1
    else db
  | some "wake" =>
    let db := db.log now (some t.owner) "pr-wake" none (some key)
    let body := if v == "green" then
        s!"PR #{d num}'s checks are green (head {short head}): merge it; watchd marks #{d t.id} done once it is merged."
      else s!"PR #{d num}'s checks failed ({", ".intercalate (failedChecks (Json.items (rollup.getD .null)))}, head {short head}): fix and push; watchd wakes you on the next verdict."
    (Msgs.post db now .system (.agent t.owner) body true (some "system")).1
  | _ => db

/-- `prWatchApply` on what it reads: the task, the queue and the owner's wake for this PR's state. -/
def prWatchApplyTxn (now : Int) (gated : Bool) (t : Held) (pr : Lean.Json) : Txn Unit :=
  Txn.update [Sels.task t.id, TaskTxn.queuedSel,
      { table := .event, cond := .and (Sels.evOf t.owner "pr-wake") (.eq "data" (.text (wakeKey pr))) }] [.msg]
    fun db => (prWatchApply now gated t pr db, ())

/-- The newest open, or merged since the claim, PR from one of `branches` into `base`. -/
def pickPr (prs : List Lean.Json) (branches : List String) (base : String) (claimed : Int) : Option Lean.Json :=
  prs.foldl (fun pr x =>
    let st := Json.fstr x "state"
    if branches.contains ((Json.fstr x "headRefName").getD "") && Json.fstr x "baseRefName" == some base
      && (st == some "OPEN" || (st == some "MERGED" && (Json.fstr x "mergedAt").any (ts · ≥ claimed)))
      && (pr.isNone || (Json.fint x "number").getD 0 > ((pr.bind (Json.fint · "number")).getD 0)) then some x else pr) none

/-- ci.pr_watch: PRs from live owners' task branches, a minute apart while a live agent holds a claim of the repo. -/
def prWatch [Env m] [Sys m] (repo : Option String) : m Unit := do
  let now ← Clock.now
  let some hs ← Store.run (prWatchTxn now (← repoTasks repo)) | return
  let some prs := ghList (← Proc.output ["gh", "pr", "list", "--state", "all", "--limit", "50", "--json",
    "number,headRefName,headRefOid,baseRefName,state,mergedAt,mergeCommit,statusCheckRollup"] repo []) "" | return
  let gated := (← flow repo) == some "pr-gated"
  let main ← Workspaces.main repo
  for (t, brs) in hs do
    let base ← match main with
      | some r => Bases.forTask { id := t.id, base := t.base } r
      | none => Bases.baseFor t.base repo
    if let some pr := pickPr prs brs base (t.first_claimed_at.getD 0) then
      Store.run (prWatchApplyTxn now gated t pr)

/-- ci_poll's gate: not within 5 min of a refusal, a flow with CI, and the poll due. -/
def ciPollGate (now : Int) (noCi : Bool) (every : Int) (db : Db) : Db × Bool :=
  match db.getMeta "ci_error" with
  | some e => if now - ((e.v.bind parseInt).getD 0) < 300 then (db, false) else
      if noCi then (db, false) else due now "ci_polled" every db
  | none => if noCi then (db, false) else due now "ci_polled" every db

/-- ci_poll with gh's runs (none: refused or offline): the push runs of the configured workflow into the ci table; the
red runs whose failed jobs are not known yet. -/
def ciPollApply (now : Int) (runs : Option (List Lean.Json)) (wf : Option String) (db : Db) : Db × List Nat :=
  match runs with
  | none => (db.setMeta "ci_error" (some (d now)), [])
  | some runs =>
    let db := { db with metas := db.metas.filter (·.k != "ci_error"), cis := db.cis.filter (·.workflow.isSome) }
    let db := runs.foldl (fun db r =>
      let path := match Json.field r "path" with | some (.str p) => p | some j => j.compress | none => "nil"
      if Json.fstr r "event" == some "push" && wf.all (hasSub path ·) then
        let id := ((Json.fint r "databaseId").getD 0).toNat
        let concl := (Json.fstr r "conclusion").filter (· ≠ "")
        if db.cis.any (·.id == id) then
          { db with cis := db.cis.map fun c => if c.id == id then
              { c with status := Json.fstr r "status", conclusion := concl, updated := Json.fstr r "updatedAt" } else c }
        else { db with cis := db.cis ++ [({ id, sha := Json.fstr r "headSha", status := Json.fstr r "status", conclusion := concl, url := Json.fstr r "url", created := Json.fstr r "createdAt", updated := Json.fstr r "updatedAt", workflow := some ((Json.fstr r "workflow").getD "") } : Ci)] }
      else db) db
    (db, (db.cis.filter fun c => c.conclusion == some "failure" && c.failed.isNone).map (·.id))

/-- ci.ci_poll: the base's push runs, one request a minute (`every`), and each red run's failed jobs once. -/
def ciPoll (repo : Option String) (every : Int := 60) : m Unit := do
  let now ← Clock.now
  let noCi := (← flow repo) == some "none"
  if !(← Store.run (Txn.update [Sels.metas ["ci_error", "ci_polled"]] [] (ciPollGate now noCi every))) then return
  let base ← Bases.default repo
  if base != "main" && (← Bases.remoteRef base repo).isNone then return
  let out ← Proc.output ["gh", "api", s!"repos/\{owner}/\{repo}/actions/runs?branch={base}&event=push&per_page=20", "--jq",
    "[.workflow_runs[] | {databaseId: .id, headSha: .head_sha, status, conclusion, url: .html_url," ++
    " createdAt: .created_at, updatedAt: .updated_at, event, workflow: .name, path}]"] repo []
  let runs := match out with
    | some o => if o.code == 0 && o.stdout != "" then
        (match Json.decode o.stdout with | some (.arr a) => some a.toList | some (.obj _) => some [] | _ => none) else none
    | none => none
  let wf := Json.fstr (← ciCfg repo) "workflow"
  let reds ← Store.run (Txn.update [Sels.metas ["ci_error"], Sels.all .ci] [] (ciPollApply now runs wf))
  for id in reds do
    if let some o ← Proc.output ["gh", "run", "view", d id, "--json", "jobs", "--jq",
        "[.jobs[] | select(.conclusion==\"failure\") | .name] | join(\", \")"] repo [] then
      if o.code == 0 then
        Store.run (Txn.update [{ table := .ci, cond := .eq "id" (.int (Int.ofNat id)) }] [] fun db =>
          ({ db with cis := db.cis.map fun c => if c.id == id then { c with failed := some (strip o.stdout) } else c }, ()))

/-- What ci_check's first step leaves for the world: a new red run that needs its task (the run and the last green). -/
structure NewRed where
  red : Ci
  green : Option Ci

/-- The runs ci_check looks at, newest first: the last 10 that finished and were not cancelled. -/
def checkRuns (db : Db) : List Ci :=
  ((db.cis.filter fun c => c.status == some "completed" && c.conclusion.isSome && c.conclusion != some "cancelled").mergeSort
    fun a b => a.created.getD "" ≥ b.created.getD "").take 10

/-- ci_check before the git and gh reads: a green run on top closes the red tasks it is as new as; a new red run is
logged once and joins an open red task's body, or is returned to get its own task. The red tasks are those of `ids`,
the repo's (none: every task's): another repo's runs never touch them (board #136). -/
def ciCheckStep (now : Int) (ids : Option (List Int)) (db : Db) : Db × Option NewRed :=
  let runs := checkRuns db
  match runs with
  | [] => (db, none)
  | red :: _ =>
    let openRed := db.tasks.filter fun t => likePrefix (t.title.getD "") Tasks.RED_TASK &&
      (t.state = .open || t.state = .claimed || t.state = .blocked) && inIds ids t
    if red.conclusion == some "success" then
      (Queue.tidy <| openRed.foldl (fun db t =>
        let n := (t.title.getD "").toList.drop (Tasks.RED_TASK ++ "run ").length |>.takeWhile Char.isDigit
        let n := if (t.title.getD "").startsWith (Tasks.RED_TASK ++ "run ") && !n.isEmpty then (String.ofList n).toNat? else none
        if n.any (red.id < ·) then db else
        let db := db.set t.id fun x => { x with state := .done, evidence := some s!"green run {d red.id} at {short red.sha}", lease_until := none, hold := none, done_at := some now }
        let db := db.log now (some "swarm") "done" none (some s!"#{d t.id} green run {d red.id}")
        match t.owner with
        | some o => (Msgs.post db now .system (.agent o) s!"main is green (run {d red.id}): #{d t.id} is done; stop fixing it." false (some "system")).1
        | none => db) db, none)
    else if !(["failure", "timed_out", "startup_failure"].contains (red.conclusion.getD "")) then (db, none)
    else if db.events.any fun e => e.kind == some "ci-red" && e.data == some (d red.id) then (db, none)
    else
      let db := db.log now (some "swarm") "ci-red" none (some (d red.id))
      let failed := red.failed.filter (· ≠ "")
      match openRed with
      | t :: _ =>
        let add := s!"\nLater red: run {d red.id} at {short red.sha}" ++ (match failed with | some f => s!" ({f})" | none => "")
        let fixedAt := ((db.events.filter fun e => e.kind == some "red-fixed" && (e.data.getD "").startsWith s!"#{d t.id} ").filterMap (·.ts)).foldl max 0
        let reopen := hasSub (t.hold.getD "") "awaiting a green run" && ts (red.created.getD "") > fixedAt
        (db.set t.id fun x => { x with body := x.body.map (· ++ add), hold := if reopen then none else x.hold }, none)
      | [] => (db, some { red, green := runs.find? (·.conclusion == some "success") })

/-- ci_check's second step: the red task with the commits' authors and the failed log's tail, and the posts. -/
def ciNewRedTask (now : Int) (comms : Option String) (r : NewRed) (rng : String) (names : List String) (tail : String) (db : Db) : Db :=
  let red := r.red
  let failed := red.failed.filter (· ≠ "")
  let about := s!"main CI is red (run {d red.id} {red.url.getD "None"}), commits {rng}, authors: {if names.isEmpty then "none" else ", ".intercalate names}."
  let title := Tasks.RED_TASK ++ "run " ++ d red.id ++ (match failed with | some f => s!" ({f})" | none => "")
  let tid := db.taskNext
  let db := { db with tasks := db.tasks ++ [({ id := tid, title := some title, body := some (about ++ " Fix forward on main. When your fix is on main, `swarm task done " ++ d tid ++ " --evidence <sha>` releases you; watchd closes the task on the next green run.\n" ++ tail), created_by := some "swarm", created_at := some now } : Task)], taskNext := db.taskNext + 1 }
  let db := db.log now (some "swarm") "task-add" none (some s!"#{d tid} {title}")
  let live := (Agents.live db).map (·.name)
  let msg := s!"{about} Task #{d tid} is its one fix: `swarm task claim {d tid}` if your commit broke it, then fix forward; if someone holds it, leave it to them."
  let sus := names.filter live.contains
  let db := sus.foldl (fun db n => (Msgs.post db now .system (.agent n) msg true (some "system")).1) db
  match comms with
  | some c => if sus.isEmpty then (Msgs.post db now .system (.agent c) (msg ++ " No live agent has commits in it.") true (some "system")).1 else db
  | none => db

/-- ci_check's first transaction: `ciCheckStep`'s commit when it needs no task; a new red run comes back uncommitted,
for `ciCheckApply` to log with its task once the reads are done. -/
def ciCheckFirst (now : Int) (ids : Option (List Int)) (db : Db) : Db × Option NewRed :=
  match ciCheckStep now ids db with
  | (_, some r) => (db, some r)
  | x => x

/-- ci_check's second transaction: the `ci-red` event and the task for red run `r` in one commit, so a stop never
leaves the event without its task; if the check now finds another outcome it commits nothing (the next check redoes it). -/
def ciCheckApply (now : Int) (ids : Option (List Int)) (comms : Option String) (r : NewRed) (rng : String)
    (names : List String) (tail : String) (db : Db) : Db :=
  match ciCheckStep now ids db with
  | (db', some r') => if r'.red.id == r.red.id then ciNewRedTask now comms r' rng names tail db' else db
  | _ => db

/-- What `ciCheckStep` reads: the repo's runs, the open, claimed and blocked tasks of `ids`, the queue, the `red-fixed`
events and the newest run's `ci-red`. -/
def ciCheckSels (ids : Option (List Int)) : Txn (List Sel) := do
  let red := (checkRuns (← Txn.slice [Sels.all .ci])).head?.map fun r =>
    ({ table := .event, cond := .and (.eq "kind" (.text "ci-red")) (.eq "data" (.text (d r.id))) } : Sel)
  return [Sels.all .ci, ofIds ids { table := .task, cond := .oneOf "state" [.text "open", .text "claimed", .text "blocked"] },
    TaskTxn.queuedSel, { table := .event, cond := .eq "kind" (.text "red-fixed") }] ++ red.toList

/-- The `Swarm-Agent:` names in commit messages, distinct and sorted. -/
def authors (log : String) : List String :=
  let ns := (splitlines log).filterMap fun l =>
    if l.startsWith "Swarm-Agent:" then (words (l.drop 12).toString).head? else none
  (Bases.uniq ns).mergeSort (· ≤ ·)

/-- Title `x` is red run `id`'s task's. -/
def redTitleOf (id : Nat) (x : String) : Bool :=
  let p := Tasks.RED_TASK ++ "run " ++ d id
  x == p || x.startsWith (p ++ " ")

/-- ci.ci_check: a red run on top becomes one task naming the live suspects, a task of `repo` (sw-global §2); a green
one closes it. -/
def ciCheck [Env m] [Sys m] (repo comms : Option String) : m Unit := do
  let now ← Clock.now
  let ids := (← repoTasks repo).map (·.2)
  let some r ← Store.run (do Txn.update (← ciCheckSels ids) [.msg] (ciCheckFirst now ids)) | return
  let rng := match r.green with
    | some g => s!"{g.sha.getD ""}..{r.red.sha.getD ""}"
    | none => s!"-20 {r.red.sha.getD ""}"
  let log := match ← Git.out (["log", "--format=%B%x1e", "--end-of-options"] ++ words rng) repo with
    | some o => if o.code == 0 then o.stdout else ""
    | none => ""
  let lines := match ← Proc.output ["gh", "run", "view", d r.red.id, "--log-failed"] repo [] with
    | some o => if o.code == 0 then splitlines o.stdout else []
    | none => []
  let tail := "\n".intercalate (lines.drop (lines.length - 30))
  let title : Sel := { table := .task, cond := .pre "title" (Tasks.RED_TASK ++ "run " ++ d r.red.id) }
  let tid ← Store.run do
    Txn.update ((← ciCheckSels ids) ++ [Sels.live, title]) [.task, .msg] fun db =>
      let db := ciCheckApply now ids comms r rng (authors log) tail db
      (db, ((db.tasks.filter fun t => t.title.any (redTitleOf r.red.id)).getLast?).map (·.id))
  if let (some tid, some p) := (tid, ← Workspaces.main repo) then
    Swarms.addTaskRepos tid [(p, none, some (← Bases.default (some p)))]

/-- The verdict for `sha`: the newest completed, non-cancelled main CI run that includes it (its own, or a later run
of the batch it was pushed in), else pending with the newest unfinished one, and the run (ci.ci_for). -/
def ciFor (runs : List Ci) (sha : String) (cwd : Option String) : m (String × Option Ci) := do
  let mut pend : Option Ci := none
  for r in runs.mergeSort fun a b => a.created.getD "" ≥ b.created.getD "" do
    if r.sha == some sha || (← Git.git ["merge-base", "--is-ancestor", sha, r.sha.getD "nil"] cwd).isSome then
      if r.status != some "completed" then pend := pend.orElse fun _ => some r
      else if r.conclusion != some "cancelled" then
        return (if r.conclusion == some "success" then "success" else "failure", some r)
  return ("pending", pend)

end SwarmLean.Ci
