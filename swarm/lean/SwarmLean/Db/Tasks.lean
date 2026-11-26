import SwarmLean.Db.Agents
import SwarmLean.Db.Compact
import SwarmLean.Db.Msgs
import Std.Data.HashMap

/-! tasks.lua's board logic as pure functions of the db: deps, the pool, timing, and each `task` action's effect.
An action is `… → Db → Db × Except String α`: the db it leaves and its answer or the text it dies with. A die inside
the Lua's transaction leaves the db as the transaction found it; what the Lua wrote before its transaction stays. -/

namespace SwarmLean.Tasks
open Agents

/-- The default lease (tasks.LEASE). -/
def LEASE : Int := 7200
/-- A red main's task title prefix (tasks.RED_TASK). -/
def RED_TASK : String := "main red: "
/-- A new task's priority. -/
def DEFAULT_PRIORITY : Priority := .medium
/-- The longest title without a body (tasks.TITLE_MAX). -/
def TITLE_MAX : Nat := 100
/-- The event kinds about a task (tasks.TASK_KINDS). -/
def TASK_KINDS : List String := ["task-add", "claim", "spawn", "done", "block", "unblock", "release", "drop", "task-edit",
  "queue", "unqueue", "hold", "unhold", "task-land", "task-unland", "task-note", "task-notes-given", "task-backlog",
  "task-ready", "task-assign", "task-place", "task-duplicate", "task-parent"]
/-- The task id an event is about: data `#<id>` or `auto #<id>`, then the end or a space (tasks.event_task). -/
def eventTask (e : Event) : Option Nat :=
  let s := e.data.getD ""
  let s := if s.startsWith "auto #" then some (s.drop 6).toString else if s.startsWith "#" then some (s.drop 1).toString else none
  s.bind fun r =>
    let ds := r.toList.takeWhile Char.isDigit
    let rest := r.toList.drop ds.length
    if ds.isEmpty || !(rest.isEmpty || rest.head? == some ' ') then none else (String.ofList ds).toNat?

/-- The event kinds `task show --json` lists: TASK_KINDS and the other kinds whose data starts with the task's `#<id>`,
and `task-blocked`, whose path is the id. -/
def SHOW_KINDS : List String := TASK_KINDS ++ ["renew", "answer", "task-after", "task-priority", "task-pr", "task-ci",
  "red-fixed", "task-blocked"]

/-- An event kind as the task's activity names it: add, claim, spawn, renew, release, block, answer, unblock, note,
edit, land, unland, ci, pr, done, drop, held, unheld (old events), backlog, ready, assign, place, duplicate; the rest
without their `task-` prefix. -/
def shortKind (k : String) : String :=
  match k with
  | "hold" => "held"
  | "unhold" => "unheld"
  | "red-fixed" => "ci"
  | "task-blocked" => "block"
  | k => if k.startsWith "task-" then (k.drop 5).toString else k

/-- The events about task `tid`, in order (tasks.task_events). -/
def taskEvents (db : Db) (tid : Nat) : List Event :=
  db.events.filter fun e => (e.kind.map (TASK_KINDS.contains ·)).getD false && eventTask e == some tid

/-- A task's timing (tasks.task_timing). -/
structure Timing where
  created_at : Option Int
  first_claimed_at : Option Int
  done_at : Option Int
  dropped_at : Option Int
  queue_wait_s : Option Int
  work_s : Option Int
  total_s : Option Int
  blocked_s : Int
  claims : Nat
  releases : Nat
  holders : List String
  claim_ctx : Option Int
  done_ctx : Option Int
  pr : Option Int
  merged_at : Option Int
  ci_conclusion : Option Conclusion
  merge_to_green_s : Option Int

/-- Task `r`'s durations from its columns, else from its events `evs` (tasks.task_timing). -/
def timing (r : Task) (evs : List Event) (now : Int) : Timing :=
  let ts (k : String) (agg : Int → Int → Int) : Option Int := evs.foldl (fun v e =>
    let kind := if e.kind == some "spawn" then some "claim" else e.kind
    if kind == some k then match v, e.ts with
      | some x, some y => some (agg x y)
      | none, y => y
      | x, none => x
    else v) none
  let claimish (e : Event) := e.kind == some "claim" || e.kind == some "spawn"
  let claims := (evs.filter claimish).length
  let holders := (evs.filter claimish).foldl (fun hs e => match e.agent with
    | some a => if hs.contains a then hs else hs ++ [a]
    | none => hs) []
  let releases := (evs.filter (·.kind == some "release")).length
  let created := (pyI r.created_at).orElse fun _ => ts "task-add" min
  let first := (pyI r.first_claimed_at).orElse fun _ => ts "claim" min
  let done := (pyI r.done_at).orElse fun _ => if r.status = .completed then ts "done" max else none
  let dropped := (pyI r.dropped_at).orElse fun _ => if r.category = .cancelled then ts "drop" max else none
  let stop := ((pyI done).orElse fun _ => pyI dropped).getD now
  let (blocked, start) := evs.foldl (fun (b, s) e =>
    if e.kind == some "block" && s.isNone then (b, some (e.ts.getD 0))
    else if e.kind == some "unblock" && s.isSome then (b + e.ts.getD 0 - s.getD 0, none)
    else (b, s)) ((0 : Int), (none : Option Int))
  let blocked := match start with
    | some s => if r.status = .needsInput then blocked + stop - s else blocked
    | none => blocked
  let span (a b : Option Int) : Option Int := match a, b with
    | some x, some y => some (y - x)
    | _, _ => none
  { created_at := created, first_claimed_at := first, done_at := done, dropped_at := dropped,
    queue_wait_s := span created first, work_s := span first done, total_s := span created done, blocked_s := blocked,
    claims, releases, holders, claim_ctx := r.claim_ctx, done_ctx := r.done_ctx, pr := r.pr, merged_at := r.merged_at,
    ci_conclusion := r.ci_conclusion, merge_to_green_s := span r.merged_at r.ci_green_at }

/-- The ids a task waits on, in order (tasks.deps_of). -/
def depsOf (r : Task) : List Int := (commaPieces (r.deps.getD "")).filterMap parseInt

/-- The not-done rows of `r`'s deps, in `r`'s order (tasks.undone). -/
def undone (db : Db) (r : Task) : List Task :=
  (depsOf r).filterMap fun i => (db.find i).filter (·.status ≠ .completed)

/-- Ready and Backlog tasks whose deps name `tid` (tasks.waiters). -/
def waiters (db : Db) (tid : Int) : List Task :=
  db.tasks.filter fun t => (t.status = .ready || t.status = .backlog) && match t.deps with
    | some ds => hasSub ("," ++ ds ++ ",") ("," ++ d tid ++ ",")
    | none => false

/-- SQL's `','||t.deps||',' like '%,'||d.id||',%'` for some not-done task `d`: `t` waits on an undone task. -/
def blockedByDeps (db : Db) (t : Task) : Bool :=
  match t.deps with
  | none => false
  | some ds => db.tasks.any fun x => x.status ≠ .completed && hasSub ("," ++ ds ++ ",") ("," ++ d x.id ++ ",")

/-- The path `start, …, target` along deps, if any (tasks.dep_path): the cycle `task after` would close. -/
def depPath (db : Db) (start target : Int) : Option (List Int) :=
  let rec go (fuel : Nat) (seen : List Int) : List (List Int) → Option (List Int)
    | [] => none
    | path :: stack =>
      match fuel with
      | 0 => none
      | fuel + 1 =>
        let last := path.getLastD start
        if last == target then some path
        else if seen.contains last then go fuel seen stack
        else
          let deps := ((db.find last).map depsOf).getD []
          go fuel (last :: seen) ((deps.map fun x => path ++ [x]) ++ stack)
  -- each task is expanded once, so the pops are at most one more than all deps lists together
  go (2 + db.tasks.foldl (fun n t => n + (depsOf t).length) 0) [] [[start]]

/-- The user released `r` from an agent still at work that has not read the stop (tasks.stop_pending). -/
def stopPending (db : Db) (r : Task) : Bool :=
  match py r.stop_to with
  | none => false
  | some to =>
    match db.agent to with
    | none => false
    | some a =>
      if a.ended.isSome || (a.status != some .working && a.status != some .blocked) then false
      else
        let cur := ((db.cursor to).bind (·.last_msg_id)).getD 0
        cur < r.stop_msg.getD 0

/-- Lua's `title like 'main red: %'` as a sort key: 1 for a red task. -/
def redKey (t : Task) : Nat := if likePrefix (t.title.getD "") RED_TASK then 1 else 0

/-- Order by `red desc, place, id` (no place first); priority never orders. -/
def boardLe (red : Task → Nat) (a b : Task) : Bool :=
  let pa := a.pos.map (· + 1) |>.getD 0
  let pb := b.pos.map (· + 1) |>.getD 0
  if red a != red b then red a > red b else if pa != pb then pa < pb else a.id ≤ b.id

/-- Ready tasks with every dep completed and no pending stop, red first then by place (tasks.pool). -/
def pool (db : Db) : List Task :=
  ((db.tasks.filter fun t => t.status = .ready && !blockedByDeps db t).mergeSort (boardLe redKey)).filter
    (!stopPending db ·)

/-- `#3, #5` (tasks.ids). -/
def idsText (l : List Int) : String := ", ".intercalate (l.map fun x => "#" ++ d x)

/-- `, owned by x` when the row has an owner (tasks.owned). -/
def owned (r : Task) : String := match py r.owner with
  | some o => ", owned by " ++ o
  | none => ""

/-- task show's after: and blocks: lines (tasks.dep_lines). -/
def depLines (db : Db) (r : Task) : String :=
  let deps := depsOf r
  let a := if deps.isEmpty then "" else
    "\nafter: " ++ ", ".intercalate (deps.map fun x =>
      "#" ++ d x ++ " " ++ ((db.find x).map (·.status.name)).getD "missing")
  let w := if r.status ≠ .completed then waiters db r.id else []
  a ++ (if w.isEmpty then "" else "\nblocks: " ++ ", ".intercalate (w.map fun x => "#" ++ d x.id))

/-- Fails on a dep that is no task (tasks.no_task_to_wait_on). -/
def checkDeps (db : Db) (deps : List Int) : Except String Unit :=
  deps.forM fun x => if (db.find x).isNone then .error s!"no task #{d x} to wait on" else .ok ()

/-- A task given deps `s`. -/
def depsF (s : String) (t : Task) : Task := { t with deps := some s }

/-- A task claimed by `me` until `u` at context `k` at time `now`. -/
def claimF (me : String) (u k now : Int) (t : Task) : Task :=
  { t with state := .inProgress me u, claim_ctx := some k,
           first_claimed_at := t.first_claimed_at.orElse fun _ => some now }

/-- A task its owner gave back: Ready, no assignee, its place kept. -/
def reopenF (t : Task) : Task := { t with state := .ready none }

/-- A task the communicator took back from its owner: Ready, no assignee, its place kept. -/
def reopenFromF (t : Task) : Task := { t with state := .ready none }

/-- The place after every other: one more than the last. -/
def endPos (db : Db) : Int := ((db.tasks.filterMap (·.pos)).foldl max 0) + 1

/-- Task `id`'s goal ancestors, nearest first (a cycle, which the commands refuse, cannot loop). -/
def goalAncestors (db : Db) (id : Int) : List Int :=
  let rec go : Nat → Int → List Int
    | 0, _ => []
    | n + 1, i => match (db.find i).bind (·.parent) with
      | some p => p :: go n p
      | none => []
  go 64 id

/-- The refusal of a sub-issue `id` waiting on `x`, its parent or an ancestor of it: the parent is not staffed while
the sub-issue is open, so they would wait on each other. -/
def checkAncestorDep (anc : List Int) (id : Int) (deps : List Int) : Except String Unit :=
  match anc.find? deps.contains with
  | some a => .error s!"#{d id} is a sub-issue of #{d a}: it can't wait on it"
  | none => .ok ()

/-- Fails on a missing dep, one that would close a cycle through `id`, or an ancestor of `id`. -/
def checkCycles (db : Db) (id : Int) (deps : List Int) : Except String Unit := do
  checkAncestorDep (goalAncestors db id) id deps
  for x in deps do
    checkDeps db [x]
    if let some cyc := depPath db x id then
      throw s!"that would be a cycle: {" → ".intercalate ((id :: cyc).map fun y => "#" ++ d y)}"

/-- Refuses a missing dep or a cycle, then stores the list (tasks.set_deps): the db and the list as texts. -/
def setDeps (db : Db) (id : Int) (deps : List Int) : Except String (Db × List String) :=
  match checkCycles db id deps with
  | .error e => .error e
  | .ok () => .ok (db.set id (depsF (",".intercalate (deps.map d))), deps.map d)

/-- `n`'s context in tokens (tasks.ctx_of). -/
def ctxOf (db : Db) (n : String) : Int := ((db.agent n).bind (·.ctx_tokens)).getD 0

/-- reap took task `id` from `n` and nobody claimed it since: retaking it is n's own work (tasks.reaped_from). -/
def reapedFrom (db : Db) (n : String) (id : Int) : Bool :=
  let last := (taskEvents db id.toNat).foldl (fun l e =>
    if e.kind == some "claim" || e.kind == some "spawn" then e.agent else l) none
  last == some n && db.events.any fun e =>
    e.kind == some "reap" && e.agent == some n && e.data == some s!"task #{d id} lease expired"

/-- A `--label` text as stored: split at commas and spaces, empties and repeats dropped; none when nothing is left. -/
def labelsText (s : String) : Option String :=
  let ls := ((s.map fun c => if isSpace c then ',' else c).splitOn ",").filter (· ≠ "")
  if ls.isEmpty then none else some (",".intercalate ls.eraseDups)

/-- A task's labels (board #186). -/
def labelsOf (t : Task) : List String := ((t.labels.getD "").splitOn ",").filter (· ≠ "")

/-- The tasks a task's creator held when it was added (board #186). -/
def parentsOf (t : Task) : List Int := ((t.parents.getD "").splitOn ",").filterMap parseInt

/-- The goal hierarchy (sub-issues) as a forest over (id, state, parent): each task's children and states. A task is
open while its state's category is not completed or cancelled. -/
structure Tree where
  kids : Std.HashMap Int (List Int) := {}
  st : Std.HashMap Int Status := {}
  par : Std.HashMap Int Int := {}

/-- The forest of tasks given as (id, state, parent), in id order of the list. -/
def Tree.ofNodes (ns : List (Int × Status × Option Int)) : Tree :=
  ns.foldl (fun tr (i, s, p) =>
    { tr with st := tr.st.insert i s,
              kids := match p with | some q => tr.kids.insert q (tr.kids.getD q [] ++ [i]) | none => tr.kids,
              par := match p with | some q => tr.par.insert i q | none => tr.par }) {}

/-- The forest of the db's tasks. -/
def Tree.ofDb (db : Db) : Tree := Tree.ofNodes (db.tasks.map fun t => ((t.id : Int), t.status, t.parent))

/-- How deep the hierarchy is followed (a cycle, which the commands refuse, cannot loop). -/
def Tree.DEPTH : Nat := 64

/-- `id`'s direct children. -/
def Tree.childrenOf (tr : Tree) (id : Int) : List Int := tr.kids.getD id []

/-- Whether task `i` is open (a task not loaded is not). -/
def Tree.isOpen (tr : Tree) (i : Int) : Bool := (tr.st.get? i).any (!·.closed)

/-- `id`'s descendants at any depth, parents before their children. -/
def Tree.descendants (tr : Tree) : Nat → Int → List Int
  | 0, _ => []
  | n + 1, id => (tr.childrenOf id).flatMap fun k => k :: tr.descendants n k

/-- The open descendants of `id`. -/
def Tree.openBelow (tr : Tree) (id : Int) : List Int := (tr.descendants Tree.DEPTH id).filter tr.isOpen

/-- `id`'s ancestors, root first (the nearest last). -/
def Tree.ancestors (tr : Tree) (id : Int) : List Int :=
  let rec go : Nat → Int → List Int → List Int
    | 0, _, acc => acc
    | n + 1, i, acc => match tr.par.get? i with
      | some p => go n p (p :: acc)
      | none => acc
  go Tree.DEPTH id []

/-- (done, total) over the leaves below `id` at any depth: a leaf is a task with no children; total leaves exclude the
Cancelled and Duplicate ones, done are the Completed. None for a task with no children. -/
def Tree.progress (tr : Tree) (id : Int) : Option (Nat × Nat) :=
  if (tr.childrenOf id).isEmpty then none else
  let leaves := (tr.descendants Tree.DEPTH id).filter fun k => (tr.childrenOf k).isEmpty
  let live := leaves.filter fun k => (tr.st.get? k).any (·.category != .cancelled)
  some ((live.filter fun k => (tr.st.get? k).any (· == Status.completed)).length, live.length)

/-- The ids of the open tasks that have a child or more, and no open descendant: all their sub-issues are done. -/
def Tree.allDone (tr : Tree) : List Int :=
  (tr.kids.toList.filterMap fun (p, ks) =>
    if !ks.isEmpty && tr.isOpen p && (tr.openBelow p).isEmpty then some p else none).mergeSort fun a b => decide (a ≤ b)

/-- The ids with an open descendant at any depth: the ancestors of every open task. -/
def Tree.openParents (tr : Tree) : Std.HashSet Int :=
  tr.st.fold (fun h i s => if s.closed then h else (tr.ancestors i).foldl (fun h a => h.insert a) h) {}

/-- Task `t` is a container: an open descendant, at any depth, keeps it from staffing. -/
def isContainer (db : Db) (t : Task) : Bool := !((Tree.ofDb db).openBelow t.id).isEmpty

/-- The refusal of a parent `n` for a task: it is a task, and open (a closed task takes no new sub-issue). -/
def checkParent (db : Db) (n : Int) : Except String Unit :=
  match db.find n with
  | none => .error s!"no task #{d n}"
  | some p => if p.status.closed then .error s!"task #{d n} is {p.status.name}; a closed task can't take a new sub-issue" else .ok ()

/-- `task parent`: task `id` becomes a sub-issue of `p`, or top level with none; the same refusals as `task add
--parent`, and a task can't be its own parent or below itself. -/
def setParent (c : Ctx) (id : Int) (p : Option Int) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some _ =>
    let go (db : Db) : Db × Except String Unit :=
      (( db.set id ({ · with parent := p })).log c.now (some c.me) "task-parent" none
        (some s!"#{d id} parent {match p with | some n => "#" ++ d n | none => "none"}"), .ok ())
    match p with
    | none => go db
    | some n =>
      if n == id then (db, .error s!"task #{d id} can't be its own parent")
      else match checkParent db n with
        | .error e => (db, .error e)
        | .ok () =>
          if ((Tree.ofDb db).ancestors n).contains id then
            (db, .error s!"that would be a cycle: #{d n} is below #{d id}")
          else match checkAncestorDep (n :: goalAncestors db n) id (((db.find id).map depsOf).getD []) with
            | .error e => (db, .error e)
            | .ok () => go db

/-- `task add`: the new task's id. -/
def add (c : Ctx) (a : AddArgs) (db : Db) : Db × Except String Nat :=
  if !a.title.any (!isSpace ·) then (db, .error "the title can't be empty")
  else if a.title.contains '\n' then (db, .error "the title is one line; put the rest in --body or --body-file")
  else if a.title.utf8ByteSize > TITLE_MAX && (py (some a.body)).isNone then
    (db, .error s!"the title is over {TITLE_MAX} characters with no body; move the detail to --body or --body-file")
  else match checkDeps db a.deps with
    | .error e => (db, .error e)
    | .ok () =>
    match (match a.parent with | some n => checkParent db n *> checkAncestorDep (n :: goalAncestors db n) db.taskNext a.deps | none => .ok ()) with
    | .error e => (db, .error e)
    | .ok () =>
      let id := db.taskNext
      let t : Task := { id, title := some a.title, body := some a.body, created_by := some c.me,
                        deps := py (some (",".intercalate (a.deps.map d))), model := a.model, effort := a.effort,
                        base := a.base, created_at := some c.now, priority := a.priority.getD DEFAULT_PRIORITY,
                        pos := some (endPos db),
                        labels := a.labels.bind labelsText, parent := a.parent,
                        parents := py (some (",".intercalate ((db.tasks.filter fun t => t.owner == some c.me &&
                          (t.status = .inProgress || t.status = .needsInput)).map (d ·.id)))) }
      let db := { db with tasks := db.tasks ++ [t], taskNext := db.taskNext + 1 }
      (db.log c.now (some c.me) "task-add" none (some s!"#{d id} {a.title}"), .ok id)

/-- `task claim`: `lease` is `--lease` as given. -/
def claim (c : Ctx) (id : Int) (lease : String) (db : Db) : Db × Except String Claimed :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    let forced := c.force && inCharge db c.comms c.me
    if r.status = .backlog && !forced then
      (db, .error s!"task #{d id} is in Backlog{match r.note with | some n => ": " ++ n | none => ""}; {if c.force then "only the communicator or the user can --force it"
        else "`swarm task ready` it first (or the communicator's --force)"}")
    else if (r.status = .ready || r.status = .backlog) && (py r.assignee).any (· != c.me) && !forced then
      (db, .error s!"task #{d id} is assigned to {(py r.assignee).getD ""}; only it claims it{if c.force then " (only the communicator or the user can --force it)"
        else " (or the communicator's --force)"}")
    else
    match undone db r with
    | dep :: _ =>
      (db, .error s!"#{d id} waits on #{d dep.id} ({dep.status.name}{match py dep.owner with
        | some o => ", claimed by " ++ o | none => ""})")
    | [] =>
      let db := touch db c.me none c.here c.now
      let k := ctxOf db c.me
      if Compact.over k (Compact.nudgeAt db) && !reapedFrom db c.me id then
        (db, .error s!"context ~{fdiv k 1000}k, too high to take new work: `swarm compact` (it runs when this turn ends) or finish what you hold and go idle")
      else match dur lease with
      | none => (db, .error s!"bad duration '{lease}' (use 90s, 30m, 2h)")
      | some l =>
        let «until» := c.now + l
        match db.find id with
        | none => (db, .error s!"no task #{d id}")
        | some r1 =>
          if stopPending db r1 then
            (db, .error s!"task #{d id} was released from {r1.stop_to.getD ""}, which hasn't read the stop yet; try again once it has")
          else if (r1.status = .ready || r1.status = .backlog) && !blockedByDeps db r1 then
            let db := db.set id (claimF c.me «until» k c.now)
            (db.log c.now (some c.me) "claim" none (some s!"#{d id} {r.title.getD ""}"), .ok ⟨«until», py r.body⟩)
          else match (if r1.status = .ready || r1.status = .backlog then undone db r1 else []) with
            | dep :: _ => (db, .error s!"#{d id} waits on #{d dep.id} ({dep.status.name})")
            | [] => (db, .error s!"task #{d id} is {r1.status.name}{owned r1}")

/-- `task after`: what the deps became. -/
def after (c : Ctx) (id : Int) (deps : List Int) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.status ≠ .ready && r.status ≠ .backlog then
      (db, .error s!"task #{d id} is {r.status.name}; only a Ready or Backlog task's dependencies can change")
    else match setDeps db id deps with
      | .error e => (db, .error e)
      | .ok (db', ds) =>
        (db'.log c.now (some c.me) "task-after" none (some s!"#{d id} after {(py (some (",".intercalate ds))).getD "-"}"),
         .ok ())

/-- `task priority`. -/
def priority (c : Ctx) (id : Int) (p : Priority) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.status.closed then
      (db, .error s!"task #{d id} is {r.status.name}; a closed task's priority can't change")
    else
      let db := db.set id ({ · with priority := p })
      (db.log c.now (some c.me) "task-priority" none (some s!"#{d id} {p.text}"), .ok ())

/-- The row is `n`'s claimed task (the Lua's `where id=? and owner=? and state='claimed'`). -/
def mine (r : Task) (n : String) : Bool := r.owner == some n && r.status = .inProgress

/-- `task renew`: the lease's new end. -/
def renew (c : Ctx) (id : Int) (lease : String) (db : Db) : Db × Except String Int :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    match dur lease with
    | none => (db, .error s!"bad duration '{lease}' (use 90s, 30m, 2h)")
    | some l =>
      if !mine r c.me then (db, .error s!"task #{d id} is not claimed by you")
      else ((db.set id fun t => { t with state := t.state.renew (c.now + l) }).log c.now (some c.me) "renew" none
        (some s!"#{d id} {d (c.now + l)}"), .ok (c.now + l))

/-- A claimed task handed to `lander` at commit `sha` at time `now`: landing, its lease gone, its owner kept; any
other task as it is. -/
def landF (sha : String) (lander : Option String) (now : Int) (t : Task) : Task :=
  match t.state with
  | .inProgress o _ => { t with state := .inReview o ⟨sha, lander, now⟩ }
  | _ => t

/-- `n` may close landing task `r` (board #200): the lander `task land` named, an agent whose role has the word
lander, or the communicator (or the user). -/
def isLander (db : Db) (comms : Option String) (n : String) (r : Task) : Bool :=
  r.lander == some n || inCharge db comms n ||
    ((db.agent n).bind (·.role)).any fun x => (words (x.map fun c => if c.isAlphanum then c.toLower else ' ')).contains "lander"

/-- `#3 In Review abc123 by l1`: a landing task's commit and lander. -/
def landingText (id : Int) (r : Task) : String :=
  s!"#{d id} In Review {String.ofList ((r.land_sha.getD "-").toList.take 12)} by {(py r.lander).getD "a lander"}"

/-- The refusal of a close by an agent that is not `r`'s lander. -/
def notLander (id : Int) (r : Task) : String :=
  s!"{landingText id r}; only its lander, an agent with role lander or the communicator closes it"

/-- `task land` (board #200): the owner hands claimed task `id` at commit `sha` to a lander; it is landing, no
longer the owner's to hold, and not claimable until `task done` or `task unland`. -/
def land (c : Ctx) (id : Int) (sha : String) (lander : Option String) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if strip sha == "" then (db, .error "--sha is empty: give the commit that passed its checks")
    else if r.owner != some c.me then
      (db, .error s!"task #{d id} is not yours{match py r.owner with | some o => " (" ++ o ++ " owns it)" | none => ""}; only its owner hands it to a lander")
    else if r.status ≠ .inProgress then
      (db, .error s!"task #{d id} is {r.status.name}; only a claimed task can be handed to a lander")
    else
      let lander := lander.bind fun l => py (some (strip l))
      let db := db.set id (landF (strip sha) lander c.now)
      let db := db.log c.now (some c.me) "task-land" none
        (some s!"#{d id} {strip sha}{match lander with | some l => " by " ++ l | none => ""}")
      let db := match lander with
        | some l => if l != c.me && (db.agents.any fun x => x.name == l && x.ended.isNone) then
            (Msgs.post db c.now (Msgs.Who.ofText c.me) (.agent l) s!"{c.me} handed you #{d id} at {strip sha} to land: `swarm task done {d id} --evidence <sha on its base>` once it is on its base, or `swarm task unland {d id} --why \"…\"`." false).1
          else db
        | none => db
      (db, .ok ())

/-- A task in review its lander gave back: Ready, at High unless Urgent, with why appended to its body. -/
def unlandF (by_ why : String) (t : Task) : Task :=
  { t with state := .ready none,
           priority := if t.priority = .urgent then .urgent else .high,
           body := some ((match py t.body with | some b => b ++ "\n\n" | none => "") ++
             s!"Not landed ({String.ofList ((t.land_sha.getD "-").toList.take 12)}, by {by_}): {why}") }

/-- `task unland` (board #200): the lander gives task `id` in review back as Ready, at High unless Urgent, with the
reason appended to its body; its former owner, if live, and the communicator are told. -/
def unland (c : Ctx) (id : Int) (why : String) (db : Db) : Db × Except String Unlanded :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.status ≠ .inReview then (db, .error s!"task #{d id} is {r.status.name}; only a task In Review can be unlanded")
    else if !isLander db c.comms c.me r then (db, .error (notLander id r))
    else if strip why == "" then (db, .error "--why is empty: say why it did not land")
    else
      let why := oneLine why
      let db := db.set id (unlandF c.me why)
      let p := (((db.find id).map (·.priority)).getD .high)
      let db := db.log c.now (some c.me) "task-unland" none (some s!"#{d id} {why}")
      let text := s!"{c.me} could not land #{d id} ({String.ofList ((r.land_sha.getD "-").toList.take 12)}): {why}. It is Ready again, priority {p.name}."
      let db := match py r.owner with
        | some o => if o != c.me && (db.agents.any fun x => x.name == o && x.ended.isNone) then (Msgs.post db c.now (Msgs.Who.ofText c.me) (.agent o) text false).1 else db
        | none => db
      let db := match commsOf db c.comms with
        | some k => if k != c.me && some k != r.owner then
            (Msgs.post db c.now (Msgs.Who.ofText c.me) (.agent k) (text ++ match py r.owner with | some o => s!" ({o} handed it over.)" | none => "") false).1
          else db
        | none => db
      (db, .ok ⟨r.owner, p⟩)

/-- Why `r`, a task another's or in review, is not `c.me`'s to close (the checks of `task drop`). -/
def notMineToClose (c : Ctx) (db : Db) (r : Task) : Option String :=
  if (r.status = .inProgress || r.status = .needsInput) && r.owner != some c.me && !inCharge db c.comms c.me then
    some s!"#{d r.id} is {r.status.name} by {r.owner.getD "nil"}; only it or the communicator can drop it"
  else if r.status = .inReview && !isLander db c.comms c.me r then some (notLander r.id r)
  else none

/-- `task done`. -/
def done (c : Ctx) (id : Int) (evidence : String) (db : Db) : Db × Except String DoneOut :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if strip evidence == "" then
      (db, .error "--evidence is empty: give the sha, PR or command output that shows the work is done")
    else if r.status = .inReview then
      if !isLander db c.comms c.me r then (db, .error (notLander id r))
      else if !c.onBase then
        (db, .error s!"--evidence {strip evidence}: not a commit on #{d id}'s base; land it first, then give the sha it landed as")
      else
        let db := db.set id fun t => { t with state := t.state.toCompleted, evidence := some evidence, done_at := some c.now }
        (db.log c.now (some c.me) "done" none (some s!"#{d id} {evidence}"), .ok (.landed r.owner))
    else if !mine r c.me then (db, .error s!"task #{d id} is not claimed by you")
    else if (r.title.getD "").startsWith RED_TASK then
      let note := some (strip evidence ++ " awaiting a green run")
      let db := db.set id fun t => { t with state := .backlog none, evidence := some evidence, note := note }
      (db.log c.now (some c.me) "red-fixed" none (some s!"#{d id} {evidence}"), .ok .red)
    else
      let dctx := (db.agent c.me).bind (·.ctx_tokens)
      let db := db.set id fun t => { t with state := t.state.toCompleted, evidence := some evidence, done_at := some c.now,
                                            done_ctx := dctx }
      let db := db.log c.now (some c.me) "done" none (some s!"#{d id} {evidence}")
      (db, .ok (.done (fdiv (ctxOf db c.me) 1000) (stayOf db c.me) (pool db).length))

/-- `task block`: whether the user is away. -/
def block (c : Ctx) (id : Int) (question : String) (db : Db) : Db × Except String Bool :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if !mine r c.me then (db, .error s!"task #{d id} is not claimed by you")
    else
      let db := db.set id fun t => { t with state := t.state.block question }
      (db.log c.now (some c.me) "block" none (some s!"#{d id} {question}"), .ok (away db).isSome)

/-- `task unblock`: the owner it is claimed by again. -/
def unblock (c : Ctx) (id : Int) (answer : String) (db : Db) : Db × Except String (Option String) :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.status ≠ .needsInput then (db, .error s!"task #{d id} is not blocked")
    else if some c.me != r.owner && !inCharge db c.comms c.me then
      (db, .error s!"only {r.owner.getD "nil"} or the communicator can unblock #{d id}")
    else if r.owner.isNone then (db, .error s!"task #{d id} changed under you; `swarm task show {d id}`")
    else
      let ans := py (some answer)
      let db := db.set id fun t => { t with state := t.state.unblock (c.now + LEASE), answer := ans.orElse fun _ => t.answer }
      let db := match ans with  -- the answer in the task's activity, then the unblock
        | some a => db.log c.now (some c.me) "answer" none (some s!"#{d id} {a}")
        | none => db
      let db := db.log c.now (some c.me) "unblock" none (some s!"#{d id}")
      let db := match ans, r.owner with
        | some a, some o => if c.me != o then (Msgs.post db c.now (Msgs.Who.ofText c.me) (.agent o) s!"#{d id} is unblocked. Answer: {a}").1 else db
        | _, _ => db
      (db, .ok r.owner)

/-- `task release`: who it was taken from (the communicator's release of another's task). -/
def release (c : Ctx) (id : Int) (after : Option (List Int)) (db : Db) : Db × Except String (Option String) :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    let fromA := if r.owner != some c.me && inCharge db c.comms c.me then py r.owner else none
    let opened : Except String Db := match fromA with
      | some f =>
        if r.owner == some f && (r.status = .inProgress || r.status = .needsInput) then
          .ok (db.set id reopenFromF)
        else .error s!"task #{d id} is {r.status.name}{owned r}"
      | none =>
        if mine r c.me then .ok (db.set id reopenF)
        else .error s!"task #{d id} is not claimed by you"
    match opened with
    | .error e => (db, .error e)
    | .ok db1 =>
      match (match after with | some l => (setDeps db1 id l).map Prod.fst | none => .ok db1) with
      | .error e => (db, .error e)
      | .ok db2 =>
        let db3 := db2.log c.now (some c.me) "release" none
          (some ("#" ++ d id ++ match fromA with | some f => " from " ++ f | none => ""))
        match fromA with
        | some f =>
          let p := Msgs.post db3 c.now (Msgs.Who.ofText c.me) (.agent f)
            s!"{if c.me == HUMAN then "the user" else c.me} released #{d id}: stop work on it" true
          (p.1.set id ({ · with stop_to := some f, stop_msg := some p.2 }), .ok fromA)
        | none => (db3, .ok fromA)

/-- `task edit`'s new title, body, model, effort and labels for row `r` with the new body `newBody`, the columns changed
and a note for each. -/
def editCols (id : Int) (r : Task) (a : EditArgs) (newBody : Option String) :
    (Option String × Option String × Option String × Option String × Option String) × List String × List String :=
  -- change(col, new, note): a no-op when new equals the current value, as Python truthiness reads it
  let ch (cur : Option String) (new : Option String) (col note : String) (acc : Option String × List String × List String) :=
    if new == py cur then acc else (new, acc.2.1 ++ [col], acc.2.2 ++ [note])
  let (title, f1, n1) := match a.title with
    | some t => ch r.title (some t) "title" s!"title: {r.title.getD ""} -> {t}" (r.title, [], [])
    | none => (r.title, [], [])
  let (body, f2, n2) := match newBody with
    | some b => ch r.body (some b) "body" s!"body replaced: task show {d id}" (r.body, f1, n1)
    | none => (r.body, f1, n1)
  let (body, f3, n3) := match a.append with
    | some x => ch body (some ((match py r.body with | some b => b ++ "\n" | none => "") ++ x)) "body"
        s!"body appended: {x}" (body, f2, n2)
    | none => (body, f2, n2)
  let (model, f4, n4) := match a.model with
    | some m => ch r.model (py (some m)) "model" s!"model: {(py r.model).getD "-"} -> {(py (some m)).getD "-"}" (r.model, f3, n3)
    | none => (r.model, f3, n3)
  let (effort, f5, n5) := match a.effort with
    | some e => ch r.effort (py (some e)) "effort" s!"effort: {(py r.effort).getD "-"} -> {(py (some e)).getD "-"}" (r.effort, f4, n4)
    | none => (r.effort, f4, n4)
  let (labels, fields, notes) := match a.labels with
    | some l => ch r.labels (labelsText l) "labels" s!"labels: {(py r.labels).getD "-"} -> {(labelsText l).getD "-"}" (r.labels, f5, n5)
    | none => (r.labels, f5, n5)
  ((title, body, model, effort, labels), fields, notes)

/-- `task edit`: the fields changed and the task's state. -/
def edit (c : Ctx) (id : Int) (a : EditArgs) (db : Db) : Db × Except String (List String × Status) :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.status = .completed || r.category = .cancelled then (db, .error s!"task #{d id} is {r.status.name}; it can't be edited")
    else if a.title == some "" then (db, .error "the title can't be empty")
    else if a.title.any (·.contains '\n') then (db, .error "the title is one line; put the rest in --body or --body-file")
    else
      if let some (p, none) := a.bodyFile then (db, .error s!"can't read {p}") else
      let newBody := match a.bodyFile with | some (_, some t) => some t | _ => a.body
      let ((title, body, model, effort, labels), fields, notes) := editCols id r a newBody
      if fields.isEmpty then (db, .error "nothing to change") else
      let db := db.set id ({ · with title, body, model, effort, labels })
      let db := db.log c.now (some c.me) "task-edit" none (some s!"#{d id} {", ".intercalate fields}")
      let db := match py r.owner with
        | some o =>
          if (r.status = .inProgress || r.status = .needsInput) && o != c.me && (db.agents.any fun x => x.name == o && x.ended.isNone)
          then (Msgs.post db c.now (Msgs.Who.ofText c.me) (.agent o) s!"{c.me} edited #{d id}: {"; ".intercalate notes}" a.urgent).1 else db
        | none => db
      (db, .ok (fields, r.status))

/-- `task drop`: Cancelled, or with `dup` a Duplicate of that task; `note` kept as its note. The Ready and Backlog
tasks that wait on it; a completed task is refused. -/
def drop (c : Ctx) (id : Int) (dup : Option Int) (note : Option String) (db : Db) : Db × Except String (List Task) :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.status = .completed then (db, .error s!"#{d id} is Completed; a completed task can't be dropped")
    else if dup == some id then (db, .error s!"#{d id} can't be a duplicate of itself")
    else if dup.any (db.find · |>.isNone) then (db, .error s!"no task #{(dup.map d).getD ""} to be a duplicate of")
    else if (r.status = .inProgress || r.status = .needsInput) && r.owner != some c.me && !inCharge db c.comms c.me then
      (db, .error s!"#{d id} is {r.status.name} by {r.owner.getD "nil"}; only it or the communicator can drop it")
    else if r.status = .inReview && !isLander db c.comms c.me r then (db, .error (notLander id r))
    else
      let note := note.bind fun n => py (some (oneLine n))
      let close (s : TaskState) : TaskState := match dup with
        | some o => s.toDuplicate o.toNat
        | none => s.toCancelled
      let db := db.set id fun t => { t with state := close t.state, dropped_at := some c.now, note := note.orElse fun _ => t.note }
      let db := db.log c.now (some c.me) "drop" none (some s!"#{d id}{match note with | some n => " " ++ n | none => ""}")
      let db := match dup with
        | some o => db.log c.now (some c.me) "task-duplicate" none (some s!"#{d id} #{d o}")
        | none => db
      (db, .ok (waiters db id))

/-- `rules set`. -/
def rulesSet (text : String) (db : Db) : Db := db.setMeta "rules" (some text)

/-- The caller's terminal, for an event's data: `(terminal <id>)`, `-` for the id when $HC_TERMINAL_ID is unset. -/
def callerTerm (c : Ctx) : String := s!"(terminal {c.here.getD "-"})"

/-- A step only the communicator or the user may take (security review H1): run `f`, logging `kind` with `data` and
the caller's terminal; else refuse, logging `<kind>-refused`, naming who may. -/
def inChargeStep (c : Ctx) (what kind data : String) (f : Db → Db) (db : Db) : Db × Except String Unit :=
  let data := s!"{data} {callerTerm c}"
  if inCharge db c.comms c.me then ((f db).log c.now (some c.me) kind none (some data), .ok ())
  else
    (db.log c.now (some c.me) s!"{kind}-refused" none (some data),
      .error s!"only the communicator{match commsOf db c.comms with | some n => " (" ++ n ++ ")" | none => ""} or the user ({HUMAN}) can {what}; you are {c.me}")

/-- `rules set`, by the communicator or the user only. -/
def setRules (c : Ctx) (text : String) (db : Db) : Db × Except String Unit :=
  inChargeStep c "set the rules" "rules-set" (oneLine text) (rulesSet text) db

end SwarmLean.Tasks
