import SwarmLean.Db.Agents
import SwarmLean.Db.Msgs

/-! tasks.lua's board logic as pure functions of the db: deps, the pool, timing, and each `task` action's effect.
An action is `… → Db → Db × Except String α`: the db it leaves and its answer or the text it dies with. A die inside
the Lua's transaction leaves the db as the transaction found it; what the Lua wrote before its transaction stays. -/

namespace SwarmLean.Tasks
open Agents

/-- The default lease (tasks.LEASE). -/
def LEASE : Int := 7200
/-- A red main's task title prefix (tasks.RED_TASK). -/
def RED_TASK : String := "main red: "
/-- The default priority (tasks.DEFAULT_PRIORITY). -/
def DEFAULT_PRIORITY : Int := 2
/-- The longest title without a body (tasks.TITLE_MAX). -/
def TITLE_MAX : Nat := 100
/-- The event kinds about a task (tasks.TASK_KINDS). -/
def TASK_KINDS : List String := ["task-add", "claim", "spawn", "done", "block", "unblock", "release", "drop", "task-edit",
  "queue", "unqueue", "hold", "unhold"]
/-- Context from which an agent takes no new work (hook.CTX_WARN). -/
def CTX_WARN : Int := 350000

/-- What to do at context `k` (hook.ctx_advice). -/
def ctxAdvice (k : Int) (stays : Bool) : String :=
  if stays then
    if k ≥ 550000 then
      "finish the current step, then hand off with the relaunch skill, same model, and pass on what you hold " ++
      "(what you stay for, open threads; the communicator: board, watchd PID)."
    else "wrap up this step; at ~550k hand off with the relaunch skill, same model, and pass on what you hold " ++
      "(what you stay for, open threads; the communicator: board, watchd PID)."
  else if k ≥ 550000 then
    "hand off now with the relaunch skill, same model, and post the successor's name, " ++
    "or `swarm task release` if the task is barely started."
  else "finish this task, then go idle (watchd ends you and a fresh agent takes the next task); don't claim another."

/-- The task id an event is about: data `#<id>` or `auto #<id>`, then the end or a space (tasks.event_task). -/
def eventTask (e : Event) : Option Nat :=
  let s := e.data.getD ""
  let s := if s.startsWith "auto #" then some (s.drop 6).toString else if s.startsWith "#" then some (s.drop 1).toString else none
  s.bind fun r =>
    let ds := r.toList.takeWhile Char.isDigit
    let rest := r.toList.drop ds.length
    if ds.isEmpty || !(rest.isEmpty || rest.head? == some ' ') then none else (String.ofList ds).toNat?

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
  ci_conclusion : Option String
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
  let done := (pyI r.done_at).orElse fun _ => if r.state = .done then ts "done" max else none
  let dropped := (pyI r.dropped_at).orElse fun _ => if r.state = .dropped then ts "drop" max else none
  let stop := ((pyI done).orElse fun _ => pyI dropped).getD now
  let (blocked, start) := evs.foldl (fun (b, s) e =>
    if e.kind == some "block" && s.isNone then (b, some (e.ts.getD 0))
    else if e.kind == some "unblock" && s.isSome then (b + e.ts.getD 0 - s.getD 0, none)
    else (b, s)) ((0 : Int), (none : Option Int))
  let blocked := match start with
    | some s => if r.state = .blocked then blocked + stop - s else blocked
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
  (depsOf r).filterMap fun i => (db.find i).filter (·.state ≠ .done)

/-- Open tasks whose deps name `tid` (tasks.waiters). -/
def waiters (db : Db) (tid : Int) : List Task :=
  db.tasks.filter fun t => t.state = .open && match t.deps with
    | some ds => hasSub ("," ++ ds ++ ",") ("," ++ d tid ++ ",")
    | none => false

/-- SQL's `','||t.deps||',' like '%,'||d.id||',%'` for some not-done task `d`: `t` waits on an undone task. -/
def blockedByDeps (db : Db) (t : Task) : Bool :=
  match t.deps with
  | none => false
  | some ds => db.tasks.any fun x => x.state ≠ .done && hasSub ("," ++ ds ++ ",") ("," ++ d x.id ++ ",")

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
      if a.ended.isSome || (a.status != some "working" && a.status != some "blocked") then false
      else
        let cur := ((db.cursor to).bind (·.last_msg_id)).getD 0
        cur < r.stop_msg.getD 0

/-- Lua's `title like 'main red: %'` as a sort key: 1 for a red task. -/
def redKey (t : Task) : Nat := if likePrefix (t.title.getD "") RED_TASK then 1 else 0

/-- Order by `red desc, priority, id` (NULL priority first, as SQL sorts it). -/
def boardLe (red : Task → Nat) (a b : Task) : Bool :=
  let pa := a.priority.map (· + 1) |>.getD 0
  let pb := b.priority.map (· + 1) |>.getD 0
  if red a != red b then red a > red b else if pa != pb then pa < pb else a.id ≤ b.id

/-- Open tasks with no undone deps and no pending stop, red first then by priority (tasks.pool). -/
def pool (db : Db) : List Task :=
  ((db.tasks.filter fun t => t.state = .open && !blockedByDeps db t).mergeSort (boardLe redKey)).filter
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
      "#" ++ d x ++ " " ++ ((db.find x).map (·.state.text)).getD "missing")
  let w := if r.state ≠ .done then waiters db r.id else []
  a ++ (if w.isEmpty then "" else "\nblocks: " ++ ", ".intercalate (w.map fun x => "#" ++ d x.id))

/-- Fails on a dep that is no task (tasks.no_task_to_wait_on). -/
def checkDeps (db : Db) (deps : List Int) : Except String Unit :=
  deps.forM fun x => if (db.find x).isNone then .error s!"no task #{d x} to wait on" else .ok ()

/-- A task given deps `s`. -/
def depsF (s : String) (t : Task) : Task := { t with deps := some s }

/-- A task claimed by `me` until `u` at context `k` at time `now`. -/
def claimF (me : String) (u k now : Int) (t : Task) : Task :=
  { t with state := .claimed, owner := some me, lease_until := some u, claim_ctx := some k,
           first_claimed_at := t.first_claimed_at.orElse fun _ => some now }

/-- A task its owner gave back. -/
def reopenF (t : Task) : Task := { t with state := .open, owner := none, lease_until := none }

/-- A task the communicator took back from its owner. -/
def reopenFromF (t : Task) : Task := { t with state := .open, owner := none, lease_until := none, question := none }

/-- Fails on a missing dep or one that would close a cycle through `id`. -/
def checkCycles (db : Db) (id : Int) (deps : List Int) : Except String Unit := do
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

/-- What a task command knows of the world, read before it runs. -/
structure Ctx where
  /-- the agent ($SWARM_NAME) -/
  me : String
  now : Int
  /-- $HC_TERMINAL_ID, none when unset or empty -/
  here : Option String := none
  /-- $SWARM_COMMS, none when unset or empty -/
  comms : Option String := none
  /-- the working directory -/
  cwd : Option String := none
  /-- `task claim --force`: the communicator claims a held task -/
  force : Bool := false

/-- What `task add` was given. -/
structure AddArgs where
  title : String
  body : String := ""
  deps : List Int := []
  model : Option String := none
  effort : Option String := none
  base : Option String := none
  priority : Option Int := none

/-- `task add`: the new task's id. -/
def add (c : Ctx) (a : AddArgs) (db : Db) : Db × Except String Nat :=
  if !a.title.any (!isSpace ·) then (db, .error "the title can't be empty")
  else if a.title.contains '\n' then (db, .error "the title is one line; put the rest in --body or --body-file")
  else if a.title.utf8ByteSize > TITLE_MAX && (py (some a.body)).isNone then
    (db, .error s!"the title is over {TITLE_MAX} characters with no body; move the detail to --body or --body-file")
  else match checkDeps db a.deps with
    | .error e => (db, .error e)
    | .ok () =>
      let id := db.taskNext
      let t : Task := { id, title := some a.title, body := some a.body, created_by := some c.me,
                        deps := py (some (",".intercalate (a.deps.map d))), model := a.model, effort := a.effort,
                        base := a.base, created_at := some c.now, priority := some (a.priority.getD DEFAULT_PRIORITY) }
      let db := { db with tasks := db.tasks ++ [t], taskNext := db.taskNext + 1 }
      (db.log c.now (some c.me) "task-add" none (some s!"#{d id} {a.title}"), .ok id)

/-- What a successful claim prints: the lease's end and the body. -/
structure Claimed where
  «until» : Int
  body : Option String

/-- `task claim`: `lease` is `--lease` as given. -/
def claim (c : Ctx) (id : Int) (lease : String) (db : Db) : Db × Except String Claimed :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.hold.isSome && !(c.force && inCharge db c.comms c.me) then
      (db, .error s!"task #{d id} is held: {r.hold.getD ""}; {if c.force then "only the communicator or the user can --force it"
        else "`swarm task unhold` it first (or the communicator's --force)"}")
    else
    match undone db r with
    | dep :: _ =>
      (db, .error s!"#{d id} waits on #{d dep.id} ({dep.state.text}{match py dep.owner with
        | some o => ", claimed by " ++ o | none => ""})")
    | [] =>
      let db := touch db c.me none c.here c.now
      let k := ctxOf db c.me
      if k ≥ CTX_WARN && !reapedFrom db c.me id then
        (db, .error s!"context ~{fdiv k 1000}k, too high to take new work: {ctxAdvice k false}")
      else match dur lease with
      | none => (db, .error s!"bad duration '{lease}' (use 90s, 30m, 2h)")
      | some l =>
        let «until» := c.now + l
        match db.find id with
        | none => (db, .error s!"no task #{d id}")
        | some r1 =>
          if stopPending db r1 then
            (db, .error s!"task #{d id} was released from {r1.stop_to.getD ""}, which hasn't read the stop yet; try again once it has")
          else if r1.state = .open && !blockedByDeps db r1 then
            let db := db.set id (claimF c.me «until» k c.now)
            (db.log c.now (some c.me) "claim" none (some s!"#{d id} {r.title.getD ""}"), .ok ⟨«until», py r.body⟩)
          else match (if r1.state = .open then undone db r1 else []) with
            | dep :: _ => (db, .error s!"#{d id} waits on #{d dep.id} ({dep.state.text})")
            | [] => (db, .error s!"task #{d id} is {r1.state.text}{owned r1}")

/-- `task after`: what the deps became. -/
def after (c : Ctx) (id : Int) (deps : List Int) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.state ≠ .open then (db, .error s!"task #{d id} is {r.state.text}; only an open task's dependencies can change")
    else match setDeps db id deps with
      | .error e => (db, .error e)
      | .ok (db', ds) =>
        (db'.log c.now (some c.me) "task-after" none (some s!"#{d id} after {(py (some (",".intercalate ds))).getD "-"}"),
         .ok ())

/-- `task priority`. -/
def priority (c : Ctx) (id : Int) (p : Int) (db : Db) : Db × Except String Unit :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.state ≠ .open && r.state ≠ .claimed then
      (db, .error s!"task #{d id} is {r.state.text}; only an open or claimed task's priority can change")
    else
      let db := db.set id ({ · with priority := some p })
      (db.log c.now (some c.me) "task-priority" none (some s!"#{d id} P{d p}"), .ok ())

/-- The row is `n`'s claimed task (the Lua's `where id=? and owner=? and state='claimed'`). -/
def mine (r : Task) (n : String) : Bool := r.owner == some n && r.state = .claimed

/-- `task renew`: the lease's new end. -/
def renew (c : Ctx) (id : Int) (lease : String) (db : Db) : Db × Except String Int :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    match dur lease with
    | none => (db, .error s!"bad duration '{lease}' (use 90s, 30m, 2h)")
    | some l =>
      if !mine r c.me then (db, .error s!"task #{d id} is not claimed by you")
      else (db.set id ({ · with lease_until := some (c.now + l) }), .ok (c.now + l))

/-- What `task done` says after: a red task stays claimed, else the context line's parts. -/
inductive DoneOut
  | red
  | done (k : Int) (stay : Option String) (poolSize : Nat)

/-- `task done`. -/
def done (c : Ctx) (id : Int) (evidence : String) (db : Db) : Db × Except String DoneOut :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if strip evidence == "" then
      (db, .error "--evidence is empty: give the sha, PR or command output that shows the work is done")
    else if !mine r c.me then (db, .error s!"task #{d id} is not claimed by you")
    else if (r.title.getD "").startsWith RED_TASK then (db.set id ({ · with evidence := some evidence }), .ok .red)
    else
      let dctx := (db.agent c.me).bind (·.ctx_tokens)
      let db := db.set id fun t => { t with state := .done, evidence := some evidence, lease_until := none,
                                            done_at := some c.now, done_ctx := dctx }
      let db := db.log c.now (some c.me) "done" none (some s!"#{d id} {evidence}")
      (db, .ok (.done (fdiv (ctxOf db c.me) 1000) (stayOf db c.me) (pool db).length))

/-- `task block`: whether the user is away. -/
def block (c : Ctx) (id : Int) (question : String) (db : Db) : Db × Except String Bool :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if !mine r c.me then (db, .error s!"task #{d id} is not claimed by you")
    else
      let db := db.set id ({ · with state := .blocked, question := some question })
      (db.log c.now (some c.me) "block" none (some s!"#{d id} {question}"), .ok (away db).isSome)

/-- `task unblock`: the owner it is claimed by again. -/
def unblock (c : Ctx) (id : Int) (answer : String) (db : Db) : Db × Except String (Option String) :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.state ≠ .blocked then (db, .error s!"task #{d id} is not blocked")
    else if some c.me != r.owner && !inCharge db c.comms c.me then
      (db, .error s!"only {r.owner.getD "nil"} or the communicator can unblock #{d id}")
    else if r.owner.isNone then (db, .error s!"task #{d id} changed under you; `swarm task show {d id}`")
    else
      let ans := py (some answer)
      let db := db.set id fun t => { t with state := .claimed, question := none, answer := ans.orElse fun _ => t.answer,
                                            lease_until := some (c.now + LEASE) }
      let db := db.log c.now (some c.me) "unblock" none (some s!"#{d id}")
      let db := match ans, r.owner with
        | some a, some o => if c.me != o then (Msgs.post db c.now c.me o s!"#{d id} is unblocked. Answer: {a}").1 else db
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
        if r.owner == some f && (r.state = .claimed || r.state = .blocked) then
          .ok (db.set id reopenFromF)
        else .error s!"task #{d id} is {r.state.text}{owned r}"
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
          let p := Msgs.post db3 c.now c.me f
            s!"{if c.me == HUMAN then "the user" else c.me} released #{d id}: stop work on it" true
          (p.1.set id ({ · with stop_to := some f, stop_msg := some p.2 }), .ok fromA)
        | none => (db3, .ok fromA)

/-- What `task edit` was given. -/
structure EditArgs where
  title : Option String := none
  body : Option String := none
  /-- `--body-file`: its path and text, none when it could not be read -/
  bodyFile : Option (String × Option String) := none
  append : Option String := none
  model : Option String := none
  effort : Option String := none
  urgent : Bool := false

/-- `task edit`'s new title, body, model and effort for row `r` with the new body `newBody`, the columns changed and a
note for each. -/
def editCols (id : Int) (r : Task) (a : EditArgs) (newBody : Option String) :
    (Option String × Option String × Option String × Option String) × List String × List String :=
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
  let (effort, fields, notes) := match a.effort with
    | some e => ch r.effort (py (some e)) "effort" s!"effort: {(py r.effort).getD "-"} -> {(py (some e)).getD "-"}" (r.effort, f4, n4)
    | none => (r.effort, f4, n4)
  ((title, body, model, effort), fields, notes)

/-- `task edit`: the fields changed and the task's state. -/
def edit (c : Ctx) (id : Int) (a : EditArgs) (db : Db) : Db × Except String (List String × Status) :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if r.state = .done || r.state = .dropped then (db, .error s!"task #{d id} is {r.state.text}; it can't be edited")
    else if a.title == some "" then (db, .error "the title can't be empty")
    else
      if let some (p, none) := a.bodyFile then (db, .error s!"can't read {p}") else
      let newBody := match a.bodyFile with | some (_, some t) => some t | _ => a.body
      let ((title, body, model, effort), fields, notes) := editCols id r a newBody
      if fields.isEmpty then (db, .error "nothing to change") else
      let db := db.set id ({ · with title, body, model, effort })
      let db := db.log c.now (some c.me) "task-edit" none (some s!"#{d id} {", ".intercalate fields}")
      let db := match py r.owner with
        | some o =>
          if (r.state = .claimed || r.state = .blocked) && o != c.me && (db.agents.any fun x => x.name == o && x.ended.isNone)
          then (Msgs.post db c.now c.me o s!"{c.me} edited #{d id}: {"; ".intercalate notes}" a.urgent).1 else db
        | none => db
      (db, .ok (fields, r.state))

/-- `task drop`: the open tasks that wait on it. -/
def drop (c : Ctx) (id : Int) (db : Db) : Db × Except String (List Task) :=
  match db.find id with
  | none => (db, .error s!"no task #{d id}")
  | some r =>
    if (r.state = .claimed || r.state = .blocked) && r.owner != some c.me && !inCharge db c.comms c.me then
      (db, .error s!"#{d id} is {r.state.text} by {r.owner.getD "nil"}; only it or the communicator can drop it")
    else
      let db := db.set id fun t => { t with state := .dropped, owner := none, lease_until := none, dropped_at := some c.now }
      let db := db.log c.now (some c.me) "drop" none (some s!"#{d id}")
      (db, .ok (waiters db id))

/-- `rules set`. -/
def rulesSet (text : String) (db : Db) : Db := db.setMeta "rules" (some text)

end SwarmLean.Tasks
