section
open Lean (Json)
open _root_.SwarmLean.Run (obj)
variable [Fs m] [Proc m] [Git m]

/-- An optional text, null when nil (state.lua's N). -/
def N (o : Option String) : Json := Json.ostr o
/-- An optional integer, null when nil. -/
def NI (o : Option Int) : Json := Json.oint o

/-- `git rev-parse --abbrev-ref HEAD` in worktree `wt` without a subprocess: its HEAD file. -/
def headBranch (wt : String) : m (Option String) := do
  let g := joinPath wt ".git"
  let g ← if (← Sys.kind g true) == .file then
      match ((← Fs.read g).getD "").splitOn "gitdir:" with
      | _ :: rest@(_ :: _) => pure (some (joinPath wt (strip ("gitdir:".intercalate rest))))
      | _ => pure none
    else pure (some g)
  let some g := g | return none
  let some s ← Fs.read (joinPath g "HEAD") | return none
  let s := strip s
  return some (if s.startsWith "ref: refs/heads/" then (s.drop 16).toString else "HEAD")

/-- An event row as state prints it (the columns asked for, null where NULL); a push event's branch and subject come
from its path (JSON). -/
def eventJson (e : Event) (withId withAgent : Bool) : Json :=
  let base : List (String × Json) := (if withId then [("id", Json.int e.id)] else []) ++ [("ts", NI e.ts)] ++
    (if withAgent then [("agent", N e.agent)] else []) ++ [("kind", N e.kind), ("path", N e.path), ("data", N e.data)]
  if e.kind != some "push" then Json.mkObj base else
  let p := (e.path.bind Json.decode).getD .null
  Json.mkObj ((base.filter (·.1 != "path")) ++ [("path", .null), ("branch", N (Json.fstr p "branch")), ("subject", N (Json.fstr p "subject"))])

/-- A message row (body cut to 500 characters); `fill`: NULL columns as null, else absent. -/
def msgJson (r : Msg) (fill : Bool) : Json :=
  let l : List (String × Option Json) := [("id", some (Json.int r.id)), ("ts", r.ts.map Json.int), ("frm", r.frm.map .str),
    ("dest", r.dest.map .str), ("body", r.body.map fun b => .str (cut b 500)), ("urgent", r.urgent.map Json.int), ("kind", r.kind.map .str)]
  if fill then Json.mkObj (l.map fun (k, v) => (k, v.getD .null)) else obj l

/-- A task row as state prints it: its columns but the body, its timing, lease left, deps, waiting and blocks. -/
def taskJson (db : Db) (r : Task) (evs : List Event) (t : Int) : Json :=
  let tm := Tasks.timing r evs t
  let deps := Tasks.depsOf r
  let st (i : Int) := (db.find i).map (·.state)
  let waiting := deps.any fun x => st x != some .done
  let blocks := if r.state = .done then [] else
    (db.tasks.filter fun x => x.state = .open && (Tasks.depsOf x).contains r.id).map (·.id)
  let lease := if (r.state = .claimed || r.state = .blocked) then (pyI r.lease_until).map (· - t) else none
  Json.mkObj [("id", Json.int r.id), ("title", N r.title), ("state", .str r.state.text), ("owner", N r.owner),
    ("lease_until", NI r.lease_until), ("created_by", N r.created_by), ("evidence", N r.evidence), ("deps", .arr (deps.map Json.int).toArray),
    ("model", N r.model), ("question", N r.question), ("effort", N r.effort), ("created_at", NI tm.created_at),
    ("first_claimed_at", NI tm.first_claimed_at), ("done_at", NI tm.done_at), ("dropped_at", NI tm.dropped_at), ("pr", NI tm.pr),
    ("merged_at", NI tm.merged_at), ("ci_conclusion", N tm.ci_conclusion), ("ci_green_at", NI r.ci_green_at),
    ("claim_ctx", NI tm.claim_ctx), ("done_ctx", NI tm.done_ctx), ("answer", N r.answer), ("base", N r.base),
    ("stop_to", N r.stop_to), ("stop_msg", NI r.stop_msg), ("priority", NI r.priority), ("lease_left", NI lease),
    ("waiting", .bool waiting), ("blocks", .arr (blocks.map fun b => Json.int b).toArray), ("queue_wait_s", NI tm.queue_wait_s),
    ("work_s", NI tm.work_s), ("total_s", NI tm.total_s), ("blocked_s", Json.int tm.blocked_s), ("claims", Json.int tm.claims),
    ("releases", Json.int tm.releases), ("holders", .arr (tm.holders.map .str).toArray), ("merge_to_green_s", NI tm.merge_to_green_s)]

/-- The db file (db.dbpath): $SWARM_DB, else swarm/swarm.db in the repo's git common dir. -/
def dbPath : m String := do
  if let some p ← env "SWARM_DB" then return p
  match (← Git.git ["rev-parse", "--path-format=absolute", "--git-common-dir"] none).map strip with
  | some d => if d == "" then die "not in a git repo and SWARM_DB is unset" else return joinPath (joinPath d "swarm") "swarm.db"
  | none => die "not in a git repo and SWARM_DB is unset"

/-- Which sections a view needs beyond the header (state.VIEWS); no view is everything. -/
def wants (view : Option String) (k : String) : Bool :=
  match view with
  | none => true
  | some "overview" => ["lanes", "messages", "events"].contains k
  | some "agents" => k == "lanes"
  | some "activity" => ["messages", "events"].contains k
  | some "system" => ["lanes", "events", "locks", "running"].contains k
  | _ => false

/-- `swarm state --json` (state.cmd_state): one read-only snapshot for UIs (the Herdr panel). -/
def state (a : Parsed) : m UInt32 := do
  let p ← dbPath
  let t ← Clock.now
  if (← Sys.kind p true) == .none then
    Env.out (Json.encode (Json.mkObj [("active", .bool false), ("db", .str p), ("now", Json.int t)]))
    return 0
  -- shortcut: loads the tables whole (Store has no query); the Lua reads only the rows it prints
  let db ← Store.txn [.task, .event, .agent, .msg, .lock, .conflict, .«meta», .ci, .workspace, .cursor] fun db => (db, db)
  let view := a.str "view"
  let full := view.isNone
  let lanes := wants view "lanes"
  let me := a.str "agent"
  let tev := db.events.filter fun e => (e.kind.map (Tasks.TASK_KINDS.contains ·)).getD false
  let tasksJ := db.tasks.map fun r => taskJson db r (tev.filter (Tasks.eventTask · == some r.id)) t
  let wts ← if lanes then Workspaces.wtMap db else pure []
  let allWts ← Workspaces.worktrees
  let main ← Workspaces.mainWt
  let pool := Tasks.pool db
  let mut seen : Agents.Seen := []
  let mut terms : Option (Option (List Agents.Term)) := none
  let mut ags : List (Json × Bool × String) := []
  let agents := (db.agents.filter (·.ended.isNone)).mergeSort (·.name ≤ ·.name) ++ (agents.filter (·.ended.isSome)).mergeSort (·.name ≤ ·.name)
  for x in agents do
    let own := db.tasks.filter fun r => r.owner == some x.name && (r.state = .claimed || r.state = .blocked)
    let sn := match x.snap with | some s => if s.startsWith "{" then (Json.decode s).getD .null else .null | none => .null
    let live := x.ended.isNone
    let wt := py ((wts.lookup x.name).orElse fun _ => x.wt)
    let (act, s1) ← if live && lanes then Agents.sessionActive seen x t else pure (x.last_active.getD 0, seen)
    seen := s1
    let status := if !live then some "ended" else if own.any (·.state = .blocked) then some "blocked" else x.status
    let sign := if live && (py x.stay).isSome && x.status == some "idle" then
        let got := (db.events.filter fun e => e.agent == some x.name && e.ts.getD 0 ≥ x.last_active.getD 0 && e.ts.isSome).filterMap (·.kind)
        if got.contains "stay-hung" then some "hung" else if got.contains "stay-nowaiter" then some "nowaiter"
        else if got.contains "stay-unwoken" then some "unwoken" else none
      else none
    let (cold, s2) ← if live && lanes then Agents.coldReason seen x t else pure (none, seen)
    seen := s2
    let branch ← match live, wt with
      | true, some w => pure (N (← headBranch w))
      | _, _ => pure .null
    let files := if full || live || me == some x.name then Json.items ((Json.field sn "files").getD .null) else []
    let mut l : List (String × Json) := [("name", .str x.name), ("hc", N x.hc), ("model", N x.model), ("role", N x.role),
      ("stay", N x.stay), ("stay_sign", N sign), ("ctx_tokens", Json.int (x.ctx_tokens.getD 0)), ("status", N status),
      ("idle_s", Json.int (t - (if act == 0 then t else act))), ("started", NI x.started), ("ended", NI x.ended),
      ("cache", .str (if t - act < Agents.COLD_IDLE then "warm" else "cold")), ("cold_guarded", .bool cold.isSome),
      ("worktree", N wt), ("branch", branch),
      ("cold_at", if live && x.status != some "working" then Json.int (act + Agents.COLD_IDLE) else .null),
      ("task", match own.head? with
        | some r => obj [("id", some (Json.int r.id)), ("title", r.title.map .str), ("state", some (.str r.state.text))]
        | none => .null),
      ("files", .arr files.toArray)]
    if full then
      l := l ++ [("locks", .arr ((db.locks.filter (·.agent == some x.name)).map fun k => Json.str k.path).toArray)]
    if full || (lanes && live) || me == some x.name then
      let evs := ((db.events.filter fun e => e.agent == some x.name && e.kind != some "touch" && e.kind != some "status").reverse.take 5)
      l := l ++ [("events", .arr (evs.map (eventJson · false false)).toArray)]
    if live && x.status == some "idle" && (lanes || me == some x.name) then
      if terms.isNone then terms := some (← Agents.hcTerminals)
      let by_ := terms.join
      let hx := by_.bind fun ts => (py x.hc).bind fun h => ts.find? (·.address == some h)
      l := l ++ [("fate", ← Fate.fateJson db x t main wts allWts pool hx by_.isSome (me == some x.name))]
    if full || me == some x.name then
      let ms := (db.msgs.filter fun r => r.frm == some x.name || r.dest == some x.name).reverse.take 5
      l := l ++ [("messages", .arr (ms.map (msgJson · false)).toArray)]
    ags := ags ++ [(Json.mkObj l, live, x.name)]
  -- pressure episodes, newest first, the last five
  let eps := (db.events.filter fun e => e.kind == some "pressure" || e.kind == some "pressure-end").foldl (fun (eps : List (Int × Option Int × Option String)) e =>
    if e.kind == some "pressure" then eps ++ [(e.ts.getD 0, none, e.data)]
    else match eps.getLast? with
      | some (s, none, l) => eps.dropLast ++ [(s, e.ts, l)]
      | _ => eps) []
  let press := (eps.reverse.take 5).map fun (s, e, l) => Json.mkObj [("start", Json.int s), ("end", NI e), ("line", N l)]
  let mach ← match ← Machine.mem with
    | some (av, tot, psi) => pure (Json.mkObj [("line", .str (Machine.line av tot psi)), ("avail_kb", Json.int av), ("total_kb", Json.int tot),
        ("psi", obj [("memory", psi.memory.map Json.float), ("cpu", psi.cpu.map Json.float), ("level", psi.level.map .str),
          ("load", psi.load.map Json.float), ("cores", psi.cores.map Json.int)]), ("high", .bool (Machine.pressureHigh av tot psi))])
    | none => pure .null
  let metaV (k : String) : Option String := (db.getMeta k).bind (·.v)
  let cv := (py (metaV "comms")).orElse fun _ => none
  let cv ← match cv with | some c => pure (some c) | none => env "SWARM_COMMS"
  let nlive := (ags.filter fun (_, live, n) => live && some n != cv).length
  let byCreated := db.cis.mergeSort fun x y => x.created.getD "" ≥ y.created.getD ""
  let runs := (byCreated.take 5).map fun r => Json.mkObj [("id", Json.int r.id), ("status", N r.status), ("conclusion", N r.conclusion),
    ("url", N r.url), ("created", N r.created)]
  let fin := ((byCreated.filter fun r => r.status == some "completed" && r.conclusion.isSome && r.conclusion != some "cancelled").take 50)
  let streak := (fin.takeWhile (·.conclusion != some "success")).length
  let mut out : List (String × Json) := [("active", .bool (ags.any (·.2.1))), ("db", .str p), ("now", Json.int t), ("view", N view),
    ("comms", N cv),
    ("limits", obj [("live", some (Json.int nlive)), ("min", ((metaV "agent_min").bind parseInt).map Json.int),
      ("max", ((metaV "agent_max").bind parseInt).map Json.int), ("held", (metaV "spawn_held").map .str)]),
    ("tasks", .arr tasksJ.toArray), ("agents", .arr (ags.map (·.1)).toArray),
    ("conflicts", .arr (((db.conflicts.mergeSort fun x y => x.since.getD 0 ≥ y.since.getD 0)).map fun c =>
      Json.mkObj [("a", .str c.a), ("b", .str c.b), ("path", .str c.path), ("since", NI c.since)]).toArray),
    ("pressure", .arr press.toArray), ("machine", mach), ("ci", Json.mkObj [("runs", .arr runs.toArray), ("red_streak", Json.int streak)])]
  -- watchd: its record (pid, terminal), what it was started with, and whether the swarm code changed since it started
  let runJ := match (metaV "watchd_run").bind Json.decode with | some j@(.obj _) => j | _ => Json.mkObj []
  match metaV "watchd" with
  | some wr =>
    let ws := words wr
    let pid := (ws.head?.bind parseInt)
    let term := (ws[1]?).filter fun x => x != "-"
    let here ← match ← env "SWARM_HERE" with
      | some h => pure h
      | none => pure (dirname ((← Proc.luaCli).getD "./swarm"))
    let dir := joinPath (joinPath here "lua") "swarm"
    let mut newest : Int := 0
    for f in (← Fs.list dir).getD [] do
      if f.endsWith ".lua" then if let some mt ← Sys.mtime (joinPath dir f) then newest := max newest mt
    let started := Json.fint runJ "started"
    let alive ← match pid with | some x => Sys.pidAlive x | none => pure false
    out := out ++ [("watchd", obj [("pid", pid.map Json.int), ("terminal", some (N term)), ("started", some (NI started)),
      ("alive", some (.bool alive)), ("stale", some (.bool (started.any (newest > ·)))),
      ("flags", some (match Json.field runJ "flags" with | some f@(.arr _) => f | some (.obj _) => .arr #[] | _ => .null))])]
  | none => out := out ++ [("watchd", .null)]
  out := out ++ [("away", match metaV "away" with
    | some aw =>
      let ds := aw.toList.takeWhile Char.isDigit
      let rest := (aw.toList.drop ds.length)
      let note := if !ds.isEmpty && rest.head? == some ' ' && rest.length > 1 then some (String.ofList rest.tail) else none
      obj [("since", (parseInt (String.ofList ds)).map Json.int), ("note", some (N note))]
    | none => .null)]
  out := out ++ [("back", ((metaV "away_digest").bind Json.decode).getD .null)]
  if let some tid := a.int "task" then
    match db.find tid with
    | some r =>
      let evs := tev.filter (Tasks.eventTask · == some r.id)
      let key := "#" ++ d tid
      let ms := ((db.msgs.reverse.filter fun x => hasSub ((x.body.getD "").toLower) key).take 200).filter fun x =>
        let b := cut (x.body.getD "") 500 ++ " "
        (b.splitOn key).tail.any fun rest => rest.toList.head?.any (!·.isDigit)
      out := out ++ [("task", Json.mkObj [("id", Json.int tid), ("body", N r.body),
        ("events", .arr (evs.map fun e => obj [("ts", e.ts.map Json.int), ("agent", e.agent.map .str), ("kind", e.kind.map .str), ("data", e.data.map .str)]).toArray),
        ("messages", .arr ((ms.take 20).map (msgJson · false)).toArray)])]
    | none => out := out ++ [("task", .null)]
  let deep := view == some "activity"
  if wants view "messages" then
    out := out ++ [("messages", .arr ((db.msgs.reverse.take (if deep then 120 else 40)).map (msgJson · true)).toArray)]
  if wants view "events" then
    let evs := (db.events.filter fun e => e.kind != some "touch" && e.kind != some "status").reverse.take (if deep then 300 else 60)
    out := out ++ [("events", .arr (evs.map (eventJson · true true)).toArray)]
  if wants view "locks" then
    out := out ++ [("locks", .arr ((db.locks.mergeSort fun x y => x.since.getD 0 ≥ y.since.getD 0).map fun k =>
      Json.mkObj [("path", .str k.path), ("agent", N k.agent), ("reason", N k.reason), ("since", NI k.since),
        ("lease_until", NI k.lease_until), ("seen", NI k.seen)]).toArray)]
  if wants view "running" then
    out := out ++ (← running db t)
  Env.out (Json.encode (Json.mkObj out))
  return 0

end

