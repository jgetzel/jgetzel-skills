import SwarmLean.Lib.Swarms
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Run
import SwarmLean.Db.Plan
import SwarmLean.Db.Tasks
import SwarmLean.Lib.Watchd

/-! `swarm state --json --view swarms` (sw-global §5): every swarm on the machine in one read, for the Herdr panels. -/

namespace SwarmLean.SwarmsView
open Lean (Json)
open SwarmLean.Run (obj)
open Sqlite (Val)

/-- The task states the counts list. -/
def STATES : List Status := [.open, .claimed, .blocked, .done, .dropped, .landing]

/-- The task state a row's text names (none: null or not a state). -/
def stateOf (s : Option String) : Option Status := s.bind fun x => (Status.ofText x).toOption

/-- A swarm's meta keys the view reads. -/
def KNOBS : List String := ["agent_min", "agent_max", "spawn_held", "queue_only", "away", "ctx_nudge"]

/-- The done and dropped tasks the machine-wide `tasks` lists besides every other: the newest this many. -/
def DONE_SHOWN : Nat := 80

/-- The where clause of the tasks `tasks` lists, on task columns `t.`. -/
def listed : String :=
  s!"(t.state not in ('done', 'dropped') or t.id in (select id from task where state in ('done', 'dropped') order by id desc limit {DONE_SHOWN}))"

/-- A CI run's state as the view shows it: pending until completed, then green, red, or its conclusion (cancelled,
skipped, neutral). -/
def ciState (status : Option RunStatus) (conclusion : Option Conclusion) : String :=
  if status != some .completed then "pending" else
  match conclusion with
  | some .success => "green"
  | some c => if c == .cancelled || c == .skipped || c == .neutral then c.text else "red"
  | none => "pending"

/-- A path's last segment. -/
def baseName (p : String) : String := ((p.splitOn "/").filter (· ≠ "")).getLast?.getD p

/-- `p` is `dir` or below it. -/
def under (dir p : String) : Bool := p == dir || p.startsWith (dir ++ "/")

/-- One task as the view reads it. -/
structure T where
  id : Int
  state : Status
  owner : Option String
  by_ : Option String
  title : Option String
  question : Option String
  deps : List Int
  hold : Option String
  qpos : Option Int
  priority : Option Int

/-- The open tasks auto-spawn could start (as `Queue.staffing` orders them, its stop-pending test left out): no hold, no
undone dep; a `main red:` task first, then the queue by position, then the rest by priority and id. -/
def startable (all ks : List T) : List T :=
  let undone : Std.HashSet Int := all.foldl (fun h k => if k.state == .done || k.state == .dropped then h else h.insert k.id) {}
  let ok := ks.filter fun k => k.state == .open && (py k.hold).isNone && !k.deps.any undone.contains
  let rank (k : T) : List Int :=
    [if (k.title.getD "").startsWith "main red: " then 0 else 1, k.qpos.getD (1 <<< 40), k.priority.getD 2, k.id]
  let rec lex : List Int → List Int → Bool
    | x :: xs, y :: ys => x < y || (x == y && lex xs ys)
    | _, _ => true
  ok.mergeSort fun a b => lex (rank a) (rank b)

/-- An agent's hung sign (watchd.hung, as `State.staySign`): a stayer, idle, with a stay-hung event since it was active. -/
def hung (x : Agent) (evs : List (String × String × Int)) : Bool :=
  (py x.stay).isSome && x.status == some .idle &&
    evs.any fun (a, k, ts) => a == x.name && k == "stay-hung" && ts ≥ x.last_active.getD 0

/-- The machine-wide board (board #120), from `view`'s rows: every task listed (`listed`) with its repos (each with its
base and its holder's worktree there), holder and its swarm, deps, hold, lease left and last change; every repo with its
CI on the base, locks and swarms; and what needs the human, each with a kind: ask (a blocked task's question), hung (a
stayer's wait), lander (a landing task whose lander is gone, or that waited LANDING_LATE), held (a held task), lock (a
lock of an agent gone, or past its lease), ctx (a live agent at its swarm's ctx_nudge), ci-red (a repo's newest finished
run on its base). `ts`: the tasks; `trs`: their repos; `ws`: worktrees (agent, repo, path); `rps`: repos; `lks`: locks;
`upd`: each task's last event; `cis`: CI runs, newest first; `agents`: (swarm, row); `evs`: stay-hung events. -/
def machine (t : Int) (ts trs : List (Array Val)) (ws : List (String × String × String)) (rps lks upd cis : List (Array Val))
    (agents : List (String × Agent)) (sws : List Swarms.Row) (knob : String → String → Option String)
    (evs : List (String × String × Int)) : Array Json × Array Json × Array Json :=
  let txt (v : Option Val) : Option String := Swarms.txt v
  let int (v : Option Val) : Option Int := Swarms.int v
  let swarmOf (n : String) : Option String := (agents.find? (·.2.name == n)).map (·.1)
  let live := agents.filter fun (_, a) => a.ended.isNone
  let isLive (n : String) : Bool := live.any (·.2.name == n)
  let last : Std.HashMap Int Int := upd.foldl (init := {}) fun h r =>
    match int r[0]?, int r[1]? with
    | some k, some v => h.insert k v
    | _, _ => h
  let repos : Std.HashMap Int (List (String × Option String)) := trs.foldl (init := {}) fun h r =>
    match int r[0]?, txt r[1]? with
    | some k, some rp => h.insert k (h.getD k [] ++ [(rp, py (txt r[2]?))])
    | _, _ => h
  let newest (xs : List Int) : Option Int := xs.foldl (fun a x => some (match a with | some y => max x y | none => x)) none
  let tasksJ := ts.filterMap fun r => (int r[0]?).map fun id =>
    let state := (stateOf (txt r[2]?)).getD .open
    let owner := py (txt r[9]?)
    let lease := if state == .claimed || state == .blocked then (pyI (int r[7]?)).map (· - t) else none
    let wt (rp : String) : Option String := owner.bind fun o => (ws.find? fun (a, p, _) => a == o && p == rp).map (·.2.2)
    Json.mkObj [("id", Json.int id), ("title", Json.ostr (txt r[1]?)), ("state", .str state.text),
      ("priority", Json.int ((int r[3]?).getD Tasks.DEFAULT_PRIORITY)),
      ("labels", .arr ((commaPieces ((txt r[4]?).getD "")).map Json.str).toArray),
      ("repos", .arr ((repos.getD id []).map fun (rp, b) =>
        Json.mkObj [("repo", .str rp), ("base", Json.ostr b), ("worktree", Json.ostr (wt rp))]).toArray),
      ("holder", match owner with
        | some o => Json.mkObj [("agent", .str o), ("swarm", Json.ostr (swarmOf o))]
        | none => .null),
      ("after", .arr ((((txt r[5]?).map fun x => (commaPieces x).filterMap parseInt).getD []).map Json.int).toArray),
      ("held", Json.ostr (py (txt r[6]?))), ("lease_left_s", Json.oint lease), ("created_by", Json.ostr (txt r[8]?)),
      ("updated", Json.oint (newest ([last.get? id, int r[10]?, int r[14]?, int r[15]?, int r[16]?, int r[17]?].filterMap fun x => x)))]
  let lock (r : Array Val) : Option (String × String × Option String × Option Int × Option Int) :=
    match txt r[0]?, txt r[1]? with
    | some rp, some lp => some (rp, lp, py (txt r[2]?), pyI (int r[3]?), int r[4]?)
    | _, _ => none
  let locks := lks.filterMap lock
  let reposJ := rps.filterMap fun r => (txt r[0]?).map fun rp =>
    let ci := cis.find? fun c => txt c[0]? == some rp
    Json.mkObj [("path", .str rp), ("name", .str (baseName rp)), ("base", Json.ostr (py (txt r[1]?))),
      ("ci", match ci with
        | some c => Json.mkObj [("state", .str (ciState ((txt c[1]?).map RunStatus.ofText) ((txt c[2]?).map Conclusion.ofText))), ("sha", Json.ostr (txt c[6]?)),
            ("run", Json.oint (int c[5]?)), ("url", Json.ostr (txt c[3]?))]
        | none => .null),
      ("locks", .arr ((locks.filter (·.1 == rp)).map fun (_, lp, a, _, _) =>
        Json.mkObj [("path", .str lp), ("agent", Json.ostr a)]).toArray),
      ("swarms", .arr ((sws.filter (·.repos.contains rp)).map fun w => Json.str w.name).toArray)]
  let need (kind : String) (l : List (String × Json)) : Json := Json.mkObj (("kind", .str kind) :: l)
  let ofTask (kind : String) (r : Array Val) (l : List (String × Json)) : Json :=
    need kind ([("task", Json.oint (int r[0]?)), ("title", Json.ostr (txt r[1]?))] ++ l)
  let asks := (ts.filter fun r => stateOf (txt r[2]?) == some .blocked).map fun r =>
    let o := py (txt r[9]?)
    ofTask "ask" r [("question", Json.ostr (txt r[11]?)), ("agent", Json.ostr o), ("swarm", Json.ostr (o.bind swarmOf))]
  let hungs := (live.filter fun (_, x) => hung x evs).map fun (sw, x) =>
    need "hung" [("agent", .str x.name), ("swarm", .str sw), ("stay", Json.ostr (py x.stay))]
  let landers := (ts.filter fun r => stateOf (txt r[2]?) == some .landing &&
      ((int r[14]?).any (· ≤ t - Watchd.LANDING_LATE) || (py (txt r[13]?)).any (!isLive ·))).map fun r =>
    let o := py (txt r[9]?)
    ofTask "lander" r [("agent", Json.ostr o), ("lander", Json.ostr (py (txt r[13]?))), ("sha", Json.ostr (txt r[12]?)),
      ("since", Json.oint (int r[14]?)), ("swarm", Json.ostr (o.bind swarmOf))]
  let helds := (ts.filter fun r => (py (txt r[6]?)).isSome && !(stateOf (txt r[2]?) == some .done || stateOf (txt r[2]?) == some .dropped)).map fun r =>
    ofTask "held" r [("why", Json.ostr (py (txt r[6]?)))]
  let lockNeeds := (locks.filter fun (_, _, a, lu, _) => !(a.any isLive) || lu.any (· < t)).map fun (rp, lp, a, _, since) =>
    need "lock" [("repo", .str rp), ("path", .str lp), ("agent", Json.ostr a), ("since", Json.oint since)]
  let ctxs := live.filterMap fun (sw, x) =>
    let lim := ((knob sw "ctx_nudge").bind parseInt).getD Compact.NUDGE_AT
    let k := x.ctx_tokens.getD 0
    if lim > 0 && k ≥ lim then some (need "ctx" [("agent", .str x.name), ("swarm", .str sw), ("ctx", Json.int k), ("limit", Json.int lim)])
    else none
  let reds := rps.filterMap fun r => (txt r[0]?).bind fun rp =>
    let fin := cis.find? fun c => txt c[0]? == some rp && (txt c[1]?).map RunStatus.ofText == some .completed && (txt c[2]?).any (Conclusion.ofText · != .cancelled)
    match fin with
    | some c => if (txt c[2]?).map Conclusion.ofText != some .success then
        some (need "ci-red" [("repo", .str rp), ("run", Json.oint (int c[5]?)), ("sha", Json.ostr (txt c[6]?)), ("url", Json.ostr (txt c[3]?))])
      else none
    | none => none
  (tasksJ.toArray, reposJ.toArray, (asks ++ hungs ++ landers ++ helds ++ lockNeeds ++ ctxs ++ reds).toArray)

variable {m : Type → Type} [Monad m] [Env m] [Sys m] [Proc m] [Git m]

/-- The repo a folder is in: the known repo it is under, else its main worktree (`git rev-parse --git-common-dir`'s
parent), else none. -/
def repoOf (known : List String) (dir : String) : m (Option String) := do
  if let some r := known.find? (under · dir) then return some r
  match ← Git.git ["rev-parse", "--path-format=absolute", "--git-common-dir"] (some dir) with
  | some d =>
    let d := strip d
    return if d.endsWith "/.git" then some (d.dropEnd 5).toString else none
  | none => return none

/-- The view: `now`, the db, the machine's task counts, and per swarm its communicator (and its terminal), staffing,
repos (each with its base, latest CI run, lock count and the other live swarms on it), live agents (each with its
repo, every repo it has a worktree in, status, task, idle time, hung sign and whether its terminal is gone), tasks by state, what needs the human
and whether the user is away. -/
def view (t : Int) : m Json := do
  let p ← Swarms.dbPath
  let sws ← Swarms.list
  let acols := ", ".intercalate (Row.cols Agent)
  let rs ← Sys.sqlAt p schema [
    (s!"select swarm, {acols} from agent where swarm is not null", []),
    ("select id, state, owner, created_by, title, question, deps, hold, qpos, priority from task", []),
    ("select task, repo from task_repo", []),
    ("select agent, repo from workspace where repo <> '' order by path", []),
    (s!"select scope, k, v from meta where k in ({", ".intercalate (KNOBS.map fun k => s!"'{k}'")})", []),
    ("select path from repo order by length(path) desc", []),
    ("select agent, kind, ts from event where kind = 'stay-hung' and ts >= ?", [.int (t - 86400)]),
    ("select repo, status, conclusion, url, created, id, sha from ci order by created desc", []),
    ("select path, base from repo", []),
    ("select repo, count(*) from lock group by repo", []),
    -- the machine-wide board (board #120): the tasks listed, their repos with bases, worktrees, repos, locks, last events
    (s!"select t.id, t.title, t.state, t.priority, t.labels, t.deps, t.hold, t.lease_until, t.created_by, t.owner, " ++
      s!"t.created_at, t.question, t.land_sha, t.lander, t.landing_at, t.first_claimed_at, t.done_at, t.dropped_at from task t where {listed} order by t.id", []),
    (s!"select tr.task, tr.repo, coalesce(nullif(tr.base, ''), nullif(t.base, ''), r.base) from task_repo tr " ++
      s!"join task t on t.id = tr.task left join repo r on r.path = tr.repo where {listed} order by tr.task, tr.rowid", []),
    ("select agent, repo, path from workspace where repo <> '' and agent is not null order by path", []),
    ("select path, base from repo order by path", []),
    ("select repo, path, agent, lease_until, since from lock order by repo, path", []),
    (s!"select case when data like 'auto #%' then cast(substr(data, 7) as integer) else cast(substr(data, 2) as integer) end, " ++
      s!"max(ts) from event where kind in ({", ".intercalate (Tasks.SHOW_KINDS.map fun _ => "?")}) and (data like '#%' or data like 'auto #%') group by 1",
      Tasks.SHOW_KINDS.map Val.text)] true
  let rows (i : Nat) : List (Array Val) := (rs.getD i #[]).toList
  let txt (v : Option Val) : Option String := Swarms.txt v
  let int (v : Option Val) : Option Int := Swarms.int v
  let agents : List (String × Agent) := (rows 0).filterMap fun r =>
    match txt r[0]?, (Row.dec (r.extract 1 r.size) : Except String Agent) with
    | some s, .ok a => some (s, a)
    | _, _ => none
  let tasks : List T := (rows 1).filterMap fun r => (int r[0]?).map fun id =>
    { id, state := (stateOf (txt r[1]?)).getD .open, owner := py (txt r[2]?), by_ := py (txt r[3]?), title := txt r[4]?,
      question := txt r[5]?, deps := ((txt r[6]?).map fun d => (commaPieces d).filterMap parseInt).getD [],
      hold := txt r[7]?, qpos := int r[8]?, priority := int r[9]? }
  let taskRepos : Std.HashMap Int (List String) := (rows 2).foldl (init := {}) fun h r =>
    match int r[0]?, txt r[1]? with
    | some k, some rp => h.insert k (rp :: h.getD k [])
    | _, _ => h
  let wsRepo : Std.HashMap String String := (rows 3).foldl (init := {}) fun h r =>
    match txt r[0]?, txt r[1]? with
    | some a, some rp => if h.contains a then h else h.insert a rp
    | _, _ => h
  -- every repo an agent has a worktree in, for the rail's repo tags (an agent may work across repos)
  let wsRepos : Std.HashMap String (List String) := (rows 3).foldl (init := {}) fun h r =>
    match txt r[0]?, txt r[1]? with
    | some a, some rp => let l := h.getD a []; if l.contains rp then h else h.insert a (l ++ [rp])
    | _, _ => h
  let bases : Std.HashMap String String := (rows 8).foldl (init := {}) fun h r =>
    match txt r[0]?, py (txt r[1]?) with
    | some rp, some b => h.insert rp b
    | _, _ => h
  let locks : Std.HashMap String Int := (rows 9).foldl (init := {}) fun h r =>
    match txt r[0]?, int r[1]? with
    | some rp, some n => h.insert rp n
    | _, _ => h
  let ciJson (r : Array Val) : Json := obj [("repo", (txt r[0]?).map .str), ("status", (txt r[1]?).map .str),
    ("conclusion", (txt r[2]?).map .str), ("url", (txt r[3]?).map .str), ("created", (txt r[4]?).map .str),
    ("id", (int r[5]?).map Json.int)]
  let knob (s k : String) : Option String :=
    ((rows 4).find? fun r => txt r[0]? == some s && txt r[1]? == some k).bind fun r => py (txt r[2]?)
  let known := ((rows 5).filterMap (txt ·[0]?)) ++ (sws.flatMap (·.repos))
  let evs : List (String × String × Int) := (rows 6).filterMap fun r =>
    match txt r[0]?, txt r[1]?, int r[2]? with
    | some a, some k, some ts => some (a, k, ts)
    | _, _, _ => none
  let everyone : Std.HashSet String := agents.foldl (fun h (_, a) => h.insert a.name) {}
  let live := agents.filter fun (_, a) => a.ended.isNone
  -- the terminals hc lists live here, read once and only when a live agent is bound to one; none when hc fails
  let up ← if live.any (fun (_, a) => (py a.hc).isSome) then
      pure ((← Agents.hcTerminals).map fun ts => ts.filterMap fun x => if x.state == some "live" then x.address else none)
    else pure none
  -- bound to a terminal hc no longer lists (watchd's reap ends it; until then nothing can open or answer it)
  let gone (x : Agent) : Bool := match up, py x.hc with
    | some u, some h => !u.contains h
    | _, _ => false
  -- memory per swarm: the live agents' process trees on this machine, one ps for them all
  let held := (Machine.holders (live.map (·.2)) (← Machine.procs)).filter (·.agent != "other session")
  -- each agent's worktrees (agent, repo, path): a task holder's worktree in each of the task's repos
  let wsRows : List (String × String × String) := (rows 12).filterMap fun r =>
    match txt r[0]?, txt r[1]?, txt r[2]? with
    | some a, some rp, some wp => some (a, rp, wp)
    | _, _, _ => none
  let mut out : Array Json := #[]
  for sw in sws do
    let members : Std.HashSet String := agents.foldl (fun h (s, a) => if s == sw.name then h.insert a.name else h) {}
    let ks := tasks.filter fun k => Swarms.mine sw.repos members everyone (taskRepos.getD k.id []) k.owner k.by_
    let cv := sw.comms
    let mut ags : Array Json := #[]
    let mut needs : Array Json := #[]
    let alive := ((live.filter (·.1 == sw.name)).map (·.2)).mergeSort (·.name ≤ ·.name)
    for x in alive do
      let own := ks.filter fun k => k.owner == some x.name && (k.state == .blocked || k.state == .claimed || k.state == .landing)
      let own := (own.filter (·.state == .blocked)) ++ (own.filter (·.state != .blocked))
      let rp ← match wsRepo.get? x.name with
        | some r => pure (some r)
        | none => match py (x.wt.orElse fun _ => x.cwd) with
          | some d => repoOf known d
          | none => pure none
      let act := x.last_active.getD 0
      let h := hung x evs
      let asks := own.any (·.state == .blocked)
      let g := gone x
      if !g && !asks && x.status == some .blocked then needs := needs.push (Json.mkObj [("kind", .str "prompt"), ("agent", .str x.name)])
      if h && !g then needs := needs.push (Json.mkObj [("kind", .str "hung"), ("agent", .str x.name)])
      let rps := (wsRepos.get? x.name).getD rp.toList
      ags := ags.push (obj [("name", some (.str x.name)), ("hc", some (Json.ostr x.hc)), ("repo", some (Json.ostr rp)),
        ("repos", some (.arr (rps.map Json.str).toArray)),
        ("status", some (Json.ostr ((if asks then some AgentStatus.blocked else x.status).map (·.text)))), ("role", some (Json.ostr x.role)),
        ("model", some (Json.ostr x.model)), ("stay", some (Json.ostr (py x.stay))),
        ("ctx", some (Json.int (x.ctx_tokens.getD 0))),
        ("task", some (match own.head? with
          | some k => obj [("id", some (Json.int k.id)), ("title", k.title.map .str), ("state", some (.str k.state.text))]
          | none => .null)),
        ("idle_s", some (Json.int (t - (if act == 0 then t else act)))), ("hung", some (.bool h)), ("gone", some (.bool g))])
    let qs := (ks.filter (·.state == .blocked)).map fun k => obj [("kind", some (.str "question")),
      ("task", some (Json.int k.id)), ("agent", k.owner.map .str), ("question", k.question.map .str), ("title", k.title.map .str)]
    let names := alive.map (·.name)
    let rss := (held.filter fun h => names.contains h.agent).foldl (· + ·.kb) 0
    let commsHc := (alive.find? fun x => some x.name == cv && !gone x).bind (py ·.hc)
    let nlive := (alive.filter fun x => some x.name != cv).length
    let ni (k : String) : Json := Json.oint ((knob sw.name k).bind parseInt)
    let next := startable tasks ks
    let ci := (rows 7).find? fun r => (txt r[0]?).any sw.repos.contains
    -- each repo with its base, its latest CI run, how many locks it holds and the other live swarms that share it
    let repoJs : List Json := sw.repos.map fun rp => Json.mkObj [("path", .str rp), ("base", Json.ostr (bases.get? rp)),
      ("ci", (((rows 7).find? fun r => txt r[0]? == some rp).map ciJson).getD .null),
      ("locks", Json.int (locks.getD rp 0)),
      ("swarms", .arr ((sws.filter fun o => o.name != sw.name && o.ended.isNone && o.repos.contains rp).map
        fun o => Json.str o.name).toArray)]
    out := out.push (Json.mkObj [("name", .str sw.name), ("active", .bool (!alive.isEmpty && sw.ended.isNone)),
      ("comms", Json.ostr cv), ("comms_hc", Json.ostr commsHc),
      ("repos", .arr repoJs.toArray), ("folder", Json.ostr sw.repos.head?),
      ("created", Json.oint sw.created), ("ended", Json.oint sw.ended),
      ("staffing", Json.mkObj [("live", Json.int nlive), ("min", ni "agent_min"), ("max", ni "agent_max"),
        ("held", Json.ostr (knob sw.name "spawn_held")), ("queue_only", .bool (knob sw.name "queue_only" == some "on"))]),
      ("counts", Json.mkObj (STATES.map fun s => (s.text, Json.int (ks.filter (·.state == s)).length))),
      ("next", .arr ((next.take 5).map fun k => obj [("id", some (Json.int k.id)), ("title", k.title.map .str),
        ("qpos", k.qpos.map Json.int), ("priority", k.priority.map Json.int)]).toArray),
      ("ready", Json.int next.length),
      ("ci", (ci.map ciJson).getD .null),
      ("agents", .arr ags), ("needs", .arr (qs.toArray ++ needs)), ("rss_kb", Json.int rss),
      ("away", .bool (knob sw.name "away").isSome)])
  let (tasksJ, reposJ, needsJ) := machine t (rows 10) (rows 11) wsRows (rows 13) (rows 14) (rows 15) (rows 7) agents sws knob evs
  return Json.mkObj [("now", Json.int t), ("view", .str "swarms"), ("db", .str p),
    ("counts", Json.mkObj (STATES.map fun s => (s.text, Json.int (tasks.filter (·.state == s)).length))),
    ("swarms", .arr out), ("tasks", .arr tasksJ), ("repos", .arr reposJ), ("needs", .arr needsJ)]

end SwarmLean.SwarmsView
