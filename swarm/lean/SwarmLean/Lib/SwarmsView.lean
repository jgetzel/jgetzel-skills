import SwarmLean.Lib.Swarms
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Run
import SwarmLean.Db.Plan
import SwarmLean.Db.Tasks

/-! `swarm state --json --view swarms` (sw-global §5): every swarm on the machine in one read, for the Herdr panels. -/

namespace SwarmLean.SwarmsView
open Lean (Json)
open SwarmLean.Run (obj)
open Sqlite (Val)

/-- The task states the counts list. -/
def STATES : List String := ["open", "claimed", "blocked", "done", "dropped", "landing"]

/-- A swarm's meta keys the view reads. -/
def KNOBS : List String := ["agent_min", "agent_max", "spawn_held", "queue_only", "away"]

/-- `p` is `dir` or below it. -/
def under (dir p : String) : Bool := p == dir || p.startsWith (dir ++ "/")

/-- One task as the view reads it. -/
structure T where
  id : Int
  state : String
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
  let undone : Std.HashSet Int := all.foldl (fun h k => if k.state == "done" || k.state == "dropped" then h else h.insert k.id) {}
  let ok := ks.filter fun k => k.state == "open" && (py k.hold).isNone && !k.deps.any undone.contains
  let rank (k : T) : List Int :=
    [if (k.title.getD "").startsWith "main red: " then 0 else 1, k.qpos.getD (1 <<< 40), k.priority.getD 2, k.id]
  let rec lex : List Int → List Int → Bool
    | x :: xs, y :: ys => x < y || (x == y && lex xs ys)
    | _, _ => true
  ok.mergeSort fun a b => lex (rank a) (rank b)

/-- Task `k` is swarm `s`'s: one of its repos is the swarm's, a member owns or added it, or it has no repo and no swarm's
agent owns or added it (a task before `task_repo`, or the human's: every swarm's board shows it). -/
def mine (repos : List String) (members everyone : Std.HashSet String) (taskRepos : List String) (owner by_ : Option String) :
    Bool :=
  taskRepos.any repos.contains || owner.any members.contains || by_.any members.contains ||
    (taskRepos.isEmpty && !owner.any everyone.contains && !by_.any everyone.contains)

/-- An agent's hung sign (watchd.hung, as `State.staySign`): a stayer, idle, with a stay-hung event since it was active. -/
def hung (x : Agent) (evs : List (String × String × Int)) : Bool :=
  (py x.stay).isSome && x.status == some "idle" &&
    evs.any fun (a, k, ts) => a == x.name && k == "stay-hung" && ts ≥ x.last_active.getD 0

variable {m : Type → Type} [Monad m] [Env m] [Sys m] [Proc m] [Git m]

/-- The ids of swarm `s`'s tasks (`mine`): what its panel's board and Next up list (sw-global §5). -/
def mineIds (s : String) : m (Std.HashSet Int) := do
  let rs ← Sys.sqlAt (← Swarms.dbPath) schema [
    ("select id, owner, created_by from task", []),
    ("select task, repo from task_repo", []),
    ("select name, swarm from agent where swarm is not null", []),
    ("select repo from swarm_repo where swarm=?", [.text s])] true
  let rows (i : Nat) : List (Array Val) := (rs.getD i #[]).toList
  let taskRepos : Std.HashMap Int (List String) := (rows 1).foldl (init := {}) fun h r =>
    match Swarms.int r[0]?, Swarms.txt r[1]? with
    | some k, some rp => h.insert k (rp :: h.getD k [])
    | _, _ => h
  let everyone : Std.HashSet String := (rows 2).foldl (init := {}) fun h r =>
    match Swarms.txt r[0]? with
    | some a => h.insert a
    | none => h
  let members : Std.HashSet String := (rows 2).foldl (init := {}) fun h r =>
    match Swarms.txt r[0]?, Swarms.txt r[1]? with
    | some a, some w => if w == s then h.insert a else h
    | _, _ => h
  let repos := (rows 3).filterMap (Swarms.txt ·[0]?)
  return (rows 0).foldl (init := {}) fun h r =>
    match Swarms.int r[0]? with
    | some k =>
      if mine repos members everyone (taskRepos.getD k []) (py (Swarms.txt r[1]?)) (py (Swarms.txt r[2]?)) then h.insert k
      else h
    | none => h

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
repos, live agents (each with its repo, status, task, idle time and hung sign), tasks by state, what needs the human
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
    ("select repo, status, conclusion, url, created, id from ci order by created desc", [])] true
  let rows (i : Nat) : List (Array Val) := (rs.getD i #[]).toList
  let txt (v : Option Val) : Option String := Swarms.txt v
  let int (v : Option Val) : Option Int := Swarms.int v
  let agents : List (String × Agent) := (rows 0).filterMap fun r =>
    match txt r[0]?, (Row.dec (r.extract 1 r.size) : Except String Agent) with
    | some s, .ok a => some (s, a)
    | _, _ => none
  let tasks : List T := (rows 1).filterMap fun r => (int r[0]?).map fun id =>
    { id, state := (txt r[1]?).getD "open", owner := py (txt r[2]?), by_ := py (txt r[3]?), title := txt r[4]?,
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
  let knob (s k : String) : Option String :=
    ((rows 4).find? fun r => txt r[0]? == some s && txt r[1]? == some k).bind fun r => py (txt r[2]?)
  let known := ((rows 5).filterMap (txt ·[0]?)) ++ (sws.flatMap (·.repos))
  let evs : List (String × String × Int) := (rows 6).filterMap fun r =>
    match txt r[0]?, txt r[1]?, int r[2]? with
    | some a, some k, some ts => some (a, k, ts)
    | _, _, _ => none
  let everyone : Std.HashSet String := agents.foldl (fun h (_, a) => h.insert a.name) {}
  let live := agents.filter fun (_, a) => a.ended.isNone
  -- memory per swarm: the live agents' process trees on this machine, one ps for them all
  let held := (Machine.holders (live.map (·.2)) (← Machine.procs)).filter (·.agent != "other session")
  let mut out : Array Json := #[]
  for sw in sws do
    let members : Std.HashSet String := agents.foldl (fun h (s, a) => if s == sw.name then h.insert a.name else h) {}
    let ks := tasks.filter fun k => mine sw.repos members everyone (taskRepos.getD k.id []) k.owner k.by_
    let cv := sw.comms
    let mut ags : Array Json := #[]
    let mut needs : Array Json := #[]
    let alive := ((live.filter (·.1 == sw.name)).map (·.2)).mergeSort (·.name ≤ ·.name)
    for x in alive do
      let own := ks.filter fun k => k.owner == some x.name && (k.state == "blocked" || k.state == "claimed" || k.state == "landing")
      let own := (own.filter (·.state == "blocked")) ++ (own.filter (·.state != "blocked"))
      let rp ← match wsRepo.get? x.name with
        | some r => pure (some r)
        | none => match py (x.wt.orElse fun _ => x.cwd) with
          | some d => repoOf known d
          | none => pure none
      let act := x.last_active.getD 0
      let h := hung x evs
      let asks := own.any (·.state == "blocked")
      if !asks && x.status == some "blocked" then needs := needs.push (Json.mkObj [("kind", .str "prompt"), ("agent", .str x.name)])
      if h then needs := needs.push (Json.mkObj [("kind", .str "hung"), ("agent", .str x.name)])
      ags := ags.push (obj [("name", some (.str x.name)), ("hc", some (Json.ostr x.hc)), ("repo", some (Json.ostr rp)),
        ("status", some (Json.ostr (if asks then some "blocked" else x.status))), ("role", some (Json.ostr x.role)),
        ("model", some (Json.ostr x.model)), ("stay", some (Json.ostr (py x.stay))),
        ("task", some (match own.head? with
          | some k => obj [("id", some (Json.int k.id)), ("title", k.title.map .str), ("state", some (.str k.state))]
          | none => .null)),
        ("idle_s", some (Json.int (t - (if act == 0 then t else act)))), ("hung", some (.bool h))])
    let qs := (ks.filter (·.state == "blocked")).map fun k => obj [("kind", some (.str "question")),
      ("task", some (Json.int k.id)), ("agent", k.owner.map .str), ("question", k.question.map .str), ("title", k.title.map .str)]
    let names := alive.map (·.name)
    let rss := (held.filter fun h => names.contains h.agent).foldl (· + ·.kb) 0
    let commsHc := (alive.find? fun x => some x.name == cv).bind (py ·.hc)
    let nlive := (alive.filter fun x => some x.name != cv).length
    let ni (k : String) : Json := Json.oint ((knob sw.name k).bind parseInt)
    let next := startable tasks ks
    let ci := (rows 7).find? fun r => (txt r[0]?).any sw.repos.contains
    out := out.push (Json.mkObj [("name", .str sw.name), ("active", .bool (!alive.isEmpty && sw.ended.isNone)),
      ("comms", Json.ostr cv), ("comms_hc", Json.ostr commsHc),
      ("repos", .arr (sw.repos.map Json.str).toArray), ("folder", Json.ostr sw.repos.head?),
      ("created", Json.oint sw.created), ("ended", Json.oint sw.ended),
      ("staffing", Json.mkObj [("live", Json.int nlive), ("min", ni "agent_min"), ("max", ni "agent_max"),
        ("held", Json.ostr (knob sw.name "spawn_held")), ("queue_only", .bool (knob sw.name "queue_only" == some "on"))]),
      ("counts", Json.mkObj (STATES.map fun s => (s, Json.int (ks.filter (·.state == s)).length))),
      ("next", .arr ((next.take 5).map fun k => obj [("id", some (Json.int k.id)), ("title", k.title.map .str),
        ("qpos", k.qpos.map Json.int), ("priority", k.priority.map Json.int)]).toArray),
      ("ready", Json.int next.length),
      ("ci", match ci with
        | some r => obj [("repo", (txt r[0]?).map .str), ("status", (txt r[1]?).map .str),
            ("conclusion", (txt r[2]?).map .str), ("url", (txt r[3]?).map .str), ("created", (txt r[4]?).map .str),
            ("id", (int r[5]?).map Json.int)]
        | none => .null),
      ("agents", .arr ags), ("needs", .arr (qs.toArray ++ needs)), ("rss_kb", Json.int rss),
      ("away", .bool (knob sw.name "away").isSome)])
  return Json.mkObj [("now", Json.int t), ("view", .str "swarms"), ("db", .str p),
    ("counts", Json.mkObj (STATES.map fun s => (s, Json.int (tasks.filter (·.state == s)).length))),
    ("swarms", .arr out)]

end SwarmLean.SwarmsView
