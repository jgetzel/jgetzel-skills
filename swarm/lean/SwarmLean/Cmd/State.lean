import Std.Data.HashMap
import SwarmLean.Cmd
import SwarmLean.Cmd.OpsHelp
import SwarmLean.Db.Agents
import SwarmLean.Sys
import SwarmLean.Lib.Lifecycle
import SwarmLean.Lib.Spawn
import SwarmLean.Lib.Cost
import SwarmLean.Lib.Run

/-! `swarm state --json` (one read-only snapshot for UIs) and `swarm watch` (state.lua). -/

namespace SwarmLean.Cmd.State
open Args

/-- The panel views (state.VIEWS' keys, sorted). -/
def VIEWS : List String := ["activity", "agents", "board", "overview", "summary", "swarms", "system"]

/-- The `state` parser. -/
def stateSpec : Spec := .mk "state" helpState []
  [{ flag "--json" with minCount := 1 }, { opt "--view" with choices := VIEWS }, opt "--agent", opt "--task" none (some int)]
  [] [] none

/-- The `watch` parser. -/
def watchSpec : Spec := .mk "watch" helpWatch [] [opt "--tail" (some "20") (some int), flag "--once"] [] [] none

variable {m : Type → Type} [Monad m] [MonadExceptOf Exit m] [Store m] [Clock m] [Env m] [Sys m]

/-- An event's line: time, the agent in a colour of its name, kind, path and data. -/
def eventLine (e : Event) : m String := do
  let ag := e.agent.getD ""
  let sum := ag.toUTF8.foldl (fun s b => s + b.toNat) 0
  let col := ["31", "32", "33", "34", "35", "36"][sum % 6]!
  let t ← match e.ts with | some t => pure t | none => Clock.now
  return s!"{← Sys.date "%H:%M:%S" t} \x1b[{col}m{padRight (e.agent.getD "-") 12}\x1b[0m {padRight (e.kind.getD "nil") 9} {e.path.getD ""} {e.data.getD ""}"

/-- `swarm watch` (state.cmd_watch): the events as they come, and the live agents every 30 s. -/
def watch (a : Parsed) : m UInt32 := do
  -- shortcut: each second loads the event table whole (Store has no query); fine for a human's terminal
  let mx ← Store.txn [.event] fun db => (db, db.events.foldl (fun x e => max x e.id) 0)
  let mut last : Int := max 0 (mx - (a.int "tail").getD 20)
  let mut tick : Nat := 0
  repeat
    let db ← Store.txn [.event, .agent] fun db => (db, db)
    for e in db.events do
      if (e.id : Int) > last then
        last := e.id
        Env.out (← eventLine e)
    if tick % 30 == 0 then
      Env.out s!"\x1b[2m-- {" | ".intercalate ((Agents.live db).map fun x => x.name ++ ":" ++ x.status.getD "nil")} --\x1b[0m"
    tick := tick + 1
    if a.flag "once" then break
    Sys.sleep 1000
  return 0

section
open Lean (Json)
open _root_.SwarmLean.Run (obj)
variable [Fs m] [Proc m] [Git m]

/-- An optional text, null when nil (state.lua's N). -/
def N (o : Option String) : Json := Json.ostr o
/-- An optional integer, null when nil. -/
def NI (o : Option Int) : Json := Json.oint o

/-- fate's checks in the order the agent screen shows them (REDESIGN.md §2). -/
def CHECKS : List String := ["stay", "task", "lock", "unlanded", "job", "unread", "terminal", "waiter", "idle", "context"]

/-- A check's line on the agent screen. -/
def label : String → String
  | "stay" => "Stays" | "task" => "Holds a task" | "lock" => "Holds a lock" | "unlanded" => "Work not on its base"
  | "job" => "Background process" | "unread" => "Unread messages" | "terminal" => "Terminal" | "waiter" => "Waiter"
  | "idle" => "Idle" | "context" => "Context" | k => k

/-- `l` with `k` set to `v`. -/
def setKey (l : List (String × α)) (k : String) (v : α) : List (String × α) :=
  if l.any (·.1 == k) then l.map fun (x, y) => (x, if x == k then v else y) else l ++ [(k, v)]

/-- watchd's verdict on live idle agent row `x` and the checks behind it (state.fate): watchd's fate, heard. `all`:
every check (the agent screen); else only those fate made, which end at the first that holds (Home's chip). `f`: its
reads; `byT`: hc's terminals (none: hc did not answer). -/
def fateJson (db : Db) (x : Agent) (t : Int) (f : Lifecycle.Reads m) (byT : Option (List Agents.Term)) (all : Bool) :
    m Json := do
  let dur (s : Int) : String := ago t (t - s)
  let hx := byT.bind fun ts => (py x.hc).bind fun h => ts.find? (·.address == some h)
  let (v, g) ← Lifecycle.fateHeard x t hx byT.isSome f
  let mut last := (g.checks.filter (·.2)).getLast?.map (·.1)
  let mut on : List (String × Bool) := g.checks.map fun (k, _) => (k, some k == last)
  let mut h := g
  if all then  -- every check, from a second run in which none holds
    let (_, h2) ← Lifecycle.fateHeard x t hx byT.isSome f (all := true)
    h := h2
    on := setKey h2.checks "unread" false
  let has (k : String) (on : List (String × Bool)) := (on.lookup k).isSome
  let reuse := v == some "reuse"
  if has "context" on then on := setKey (setKey on "context" reuse) "waiter" reuse  -- they keep it only together
  if v.isSome && v != some "unclean" then last := none  -- a verdict past every keeping check: none of them holds
  let pool := Queue.staffing db
  let (w, u) := Lifecycle.waking db x.name
  if has "unread" on then on := setKey on "unread" (reuse && w > 0)
  let mut detail : List (String × String) := []
  let mut short : List (String × String) := []
  if has "stay" on then
    let e := (db.events.filter fun e => e.agent == some x.name && e.kind == some "stay").getLast?
    detail := detail ++ [("stay", match x.stay with
      | some st => s!"'{st}'{match e with | some e => ", for " ++ dur (t - e.ts.getD 0) | none => ""}"
      | none => "no stay")]
    short := short ++ [("stay", "stays")]
  if has "task" on then
    let r := db.tasks.find? fun r => r.owner == some x.name && (r.state = .claimed || r.state = .blocked)
    detail := detail ++ [("task", match r with
      | some r => s!"#{r.id} {r.title.getD ""}{match r.lease_until with | some l => s!", lease {dur (max 0 (l - t))} left" | none => ""}"
      | none => "none")]
    short := short ++ [("task", match r with | some r => s!"holds #{r.id}" | none => "holds a task")]
  if has "lock" on then
    let l := ((db.locks.filter (·.agent == some x.name)).map (·.path)).mergeSort (· ≤ ·)
    detail := detail ++ [("lock", if l.isEmpty then "none" else ", ".intercalate l)]
    short := short ++ [("lock", "holds a lock")]
  if has "unlanded" on then
    match h.held with
    | some (held, bs) =>
      let b := bs.headD "nil"
      let ls := splitlines (← Lifecycle.uncleanList held b)
      let commits := (ls.filter (·.startsWith "commit ")).length
      let files := (ls.filter fun l => !l.startsWith "commit " && l != "").length
      let pr := ((db.tasks.filter fun r => r.owner == some x.name && r.pr.isSome).getLast?).bind (·.pr)
      detail := detail ++ [("unlanded", s!"{held}: {files} uncommitted file{if files == 1 then "" else "s"}, {commits} commit{if commits == 1 then "" else "s"} not on {b}{match pr with | some p => s!" (PR #{p})" | none => ""}")]
      short := short ++ [("unlanded", if files > 0 then "uncommitted work" else "unlanded commits")]
    | none => detail := detail ++ [("unlanded", "all on its base")]
  if has "job" on then
    detail := detail ++ [("job", match h.proc with
      | some p => s!"{cut p.args 80}, {dur p.age}"
      | none => "none")]
    short := short ++ [("job", "background job")]
  detail := detail ++ [("unread", if w > 0 then s!"{w}{if u > 0 then s!", {u} urgent" else ""}" else "none")]
  if has "terminal" on then
    let other ← match hx with
      | some y => match py y.cwd with
        | some c => pure !(← f.ours c)
        | none => pure false
      | none => pure false
    let hc := x.hc.getD ""
    detail := detail ++ [("terminal", if (py x.hc).isNone then "none bound" else if byT.isNone then hc ++ ": hc did not answer"
      else match hx with
        | none => hc ++ " gone"
        | some y => if other then s!"{hc} in another repo ({y.cwd.getD ""})" else s!"{hc} {y.status.getD "?"}")]
    short := short ++ [("terminal", match hx with
      | none => "terminal gone"
      | some y => if other then "in another repo" else "terminal " ++ y.status.getD "busy")]
  if has "waiter" on then
    let alive ← match x.waiter with | some p => f.alive p | none => pure false
    detail := detail ++ [("waiter", if alive then s!"present (pid {x.waiter.getD 0})" else "gone: no message can wake it")]
  if has "idle" on then
    let st := x.status.getD "nil"
    detail := detail ++ [("idle", if x.status != some "idle" then st else s!"{dur (t - x.last_active.getD 0)} (watchd waits 2m)")]
    short := short ++ [("idle", if x.status != some "idle" then st else "idle under 2 min")]
  if has "context" on then
    let ctx := x.ctx_tokens.getD 0
    let k := fdiv ctx 1000
    detail := detail ++ [("context", if ctx ≥ Agents.SMALL_CTX then s!"{k}k: too big to be given another task"
      else match pool.head? with
        | none => s!"{k}k: small enough, but no task is ready"
        | some p => if f.passedOver then s!"{k}k: small enough, but it passed over the ready tasks"
          else s!"{k}k: small enough for another task; #{p.id} is ready")]
    short := short ++ [("context", match pool.head? with | some p => s!"#{p.id} is ready" | none => "a task is ready")]
  let checks := CHECKS.filterMap fun k => (on.lookup k).map fun o =>
    Json.mkObj [("label", .str (label k)), ("on", .bool o), ("detail", .str ((detail.lookup k).getD ""))]
  let held := CHECKS.filterMap fun k => if on.lookup k == some true && k != "waiter" && k != "unread" then List.lookup k short else none
  let verdict := v.getD "kept"
  let sc := (short.lookup "context").getD "nil"
  return Json.mkObj [("verdict", .str verdict),
    ("says", .str (if verdict == "end" then "watchd ends it at its next tick" else if verdict == "reuse" then "Kept for reuse: " ++ sc
      else "Kept: " ++ " and ".intercalate held)),
    ("short", if verdict == "end" then .str "ending" else if verdict == "reuse" then .str sc
      else N (last.bind (List.lookup · short))),
    ("checks", .arr (if all then checks.toArray else #[]))]

/-- `git rev-parse --abbrev-ref HEAD` in worktree `wt` without a subprocess: its HEAD file. -/
def headBranch (wt : String) : m (Option String) := do
  let g := joinPath wt ".git"
  let g ← if (← Sys.kind g true) == .file then  -- a linked worktree: .git names its gitdir
      match ((← Fs.read g).getD "").splitOn "gitdir:" with
      | _ :: rest@(_ :: _) => pure (some (joinPath wt (strip ("gitdir:".intercalate rest))))
      | _ => pure none
    else pure (some g)
  let some g := g | return none
  let some s ← Fs.read (joinPath g "HEAD") | return none
  let s := strip s
  return some (if s.startsWith "ref: refs/heads/" then (s.drop 16).toString else "HEAD")

/-- Not a touch or status event (SQL's `kind not in ('touch','status')`, which a NULL kind fails). -/
def shown (e : Event) : Bool := e.kind.any fun k => k != "touch" && k != "status"

/-- An event row as state prints it (the columns asked for, null where NULL); a push event's branch and subject come
from its path (JSON), and its path is null. -/
def eventJson (e : Event) (withId withAgent : Bool) : Json :=
  let base : List (String × Json) := (if withId then [("id", Json.int e.id)] else []) ++ [("ts", NI e.ts)] ++
    (if withAgent then [("agent", N e.agent)] else []) ++ [("kind", N e.kind), ("path", N e.path), ("data", N e.data)]
  if e.kind != some "push" then Json.mkObj base else
  let p := match e.path.bind Json.decode with | some j@(.obj _) => j | _ => Json.mkObj []
  let str (k : String) : Json := (Json.field p k).getD .null
  Json.mkObj (base.map (fun (k, v) => (k, if k == "path" then .null else v)) ++ [("branch", str "branch"), ("subject", str "subject")])

/-- A message row (body cut to 500 characters); `fill`: NULL columns as null, else absent. -/
def msgJson (r : Msg) (fill : Bool) : Json :=
  let l : List (String × Option Json) := [("id", some (Json.int r.id)), ("ts", r.ts.map Json.int), ("frm", r.frm.map .str),
    ("dest", r.dest.map .str), ("body", r.body.map fun b => .str (cut b 500)), ("urgent", r.urgent.map Json.int), ("kind", r.kind.map .str)]
  if fill then Json.mkObj (l.map fun (k, v) => (k, v.getD .null)) else obj l

/-- `xs` grouped by `key` (the groups an element is in), each group in `xs`' order. -/
def groupBy [BEq κ] [Hashable κ] (xs : List α) (key : α → List κ) : Std.HashMap κ (Array α) :=
  xs.foldl (fun g x => (key x).foldl (fun g k => g.alter k fun a => some ((a.getD #[]).push x)) g) {}

/-- A task row as state prints it: its columns but the body, its timing, lease left, deps, the deps not done (`undone`),
waiting and blocks. `evs`: its events; `st`: each task's state; `waitersOf`: the open tasks naming it a dep. -/
def taskJson (r : Task) (evs : List Event) (t : Int) (st : Std.HashMap Int Status) (waitersOf : Array Task) : Json :=
  let tm := Tasks.timing r evs t
  let deps := Tasks.depsOf r
  let undone := deps.filter fun x => st[x]? != some .done
  let blocks := if r.state = .done then [] else waitersOf.toList.map fun x => (x.id : Int)
  let lease := if r.state = .claimed || r.state = .blocked then (pyI r.lease_until).map (· - t) else none
  Json.mkObj [("id", Json.int r.id), ("title", N r.title), ("state", .str r.state.text), ("owner", N r.owner),
    ("lease_until", NI r.lease_until), ("created_by", N r.created_by), ("evidence", N r.evidence),
    ("deps", .arr (deps.map Json.int).toArray), ("model", N r.model), ("question", N r.question), ("effort", N r.effort),
    ("created_at", NI tm.created_at), ("first_claimed_at", NI tm.first_claimed_at), ("done_at", NI tm.done_at),
    ("dropped_at", NI tm.dropped_at), ("pr", NI tm.pr), ("merged_at", NI tm.merged_at), ("ci_conclusion", N tm.ci_conclusion),
    ("ci_green_at", NI r.ci_green_at), ("claim_ctx", NI tm.claim_ctx), ("done_ctx", NI tm.done_ctx), ("answer", N r.answer),
    ("base", N r.base), ("stop_to", N r.stop_to), ("stop_msg", NI r.stop_msg), ("priority", NI r.priority),
    ("qpos", NI r.qpos), ("hold", N r.hold),
    ("lease_left", NI lease), ("waiting", .bool !undone.isEmpty), ("undone", .arr (undone.map Json.int).toArray),
    ("blocks", .arr (blocks.map fun b => Json.int b).toArray),
    ("queue_wait_s", NI tm.queue_wait_s), ("work_s", NI tm.work_s), ("total_s", NI tm.total_s),
    ("blocked_s", Json.int tm.blocked_s), ("claims", Json.int tm.claims), ("releases", Json.int tm.releases),
    ("holders", .arr (tm.holders.map .str).toArray), ("merge_to_green_s", NI tm.merge_to_green_s)]

/-- Which sections a view needs beyond the header (state.VIEWS); no view is everything. "lanes": hc idle lookups,
worktrees and each live agent's last events. -/
def wants (view : Option String) (k : String) : Bool :=
  match view with
  | none => true
  | some "overview" => ["lanes", "messages", "events"].contains k
  | some "agents" => k == "lanes"
  | some "activity" => ["messages", "events"].contains k
  | some "system" => ["lanes", "events", "locks", "running"].contains k
  | _ => false

/-- A history cell as JSON (a NULL is absent). -/
def valJson : Sqlite.Val → Option Json
  | .int i => some (Json.int i)
  | .real f => some (Json.float f)
  | .text s => some (.str s)
  | .null => none

/-- A JSON field as is, when present (Lua's `x.k ~= nil`; a decoded null counts as present). -/
def raw (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

/-- A pid as Lua's `tonumber` reads it: a number, or numeric text. -/
def pidOf (j : Option Json) : Option Int := j.bind fun j => (Json.int? j).orElse fun _ => (Json.str? j).bind parseInt

/-- The System view's running commands: memory holders from one ps, and other machines' jobs with watchd's reading of
each (lost: its `swarm run` and its terminal are gone; unreachable: watchd's probe of the machine failed); and from the
cmd-cost history, this repo on this machine, the last finished costly commands and the most intensive by peak. -/
def running (db : Db) (t : Int) : m (List (String × Json)) := do
  let hv := Machine.holders db.agents (← Machine.procs)
  let mut run : List Json := hv.map fun h =>
    let age := h.age.getD 0
    Json.mkObj [("agent", .str h.agent), ("command", .str (cut (h.top.getD "") 120)), ("elapsed_s", Json.int age),
      ("start", Json.int (t - age)), ("rss_kb", Json.int h.kb), ("top_kb", if h.top.isSome then Json.int h.top_kb else .null)]
  let mut rc : List Json := []
  let mut top : List Json := []
  if ← Cost.exists? then
    let host ← Sys.hostname
    let repo := (← Cost.repoName).getD "?"
    let rows ← Sys.sqlAt (← Cost.path) Cost.SCHEMA
      [("select ts,agent,cmd,wall_s,peak_kb from cmd where machine=? and repo=? order by id desc limit 6", [.text host, .text repo]),
       ("select key,count(*) n,max(peak_kb) peak_kb,max(wall_s) wall_s,max(cpu_s) cpu_s from cmd where machine=? and repo=? " ++
        "group by key order by max(peak_kb) desc limit 5", [.text host, .text repo])]
    let named (ks : List String) (r : Array Sqlite.Val) : Json := obj (ks.mapIdx fun i k => (k, valJson (r.getD i .null)))
    rc := ((rows.headD #[]).toList.map (named ["ts", "agent", "cmd", "wall_s", "peak_kb"]))
    top := (((rows.drop 1).headD #[]).toList.map (named ["key", "n", "peak_kb", "wall_s", "cpu_s"]))
  let js := if db.events.any (·.kind == some "job-start") then
      (Machine.liveJobs db.events t).filter fun j => (raw j.data "machine").isSome
    else []
  let mut gone : List Machine.Job := []
  for j in js do
    let alive ← match pidOf (raw j.data "pid") with | some p => Sys.pidAlive p | none => pure false
    if !alive then gone := gone ++ [j]
  let terms ← if gone.isEmpty then pure none else Agents.hcTerminals
  let live : List String := (terms.getD []).filterMap (·.address)
  let ms := match (db.getMeta "machines").bind (·.v) |>.bind Json.decode with | some j => j | none => Json.mkObj []
  for j in js do
    let mach := (raw j.data "machine").getD .null
    let mt := match mach with
      | .str k => match raw ms k with | some x@(.obj _) => x | _ => Json.mkObj []
      | _ => Json.mkObj []
    let r := match (raw mt "jobs"), j.id with
      | some jobs@(.obj _), some id => match raw jobs id with | some x@(.obj _) => x | _ => Json.mkObj []
      | _, _ => Json.mkObj []
    let unreach := match raw mt "state" with | some (.str "connected") => false | some _ => true | none => false
    let g := (raw r "gone").isSome || ((raw r "rss_kb").isNone && !(j.str "hc").any live.contains)
    let isgone := gone.any fun x => x.id == j.id && x.ts == j.ts
    let ts := j.ts.getD 0
    run := run ++ [obj [("agent", j.agent.map .str), ("command", some (.str (cut ((j.str "cmd").getD "") 120))),
      ("elapsed_s", some (Json.int (t - ts))), ("start", j.ts.map Json.int), ("rss_kb", some ((raw r "rss_kb").getD .null)),
      ("cpu", some ((raw r "cpu").getD .null)), ("machine", some mach), ("job", j.id.map .str),
      ("unreachable", some (.bool unreach)), ("lost", some (.bool (!unreach && isgone && g)))]]
  return [("costly", .arr rc.toArray), ("cost_top", .arr top.toArray), ("running", .arr run.toArray)]

/-- watchd's record (pid, terminal), what it was started with, and whether the swarm code changed since it started
(stale: a swarm-lean binary the launcher runs is newer). -/
def watchdJson (wr : String) (runV : Option String) : m Json := do
  let runJ := match runV.bind Json.decode with | some j@(.obj _) => j | _ => Json.mkObj []
  let cs := wr.toList
  let pidT := cs.takeWhile (!isSpace ·)
  let term := String.ofList (((cs.drop pidT.length).dropWhile isSpace).takeWhile (!isSpace ·))
  let pid := if pidT.isEmpty then none else parseInt (String.ofList pidT)
  let here := (← Spawn.swarmHere).getD "."
  let mut newest : Int := 0
  for b in ["lean/.lake/build/bin/swarm-lean", "lean/.lake/nix"] do
    if let some mt ← Sys.mtime (joinPath here b) then newest := max newest mt
  let started := raw runJ "started"
  let alive ← match pid with | some x => Sys.pidAlive x | none => pure false
  return obj [("pid", pid.map Json.int), ("terminal", some (if pidT.isEmpty || term == "" || term == "-" then .null else .str term)),
    ("started", some (started.getD .null)), ("alive", some (.bool alive)),
    ("stale", some (.bool (match started.bind Json.num? with | some s => Float.ofInt newest > s | none => false))),
    ("flags", some (match raw runJ "flags" with | some f@(.arr _) => f | some (.obj _) => .arr #[] | _ => .null))]

/-- A live stayer's hung sign (watchd.hung): its worst stay-* event since it was last active. -/
def staySign (x : Agent) (aev : List Event) : Option String :=
  if (py x.stay).isSome && x.status == some "idle" then
    let got := (aev.filter fun e => e.ts.any (· ≥ x.last_active.getD 0)).filterMap (·.kind)
    if got.contains "stay-hung" then some "hung" else if got.contains "stay-nowaiter" then some "nowaiter"
    else if got.contains "stay-unwoken" then some "unwoken" else none
  else none

/-- `--view summary` (UI-SPEC.md, "New swarm CLI output" 1): task counts, the live agents in six fields (`hc` ties a row
to its terminal), the Herdr space the swarm runs in, and what needs the human as the panel's Needs you lists it; no ended agents, events or messages. -/
def summary (db : Db) (p : String) (t : Int) : m Json := do
  let cv ← match py ((db.getMeta "comms").bind (·.v)) with | some c => pure (some c) | none => env "SWARM_COMMS"
  let live := (db.agents.filter (·.ended.isNone)).mergeSort (·.name ≤ ·.name)
  let names := live.map (·.name)
  let evs := db.events.filter fun e => e.kind.any (·.startsWith "stay-") && e.agent.any names.contains
  let mine (s : Status) (n : String) := db.tasks.filter fun r => r.state = s && r.owner == some n
  let asks := db.tasks.filter (·.state = .blocked)
  let ags := live.map fun x =>
    let own := mine .blocked x.name ++ mine .claimed x.name
    let act := x.last_active.getD 0
    let hung := staySign x (evs.filter (·.agent == some x.name)) == some "hung"
    (x, hung, Json.mkObj [("name", .str x.name), ("hc", N x.hc),
      ("status", N (if own.any (·.state = .blocked) then some "blocked" else x.status)),
      ("task", match own.head? with
        | some r => obj [("id", some (Json.int r.id)), ("title", r.title.map .str)]
        | none => .null),
      ("idle_s", Json.int (t - (if act == 0 then t else act))),
      ("hung", .bool hung)])
  let need (kind : String) (l : List (String × Option Json)) := obj ((("kind", some (Json.str kind))) :: l)
  let ci := db.cis.mergeSort fun x y => x.created.getD "" ≥ y.created.getD ""
  let fin := ci.filter fun r => r.status == some "completed" && r.conclusion.any (· != "cancelled")
  let mach ← Machine.mem
  -- memory per swarm ("New swarm CLI output" 3): the live agents' process trees on this machine, from their claude
  let rss := ((Machine.holders db.agents (← Machine.procs)).filter (·.agent != "other session")).foldl (· + ·.kb) 0
  let needs := asks.map (fun r => need "question" [("task", some (Json.int r.id)), ("agent", r.owner.map .str),
      ("question", r.question.map .str), ("title", r.title.map .str)]) ++
    (live.filter fun x => x.status == some "blocked" && !asks.any (·.owner == some x.name)).map
      (fun x => need "prompt" [("agent", some (.str x.name))]) ++
    (ags.filter (·.2.1)).map (fun (x, _) => need "hung" [("agent", some (.str x.name))]) ++
    (match fin.head? with
      | some r => if r.conclusion != some "success" then
          [need "ci" [("run", some (Json.int r.id)), ("url", r.url.map .str), ("created", r.created.map .str)]] else []
      | none => []) ++
    (match mach with
      | some (av, tot, psi) => if Machine.pressureHigh av tot psi then [need "memory" [("line", some (.str (Machine.line av tot psi)))]] else []
      | none => [])
  return Json.mkObj [("active", .bool !live.isEmpty), ("db", .str p), ("now", Json.int t), ("view", .str "summary"),
    ("comms", N cv), ("space", N (py ((db.getMeta "space").bind (·.v)))), ("rss_kb", Json.int rss),
    ("counts", Json.mkObj (["open", "claimed", "blocked", "done", "dropped"].map fun k =>
      (k, Json.int (db.tasks.filter (·.state.text == k)).length))),
    ("agents", .arr (ags.map (·.2.2)).toArray), ("needs", .arr needs.toArray)]

/-- `swarm state --json` (state.cmd_state): one read-only snapshot for UIs (the Herdr panel). -/
def state (a : Parsed) : m UInt32 := do
  let t ← Clock.now
  if a.str "view" == some "swarms" then  -- before the db: it lists every repo's
    Env.out (Json.encode (Json.mkObj [("now", Json.int t), ("view", .str "swarms"), ("swarms", .arr (← Spawn.registered).toArray)]))
    return 0
  let p ← Spawn.dbPath
  if (← Sys.kind p true) == .none then
    Env.out (Json.encode (Json.mkObj [("active", .bool false), ("db", .str p), ("now", Json.int t)]))
    return 0
  let db ← Store.txn [.task, .event, .agent, .msg, .lock, .conflict, .«meta», .ci, .workspace, .cursor] fun db => (db, db)
  let view := a.str "view"
  if view == some "summary" then
    Env.out (Json.encode (← summary db p t))
    return 0
  let full := view.isNone
  let lanes := wants view "lanes"
  let me := a.str "agent"
  let tid := a.int "task"
  -- every per-task and per-agent lookup below reads these, built in one pass each (a list scan per row took seconds)
  let tev := db.events.filter fun e => (e.kind.map (Tasks.TASK_KINDS.contains ·)).getD false
  let tevBy := groupBy tev fun e => (Tasks.eventTask e).toList
  let stOf : Std.HashMap Int Status := db.tasks.foldl (fun h r => h.insert r.id r.state) {}
  let waitersBy := groupBy (db.tasks.filter (·.state = .open)) fun x => (Tasks.depsOf x).eraseDups
  let ownBy := groupBy (db.tasks.filter fun r => r.state = .claimed || r.state = .blocked) (·.owner.toList)
  let evBy := groupBy db.events (·.agent.toList)
  let msgBy := groupBy db.msgs fun r => (r.frm.toList ++ r.dest.toList).eraseDups
  let lockBy := groupBy db.locks (·.agent.toList)
  -- what the view lists (no view: everything): open work and live agents always; the Board the newest 80 done and
  -- dropped (it shows 80), the Agents screen the newest 60 ended (it shows 60), an agent's screen its done tasks, a
  -- task's screen it and its deps, the event feeds the tasks their events name; the rest only as `counts`
  let deep := view == some "activity"  -- the Activity tab folds and filters, so it reads further back
  let evShown := if wants view "events" then (db.events.filter shown).reverse.take (if deep then 300 else 60) else []
  let newest (s : Status) : List Int := ((db.tasks.filter (·.state = s)).reverse.take 80).map (·.id)
  let page : List Int := (if view == some "board" then newest .done ++ newest .dropped else []) ++
    (match tid with | some i => i :: ((db.find i).map Tasks.depsOf).getD [] | none => []) ++
    evShown.filterMap fun e => (Tasks.eventTask e).map fun i => (i : Int)
  let sent (r : Task) : Bool := full || !(r.state = .done || r.state = .dropped) || page.contains r.id ||
    (r.state = .done && me.isSome && r.owner == me)
  let tasksJ := (db.tasks.filter sent).map fun r => taskJson r (tevBy.getD r.id #[]).toList t stOf (waitersBy.getD r.id #[])
  let endedPage := if view == some "agents" then
      (((db.agents.filter (·.ended.isSome)).mergeSort fun x y => x.ended.getD 0 ≥ y.ended.getD 0).take 60).map (·.name)
    else []
  let sentA (x : Agent) : Bool := full || x.ended.isNone || me == some x.name || endedPage.contains x.name
  let wts ← if lanes then Workspaces.wtMap db else pure []
  let mut seen : Agents.Seen := []
  -- the reads' inputs, once read: hc's terminals, the main worktree, the agents' and every worktree, the pool
  let mut reads : Option (Option (List Agents.Term) × Option String × List (String × String) × List (String × String) ×
    List Task) := none
  let mut agsA : Array (Json × Bool × String) := #[]
  let byName := fun (l : List Agent) => l.mergeSort (·.name ≤ ·.name)
  for x in byName (db.agents.filter fun x => x.ended.isNone && sentA x) ++ byName (db.agents.filter fun x => x.ended.isSome && sentA x) do
    let own := (ownBy.getD x.name #[]).toList
    let aev := (evBy.getD x.name #[]).toList
    let live := x.ended.isNone
    let wt := py ((wts.lookup x.name).orElse fun _ => x.wt)
    let (act, s1) ← if live && lanes then Agents.sessionActive seen x t else pure (x.last_active.getD 0, seen)
    seen := s1
    let status := if !live then some "ended" else if own.any (·.state = .blocked) then some "blocked" else x.status
    let sign := if live then staySign x aev else none
    let (cold, s2) ← if live && lanes then Agents.coldReason seen x t else pure (none, seen)
    seen := s2
    let branch ← match live, wt with
      | true, some w => pure (N (← headBranch w))
      | _, _ => pure .null
    let files := if full || live || me == some x.name then
        let sn := match x.snap with | some s => if s.startsWith "{" then (Json.decode s).getD .null else .null | none => .null
        Json.items ((Json.field sn "files").getD .null)
      else []
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
      l := l ++ [("locks", .arr ((lockBy.getD x.name #[]).map fun k => Json.str k.path))]
    if full || (lanes && live) || me == some x.name then
      let evs := ((aev.filter shown).reverse.take 5)
      l := l ++ [("events", .arr (evs.map (eventJson · false false)).toArray)]
    if live && x.status == some "idle" && (lanes || me == some x.name) then  -- watchd's verdict and why (REDESIGN.md §2)
      let (byT, main, wm, all, pool) ← match reads with
        | some r => pure r
        | none => do
          let byT ← Agents.hcTerminals
          let main ← Workspaces.main none
          let wm ← if lanes then pure wts else Workspaces.wtMap db
          let all ← Workspaces.worktrees
          pure (byT, main, wm, all, Queue.staffing db)
      reads := some (byT, main, wm, all, pool)
      let f := Lifecycle.reads (m := m) db main wm all x.name pool
      l := l ++ [("fate", ← fateJson db x t f byT (me == some x.name))]
    if full || me == some x.name then  -- the detail pane's messages
      let ms := (msgBy.getD x.name #[]).toList.reverse.take 5
      l := l ++ [("messages", .arr (ms.map (msgJson · false)).toArray)]
    agsA := agsA.push (Json.mkObj l, live, x.name)
  let ags := agsA.toList
  -- pressure episodes, newest first, the last five
  let eps := (db.events.filter fun e => e.kind == some "pressure" || e.kind == some "pressure-end").foldl
    (fun (eps : List (Option Int × Option Int × Option String)) e =>
      if e.kind == some "pressure" then (e.ts, none, e.data) :: eps
      else match eps with
        | (s, none, l) :: rest => (s, e.ts, l) :: rest
        | _ => eps) []
  let press := (eps.take 5).map fun (s, e, l) => obj [("start", s.map Json.int), ("end", some (NI e)), ("line", some (N l))]
  let mach ← match ← Machine.mem with
    | some (av, tot, psi) => pure (Json.mkObj [("line", .str (Machine.line av tot psi)), ("avail_kb", Json.int av),
        ("total_kb", Json.int tot), ("psi", obj [("memory", psi.memory.map Json.float), ("cpu", psi.cpu.map Json.float),
          ("level", psi.level.map .str), ("load", psi.load.map Json.float), ("cores", psi.cores.map Json.int)]),
        ("high", .bool (Machine.pressureHigh av tot psi))])
    | none => pure .null
  let metaV (k : String) : Option String := (db.getMeta k).bind (·.v)
  let cv ← match py (metaV "comms") with | some c => pure (some c) | none => env "SWARM_COMMS"
  let nlive := (ags.filter fun (_, live, n) => live && some n != cv).length
  let byCreated := db.cis.mergeSort fun x y => x.created.getD "" ≥ y.created.getD ""
  let runs := (byCreated.take 5).map fun r => Json.mkObj [("id", Json.int r.id), ("status", N r.status),
    ("conclusion", N r.conclusion), ("url", N r.url), ("created", N r.created)]
  let fin := (byCreated.filter fun r => r.status == some "completed" && r.conclusion.any (· != "cancelled")).take 50
  let streak := (fin.takeWhile (·.conclusion != some "success")).length
  let mut out : List (String × Json) := [("active", .bool (ags.any (·.2.1))), ("db", .str p), ("now", Json.int t),
    ("view", N view), ("comms", N cv),
    -- the user's staffing numbers (agents.limits) and the board's "auto-spawn holding" line while it holds
    ("limits", obj [("live", some (Json.int nlive)), ("min", some (NI ((metaV "agent_min").bind parseInt))),
      ("max", some (NI ((metaV "agent_max").bind parseInt))), ("held", some (N (metaV "spawn_held"))),
      ("queue_only", some (.bool (Queue.queueOnly db)))]),
    ("tasks", .arr tasksJ.toArray), ("agents", .arr (ags.map (·.1)).toArray),
    -- every task by state, and the ended agents but the communicator: what the trimmed lists leave out
    ("counts", Json.mkObj ((["open", "claimed", "blocked", "done", "dropped"].map fun k =>
      (k, Json.int (db.tasks.filter (·.state.text == k)).length)) ++
      [("ended", Json.int (db.agents.filter fun x => x.ended.isSome && some x.name != cv).length)])),
    ("conflicts", .arr ((db.conflicts.mergeSort fun x y => x.since.getD 0 ≥ y.since.getD 0).map fun c =>
      Json.mkObj [("a", .str c.a), ("b", .str c.b), ("path", .str c.path), ("since", NI c.since)]).toArray),
    ("pressure", .arr press.toArray), ("machine", mach),
    -- the latest runs on the base, from the ci table watchd fills, and how many of the newest finished ones are red
    ("ci", Json.mkObj [("runs", .arr runs.toArray), ("red_streak", Json.int streak)])]
  out := out ++ [("watchd", ← match metaV "watchd" with
    | some wr => watchdJson wr (metaV "watchd_run")
    | none => pure .null)]
  out := out ++ [("away", match metaV "away" with  -- "<since> <note>" while the user is away (`swarm away`)
    | some aw =>
      let ds := aw.toList.takeWhile Char.isDigit
      let rest := aw.toList.drop ds.length
      let note := if !ds.isEmpty && rest.head? == some ' ' && rest.length > 1 then some (String.ofList rest.tail) else none
      obj [("since", if ds.isEmpty then none else (parseInt (String.ofList ds)).map Json.int), ("note", some (N note))]
    | none => .null)]
  out := out ++ [("back", ((metaV "away_digest").bind Json.decode).getD .null)]  -- `swarm away --back`'s digest
  if let some tid := tid then  -- the task screen: what the board's rows leave out
    match db.find tid with
    | some r =>
      let evs := (tevBy.getD r.id #[]).toList
      let key := "#" ++ d tid
      let ms := ((db.msgs.reverse.filter fun x => hasSub (x.body.getD "") key).take 200).filter fun x =>
        (((cut (x.body.getD "") 500 ++ " ").splitOn key).tail.any fun rest => rest.toList.head?.any (!·.isDigit))
      out := out ++ [("task", Json.mkObj [("id", Json.int tid), ("body", N r.body),
        ("events", .arr (evs.map fun e => obj [("ts", e.ts.map Json.int), ("agent", e.agent.map .str),
          ("kind", e.kind.map .str), ("data", e.data.map .str)]).toArray),
        ("messages", .arr ((ms.take 20).map (msgJson · false)).toArray)])]
    | none => out := out ++ [("task", .null)]
  if wants view "messages" then
    out := out ++ [("messages", .arr ((db.msgs.reverse.take (if deep then 120 else 40)).map (msgJson · true)).toArray)]
  if wants view "events" then
    out := out ++ [("events", .arr (evShown.map (eventJson · true true)).toArray)]
  if wants view "locks" then
    out := out ++ [("locks", .arr ((db.locks.mergeSort fun x y => x.since.getD 0 ≥ y.since.getD 0).map fun k =>
      Json.mkObj [("path", .str k.path), ("agent", N k.agent), ("reason", N k.reason), ("since", NI k.since),
        ("lease_until", NI k.lease_until), ("seen", NI k.seen)]).toArray)]
  if wants view "running" then  -- one ps, only where the System view shows it
    out := out ++ (← running db t)
  Env.out (Json.encode (Json.mkObj out))
  return 0

end

/-- The group: state and watch. -/
def group [Fs m] [Proc m] [Git m] : Group m where
  specs := [("state", stateSpec), ("watch", watchSpec)]
  run a := if a.cmd == "state" then state a else watch a

end SwarmLean.Cmd.State
