import SwarmLean.RealSys
import SwarmLean.Lib.Cost
import SwarmLean.Lib.Hook
import SwarmLean.Lib.Re
import SwarmLean.Lib.Json

/-! swarm-report (swarm-retro/swarm-report.lua): evidence for a swarm retro, read from the swarm db: who did what, where
time and attention went. Read-only. Run through ../../swarm-retro/swarm-report, which sets SWARM_RETRO_HERE. Rows are
JSON objects with a NULL column absent, as the Lua's tables; numbers summed from JSON are exact decimals, which print
as cjson's `%.16g` does for the values these hold. -/

namespace SwarmLean.Report
open Lean (Json JsonNumber)
open SwarmLean.Sqlite (Val Conn)

/-- conflict/shared-tree come from watchd's trial merges; conflict-compat is a line conflict whose tokens merge (no
notice sent); conflict-stale a pair skipped because one agent's own changes conflict with main; overlap the pre-sw-locks
touch notice, kept so old dbs still report. -/
def CONFLICTS : List String := ["conflict", "conflict-compat", "shared-tree", "conflict-error", "conflict-stale", "overlap"]
/-- The friction kinds (push is counted, not listed). -/
def FRICTION : List String := ["conflict", "shared-tree", "overlap", "reap", "compact", "ci-red", "blocked"]
/-- As swarm: the prompt cache is warm this long. -/
def COLD_IDLE : Int := 55 * 60
/-- Hook text's source by a marker in its first 80 bytes. -/
def SOURCES : List (String × String) := [("inbox", "swarm messages"), ("machine", "machine:"), ("conflict", "worktree"), ("digest", "idle")]
def EVK : List String := ["ts", "agent", "kind", "path", "data"]
def TASK_KEYS : List String := ["id", "title", "state", "owner", "evidence", "queue_wait_s", "work_s", "total_s", "blocked_s",
  "claims", "releases", "holders", "merge_to_green_s", "ci_conclusion"]

/-- `swarm: <msg>`, exit 1 (util.die). -/
def die (msg : String) : IO α := do
  IO.eprintln s!"swarm: {msg}"
  IO.Process.exit 1

/-- Field `k`, none when absent or null. -/
def f (j : Json) (k : String) : Option Json := SwarmLean.Json.field j k
def fs (j : Json) (k : String) : Option String := SwarmLean.Json.fstr j k
def fi (j : Json) (k : String) : Int := (SwarmLean.Json.fint j k).getD 0
def fnum (j : Json) (k : String) : Option Float := (f j k).bind SwarmLean.Json.num?

/-- An object from pairs, a none value left out (a nil in a Lua table). -/
def obj (kvs : List (String × Option Json)) : Json := Json.mkObj (kvs.filterMap fun (k, v) => v.map (k, ·))

/-- The object's pairs in key order. -/
def pairs : Json → List (String × Json)
  | .obj kvs => kvs.toList
  | _ => []

/-- A cell as JSON, NULL as none. -/
def cell : Val → Option Json
  | .null => none
  | .int i => some (SwarmLean.Json.int i)
  | .real x => some (SwarmLean.Json.float x)
  | .text s => some (.str s)

/-- Rows of `sql` as objects keyed by column name (db:all). -/
def all (c : Conn) (sql : String) (ps : List Val := []) : IO (List Json) := do
  let s ← c.prepare sql
  let mut i : UInt32 := 1
  for p in ps do
    s.bind i p
    i := i + 1
  let n ← s.columnCount
  let mut names := #[]
  for j in [0:n.toNat] do names := names.push (← s.columnName j.toUInt32)
  let mut rows := #[]
  while (← s.stepRaw) == 1 do
    let mut kvs := []
    for j in [0:n.toNat] do kvs := (names[j]!, cell (← s.column j.toUInt32)) :: kvs
    rows := rows.push (obj kvs)
  return rows.toList

/-- An integer of the first row (db:one(...).n). -/
def one (c : Conn) (sql : String) (ps : List Val) : IO Int := do
  return ((← all c sql ps).head?.map (fi · "n")).getD 0

/-- `%02d`. -/
def two (n : Int) : String := if n < 10 then s!"0{n}" else toString n

/-- `1m30s`, `2h05m`. -/
def span (x : Float) : String :=
  let s := x.floor.toInt64.toInt
  if s ≥ 3600 then s!"{Int.fdiv s 3600}h{two (Int.fdiv (Int.emod s 3600) 60)}m" else s!"{Int.fdiv s 60}m{two (Int.emod s 60)}s"

/-- The `p` quantile, as the Lua's (sorted, element floor(p n) + 1). -/
def pct (xs : List Float) (p : Float) : Option Float :=
  let a := (xs.toArray.qsort (· < ·))
  if a.isEmpty then none else a[min (a.size - 1) (p * a.size.toFloat).floor.toUInt64.toNat]?

/-- An exact decimal with no trailing zeros. -/
def norm (n : JsonNumber) : JsonNumber := Id.run do
  let mut m := n.mantissa
  let mut e := n.exponent
  while e > 0 && m % 10 == 0 do
    m := m / 10
    e := e - 1
  return ⟨m, e⟩

def addN (a b : JsonNumber) : JsonNumber :=
  let e := max a.exponent b.exponent
  norm ⟨a.mantissa * 10 ^ (e - a.exponent) + b.mantissa * 10 ^ (e - b.exponent), e⟩

/-- `%.0f`: rounded half to even. -/
def round0 (n : JsonNumber) : Int :=
  let p : Int := 10 ^ n.exponent
  let q := Int.fdiv n.mantissa p
  let r := n.mantissa - q * p
  if 2 * r > p || (2 * r == p && q % 2 != 0) then q + 1 else q

/-- A number field as an exact decimal, 0 when absent. -/
def dec (j : Json) (k : String) : JsonNumber := match f j k with | some (.num n) => n | _ => 0

/-- Lua's tostring of a value (`None` for nil, as the report's s()). -/
def s : Option Json → String
  | none | some .null => "None"
  | some (.str x) => x
  | some (.bool b) => toString b
  | some j => j.compress

/-- `k=v` pairs of an object, sorted. -/
def kv (d : Json) (sep := ", ") : String := sep.intercalate ((pairs d).map fun (k, v) => s!"{k}={s v}")

/-- Lines of a file, the first `n` only when given; none when it can't be read. -/
def lines (p : String) (n : Option Nat := none) : IO (Array String) := do
  try
    let h ← IO.FS.Handle.mk p .read
    let mut acc := #[]
    repeat
      if n.any (acc.size ≥ ·) then break
      let l ← h.getLine
      if l.isEmpty then break
      acc := acc.push (if l.endsWith "\n" then String.ofList l.toList.dropLast else l)
    return acc
  catch _ => return #[]

/-- The agent name of a transcript line's `"type":"agent-name","agentName":"…"` record. -/
def agentName (line : String) : Option String :=
  (line.splitOn "\"type\":\"agent-name\",\"agentName\":\"").tail.findSome? fun p =>
    let nm := p.takeWhile (· != '"')
    if nm.isEmpty || nm.length == p.length then none else some nm.toString

/-- Transcripts whose agent-name record is `name` or a relaunched successor (`name-2`), oldest first. -/
def transcripts (name : String) (cwd : Option String) : IO (List String) := do
  let some cwd := py cwd | return []
  let slug := String.ofList (cwd.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if b < 128 && c.isAlphanum then c else '-')
  let d := ((← IO.getEnv "HOME").getD "") ++ "/.claude/projects/" ++ slug
  let es ← try System.FilePath.readDir d catch _ => return []
  let mut hit := #[]
  for e in es do
    if e.fileName.endsWith ".jsonl" then
      let p := d ++ "/" ++ e.fileName
      -- the record sits near the top
      if let some m := (← lines p (some 40)).findSome? agentName then
        let rest := m.drop (name.length + 1)
        if m == name || (m.startsWith (name ++ "-") && !rest.isEmpty && rest.all Char.isDigit) then
          hit := hit.push (p, (← System.FilePath.metadata p).modified.sec)
  return (hit.toList.mergeSort fun a b => a.2 ≤ b.2).map (·.1)

/-- Bytes of hook-injected context (additionalContext, as hook_additional_context attachments) per source. -/
def hookBytes (files : List String) : IO Json := do
  let mut n : List (String × Int) := []
  for file in files do
    for line in ← lines file do
      if hasSub line "\"hook_additional_context\"" then
        let a := ((SwarmLean.Json.decode line).bind (f · "attachment")).getD .null
        let cs := match f a "content" with | some (.str c) => [c] | some j => (SwarmLean.Json.items j).filterMap SwarmLean.Json.str? | none => []
        for c in cs do
          let src := (SOURCES.find? fun (_, m) => hasSub c m && (c.splitOn m).head!.utf8ByteSize + m.utf8ByteSize ≤ 80).map (·.1)
          let k := src.getD "other"
          n := (k, (n.lookup k).getD 0 + c.length) :: n.filter (·.1 != k)
  return Json.mkObj (n.map fun (k, v) => (k, SwarmLean.Json.int v))

/-- Characters of the spawn prompt (brief + roster + task + repo rules): the first user message of the first transcript. -/
def briefSize (files : List String) (dflt : Int) : IO Int := do
  let some f0 := files.head? | return dflt
  for line in ← lines f0 do
    if hasSub line "\"type\":\"user\"" then
      if let some (.str m) := ((SwarmLean.Json.decode line).bind (f · "message")).bind (f · "content") then return m.length
  return dflt

/-- Wakes after ≥ COLD_IDLE of that agent's silence with no compaction in between (the wake re-sent its context
uncached). -/
def coldWakes (ev : List Json) : Nat := Id.run do
  let mut n := 0
  let mut last : Std.HashMap String Int := {}
  let mut comp : Std.HashMap String Int := {}
  for e in ev do
    let a := (fs e "agent").getD ""
    let ts := fi e "ts"
    if fs e "kind" == some "wake" then
      if let some l := last[a]? then
        if ts - l ≥ COLD_IDLE && comp.getD a (-1) < l then n := n + 1
    if fs e "kind" == some "compact" then comp := comp.insert a ts
    last := last.insert a ts
  return n

/-- stdout of a command, "" when it fails. -/
def sh (argv : List String) : IO String := do
  let r ← execIO' argv {}
  return if r.code == 0 then r.stdout else ""

/-- The first `Swarm-Agent:` line anywhere in a message (squash merges put it in its own paragraph, so a trailer
parse misses it). -/
def swarmAgent (body : String) : Option String :=
  (("\n" ++ body).splitOn "\nSwarm-Agent:").tail.findSome? fun p =>
    let w := (p.dropWhile isSpace).takeWhile (!isSpace ·)
    if w.isEmpty then none else some w.toString

/-- Landed commits per agent-hour and files two or more agents changed; also each commit's (time, sha, agent). -/
def gitEvidence (since : Int) (ref := "origin/main") : IO (List (String × Json) × List (Int × String × String)) := do
  let args := ["git", "log", ref] ++ (if since != 0 then [s!"--since={since}"] else []) ++
    ["--name-only", "--format=%x01%H%x00%ct%x00%B%x00"]
  let mut hours : List ((String × String) × Int) := []
  let mut files : Std.HashMap String (List String) := {}
  let mut commits := #[]
  for blk in ((← sh args).splitOn "\x01").drop 1 do
    let p := blk.splitOn "\x00"
    let sha := p.getD 0 ""
    let ct := (parseInt (p.getD 1 "")).getD 0
    let agent := (swarmAgent (p.getD 2 "")).getD "(none)"
    commits := commits.push (ct, sha, agent)
    let k := (← Shim.strftime "%Y-%m-%d %H:00" (Int64.ofInt ct), agent)
    hours := (k, (hours.lookup k).getD 0 + 1) :: hours.filter (·.1 != k)
    for fl in (strip (p.getD 3 "")).splitOn "\n" do
      if fl != "" then files := files.insert fl (if (files.getD fl []).contains agent then files.getD fl [] else agent :: files.getD fl [])
  let order := hours.mergeSort fun a b => a.1.1 < b.1.1 || (a.1.1 == b.1.1 && a.1.2 ≤ b.1.2)
  let cph := order.filter (·.1.2 != "(none)") |>.map fun ((h, a), n) =>
    Json.mkObj [("hour", .str h), ("agent", .str a), ("n", SwarmLean.Json.int n)]
  let none_ := (order.filter (·.1.2 == "(none)")).foldl (· + ·.2) 0
  let multi := files.toList.filterMap fun (fl, as) =>
    if (as.filter (· != "(none)")).length > 1 then some (fl, Json.arr ((as.mergeSort (· ≤ ·)).map Json.str).toArray) else none
  return ([("commits_per_hour", Json.arr cph.toArray), ("not_swarm_commits", SwarmLean.Json.int none_),
    ("multi_agent_files", Json.mkObj multi)], commits.toList)

/-- Failed main runs and the agent whose later green run's commit fixed it (needs gh). -/
def redRuns (commits : List (Int × String × String)) (since : Int) : IO Json := do
  let runs := ((SwarmLean.Json.decode (← sh ["gh", "run", "list", "--branch", "main", "--limit", "100", "--json",
    "conclusion,headSha,createdAt,databaseId"])).map SwarmLean.Json.items).getD []
  let by_ := fun (sha : Option String) => ((sha.bind fun h => commits.find? (·.2.1 == h)).map (·.2.2)).getD "?"
  let from_ ← Shim.strftime "!%Y-%m-%dT%H:%M:%S" (Int64.ofInt since)
  let keep := (runs.filter fun r => (fs r "createdAt").any (· ≥ from_)).mergeSort fun a b =>
    (fs a "createdAt").getD "" ≤ (fs b "createdAt").getD ""
  let mut out := #[]
  for (r, i) in keep.zipIdx do
    if fs r "conclusion" == some "failure" then
      -- a green run created at the same second does not fix it (the Lua's sort left such ties in no set order)
      let fix := (keep.drop (i + 1)).find? fun x => fs x "conclusion" == some "success" && fs x "createdAt" != fs r "createdAt"
      out := out.push (Json.mkObj [("run", (f r "databaseId").getD .null), ("broke", .str (by_ (fs r "headSha"))),
        ("fixed_by", (fix.map fun x => Json.str (by_ (fs x "headSha"))).getD .null)])
  return .arr out

/-- One machine's `swarm run` jobs. -/
structure Jobs where
  jobs : Int := 0
  tenths : Int := 0
  exits : List (String × Int) := []
  lost : Int := 0
  unfinished : Int := 0
  sync_s : JsonNumber := 0
  back_s : JsonNumber := 0

/-- Lua's tostring of an exit value. -/
def exitText : Option Json → String
  | none | some .null => "nil"
  | some (.str x) => x
  | some (.bool b) => toString b
  | some j => j.compress

/-- `swarm run` jobs per machine ('here' = local): count, minutes, exit codes, lost and unfinished, sync and bring-back
seconds. -/
def jobs (ev : List Json) : List (String × Jobs) := Id.run do
  let data := fun (e : Json) => match fs e "data" with
    | some d => if d.startsWith "{" then (SwarmLean.Json.decode d).getD (Json.mkObj []) else Json.mkObj []
    | none => Json.mkObj []
  let ends := ev.filter (fs · "kind" == some "job-end") |>.map fun e => (fs e "path", data e)
  let mut out : List (String × Jobs) := []
  for e in ev do
    if fs e "kind" == some "job-start" then
      let mname := (fs (data e) "machine").getD "here"
      let mut m := (out.lookup mname).getD {}
      m := { m with jobs := m.jobs + 1 }
      -- the last job-end of the path wins, as the Lua's table
      match (ends.reverse.find? (·.1 == fs e "path")).map (·.2) with
      | none => m := { m with unfinished := m.unfinished + 1 }
      | some x =>
        let secs := (fnum x "s").getD 0
        m := { m with tenths := m.tenths + (secs / 60 * 10 + 0.5).floor.toInt64.toInt }
        if fs x "exit" == some "lost" then m := { m with lost := m.lost + 1 }
        else
          let k := exitText (f x "exit")
          m := { m with exits := (k, (m.exits.lookup k).getD 0 + 1) :: m.exits.filter (·.1 != k) }
        m := { m with sync_s := addN m.sync_s (dec x "sync_s"), back_s := addN m.back_s (dec x "back_s") }
      out := (mname, m) :: out.filter (·.1 != mname)
  return out

def Jobs.json (m : Jobs) : Json :=
  Json.mkObj [("jobs", SwarmLean.Json.int m.jobs), ("minutes", .num (norm ⟨m.tenths, 1⟩)),
    ("exits", Json.mkObj (m.exits.map fun (k, v) => (k, SwarmLean.Json.int v))), ("lost", SwarmLean.Json.int m.lost),
    ("unfinished", SwarmLean.Json.int m.unfinished), ("sync_s", .num m.sync_s), ("back_s", .num m.back_s)]

/-- The keys of `row`, a missing one as null. -/
def pick (row : Json) (keys : List String) : Json := Json.mkObj (keys.map fun k => (k, (f row k).getD .null))

/-- Per-task timing from the CLI's own `swarm state --json`, so the report and `swarm state` agree. -/
def stateTasks (path : String) : IO (List Json) := do
  let cli := ((← IO.getEnv "SWARM_RETRO_HERE").getD "") ++ "/../swarm/swarm"
  let r ← execIO' [cli, "state", "--json"] { env := [("SWARM_DB", some path)] }
  if r.code != 0 then die s!"swarm-report: swarm state --json failed: {strip r.stderr}"
  return (((SwarmLean.Json.decode r.stdout).bind (f · "tasks")).map SwarmLean.Json.items).getD []

/-- swarm/brief.md's size. -/
def briefBytes : IO Int := do
  let p := ((← IO.getEnv "SWARM_RETRO_HERE").getD "") ++ "/../swarm/brief.md"
  try return (← System.FilePath.metadata p).byteSize.toNat catch _ => return 0

/-- Counts of `k` in an association list. -/
def bump (l : List (String × Int)) (k : String) (by_ : Int := 1) : List (String × Int) :=
  (k, (l.lookup k).getD 0 + by_) :: l.filter (·.1 != k)

def counts (l : List (String × Int)) : Json := Json.mkObj (l.map fun (k, v) => (k, SwarmLean.Json.int v))

/-- The report. `c`: the read-only db; `state`: the tasks of `swarm state --json`. -/
def report (c : Conn) (since? : Option Int) (state : List Json) : IO Json := do
  let since ← match since? with
    | some x => pure x
    | none => one c "select coalesce(min(started),0) n from agent" []
  let ev ← all c "select * from event where ts>=? order by ts, id" [.int since]
  let agents0 ← all c "select name,model,cwd,started,ended,ctx_tokens,status from agent where coalesce(started,0)>=? or ended is null" [.int since]
  let mut tasks := #[]
  let mut works := []
  let mut qw := []
  let mut m2g := []
  let mut red := #[]
  let mut blocked : Float := 0
  let mut reclaimed := #[]
  for t in state do
    let r := pick t TASK_KEYS
    let r := r.setObjVal! "took" ((fnum t "work_s").map (Json.str ∘ span) |>.getD .null)
    tasks := tasks.push r
    if let some x := fnum t "work_s" then works := works ++ [x]
    if let some x := fnum t "queue_wait_s" then qw := qw ++ [x]
    if let some x := fnum t "merge_to_green_s" then m2g := m2g ++ [x]
    if fs t "ci_conclusion" == some "failure" then red := red.push ((f t "id").getD .null)
    blocked := blocked + (fnum t "blocked_s").getD 0
    if fi t "claims" > 1 then
      reclaimed := reclaimed.push (Json.mkObj [("id", (f t "id").getD .null), ("claims", (f t "claims").getD .null),
        ("holders", (f t "holders").getD (.arr #[]))])
  let longest := (tasks.toList.filterMap fun t => (fnum t "work_s").map (t, ·)).mergeSort fun a b => a.2 ≥ b.2
  let top := (longest.take 5).map fun (t, _) => pick t ["id", "title", "work_s"]
  let fl := fun (o : Option Float) => o.map SwarmLean.Json.float
  let durations := obj [("n_done", some (SwarmLean.Json.int works.length)), ("work_median_s", fl (pct works 0.5)),
    ("work_p90_s", fl (pct works 0.9)), ("longest", some (.arr top.toArray)), ("queue_wait_median_s", fl (pct qw 0.5)),
    ("queue_wait_max_s", fl (qw.max?)), ("merge_to_green_median_s", fl (pct m2g 0.5)), ("red_after_merge", some (.arr red)),
    ("blocked_total_s", some (SwarmLean.Json.float blocked)), ("reclaimed", some (.arr reclaimed))]
  let mut byagent : List (String × List (String × Int)) := []
  for e in ev do
    let a := (fs e "agent").getD "watchd"
    byagent := (a, bump ((byagent.lookup a).getD []) ((fs e "kind").getD "nil")) :: byagent.filter (·.1 != a)
  let b ← briefBytes
  let mut hs : List (String × Int) := []
  let mut totalBrief : Int := 0
  let mut agents := #[]
  for a in agents0 do
    let n := (fs a "name").getD ""
    let tr ← transcripts n (fs a "cwd")
    let hb ← hookBytes tr
    let bs ← briefSize tr b
    let q := fun sql ps => one c sql ps
    let a := (["model", "cwd", "started", "ended", "ctx_tokens"].foldl (fun a k => if (f a k).isNone then a.setObjVal! k .null else a) a)
      |>.setObjVal! "transcripts" (.arr (tr.map Json.str).toArray)
      |>.setObjVal! "hook_bytes" hb
      |>.setObjVal! "brief_bytes" (SwarmLean.Json.int bs)
      |>.setObjVal! "msgs_sent" (SwarmLean.Json.int (← q "select count(*) n from msg where frm=? and ts>=?" [.text n, .int since]))
      |>.setObjVal! "msgs_to_all" (SwarmLean.Json.int (← q "select count(*) n from msg where frm=? and dest='@all' and ts>=?" [.text n, .int since]))
      |>.setObjVal! "msgs_recv" (SwarmLean.Json.int (← q "select count(*) n from msg where (dest=? or dest='@all') and frm!=? and coalesce(kind,'') not in ('system','notice') and ts>=?" [.text n, .text n, .int since]))
      |>.setObjVal! "tasks_done_no_evidence" (SwarmLean.Json.int (← q "select count(*) n from task where owner=? and state='done' and coalesce(evidence,'')=''" [.text n]))
    for (k, v) in pairs hb do hs := bump hs k (SwarmLean.Json.int? v |>.getD 0)
    totalBrief := totalBrief + bs
    agents := agents.push a
  let alwaysLoaded := Json.mkObj [("brief_md_bytes", SwarmLean.Json.int b), ("agents", SwarmLean.Json.int agents.size), ("brief_total", SwarmLean.Json.int totalBrief),
    ("cold_wakes", SwarmLean.Json.int (coldWakes ev)), ("hook_total", SwarmLean.Json.int (hs.foldl (· + ·.2) 0)), ("hook_by_source", counts hs)]
  let isK := fun (l : List String) (e : Json) => (fs e "kind").any l.contains
  let friction := ev.filter (isK FRICTION) |>.map (pick · EVK)
  let conflicts := ev.filter (isK CONFLICTS) |>.map (pick · EVK)
  let idle := ev.filter (fs · "kind" == some "digest") |>.map fun e => Json.mkObj [("ts", (f e "ts").getD .null), ("agent", (f e "agent").getD .null)]
  let mut start : Option Int := none
  let mut eps : Int := 0
  let mut tot : Int := 0
  let mut kills : Int := 0
  for e in ev do
    match fs e "kind" with
    | some "pressure" => start := some (fi e "ts")
    | some "pressure-end" => if let some s0 := start then eps := eps + 1; tot := tot + fi e "ts" - s0; start := none
    | some "orphan-kill" => kills := kills + 1
    | _ => pure ()
  -- finished commands that cost something, from the cmd-cost history (a measurement, not a word list)
  let hist ← match ← (Cost.path : App String).run.run { conn := ← IO.mkRef none } with
    | .ok p => pure p
    | .error _ => pure ""
  let rows ← try
      let h ← Conn.open hist true
      all h "select agent,peak_kb from cmd where ts>=?" [.int since]
    catch _ => pure []
  let costly := rows.foldl (fun l r => bump l ((fs r "agent").getD "?")) []
  let peak := rows.foldl (fun m r => max m (fi r "peak_kb")) 0
  let pressure := Json.mkObj [("episodes", SwarmLean.Json.int (eps + if start.isSome then 1 else 0)), ("total_s", SwarmLean.Json.int tot),
    ("ongoing", .bool start.isSome), ("max_command_peak_kb", SwarmLean.Json.int peak), ("orphan_kills", SwarmLean.Json.int kills),
    ("costly_commands", counts costly)]
  let (git, commits) ← gitEvidence since
  let msgs ← all c "select frm, count(*) n, sum(urgent) urgent from msg where ts>=? group by frm" [.int since]
  let locks ← all c "select path,agent,reason from lock"
  return Json.mkObj ([("since", SwarmLean.Json.int since), ("agents", .arr agents), ("task_durations", durations), ("tasks", .arr tasks),
    ("events", Json.mkObj (byagent.map fun (a, l) => (a, counts l))), ("always_loaded", alwaysLoaded),
    ("friction", .arr friction.toArray), ("conflicts", .arr conflicts.toArray), ("idle_with_open_tasks", .arr idle.toArray),
    ("pressure", pressure), ("jobs", Json.mkObj ((jobs ev).map fun (k, m) => (k, m.json))),
    ("red_main_runs", ← redRuns commits since), ("messages", .arr msgs.toArray), ("locks", .arr locks.toArray)] ++ git)

/-- Pretty JSON, Python's indent=1 with sorted keys. -/
partial def enc (v : Json) (ind : Nat) : String :=
  let pad := "\n" ++ "".pushn ' ' ind
  let inner := "\n" ++ "".pushn ' ' (ind + 1)
  match v with
  | .arr xs => if xs.isEmpty then "[]" else "[" ++ inner ++ ("," ++ inner).intercalate (xs.toList.map (enc · (ind + 1))) ++ pad ++ "]"
  | .obj _ =>
    let o := (pairs v).map fun (k, x) => Hook.jstr k ++ ": " ++ enc x (ind + 1)
    if o.isEmpty then "{}" else "{" ++ inner ++ ("," ++ inner).intercalate o ++ pad ++ "}"
  | .str x => Hook.jstr x
  | j => j.compress

/-- Lua's `%s` class stripped from the right. -/
def rstrip (x : String) : String := String.ofList (x.toList.reverse.dropWhile isSpace).reverse

/-- The report as text. -/
def showText (r : Json) : IO Unit := do
  let t := fun (o : Option Json) => do
    match o.bind SwarmLean.Json.int? with
    | some x => if x != 0 then Shim.strftime "%H:%M" (Int64.ofInt x) else pure "-"
    | none => pure "-"
  let fd := fun (o : Option Json) => ((o.bind SwarmLean.Json.num?).map span).getD "-"
  let arr := fun (k : String) => SwarmLean.Json.items ((f r k).getD .null)
  let get := fun (k : String) => (f r k).getD (Json.mkObj [])
  IO.println "## agents"
  for a in arr "agents" do
    IO.println s!"- {s (f a "name")} {(fs a "model").getD "?"} {← t (f a "started")}-{← t (f a "ended")} {s (f a "status")} ctx={Int.fdiv (fi a "ctx_tokens") 1000}k msgs sent/recv={fi a "msgs_sent"}/{fi a "msgs_recv"} (@all {fi a "msgs_to_all"}) done-without-evidence={fi a "tasks_done_no_evidence"}"
    for p in SwarmLean.Json.items ((f a "transcripts").getD .null) do IO.println s!"    transcript: {s p}"
  let al := get "always_loaded"
  let per := (arr "agents").map fun x => s!"{s (f x "name")}={(pairs ((f x "hook_bytes").getD .null)).foldl (fun n kv => n + (SwarmLean.Json.int? kv.2).getD 0) 0}"
  IO.println s!"\n## always-loaded context\n- spawn prompts (swarm/brief.md {fi al "brief_md_bytes"} B + roster, task, rules) x {fi al "agents"} agents = {fi al "brief_total"} B; cold-cache wakes re-sending context uncached: {fi al "cold_wakes"}\n- hook-injected text: {fi al "hook_total"} B ({kv ((f al "hook_by_source").getD .null)}); per agent: {if per.isEmpty then "-" else ", ".intercalate per}"
  IO.println "\n## tasks"
  for k in arr "tasks" do
    let ev := match fs k "evidence" with | some e => if e != "" then s!"\n    evidence: {e}" else "" | none => ""
    IO.println (s!"- #{s (f k "id")} {s (f k "state")} {(fs k "owner").getD "-"} {(fs k "took").getD "-"}: {s (f k "title")}" ++ ev)
  let d := get "task_durations"
  let ids := (SwarmLean.Json.items ((f d "red_after_merge").getD .null)).map fun i => "#" ++ s (some i)
  IO.println s!"\n## task durations\n- {fi d "n_done"} done: work median {fd (f d "work_median_s")}, p90 {fd (f d "work_p90_s")}; queue wait median {fd (f d "queue_wait_median_s")}, max {fd (f d "queue_wait_max_s")}; blocked total {fd (f d "blocked_total_s")}; merge to green CI median {fd (f d "merge_to_green_median_s")}, red after merge: {if ids.isEmpty then "none" else ", ".intercalate ids}"
  for k in SwarmLean.Json.items ((f d "longest").getD .null) do IO.println s!"- longest: #{s (f k "id")} {fd (f k "work_s")} {s (f k "title")}"
  for k in SwarmLean.Json.items ((f d "reclaimed").getD .null) do
    IO.println s!"- reclaimed: #{s (f k "id")} claimed {fi k "claims"}x by {", ".intercalate ((SwarmLean.Json.items ((f k "holders").getD .null)).map (s ∘ some))}"
  IO.println "\n## events per agent"
  let names := (pairs (get "events")).mergeSort fun a b => a.1 == "watchd" || (b.1 != "watchd" && a.1 ≤ b.1)
  for (a, x) in names do IO.println s!"- {a}: {kv x}"
  IO.println "\n## friction"
  for e in arr "friction" do
    IO.println (rstrip s!"- {← t (f e "ts")} {s (f e "agent")} {(fs e "kind").getD ""} {(fs e "path").getD ""} {(fs e "data").getD ""}")
  let sect := fun (title key : String) (keys : List String) => do
    IO.println s!"\n## {title}"
    for x in arr key do IO.println ("- " ++ " ".intercalate (keys.map fun k => s!"{k}={s (f x k)}"))
  sect "landed commits per hour" "commits_per_hour" ["hour", "agent", "n"]
  IO.println s!"- not swarm: {fi r "not_swarm_commits"}"
  sect "red main runs" "red_main_runs" ["run", "broke", "fixed_by"]
  sect "conflict, conflict-compat and shared-tree events" "conflicts" EVK
  sect "watchd digests (idle with open tasks)" "idle_with_open_tasks" ["ts", "agent"]
  let p := get "pressure"
  let costly := (f p "costly_commands").getD (Json.mkObj [])
  IO.println s!"\n## resources\n- pressure episodes: {fi p "episodes"} ({span (fi p "total_s").toFloat} total{if f p "ongoing" == some (.bool true) then ", ongoing" else ""})\n- largest command peak: {fixed ((fi p "max_command_peak_kb").toFloat / 1048576) 1}G\n- orphan kills: {fi p "orphan_kills"}\n- costly commands per agent: {if (pairs costly).isEmpty then "-" else kv costly}"
  IO.println "\n## swarm run jobs"
  for (k, m) in pairs (get "jobs") do
    let ex := (f m "exits").getD (Json.mkObj [])
    IO.println s!"- {k}: {fi m "jobs"} jobs, {round0 (dec m "minutes")} min, exits {if (pairs ex).isEmpty then "-" else kv ex ","}, lost {fi m "lost"}, unfinished {fi m "unfinished"}, sync {round0 (dec m "sync_s")}s, back {round0 (dec m "back_s")}s"
  IO.println "\n## files changed by 2+ agents"
  for (fl, as) in pairs (get "multi_agent_files") do IO.println s!"- {fl}: {", ".intercalate ((SwarmLean.Json.items as).map (s ∘ some))}"
  IO.println "\n## messages sent"
  for m in arr "messages" do IO.println s!"- {s (f m "frm")}: {fi m "n"} ({fi m "urgent"} urgent)"
  let locks := arr "locks"
  if !locks.isEmpty then
    IO.println "\n## locks still held"
    for k in locks do IO.println s!"- {(fs k "path").getD "nil"} {(fs k "agent").getD "nil"} {(fs k "reason").getD ""}"

/-- `--since`: `2026-11-07T08:00` (time parts optional) as local epoch seconds (os.time). -/
def parseSince (x : String) : IO Int := do
  let bad : IO Int := die s!"swarm-report: bad --since '{x}' (use 2026-11-07T08:00)"
  let .ok (some m) := Re.fullmatch "(\\d+)-(\\d+)-(\\d+)[T ]?(\\d*):?(\\d*):?(\\d*)" x | bad
  let g := fun k => Int64.ofNat (((m.group k).bind String.toNat?).getD 0)
  try return (← Shim.mktime (g 1) (g 2) (g 3) (g 4) (g 5) (g 6)).toInt64.toInt catch _ => bad

def USAGE : String := "Usage: swarm-report [-h] [--db <db>] [--since <since>] [--json]"

def HELP : String := USAGE ++ "

Evidence for a swarm retro, read from the swarm db: who did what, where time and attention went.
Default db: <git-common-dir>/swarm/swarm.db (or $SWARM_DB). Sections: agents, tasks (claim -> done time, evidence), event counts per agent (conflicts, shared trees, reaps, compactions, pushes, ci-red are the friction signals), messages, locks. Read-only.

Options:
   -h, --help            Show this help message and exit.
   --db <db>
   --since <since>       ISO start, e.g. 2026-11-07T08:00
   --json"

/-- argparse's error: usage, the message, exit 1. -/
def usageErr (msg : String) : IO α := do
  IO.eprintln s!"{USAGE}\n\nError: {msg}"
  IO.Process.exit 1

/-- The options: --db, --since, --json (argparse's grammar for these three). -/
partial def parse (args : List String) (o : List (String × String)) : IO (List (String × String)) := do
  -- a repeated option: the last wins
  let set := fun (k v : String) (rest : List String) => parse rest ((k, v) :: o)
  match args with
  | [] => return o
  | a :: rest =>
    if a == "-h" || a == "--help" then IO.println HELP; IO.Process.exit 0
    let (k, inl) := match a.splitOn "=" with
      | k :: v :: vs => if k.startsWith "--" then (k, some ("=".intercalate (v :: vs))) else (a, none)
      | _ => (a, none)
    if k == "--json" then
      if inl.isSome then usageErr "option '--json' does not take arguments" else set "--json" "" rest
    else if k == "--db" || k == "--since" then
      match inl, rest with
      | some v, _ => set k v rest
      | none, v :: rest' => if v.startsWith "-" && v.length > 1 then usageErr s!"option '{k}' requires an argument" else set k v rest'
      | none, [] => usageErr s!"option '{k}' requires an argument"
    else if a.startsWith "-" && a.length > 1 then usageErr s!"unknown option '{k}'"
    else usageErr "too many arguments"

end SwarmLean.Report

open SwarmLean SwarmLean.Report in
def main (args : List String) : IO UInt32 := do
  let o ← parse args []
  let path ← match o.lookup "--db" with
    | some p => pure p
    | none => try dbPath catch e => die (toString e)
  unless ← System.FilePath.pathExists path do die s!"swarm-report: no db at {path}"
  let c ← try Sqlite.Conn.open path true catch e => die s!"swarm-report: can't open {path}: {e}"
  let since ← (o.lookup "--since").mapM parseSince
  let r ← report c since (← stateTasks path)
  if (o.lookup "--json").isSome then IO.println (enc r 0) else showText r
  return 0
