import Tests.Cli.Fixture

/-! swarm-retro's test_swarm_report.lua: swarm-report (Report.lean) driven through its CLI, on a db built by `swarm`
itself and filled with fixture rows. -/

namespace SwarmLean.Tests.Spec.Report
open SwarmLean SwarmLean.Tests.Cli
open Lean (Json toJson)

/-- No history, no gh. -/
def NOGIT : List (String × Option String) := [("GIT_DIR", some "/nonexistent")]

/-- Element `i` of an array. -/
def nth (j : Json) (i : Nat) : Json := match j with | .arr a => a[i]?.getD .null | _ => .null

/-- Each element's `kind`. -/
def kinds (j : Json) : List String := match j with | .arr a => a.toList.map fun e => (e.f "kind").s?.getD "" | _ => []

/-- swarm-report with `args` on t's db (the swarm next to swarm-retro answers its `swarm state`). -/
def report (t : T) (args : List String) (home : Option String := none) (env : List (String × Option String) := [])
    (cwd : Option String := none) : IO R := do
  let bin := ((← IO.appPath).parent.getD "." / "swarm-report").toString
  let r ← t.exec (bin :: args) { cwd := some (cwd.getD t.d), env := [("SWARM_DB", some t.db), ("SWARM_NAME", some "t"),
    ("HOME", some (home.getD t.d)), ("SWARM_RETRO_HERE", some s!"{← swarmDir}/../swarm-retro")] ++ env }
  if r.code ≠ 0 then fail s!"swarm-report exited {r.code}: {r.stderr}"
  return r

/-- The report as JSON on a fresh db after running the sql. -/
def run (t : T) (sql : String := "") (home : Option String := none) (env : List (String × Option String) := [])
    (cwd : Option String := none) : IO Json := do
  t.sw_ "t" ["task", "add", "seed"]  -- makes the schema
  (← Sqlite.Conn.open t.db false).script ("delete from task; delete from event;" ++ sql)
  match Json.parse (← report t ["--json"] home env cwd).stdout with
  | .ok j => return j
  | .error e => fail s!"not JSON: {e}"

def test_claim_to_done (t : T) : IO Unit := do
  let r ← run t "insert into task(id,title,state,owner,evidence) values(1,'t','done','a','sha');
insert into event(ts,agent,kind,data) values(100,'a','claim','#1 t'),(190,'a','done','#1 sha'),(150,'a','reap','x'),(160,'a','digest',null);" (env := NOGIT)
  eq ((nth (r.f "tasks") 0).f "took") "1m30s"
  eq ((nth (r.f "friction") 0).f "kind") "reap"
  eq (r.f "idle_with_open_tasks").len 1

def test_task_durations_from_events (t : T) : IO Unit := do
  let r ← run t "insert into task(id,title,state,owner,evidence) values(1,'t','done','b','sha');
insert into event(ts,agent,kind,data) values(10,'a','task-add','#1 t'),(100,'a','claim','#1 t'),(130,'a','block','#1 q'),(160,'a','unblock','#1'),
 (200,'a','release','#1'),(300,'b','claim','#1 t'),(400,'b','done','#1 sha');" (env := NOGIT)
  let k := nth (r.f "tasks") 0
  eq (["queue_wait_s", "work_s", "total_s", "blocked_s", "claims", "releases", "holders"].map k.f)
    [toJson 90, toJson 300, toJson 390, toJson 30, toJson 2, toJson 1, toJson ["a", "b"]]
  eq ((r.f "task_durations").f "work_median_s") 300
  eq ((nth ((r.f "task_durations").f "reclaimed") 0).f "id") 1

def test_conflict_events (t : T) : IO Unit := do
  let r ← run t "insert into event(ts,agent,kind,path,data) values(1,'a','conflict','L.hs','b'),(2,'a','conflict-compat',null,'b'),(3,'b','shared-tree','/r','a');" (env := NOGIT)
  eq (kinds (r.f "conflicts")) ["conflict", "conflict-compat", "shared-tree"]
  eq (kinds (r.f "friction")) ["conflict", "shared-tree"]  -- compat is not friction

def test_jobs_per_machine (t : T) : IO Unit := do
  let j := (← run t "insert into event(ts,agent,kind,path,data) values(1,'a','job-start','1','{\"machine\":\"laptop\"}'),(2,'a','job-end','1','{\"exit\":1,\"s\":120,\"sync_s\":0.5,\"back_s\":0.25}'),
 (3,'a','job-start','2','{\"machine\":\"laptop\"}'),(4,'a','job-end','2','{\"exit\":\"lost\",\"s\":60}'),(5,'b','job-start','3','{\"machine\":null}');" (env := NOGIT)).f "jobs"
  let l := j.f "laptop"
  eq ([l.f "jobs", l.f "minutes", (l.f "exits").f "1", l.f "lost", l.f "unfinished", l.f "sync_s", l.f "back_s"].map (·.compress))
    ["2", "3", "1", "1", "0", "0.5", "0.25"]
  eq ((j.f "here").f "unfinished") 1

/-- The first agent's report with these transcripts (name → body) under its project dir. -/
def agentTranscripts (t : T) (files : List (String × String)) : IO Json := do
  let h := t.d ++ "/home"
  IO.FS.createDirAll (h ++ "/.claude/projects/-w")
  for (f, body) in files do put s!"{h}/.claude/projects/-w/{f}.jsonl" body
  return nth ((← run t "insert into agent(name,cwd,started,status) values('jl-1','/w',1,'idle');" (home := h) (env := NOGIT)).f "agents") 0

def test_transcript_name_is_exact (t : T) : IO Unit := do
  let recd := fun (n : String) => s!"\{\"type\":\"agent-name\",\"agentName\":\"{n}\"}\n"
  let a ← agentTranscripts t [("a", recd "jl-1"), ("b", recd "jl-11"), ("c", recd "jl-1-2"), ("d", recd "jl-10")]
  let names := match a.f "transcripts" with | .arr xs => xs.toList.map fun (x : Json) => basename (x.s?.getD "") | _ => []
  eq (names.mergeSort (· ≤ ·)) ["a.jsonl", "c.jsonl"]

def test_hook_bytes_by_source_and_brief_size (t : T) : IO Unit := do
  let h := fun (c : String) => (Json.mkObj [("attachment", Json.mkObj [("type", "hook_additional_context"),
    ("content", toJson [c])])]).compress ++ "\n"
  let body := "{\"type\":\"agent-name\",\"agentName\":\"jl-1\"}\n{\"type\":\"user\",\"message\":{\"content\":\"abcde\"}}\n" ++
    h "swarm messages (x" ++ h "machine: 1G" ++ h "zzz" ++ "{\"attachment\":{\"type\":\"date\"}}\n"
  let a ← agentTranscripts t [("a", body)]
  eq (a.f "hook_bytes") (Json.mkObj [("inbox", 17), ("machine", 11), ("other", 3)])
  eq (a.f "brief_bytes") 5

def test_cold_wakes (t : T) : IO Unit := do
  let cw := fun (evs : List (Nat × String)) => do
    let vals := evs.map fun (ts, k) => s!"({ts},'a','{k}')"
    return ((← run t s!"insert into event(ts,agent,kind) values{",".intercalate vals};" (env := NOGIT)).f "always_loaded").f "cold_wakes"
  eq (← cw [(0, "push"), (4000, "wake"), (4100, "wake")]) 1  -- second wake is warm
  eq (← cw [(0, "push"), (1000, "compact"), (1100, "push"), (5000, "wake")]) 1
  eq (← cw [(0, "push"), (3000, "compact"), (3100, "wake")]) 0

def test_resources (t : T) : IO Unit := do
  let st := t.d ++ "/st"
  IO.FS.createDirAll (st ++ "/cmd-cost")
  (← Sqlite.Conn.open (st ++ "/cmd-cost/history.db") false).script "create table cmd(id integer primary key, ts int, machine text,
    repo text, agent text, source text, cmd text, key text, wall_s int, cpu_s int, peak_kb int, exact int);
    insert into cmd(ts,agent,peak_kb) values(30,'a',2097152),(40,'a',1048576),(50,'b',3145728)"
  let p := (← run t "insert into event(ts,agent,kind,data) values(20,null,'pressure',null),(80,null,'pressure-end',null),
 (90,null,'pressure',null),(50,'b','orphan-kill','1 ghc');" (env := NOGIT ++ [("XDG_STATE_HOME", some st)])).f "pressure"
  eq (["episodes", "total_s", "ongoing", "max_command_peak_kb", "orphan_kills"].map p.f)
    [toJson 2, toJson 60, toJson true, toJson 3145728, toJson 1]
  eq (p.f "costly_commands") (Json.mkObj [("a", 2), ("b", 1)])

def test_agent_line_anywhere_in_body (t : T) : IO Unit := do
  let d := t.d ++ "/g"
  IO.FS.createDirAll d
  discard <| t.git d ["init", "-q", "-b", "main"]
  put (d ++ "/f") "1\n"
  discard <| t.git d ["add", "f"]
  discard <| t.git d ["commit", "-qm", "t\n\n@@ -1 +1 @@\n\nSwarm-Agent: sp-a\n\nCo-authored-by: y"]
  discard <| t.git d ["commit", "-q", "--allow-empty", "-m", "plain"]
  discard <| t.git d ["update-ref", "refs/remotes/origin/main", "HEAD"]
  let r ← run t (cwd := some d)
  eq (r.f "commits_per_hour").len 1
  eq ((nth (r.f "commits_per_hour") 0).f "agent") "sp-a"
  eq (r.f "not_swarm_commits") 1

def test_text_report (t : T) : IO Unit := do
  t.sw_ "t" ["task", "add", "x"]
  has (← report t [] (env := NOGIT)).stdout "## tasks"

def tests : List Case := [
  ("agent_line_anywhere_in_body", test_agent_line_anywhere_in_body),
  ("claim_to_done", test_claim_to_done),
  ("cold_wakes", test_cold_wakes),
  ("conflict_events", test_conflict_events),
  ("hook_bytes_by_source_and_brief_size", test_hook_bytes_by_source_and_brief_size),
  ("jobs_per_machine", test_jobs_per_machine),
  ("resources", test_resources),
  ("task_durations_from_events", test_task_durations_from_events),
  ("text_report", test_text_report),
  ("transcript_name_is_exact", test_transcript_name_is_exact)]

end SwarmLean.Tests.Spec.Report
