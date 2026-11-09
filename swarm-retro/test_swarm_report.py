import importlib.util, os, sqlite3, unittest
spec = importlib.util.spec_from_file_location("sr", os.path.join(os.path.dirname(__file__), "swarm-report.py"))
sr = importlib.util.module_from_spec(spec); spec.loader.exec_module(sr)

class T(unittest.TestCase):
  def test_claim_to_done(self):
    c = sqlite3.connect(":memory:"); c.row_factory = sqlite3.Row
    c.executescript("""create table agent(name,model,cwd,started,ended,ctx_tokens,status);
create table task(id,title,state,owner,evidence);
create table event(id integer primary key,ts,agent,kind,path,data);
create table msg(ts,frm,dest,urgent);create table lock(path,agent,reason);
insert into task values(1,'t','done','a','sha');
insert into event(ts,agent,kind,data) values(100,'a','claim','#1 t'),(190,'a','done','#1 sha'),(150,'a','reap','x'),(160,'a','digest',null);""")
    r = sr.report(c, git=False, state=[{"id": 1, "work_s": 90, "claims": 1, "blocked_s": 0}])
    self.assertEqual(r["tasks"][0]["took"], "1m30s"); self.assertEqual(r["friction"][0]["kind"], "reap"); self.assertEqual(len(r["idle_with_open_tasks"]), 1)

  def test_task_durations_from_events(self):
    c = sqlite3.connect(":memory:"); c.row_factory = sqlite3.Row
    c.executescript("""create table agent(name,model,cwd,started,ended,ctx_tokens,status);
create table task(id,title,state,owner,evidence);
create table event(id integer primary key,ts,agent,kind,path,data);
create table msg(ts,frm,dest,urgent);create table lock(path,agent,reason);
insert into task values(1,'t','done','b','sha');
insert into event(ts,agent,kind,data) values(10,'a','task-add','#1 t'),(100,'a','claim','#1 t'),(130,'a','block','#1 q'),(160,'a','unblock','#1'),
 (200,'a','release','#1'),(300,'b','claim','#1 t'),(400,'b','done','#1 sha');""")
    r = sr.report(c, since=0, git=False, state=[{"id": 1, "queue_wait_s": 90, "work_s": 300, "total_s": 390, "blocked_s": 30, "claims": 2, "releases": 1, "holders": ["a", "b"]}])
    t = r["tasks"][0]
    self.assertEqual((t["queue_wait_s"], t["work_s"], t["total_s"], t["blocked_s"], t["claims"], t["releases"], t["holders"]), (90, 300, 390, 30, 2, 1, ["a", "b"]))
    self.assertEqual(r["task_durations"]["work_median_s"], 300); self.assertEqual(r["task_durations"]["reclaimed"][0]["id"], 1)

  def test_conflict_events(self):
    c = sqlite3.connect(":memory:"); c.row_factory = sqlite3.Row
    c.executescript("""create table agent(name,model,cwd,started,ended,ctx_tokens,status);
create table task(id,title,state,owner,evidence);
create table event(id integer primary key,ts,agent,kind,path,data);
create table msg(ts,frm,dest,urgent);create table lock(path,agent,reason);
insert into event(ts,agent,kind,path,data) values(1,'a','conflict','L.hs','b'),(2,'a','conflict-compat',null,'b'),(3,'b','shared-tree','/r','a');""")
    r = sr.report(c, git=False)
    self.assertEqual([e["kind"] for e in r["conflicts"]], ["conflict", "conflict-compat", "shared-tree"])
    self.assertEqual([e["kind"] for e in r["friction"]], ["conflict", "shared-tree"])  # compat is not friction

  def test_jobs_per_machine(self):
    c = sqlite3.connect(":memory:"); c.row_factory = sqlite3.Row
    c.executescript("""create table agent(name,model,cwd,started,ended,ctx_tokens,status);
create table task(id,title,state,owner,evidence);
create table event(id integer primary key,ts,agent,kind,path,data);
create table msg(ts,frm,dest,urgent);create table lock(path,agent,reason);
insert into event(ts,agent,kind,path,data) values(1,'a','job-start','1','{"machine":"laptop"}'),(2,'a','job-end','1','{"exit":1,"s":120,"sync_s":0.5,"back_s":0.25}'),
 (3,'a','job-start','2','{"machine":"laptop"}'),(4,'a','job-end','2','{"exit":"lost","s":60}'),(5,'b','job-start','3','{"machine":null}');""")
    j = sr.report(c, since=0, git=False)["jobs"]
    self.assertEqual(j["laptop"], {"jobs": 2, "minutes": 3.0, "exits": {"1": 1}, "lost": 1, "unfinished": 0, "sync_s": 0.5, "back_s": 0.25})
    self.assertEqual(j["here"]["unfinished"], 1)

  def test_transcript_name_is_exact(self):
    import tempfile
    h = tempfile.mkdtemp(); os.environ["HOME"] = h
    d = os.path.join(h, ".claude/projects/-w"); os.makedirs(d)
    for f, n in (("a", "jl-1"), ("b", "jl-11"), ("c", "jl-1-2"), ("d", "jl-10")):
        open(os.path.join(d, f + ".jsonl"), "w").write('{"type":"agent-name","agentName":"%s"}\n' % n)
    got = [os.path.basename(x) for x in sr.transcripts("jl-1", "/w")]
    self.assertEqual(sorted(got), ["a.jsonl", "c.jsonl"])

  def test_hook_bytes_by_source(self):
    import tempfile, json
    f = tempfile.mktemp(suffix=".jsonl")
    h = lambda c: json.dumps({"attachment": {"type": "hook_additional_context", "content": c}}) + "\n"
    open(f, "w").write(h(["swarm messages (x"]) + h(["machine: 1G"]) + h(["zzz"]) + json.dumps({"attachment": {"type": "date"}}) + "\n")
    self.assertEqual(sr.hook_bytes([f]), {"inbox": 17, "machine": 11, "other": 3})

  def test_brief_size(self):
    import tempfile, json
    f = tempfile.mktemp(suffix=".jsonl")
    open(f, "w").write(json.dumps({"type": "user", "message": {"content": "abcde"}}, separators=(",", ":")) + "\n")
    self.assertEqual((sr.brief_size([f], 9), sr.brief_size([], 9)), (5, 9))

  def test_cold_wakes(self):
    ev = lambda *r: [dict(ts=t, agent="a", kind=k) for t, k in r]
    self.assertEqual(sr.cold_wakes(ev((0, "push"), (4000, "wake"), (4100, "wake"))), 1)  # second wake is warm
    self.assertEqual(sr.cold_wakes(ev((0, "push"), (1000, "compact"), (1100, "push"), (5000, "wake"))), 1)
    self.assertEqual(sr.cold_wakes(ev((0, "push"), (3000, "compact"), (3100, "wake"))), 0)

  def test_resources(self):
    c = sqlite3.connect(":memory:"); c.row_factory = sqlite3.Row
    c.executescript("""create table agent(name,model,cwd,started,ended,ctx_tokens,status);
create table task(id,title,state,owner,evidence);
create table event(id integer primary key,ts,agent,kind,path,data);
create table msg(ts,frm,dest,urgent);create table lock(path,agent,reason);
insert into event(ts,agent,kind,data) values(10,null,'heavy-count','2'),(20,null,'pressure',null),(80,null,'pressure-end',null),
 (90,null,'pressure',null),(95,null,'heavy-count','1'),(30,'a','heavy-start','cabal build'),(40,'a','heavy-start','x'),(50,'b','orphan-kill','1 ghc');""")
    p = sr.report(c, git=False)["pressure"]
    self.assertEqual((p["episodes"], p["total_s"], p["ongoing"], p["max_concurrent_heavy"], p["orphan_kills"]), (2, 60, True, 2, 1))
    self.assertEqual(p["heavy_starts"], {"a": 2})

  def test_agent_line_anywhere_in_body(self):
    import subprocess, tempfile
    d = tempfile.mkdtemp(); g = lambda *a: subprocess.run(("git", "-C", d, "-c", "user.name=x", "-c", "user.email=x@x") + a, check=True, capture_output=True)
    g("init", "-q"); open(d + "/f", "w").write("1")
    g("add", "f"); g("commit", "-qm", "t\n\n@@ -1 +1 @@\n\nSwarm-Agent: sp-a\n\nCo-authored-by: y")
    g("commit", "-q", "--allow-empty", "-m", "plain")
    cwd = os.getcwd(); os.chdir(d)
    try: ev = sr.git_evidence(ref="HEAD")
    finally: os.chdir(cwd)
    self.assertEqual([c[2] for c in ev["_commits"]], ["(none)", "sp-a"]); self.assertEqual(ev["not_swarm_commits"], 1)

if __name__ == '__main__':
    unittest.main()
