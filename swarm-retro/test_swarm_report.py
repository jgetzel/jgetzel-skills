"""swarm-report (Lua) driven through its CLI, on a db built by `swarm` itself and filled with fixture rows."""
import json, os, sqlite3, subprocess, tempfile, unittest
HERE = os.path.dirname(os.path.realpath(__file__))
REPORT, SWARM = os.path.join(HERE, "swarm-report"), os.path.join(HERE, "..", "swarm", "swarm")

def run(sql="", home=None, cwd=None, args=(), env_extra=None):
    """Report (as json) on a fresh db after running the sql."""
    d = tempfile.mkdtemp()
    env = {**os.environ, "SWARM_DB": d + "/swarm.db", "HOME": home or d, **(env_extra or {})}
    subprocess.run([SWARM, "task", "add", "seed"], env=env, check=True, capture_output=True)  # makes the schema
    c = sqlite3.connect(d + "/swarm.db")
    c.execute("delete from task"); c.execute("delete from event")
    c.executescript(sql); c.commit(); c.close()
    r = subprocess.run([REPORT, "--json", *args],
                       env=env, cwd=cwd or d, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    return json.loads(r.stdout)

NOGIT = {"GIT_DIR": "/nonexistent"}  # no history, no gh

class T(unittest.TestCase):
  def test_claim_to_done(self):
    r = run("""insert into task(id,title,state,owner,evidence) values(1,'t','done','a','sha');
insert into event(ts,agent,kind,data) values(100,'a','claim','#1 t'),(190,'a','done','#1 sha'),(150,'a','reap','x'),(160,'a','digest',null);""",
            env_extra=NOGIT)
    self.assertEqual(r["tasks"][0]["took"], "1m30s"); self.assertEqual(r["friction"][0]["kind"], "reap")
    self.assertEqual(len(r["idle_with_open_tasks"]), 1)

  def test_task_durations_from_events(self):
    r = run("""insert into task(id,title,state,owner,evidence) values(1,'t','done','b','sha');
insert into event(ts,agent,kind,data) values(10,'a','task-add','#1 t'),(100,'a','claim','#1 t'),(130,'a','block','#1 q'),(160,'a','unblock','#1'),
 (200,'a','release','#1'),(300,'b','claim','#1 t'),(400,'b','done','#1 sha');""", env_extra=NOGIT)
    t = r["tasks"][0]
    self.assertEqual((t["queue_wait_s"], t["work_s"], t["total_s"], t["blocked_s"], t["claims"], t["releases"], t["holders"]), (90, 300, 390, 30, 2, 1, ["a", "b"]))
    self.assertEqual(r["task_durations"]["work_median_s"], 300); self.assertEqual(r["task_durations"]["reclaimed"][0]["id"], 1)

  def test_conflict_events(self):
    r = run("""insert into event(ts,agent,kind,path,data) values(1,'a','conflict','L.hs','b'),(2,'a','conflict-compat',null,'b'),(3,'b','shared-tree','/r','a');""",
            env_extra=NOGIT)
    self.assertEqual([e["kind"] for e in r["conflicts"]], ["conflict", "conflict-compat", "shared-tree"])
    self.assertEqual([e["kind"] for e in r["friction"]], ["conflict", "shared-tree"])  # compat is not friction

  def test_jobs_per_machine(self):
    j = run("""insert into event(ts,agent,kind,path,data) values(1,'a','job-start','1','{"machine":"laptop"}'),(2,'a','job-end','1','{"exit":1,"s":120,"sync_s":0.5,"back_s":0.25}'),
 (3,'a','job-start','2','{"machine":"laptop"}'),(4,'a','job-end','2','{"exit":"lost","s":60}'),(5,'b','job-start','3','{"machine":null}');""", env_extra=NOGIT)["jobs"]
    self.assertEqual(j["laptop"], {"jobs": 2, "minutes": 3.0, "exits": {"1": 1}, "lost": 1, "unfinished": 0, "sync_s": 0.5, "back_s": 0.25})
    self.assertEqual(j["here"]["unfinished"], 1)

  def agent_transcripts(self, files, name="jl-1"):
    h = tempfile.mkdtemp(); d = os.path.join(h, ".claude/projects/-w"); os.makedirs(d)
    for f, body in files.items():
        open(os.path.join(d, f + ".jsonl"), "w").write(body)
    return run(f"insert into agent(name,cwd,started,status) values('{name}','/w',1,'idle');", home=h, env_extra=NOGIT)["agents"][0]

  def test_transcript_name_is_exact(self):
    rec = lambda n: '{"type":"agent-name","agentName":"%s"}\n' % n
    a = self.agent_transcripts({"a": rec("jl-1"), "b": rec("jl-11"), "c": rec("jl-1-2"), "d": rec("jl-10")})
    self.assertEqual(sorted(os.path.basename(x) for x in a["transcripts"]), ["a.jsonl", "c.jsonl"])

  def test_hook_bytes_by_source_and_brief_size(self):
    h = lambda c: json.dumps({"attachment": {"type": "hook_additional_context", "content": c}}) + "\n"
    body = ('{"type":"agent-name","agentName":"jl-1"}\n' + json.dumps({"type": "user", "message": {"content": "abcde"}}, separators=(",", ":")) + "\n"
            + h(["swarm messages (x"]) + h(["machine: 1G"]) + h(["zzz"]) + json.dumps({"attachment": {"type": "date"}}) + "\n")
    a = self.agent_transcripts({"a": body})
    self.assertEqual(a["hook_bytes"], {"inbox": 17, "machine": 11, "other": 3}); self.assertEqual(a["brief_bytes"], 5)

  def test_cold_wakes(self):
    cw = lambda *r: run("insert into event(ts,agent,kind) values" + ",".join(f"({t},'a','{k}')" for t, k in r), env_extra=NOGIT)["always_loaded"]["cold_wakes"]
    self.assertEqual(cw((0, "push"), (4000, "wake"), (4100, "wake")), 1)  # second wake is warm
    self.assertEqual(cw((0, "push"), (1000, "compact"), (1100, "push"), (5000, "wake")), 1)
    self.assertEqual(cw((0, "push"), (3000, "compact"), (3100, "wake")), 0)

  def test_resources(self):
    p = run("""insert into event(ts,agent,kind,data) values(10,null,'heavy-count','2'),(20,null,'pressure',null),(80,null,'pressure-end',null),
 (90,null,'pressure',null),(95,null,'heavy-count','1'),(30,'a','heavy-start','cabal build'),(40,'a','heavy-start','x'),(50,'b','orphan-kill','1 ghc');""",
            env_extra=NOGIT)["pressure"]
    self.assertEqual((p["episodes"], p["total_s"], p["ongoing"], p["max_concurrent_heavy"], p["orphan_kills"]), (2, 60, True, 2, 1))
    self.assertEqual(p["heavy_starts"], {"a": 2})

  def test_agent_line_anywhere_in_body(self):
    d = tempfile.mkdtemp(); g = lambda *a: subprocess.run(("git", "-C", d, "-c", "user.name=x", "-c", "user.email=x@x") + a, check=True, capture_output=True)
    g("init", "-q", "-b", "main"); open(d + "/f", "w").write("1")
    g("add", "f"); g("commit", "-qm", "t\n\n@@ -1 +1 @@\n\nSwarm-Agent: sp-a\n\nCo-authored-by: y")
    g("commit", "-q", "--allow-empty", "-m", "plain")
    g("update-ref", "refs/remotes/origin/main", "HEAD")
    r = run(cwd=d)
    self.assertEqual([c["agent"] for c in r["commits_per_hour"]], ["sp-a"]); self.assertEqual(r["not_swarm_commits"], 1)

  def test_text_report(self):
    d = tempfile.mkdtemp(); env = {**os.environ, "SWARM_DB": d + "/swarm.db", "HOME": d, "GIT_DIR": "/nonexistent"}
    subprocess.run([SWARM, "task", "add", "x"], env=env, check=True, capture_output=True)
    r = subprocess.run([REPORT], env=env, capture_output=True, text=True)
    self.assertEqual(r.returncode, 0, r.stderr); self.assertIn("## tasks", r.stdout)

if __name__ == '__main__':
    unittest.main()
