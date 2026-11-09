import argparse
import sys; sys.dont_write_bytecode = True
import json, os, shutil, sqlite3, subprocess, sys, tempfile, time, unittest, unittest.mock

SWARM = os.environ.get("SWARM_CLI") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "swarm")
PY = SWARM.endswith(".py")  # the Python CLI (SWARM_CLI=swarm/swarm.py) until P11 deletes it
G = ["git", "-c", "user.name=t", "-c", "user.email=t@t"]


class T(unittest.TestCase):
    def setUp(self):
        self.d = tempfile.mkdtemp()
        self.repo = os.path.join(self.d, "repo")
        self.wt = os.path.join(self.d, "wt")
        os.makedirs(self.repo)
        subprocess.run([*G, "init", "-q", "-b", "main"], cwd=self.repo, check=True)
        for f in ("a.txt", "b.txt", "e.txt"):
            with open(os.path.join(self.repo, f), "w") as h:
                h.write("mod (p, q)\n" if f == "e.txt" else "x")
        subprocess.run([*G, "add", "."], cwd=self.repo, check=True)
        subprocess.run([*G, "commit", "-qm", "init"], cwd=self.repo, check=True)
        subprocess.run([*G, "worktree", "add", "-q", "-b", "w2", self.wt], cwd=self.repo, check=True)
        self.db = os.path.join(self.d, "swarm.db")
        self.cwd = {"a": self.repo, "b": self.wt}

    def sw(self, who, *args, stdin=None, ok=True, hc=None):
        env = {**os.environ, "SWARM_DB": self.db, "SWARM_NAME": who}
        if getattr(self, "fakebin", None):
            env["PATH"] = self.fakebin + os.pathsep + env["PATH"]
        if getattr(self, "launch", None):
            env["SWARM_LAUNCH"] = self.launch
        env.pop("HC_TERMINAL_ID", None)
        if hc:
            env["HC_TERMINAL_ID"] = hc
        # an agent's own terminal would make `hc ls` part of the test
        r = subprocess.run([SWARM, *args], env=env, input=stdin, capture_output=True,
                           text=True, cwd=self.cwd.get(who, self.repo))
        if ok:
            self.assertEqual(r.returncode, 0, r.stderr)
        return r

    def hook(self, who, ev, hc=None, **payload):
        payload.setdefault("cwd", self.cwd.get(who, self.repo))
        r = self.sw(who, "hook", ev, stdin=json.dumps(payload), hc=hc)
        return json.loads(r.stdout)["hookSpecificOutput"] if r.stdout.strip() else {}

    def edit(self, who, path):
        return self.hook(who, "pre-tool", tool_name="Edit", tool_input={"file_path": os.path.join(self.cwd[who], path)})

    def q(self, sql, *a):
        c = sqlite3.connect(self.db)
        c.row_factory = sqlite3.Row
        r = c.execute(sql, a).fetchall()
        c.commit()
        return r

    def agent(self, name, **kw):
        self.sw(name, "join")
        for k, v in kw.items():
            self.q(f"update agent set {k}=? where name=?", v, name)

    # ---- tasks ----
    def test_task_timing_columns(self):
        self.sw("a", "task", "add", "t1")
        self.sw("a", "task", "claim", "1")
        self.sw("a", "task", "block", "1", "why")
        self.sw("a", "task", "unblock", "1")
        self.assertIn("claims 1, releases 0, held by a", self.sw("a", "task", "show", "1").stdout)
        self.sw("a", "task", "done", "1", "--evidence", "e")
        r = self.q("select created_at, first_claimed_at, done_at from task")[0]
        self.assertTrue(r["created_at"] <= r["first_claimed_at"] <= r["done_at"])
        t = json.loads(self.sw("a", "state", "--json").stdout)["tasks"][0]
        self.assertEqual((t["claims"], t["holders"], t["blocked_s"] >= 0), (1, ["a"], True))
        # an older db: columns null, numbers come from the events
        self.q("update task set created_at=null, first_claimed_at=null, done_at=null")
        self.q("update event set ts=ts-100 where kind='task-add'")
        t = json.loads(self.sw("a", "state", "--json").stdout)["tasks"][0]
        self.assertGreaterEqual(t["queue_wait_s"], 100)

    def test_timing_from_auto_spawn_event(self):
        self.sw("a", "task", "add", "t1")
        self.q("update task set state='done', owner='t-2', created_at=null")
        self.q("update event set ts=100 where kind='task-add'")
        self.q("insert into event(ts,agent,kind,data) values(160,'t-2','spawn','auto #1'),(400,'t-2','done','#1 e'),(5,'a','spawn','t-3')")
        t = json.loads(self.sw("a", "state", "--json").stdout)["tasks"][0]
        self.assertEqual((t["queue_wait_s"], t["work_s"], t["holders"]), (60, 240, ["t-2"]))

    def test_task_show_and_claim_print_body(self):
        self.sw("a", "task", "add", "t1", "--body", "build X and Y")
        self.sw("a", "task", "add", "t2")
        self.assertIn("[body: task show]", self.sw("a", "board").stdout)
        self.assertIn("build X and Y", self.sw("b", "task", "show", "1").stdout)
        self.assertIn("build X and Y", self.sw("a", "task", "claim", "1").stdout)
        self.assertIn("(no body)", self.sw("a", "task", "show", "2").stdout)

    def test_release_reopens(self):
        self.sw("a", "task", "add", "t1")
        self.sw("a", "task", "claim", "1")
        self.assertNotEqual(self.sw("b", "task", "release", "1", ok=False).returncode, 0)
        self.sw("a", "task", "release", "1")
        self.assertEqual(self.q("select state,owner from task")[0]["state"], "open")
        self.sw("b", "task", "claim", "1")
        self.assertEqual(self.q("select count(*) n from event where kind='release'")[0]["n"], 1)

    def test_lock_denial_logged(self):
        self.agent("a"); self.agent("b")
        self.sw("a", "lock", "a.txt")
        self.assertIn("locked", self.edit("b", "a.txt").get("permissionDecisionReason", ""))
        self.assertEqual(self.q("select path,data from event where kind='deny-lock'")[0]["data"], "a")

    def test_claim_lease_done(self):
        self.sw("a", "task", "add", "t1")
        self.sw("a", "task", "claim", "1")
        self.assertNotEqual(self.sw("b", "task", "claim", "1", ok=False).returncode, 0)
        self.assertEqual(self.sw("a", "task", "done", "1", ok=False).returncode, 2)
        self.sw("a", "task", "renew", "1", "--lease", "3h")
        self.sw("a", "task", "done", "1", "--evidence", "sha abc")
        self.assertEqual(self.q("select state,evidence from task")[0]["state"], "done")

    def test_reaping(self):
        self.sw("a", "task", "add", "t1")
        self.sw("a", "task", "claim", "1")
        self.sw("b", "join")
        self.sw("a", "lock", "a.txt")
        self.q("update task set lease_until=1")
        self.q("update lock set lease_until=1")
        self.sw("a", "watchd", "--once")
        self.assertEqual(self.q("select state from task")[0]["state"], "claimed")  # live owner: claim stays
        self.q("update agent set ended=1 where name='a'")
        self.sw("a", "watchd", "--once")
        self.assertEqual(self.q("select state from task")[0]["state"], "open")
        self.assertEqual(self.q("select * from lock"), [])
        self.assertIn("was ended", self.sw("a", "read", ok=False).stderr)  # ended: only join returns it
        self.sw("a", "join")
        self.assertIn("lease", self.sw("a", "read").stdout)
        # dead agent: hc terminal gone releases everything
        self.sw("a", "task", "claim", "1")
        self.sw("a", "lock", "b.txt")
        self.q("update agent set hc='t99' where name='a'")
        self.fakes(); self.set_hc({"address": "t1"})
        self.sw("a", "watchd", "--once")
        self.assertEqual(self.q("select count(*) from event where kind='reap' and data='agent gone'")[0][0], 1)
        self.assertEqual(self.q("select state from task")[0]["state"], "open")
        self.assertEqual(self.q("select * from lock"), [])
        self.assertIsNotNone(self.q("select ended from agent where name='a'")[0]["ended"])

    # ---- ownership transactions (sw-ownership §7.1) ----
    def mod(self):
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_tx", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_tx", ld))
        ld.exec_module(m)
        os.environ["SWARM_DB"] = self.db
        return m

    def racing(self, c, sql, fn):
        """c, but fn runs once right after the first statement containing sql has been read: a peer acting in between."""
        class Rows(list):
            fetchall = lambda s: s
            fetchone = lambda s: s[0] if s else None
        class P:
            def __getattr__(s, k): return getattr(c, k)
            def execute(s, q, *a):
                cur = c.execute(q, *a)
                if sql not in q or not hasattr(s, "fn"):
                    return cur
                rows = Rows(cur.fetchall())
                f = s.fn; del s.fn; f()
                return rows
        p = P(); p.fn = fn
        return p

    # ---- fakes for the external commands: hc, gh and the launch script (SWARM_LAUNCH) ----
    def fakes(self):
        """hc ls answers from set_hc (absent: hc fails); gh answers from set_gh by subcommand (absent: fails); the launch
        script logs its argv and the task row it saw. Every call is logged to <name>.log in the test dir."""
        D = self.d
        self.fakebin = os.path.join(D, "fb"); os.makedirs(self.fakebin, exist_ok=True)
        self.launch = os.path.join(D, "launch")
        for path, body in ((os.path.join(self.fakebin, "hc"), """
if a[0] == "ls":
    if not os.path.exists(D + "/hc.json"): sys.exit(1)
    print(open(D + "/hc.json").read())
else: print("{}")
"""), (os.path.join(self.fakebin, "gh"), """
if not os.path.exists(D + "/gh." + a[0]): sys.exit(1)
sys.stdout.write(open(D + "/gh." + a[0]).read())
"""), (self.launch, """
import sqlite3
rows = sqlite3.connect(os.environ["SWARM_DB"]).execute("select owner,state from task").fetchall()
open(D + "/launch.calls", "a").write(json.dumps({"argv": a, "task": rows}) + "\\n")
if os.path.exists(D + "/launch.fail"): sys.exit(1)
print("hc1")
""")):
            name = os.path.basename(path)
            open(path, "w").write(f"#!{sys.executable}\nimport json, os, sys\na, D = sys.argv[1:], {D!r}\n"
                                  f"open(D + '/{name}.log', 'a').write(' '.join(a) + '\\n')\n" + body)
            os.chmod(path, 0o755)

    def set_hc(self, *terminals):
        """hc ls --json lists these terminals; none given: hc ls fails."""
        f = os.path.join(self.d, "hc.json")
        if terminals:
            open(f, "w").write(json.dumps({"terminals": [{"state": "live", **t} for t in terminals]}))
        elif os.path.exists(f):
            os.remove(f)

    def set_gh(self, sub, out=None):
        """gh <sub> prints out; None: it fails (rate limited)."""
        f = os.path.join(self.d, "gh." + sub)
        if out is None:
            os.path.exists(f) and os.remove(f)
        else:
            open(f, "w").write(out if isinstance(out, str) else json.dumps(out))

    def calls(self, name):
        f = os.path.join(self.d, name + ".log")
        return open(f).read().splitlines() if os.path.exists(f) else []

    def launched(self):
        f = os.path.join(self.d, "launch.calls")
        return [json.loads(x) for x in open(f)] if os.path.exists(f) else []

    # ---- fencing on the bound terminal (sw-ownership §7.2) ----
    def live_hc(self, *addrs):
        self.fakebin = os.path.join(self.d, "fb"); os.makedirs(self.fakebin, exist_ok=True)
        hc = os.path.join(self.fakebin, "hc")
        ts = json.dumps({"terminals": [{"address": x, "state": "live"} for x in addrs]})
        open(hc, "w").write(f"#!/bin/sh\n[ \"$1\" = ls ] && echo '{ts}' || echo '{{}}'\n")
        os.chmod(hc, 0o755)

    def test_other_terminal_hook_and_wait_dont_rebind(self):
        self.sw("a", "join", hc="t1")
        self.q("update agent set status='idle'")
        out = self.hook("a", "post-tool", hc="t2", tool_name="Bash", tool_input={"command": "ls"})
        self.assertIn("a is bound to t1; this terminal is t2. `swarm join --takeover`", out["additionalContext"])
        self.assertEqual(self.hook("a", "prompt", hc="t2"), {})  # said once per terminal
        self.assertEqual(tuple(self.q("select hc,status from agent")[0]), ("t1", "idle"))  # wrote nothing
        w = self.sw("a", "wait", "--timeout", "1", hc="t2", ok=False)
        self.assertEqual((w.returncode, w.stderr.strip()), (3, "a is bound to t1; this terminal is t2. `swarm join --takeover` moves it here."))
        self.assertEqual(self.q("select hc from agent")[0]["hc"], "t1")
        self.assertIn("bound to t1", self.sw("a", "task", "add", "x", hc="t2", ok=False).stderr)
        self.sw("a", "task", "add", "x", hc="t1")
        self.sw("u", "join")  # unbound row (outside Herdr): wait binds it
        self.sw("u", "wait", "--timeout", "1", hc="t3")
        self.assertEqual(self.q("select hc from agent where name='u'")[0]["hc"], "t3")

    def test_ended_agent_not_revived(self):
        self.sw("a", "join", hc="t1")
        self.sw("a", "leave", hc="t1")
        self.assertIn("a was ended at", self.hook("a", "prompt", hc="t1")["additionalContext"])
        self.hook("a", "stop", hc="t1")
        w = self.sw("a", "wait", "--timeout", "1", hc="t1", ok=False)
        self.assertEqual(w.returncode, 3); self.assertIn("swarm join` to return", w.stderr)
        self.assertEqual(tuple(self.q("select status,ended is not null from agent")[0]), ("ended", 1))
        self.assertIn("swarm join` to return", self.sw("a", "lock", "a.txt", hc="t1", ok=False).stderr)
        self.sw("a", "join", hc="t1")
        self.assertEqual(tuple(self.q("select status,ended from agent")[0]), ("idle", None))

    def test_join_refused_on_live_binding_takeover_moves_and_logs(self):
        self.live_hc("t1", "t2")
        self.sw("a", "join", hc="t1")
        self.sw("a", "task", "add", "t", hc="t1"); self.sw("a", "task", "claim", "1", hc="t1")
        err = self.sw("a", "join", hc="t2", ok=False).stderr
        self.assertIn("a is bound to t1; this terminal is t2. `swarm join --takeover`", err)
        self.assertEqual(self.q("select hc from agent")[0]["hc"], "t1")
        # relaunch: the predecessor t1 is still live, the successor takes over from t2
        self.sw("a", "join", "--takeover", hc="t2")
        self.assertEqual(self.q("select hc from agent")[0]["hc"], "t2")
        self.assertEqual(self.q("select data from event where kind='takeover'")[0]["data"], "t1 -> t2")
        for cmd in (("task", "done", "1", "--evidence", "x"), ("read",), ("lock", "b.txt"), ("post", "@all", "hi")):
            self.assertIn("a is bound to t2; this terminal is t1", self.sw("a", *cmd, hc="t1", ok=False).stderr, cmd)
        self.assertIn("bound to t2", self.hook("a", "pre-tool", hc="t1", tool_name="Bash", tool_input={"command": "ls"})["additionalContext"])
        self.assertEqual(tuple(self.q("select state,owner from task")[0]), ("claimed", "a"))  # the claim moved with the name
        self.sw("a", "task", "done", "1", "--evidence", "x", hc="t2")
        # a binding whose terminal hc ls doesn't show live moves without --takeover
        self.sw("b", "join", hc="t9")
        self.sw("b", "join", hc="t2")
        self.assertEqual(self.q("select hc from agent where name='b'")[0]["hc"], "t2")

    def test_takeover_then_predecessor_death_keeps_agent_claims_locks(self):
        self.fakes()
        self.sw("a", "join", hc="t1")
        self.sw("a", "task", "add", "t", hc="t1"); self.sw("a", "task", "claim", "1", hc="t1")
        self.sw("a", "lock", "a.txt", hc="t1")
        self.sw("a", "join", "--takeover", hc="t2")
        self.set_hc({"address": "t2"})  # the predecessor's terminal t1 is gone; only t2 is live
        self.sw("a", "watchd", "--once")
        self.assertEqual(tuple(self.q("select hc,ended from agent")[0]), ("t2", None))
        self.assertEqual(self.q("select state from task")[0]["state"], "claimed")
        self.assertEqual(self.q("select agent from lock")[0]["agent"], "a")

    @unittest.skipUnless(PY, "needs the Python module: a race or a pure function, a Lua spec instead")
    def test_reap_spares_row_rebound_after_hc_ls(self):
        self.sw("a", "join", hc="t1")
        self.sw("a", "task", "add", "t", hc="t1"); self.sw("a", "task", "claim", "1", hc="t1")
        m = self.mod()
        rebind = lambda: self.q("update agent set hc='t2' where name='a'")  # a takeover after reap's hc ls
        self.assertEqual(m.reap(self.racing(m.connect(), "from agent where ended is null", rebind), live_addrs={"t2"}), [])
        self.assertEqual(tuple(self.q("select hc,ended from agent")[0]), ("t2", None))
        self.assertEqual(self.q("select state from task")[0]["state"], "claimed")

    def test_second_lock_on_held_path_refused(self):
        self.agent("a"); self.agent("b")
        self.sw("a", "lock", "a.txt")
        self.assertIn("locked by a", self.sw("b", "lock", "a.txt", ok=False).stderr)
        self.assertEqual([tuple(r) for r in self.q("select path,agent from lock")], [("a.txt", "a")])

    def test_concurrent_lock_waits_not_double_writes(self):
        self.agent("a"); self.agent("b")
        peer = sqlite3.connect(self.db, isolation_level=None)
        peer.execute("begin immediate")
        peer.execute("insert into lock(path,agent,since,lease_until) values('a.txt','a',?,?)", (int(time.time()), int(time.time()) + 3600))
        env = {**os.environ, "SWARM_DB": self.db, "SWARM_NAME": "b"}
        env.pop("HC_TERMINAL_ID", None)
        pr = subprocess.Popen([SWARM, "lock", "a.txt"], env=env, cwd=self.repo, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        time.sleep(1)
        self.assertIsNone(pr.poll())  # waiting on the peer's transaction
        peer.execute("commit")
        _, err = pr.communicate(timeout=15)
        self.assertNotEqual(pr.returncode, 0, err)
        self.assertEqual([tuple(r) for r in self.q("select path,agent from lock")], [("a.txt", "a")])

    @unittest.skipUnless(PY, "needs the Python module: a race or a pure function, a Lua spec instead")
    def test_done_after_reap_and_reclaim_fails(self):
        self.sw("a", "task", "add", "t1")
        self.sw("a", "task", "claim", "1")
        m = self.mod()
        reclaim = lambda: self.q("update task set owner='b' where id=1")  # reaped, then claimed by b
        for act in ("done", "renew", "block", "release"):
            c = self.racing(m.connect(), "select * from task where id=?", reclaim)
            with unittest.mock.patch.dict(os.environ, {"SWARM_NAME": "a"}), self.assertRaises(SystemExit):
                m.cmd_task(c, argparse.Namespace(act=act, id=1, evidence="e", lease="1h", question="q"))
            self.assertEqual(tuple(self.q("select state,owner from task")[0]), ("claimed", "b"), act)
            self.q("update task set owner='a'")

    @unittest.skipUnless(PY, "needs the Python module: a race or a pure function, a Lua spec instead")
    def test_reap_keeps_renew_after_its_select(self):
        self.sw("a", "task", "add", "t1")
        self.sw("a", "task", "claim", "1")
        self.sw("a", "lock", "a.txt")
        self.q("update task set lease_until=1")
        self.q("update agent set ended=1 where name='a'")
        m = self.mod()
        renew = lambda: self.q("update task set lease_until=? where id=1", int(time.time()) + 3600)
        self.assertEqual(m.reap(self.racing(m.connect(), "from task where state='claimed'", renew)), [])
        self.assertEqual(self.q("select state from task")[0]["state"], "claimed")
        self.q("update lock set lease_until=1")
        relock = lambda: self.q("update lock set lease_until=?", int(time.time()) + 3600)
        self.assertEqual(m.reap(self.racing(m.connect(), "select * from lock", relock)), [])
        self.assertEqual(len(self.q("select * from lock")), 1)

    def test_drop_claimed_only_by_owner_or_comms(self):
        for i in range(3):
            self.sw("a", "task", "add", f"t{i}")
        self.sw("a", "task", "claim", "1")
        self.sw("a", "task", "claim", "2")
        self.assertIn("only it or the communicator", self.sw("b", "task", "drop", "1", ok=False).stderr)
        self.sw("b", "task", "drop", "3")  # open: anyone
        self.sw("a", "task", "drop", "1")
        self.sw("x-comms", "task", "drop", "2")
        self.assertEqual([r["state"] for r in self.q("select state from task order by id")], ["dropped"] * 3)

    # ---- messages ----
    def test_cursor(self):
        self.agent("a"); self.agent("b")
        self.sw("a", "post", "b", "hello")
        self.sw("a", "post", "@all", "all")
        self.assertIn("hello", self.sw("b", "read").stdout)
        self.assertIn("no unread", self.sw("b", "read").stdout)
        self.assertIn("no unread", self.sw("a", "read").stdout)  # own @all not echoed
        self.sw("a", "post", "b", "again")
        self.assertIn("again", self.sw("b", "read").stdout)

    def test_post_delivery_in_post_tool(self):
        self.agent("a"); self.agent("b")
        self.sw("a", "post", "b", "look at X")
        out = self.hook("b", "post-tool", tool_name="Read", tool_input={})
        self.assertIn("look at X", out["additionalContext"])
        self.assertEqual(self.hook("b", "post-tool", tool_name="Read", tool_input={}), {})

    def test_ctx_note_steps_marker_and_claim_refusal(self):
        self.agent("b")
        tr = os.path.join(self.cwd["b"], "t.jsonl")
        def usage(n):
            open(tr, "w").write(json.dumps({"type": "assistant", "message": {"usage": {"input_tokens": n}}}) + "\n")
        sid = f"t{os.getpid()}{time.time()}"
        mark = os.path.join(tempfile.gettempdir(), f"claude-ctx-{sid}")
        post = lambda: self.hook("b", "post-tool", tool_name="Read", tool_input={}, transcript_path=tr, session_id=sid)
        self.addCleanup(lambda: os.path.exists(mark) and os.remove(mark))
        usage(300_000)
        self.assertEqual(post(), {})
        usage(360_000)
        self.assertIn("go idle", post()["additionalContext"])
        self.assertEqual(post(), {})  # same step
        self.sw("b", "task", "add", "t1")
        self.assertNotEqual(self.sw("b", "task", "claim", "1", ok=False).returncode, 0)
        usage(560_000)
        self.assertIn("hand off now", post()["additionalContext"])
        open(mark, "w").write("9")  # the repo hook already fired for this step
        usage(1_000_000 - 1)
        self.assertEqual(post(), {})

    def test_comms_ctx_note_from_commands(self):
        self.agent("x-comms")
        sid = f"c{os.getpid()}{time.time()}"
        home = os.path.join(self.d, "home", ".claude", "projects", "p")
        os.makedirs(home)
        open(os.path.join(home, sid + ".jsonl"), "w").write(
            json.dumps({"type": "assistant", "message": {"usage": {"input_tokens": 360_000}}}) + "\n")
        mark = os.path.join(tempfile.gettempdir(), f"claude-ctx-{sid}")
        self.addCleanup(lambda: os.path.exists(mark) and os.remove(mark))
        env = {**os.environ, "HOME": os.path.join(self.d, "home"), "CLAUDE_CODE_SESSION_ID": sid}
        r = subprocess.run([SWARM, "board"], env={**env, "SWARM_NAME": "x-comms", "SWARM_DB": self.db},
                           capture_output=True, text=True)
        self.assertIn("pass on the swarm", r.stdout)
        r = subprocess.run([SWARM, "who"], env={**env, "SWARM_NAME": "x-comms", "SWARM_DB": self.db},
                           capture_output=True, text=True)
        self.assertNotIn("pass on the swarm", r.stdout)  # once per step

    def test_burst_capped_rest_stays_unread(self):
        self.agent("a"); self.agent("b")
        for i in range(40):
            self.sw("a", "post", "b", f"m{i} " + "y" * 400)
        ctx = self.hook("b", "post-tool", tool_name="Read", tool_input={})["additionalContext"]
        self.assertLess(len(ctx), 10_000)
        self.assertIn("more unread", ctx)
        shown = ctx.count(" yyyy")
        left = self.sw("b", "read").stdout
        self.assertEqual(shown + left.count(" yyyy"), 40)

    def test_new_agent_skips_older_broadcasts(self):
        self.agent("a")
        self.sw("a", "post", "@all", "old rule from another run")
        self.agent("b")  # joins after it
        self.sw("a", "post", "@all", "new rule")
        self.sw("a", "post", "b", "for you")
        out = self.sw("b", "read").stdout
        self.assertNotIn("old rule", out)
        self.assertIn("new rule", out); self.assertIn("for you", out)
        self.sw("b", "leave"); self.sw("a", "post", "@all", "while b was away")
        self.agent("b")  # a rejoin keeps its cursor
        self.assertIn("while b was away", self.sw("b", "read").stdout)

    def test_post_compact_ctx(self):
        tr = os.path.join(self.d, "t.jsonl")
        with open(tr, "w") as f:
            f.write(json.dumps({"type": "assistant", "message": {"usage": {"input_tokens": 1, "cache_read_input_tokens": 200_000}}}) + "\n")
            f.write(json.dumps({"type": "system", "compactMetadata": {"postTokens": 9_000}}) + "\n")
        self.agent("a")
        self.hook("a", "session", source="compact", transcript_path=tr)
        self.assertEqual(self.q("select ctx_tokens from agent where name='a'")[0][0], 40_000)

    # ---- conflicts ----
    def write(self, who, path, text):
        with open(os.path.join(self.cwd[who], path), "w") as h:
            h.write(text)

    def tick(self):
        self.sw("a", "watchd", "--once")

    def notices(self, who):
        return self.q("select body from msg where dest=? and kind='notice'", who)

    def test_compatible_appends_are_silent(self):
        self.agent("a"); self.agent("b")
        self.edit("a", "e.txt"); self.edit("b", "e.txt")
        self.write("a", "e.txt", "mod (p, q, c)\n")
        self.write("b", "e.txt", "mod (p, q, d)\n")
        self.tick()
        self.assertEqual(self.q("select count(*) n from msg where kind='notice'")[0]["n"], 0)
        self.assertEqual(self.q("select count(*) n from event where kind='conflict-compat'")[0]["n"], 1)

    def test_same_token_episode(self):
        self.agent("a"); self.agent("b")
        self.edit("a", "a.txt"); self.edit("b", "a.txt")
        self.write("a", "a.txt", "y"); self.write("b", "a.txt", "z")
        self.tick()
        for w, o in (("a", "b"), ("b", "a")):
            n = self.notices(w)
            self.assertEqual(len(n), 1)
            self.assertIn(f"conflicts with {o}'s", n[0]["body"])
            self.assertIn("a.txt (your lines 1–1", n[0]["body"])
        self.tick()
        self.assertEqual(len(self.notices("a")), 1)  # same episode: silent
        self.write("b", "a.txt", "x")  # revert one side
        self.tick()
        self.assertEqual(self.q("select * from conflict"), [])
        self.write("b", "a.txt", "w")
        self.tick()
        self.assertEqual(len(self.notices("a")), 2)  # a new episode

    def land(self, path, text):
        """A peer's PR lands on origin/main; the repo fetches it, and its local main stays behind."""
        o = os.path.join(self.d, "origin.git")
        if not os.path.exists(o):
            subprocess.run([*G, "clone", "-q", "--bare", self.repo, o], check=True)
            subprocess.run([*G, "remote", "add", "origin", o], cwd=self.repo, check=True)
        pr = os.path.join(self.d, "pr")
        subprocess.run([*G, "clone", "-q", o, pr], check=True)
        with open(os.path.join(pr, path), "w") as h:
            h.write(text)
        subprocess.run([*G, "commit", "-qam", "pr"], cwd=pr, check=True)
        subprocess.run([*G, "push", "-q", "origin", "main"], cwd=pr, check=True)
        subprocess.run(["rm", "-rf", pr], check=True)
        subprocess.run([*G, "fetch", "-q", "origin"], cwd=self.repo, check=True)

    def test_fresh_worktree_off_origin_main_is_silent(self):
        self.agent("a"); self.agent("b")
        self.edit("b", "a.txt")
        self.write("b", "a.txt", "z")  # b's own uncommitted edit, off the old main
        self.land("a.txt", "y")
        self.cwd["c"] = os.path.join(self.d, "wt3")
        subprocess.run([*G, "worktree", "add", "-q", "-b", "c/x", self.cwd["c"], "origin/main"], cwd=self.repo, check=True)
        self.agent("c")
        self.tick()
        self.assertEqual(self.q("select count(*) n from msg where kind='notice'")[0]["n"], 0)

    def test_merge_origin_main_is_silent(self):
        self.agent("a"); self.agent("b")
        L = "".join(f"l{i}\n" for i in range(9))
        self.write("a", "e.txt", L)
        subprocess.run([*G, "commit", "-qam", "lines"], cwd=self.repo, check=True)
        subprocess.run([*G, "merge", "-q", "main"], cwd=self.wt, check=True)
        self.land("e.txt", L.replace("l0", "main0"))
        self.cwd["c"] = os.path.join(self.d, "wt3")
        subprocess.run([*G, "worktree", "add", "-q", "-b", "c/x", self.cwd["c"], "main"], cwd=self.repo, check=True)
        self.agent("c")
        self.edit("b", "e.txt"); self.edit("c", "e.txt")
        subprocess.run([*G, "merge", "-q", "origin/main"], cwd=self.cwd["c"], check=True)
        self.write("c", "e.txt", L.replace("l0", "main0").replace("l8", "c8"))  # c's own edit: line 8
        self.write("b", "e.txt", L.replace("l0", "b0"))  # b edits line 0, which main changed: b vs main, not vs c
        self.tick()
        self.assertEqual(self.q("select count(*) n from msg where kind='notice'")[0]["n"], 0)
        self.write("b", "e.txt", L.replace("l8", "b8"))  # now b's own change overlaps c's
        self.tick()
        self.assertIn("conflicts with b's", self.notices("c")[0]["body"])

    def test_shared_tree_notice_once(self):
        self.cwd["c"] = self.repo
        self.agent("a"); self.agent("c")
        self.assertEqual(self.edit("a", "a.txt"), {})
        out = self.edit("c", "a.txt")
        self.assertIn("also a's worktree", out["additionalContext"])
        self.assertIn("also edits in", self.notices("a")[0]["body"])
        self.assertEqual(self.edit("c", "a.txt"), {})
        self.edit("a", "b.txt")
        self.assertEqual(len(self.notices("a")), 1)

    @unittest.skipUnless(PY, "needs the Python module: a race or a pure function, a Lua spec instead")
    def test_real_hunk_probe_asserts(self):
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_mod2", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_mod2", ld))
        ld.exec_module(m)
        rh = m.real_hunk
        self.assertFalse(rh("module L (a, b) where\n", "module L (a, b, c) where\n", "module L (a, b, d) where\n"))
        self.assertFalse(rh("f a b\n", "f a x b\n", "g a b\n"))
        self.assertTrue(rh("x = f a\n", "x = g a\n", "x = h a\n"))
        self.assertFalse(rh("f a b c\n", "f a b c d\n", "f z\n"))  # insertion at the edge of a replaced span merges
        self.assertTrue(rh("f a b c\n", "f a x b c\n", "f z\n"))  # insertion inside a replaced span does not

    @unittest.skipUnless(shutil.which("luajit"), "no luajit for the Lua specs")
    def test_lua_specs(self):
        spec = os.path.join(os.path.dirname(os.path.realpath(SWARM)), "lua", "test", "run.lua")
        r = subprocess.run(["luajit", spec], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_join_leave_who(self):
        self.live_hc("t1", "t2")
        self.sw("x", "join")
        self.q("insert into msg(ts,frm,dest,body) values(0,'x','@all','older run')")
        self.sw("a", "join", hc="t1")
        self.assertEqual(self.q("select last_msg_id from cursor where agent='a'")[0][0], 1)  # skips older broadcasts
        self.assertIn("a is bound to t1; this terminal is t2. `swarm join --takeover`", self.sw("a", "join", hc="t2", ok=False).stderr)
        self.sw("a", "join", "--takeover", "--model", "opus", hc="t2")
        self.assertEqual(tuple(self.q("select hc, model from agent where name='a'")[0]), ("t2", "opus"))
        self.assertEqual(self.q("select data from event where kind='takeover'")[0][0], "t1 -> t2")
        self.assertEqual(self.sw("a", "join", "p", "q", ok=False).returncode, 2)  # bad usage
        self.sw("b", "join")
        self.q("insert into lock(path,agent,since,lease_until) values('x.txt','b',0,9999999999)")
        self.q("insert into task(title,state,owner,lease_until) values('t','claimed','b',9999999999)")
        self.q("update agent set ctx_tokens=52000 where name='b'")
        who = self.sw("x", "who").stdout
        self.assertIn("machine: ", who)
        self.assertRegex(who, r"(?m)^b idle ctx=52k idle=0m cache=warm wt: \? locks: x\.txt$")
        self.sw("x", "leave", "b")
        self.assertEqual(tuple(self.q("select status, ended is not null from agent where name='b'")[0]), ("ended", 1))
        self.assertEqual((tuple(self.q("select state, owner from task")[0]), self.q("select * from lock")), (("open", None), []))
        self.assertNotIn("\nb ", self.sw("x", "who").stdout)
        self.assertIn("b was ended at", self.sw("b", "leave", ok=False).stderr)  # fenced
        self.sw("b", "join")
        self.assertEqual(tuple(self.q("select status, ended from agent where name='b'")[0]), ("idle", None))
        self.assertEqual([r[0] for r in self.q("select kind from event where agent='b'")], ["join", "leave", "join"])

    def test_branch_fallback_for_wt(self):
        self.agent("w2"); self.q("update agent set wt=null")
        subprocess.run([*G, "branch", "-m", "w2", "w2/x"], cwd=self.wt, check=True)
        self.assertIn("wt: wt", self.sw("w2", "who").stdout)

    # ---- locks ----
    def test_lock_prefix_and_overlap(self):
        self.agent("a"); self.agent("b")
        self.sw("a", "lock", "migrations/0070*")
        out = self.edit("b", "migrations/0070_x.sql")
        self.assertEqual(out["permissionDecision"], "deny")
        self.sw("a", "lock", "docs/")
        self.assertEqual(self.edit("b", "docs/x/y.md")["permissionDecision"], "deny")
        self.assertNotEqual(self.sw("b", "lock", "docs/x.md", ok=False).returncode, 0)
        self.assertNotEqual(self.sw("b", "lock", "migrations/0070_a.sql", ok=False).returncode, 0)
        self.sw("b", "lock", "other/")

    def test_lock_released_when_work_lands(self):
        self.agent("a")
        self.edit("a", "a.txt")
        self.sw("a", "lock", "a.txt")
        self.tick()
        self.assertEqual(len(self.q("select * from lock")), 1)  # no change yet: not seen
        self.write("a", "a.txt", "changed")
        self.tick()
        self.assertEqual(self.q("select seen from lock")[0][0], 1)
        subprocess.run([*G, "commit", "-qam", "land"], cwd=self.repo, check=True)
        subprocess.run([*G, "worktree", "prune"], cwd=self.repo)
        self.tick()  # main moved to include the change: the file left a's working set
        self.assertEqual(self.q("select * from lock"), [])

    def test_bash_lock_violation(self):
        self.agent("a"); self.agent("b")
        self.edit("b", "b.txt")
        self.sw("a", "lock", "a.txt")
        self.write("b", "a.txt", "sneaky")
        self.tick()
        self.assertIn("violation", self.sw("b", "read").stdout)
        self.assertIn("locked path", self.sw("a", "read").stdout)

    def test_hard_lock_deny(self):
        self.agent("a"); self.agent("b")
        self.sw("a", "lock", "*.txt", "--reason", "refactor")
        out = self.edit("b", "a.txt")
        self.assertEqual(out["permissionDecision"], "deny")
        self.assertIn("locked by a", out["permissionDecisionReason"])
        self.assertEqual(self.edit("a", "a.txt"), {})
        self.sw("a", "unlock", "*.txt")
        self.assertEqual(self.edit("b", "a.txt").get("permissionDecision"), None)

    # ---- lifecycle ----
    OLD = int(time.time()) - 3600

    def comms_tick(self):
        self.sw("a", "watchd", "--once", "--comms", "comms", "--max-agents", "0")

    def idle(self, name, **kw):
        self.agent(name, status="idle", last_active=self.OLD, **kw)

    def ended(self, name):
        return self.q("select ended from agent where name=?", name)[0][0] is not None

    # ---- sweep ----
    def old_wt(self, path):
        gd = subprocess.run([*G, "rev-parse", "--absolute-git-dir"], cwd=path, capture_output=True, text=True).stdout.strip()
        for p in (path, os.path.join(gd, "logs", "HEAD")):
            os.utime(p, (self.OLD, self.OLD))

    def test_sweep(self):
        self.old_wt(self.wt)
        pr = self.fake_proc()
        swp = lambda: self.swp("a", pr, "watchd", "--once", "--comms", "comms", "--max-agents", "0")
        branches = lambda: subprocess.run(["git", "branch", "--list", "w2"], cwd=self.repo, capture_output=True, text=True).stdout
        dry = self.swp("a", pr, "watchd", "--dry-run").stdout
        self.assertIn(self.wt, dry); self.assertTrue(os.path.exists(self.wt))
        self.add_proc(pr, 500, 1, "bash", ["bash"], cwd=self.wt)
        swp(); self.assertTrue(os.path.exists(self.wt))  # a process is in it
        shutil.rmtree(os.path.join(pr, "500"))
        self.agent("x", cwd=os.path.join(self.wt, "sub"))
        swp(); self.assertTrue(os.path.exists(self.wt))  # a live agent's cwd is in it
        self.q("update agent set ended=1 where name='x'")
        self.write("b", "new.txt", "wip")
        self.old_wt(self.wt)
        swp(); self.assertTrue(os.path.exists(self.wt))  # dirty
        os.remove(os.path.join(self.wt, "new.txt"))
        self.write("b", "u.txt", "wip")
        subprocess.run([*G, "add", "."], cwd=self.wt, check=True)
        subprocess.run([*G, "commit", "-qm", "wip"], cwd=self.wt, check=True)
        self.old_wt(self.wt)
        swp(); self.assertTrue(os.path.exists(self.wt))  # unlanded
        subprocess.run([*G, "merge", "-q", "w2"], cwd=self.repo, check=True)
        os.utime(self.wt)
        swp(); self.assertTrue(os.path.exists(self.wt))  # touched just now
        self.old_wt(self.wt)
        swp()
        self.assertFalse(os.path.exists(self.wt)); self.assertEqual(branches(), "")
        self.assertEqual(self.q("select count(*) from event where kind='sweep'")[0][0], 1)
        self.assertIn("swept 1", self.q("select body from msg where kind='notice'")[0][0])

    def test_sweep_caches_not_landed(self):
        self.write("b", "u.txt", "wip")
        subprocess.run([*G, "add", "."], cwd=self.wt, check=True)
        subprocess.run([*G, "commit", "-qm", "wip"], cwd=self.wt, check=True)
        self.old_wt(self.wt)
        self.fakes(); self.set_gh("pr", "[]")
        env = {**os.environ, "SWARM_DB": self.db, "SWARM_NAME": "a", "SWARM_PROC": self.fake_proc(), "PATH": self.fakebin + os.pathsep + os.environ["PATH"]}
        asked = lambda: sum(1 for x in self.calls("gh") if x.startswith("pr list"))  # the last resort of `landed`
        ticks = lambda: sum(1 for x in self.calls("hc") if x.startswith("ls"))

        def tick(n):  # n more ticks of the running watchd
            goal = ticks() + n
            for _ in range(200):
                if ticks() >= goal:
                    return
                time.sleep(0.1)
            self.fail("watchd did not tick")
        # the verdict cache lives in the daemon: run it, not --once
        w = subprocess.Popen([SWARM, "watchd", "--comms", "comms", "--max-agents", "0", "--interval", "1"], env=env, cwd=self.repo,
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            tick(1); tick(1); self.assertEqual(asked(), 1)  # unchanged: asked once over two ticks
            subprocess.run([*G, "commit", "-q", "--allow-empty", "-m", "x"], cwd=self.repo, check=True)
            no_origin = subprocess.run(["git", "-C", self.repo, "remote", "get-url", "origin"], capture_output=True).returncode != 0
            tick(2); self.assertEqual(asked(), 1 + no_origin)  # B moved only when it is local main
            subprocess.run([*G, "commit", "-q", "--allow-empty", "-m", "y"], cwd=self.wt, check=True)
            self.old_wt(self.wt)
            n = asked(); tick(2); self.assertEqual(asked(), n + 1)  # HEAD moved
        finally:
            w.terminate(); w.wait()

    def test_landed_agent_ended_and_cleaned(self):
        self.idle("e", wt=self.wt)
        self.comms_tick()
        self.assertTrue(self.ended("e"))
        self.assertFalse(os.path.exists(self.wt))
        self.assertEqual(subprocess.run(["git", "branch", "--list", "w2"], cwd=self.repo, capture_output=True, text=True).stdout, "")
        self.assertEqual(self.q("select data from event where kind='end'")[0][0], "landed")

    def test_squash_merged_agent_ended(self):
        self.idle("e", wt=self.wt)
        for d in (self.wt, self.repo):  # same content, different commits
            self.write("b" if d == self.wt else "a", "a.txt", "squashed")
            subprocess.run([*G, "commit", "-qam", "change"], cwd=d, check=True)
        self.comms_tick()
        self.assertTrue(self.ended("e"))

    def test_dirty_or_unlanded_not_ended(self):
        self.idle("e", wt=self.wt)
        self.write("b", "new.txt", "wip")
        self.comms_tick()
        self.assertFalse(self.ended("e"))  # dirty
        subprocess.run([*G, "add", "."], cwd=self.wt, check=True)
        subprocess.run([*G, "commit", "-qm", "wip"], cwd=self.wt, check=True)
        self.comms_tick()
        self.assertFalse(self.ended("e"))  # clean but not on main
        self.assertTrue(os.path.exists(self.wt))

    def test_missing_worktree(self):
        self.idle("e", wt=self.wt)
        shutil.rmtree(self.wt)  # branch w2 still registered; its commits are on main
        self.comms_tick()
        self.assertTrue(self.ended("e"))
        self.idle("f", wt=self.wt + "-gone")  # no worktree, no branch
        self.comms_tick()
        self.assertTrue(self.ended("f"))

    def test_missing_worktree_unlanded_branch_not_ended(self):
        self.idle("e", wt=self.wt)
        self.write("b", "new.txt", "wip")
        subprocess.run([*G, "add", "."], cwd=self.wt, check=True)
        subprocess.run([*G, "commit", "-qm", "wip"], cwd=self.wt, check=True)
        shutil.rmtree(self.wt)
        self.comms_tick()
        self.assertFalse(self.ended("e"))

    def test_missing_worktree_squash_merged_branch_ended(self):
        self.fakes()
        self.idle("e", wt=self.wt)
        for d in (self.wt, self.repo):  # same content, different commits
            self.write("b" if d == self.wt else "a", "a.txt", "squashed")
            subprocess.run([*G, "commit", "-qam", "change"], cwd=d, check=True)
        shutil.rmtree(self.wt)
        self.comms_tick()
        self.assertTrue(self.ended("e"))

    def end_mod(self):
        sys.path.insert(0, os.path.dirname(SWARM))
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_mod_end", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_mod_end", ld))
        ld.exec_module(m)
        os.environ["SWARM_DB"] = self.db
        return m, m.connect()

    @unittest.skipUnless(PY, "needs the Python module: a race or a pure function, a Lua spec instead")
    def test_end_agent_skips_agent_that_claimed_since_decision(self):
        self.idle("e", wt=self.wt)
        self.sw("e", "task", "add", "t")
        m, c = self.end_mod()
        a = dict(c.execute("select * from agent where name='e'").fetchone())
        self.sw("e", "task", "claim", "1")  # after lifecycle judged it idle
        m.run = lambda *x, **k: None
        m.end_agent(c, a, self.wt, self.repo, None)
        self.assertFalse(self.ended("e"))
        self.assertEqual(self.q("select owner from task where id=1")[0][0], "e")
        self.assertTrue(os.path.isdir(self.wt))

    def test_end_agent_keeps_worktree_a_live_peer_uses(self):
        self.fakes()
        self.idle("e", wt=self.wt)
        self.agent("p", wt=self.wt)
        self.comms_tick()
        self.assertTrue(self.ended("e"))
        self.assertTrue(os.path.isdir(self.wt))

    def test_claim_keeps_agent_and_lease(self):
        self.idle("e", wt=self.wt)
        self.sw("e", "task", "add", "t"); self.sw("e", "task", "claim", "1")
        self.q("update task set lease_until=1")
        self.comms_tick()
        self.assertFalse(self.ended("e"))
        self.assertEqual(self.q("select state from task")[0][0], "claimed")
        self.assertIn("past its lease", self.sw("comms", "read").stdout)
        self.comms_tick()
        self.assertEqual(self.q("select count(*) from msg where dest='comms'")[0][0], 1)  # once per lease period
        self.assertNotIn("open task", self.sw("e", "read").stdout)  # not digested

    def test_comms_never_digested_or_ended_reusable_digested(self):
        self.idle("comms"); self.idle("r")
        self.sw("comms", "task", "add", "t")
        self.comms_tick()
        self.assertFalse(self.ended("comms")); self.assertFalse(self.ended("r"))
        self.assertIn("1 open task", self.sw("r", "read").stdout)
        self.assertNotIn("open task", self.sw("comms", "read").stdout)

    def test_digest_edge_triggered(self):
        self.idle("comms"); self.idle("r")
        digests = lambda: len(self.q("select 1 from msg where dest='r' and body like '%open task%'"))
        self.sw("comms", "task", "add", "t1")
        self.comms_tick(); self.assertEqual(digests(), 1)
        self.q("update event set ts=ts-5000"); self.q("update agent set last_active=last_active-5000")
        self.comms_tick(); self.assertEqual(digests(), 1)  # unchanged pool, 900 s later: silent
        self.sw("comms", "task", "add", "t2")
        self.comms_tick(); self.assertEqual(digests(), 2)  # a new id
        self.sw("comms", "task", "claim", "2"); self.sw("comms", "task", "block", "2", "q")
        self.sw("comms", "task", "add", "t3", "--after", "2")  # waits on a blocked task: not startable
        self.comms_tick(); self.assertEqual(digests(), 2)

    def test_big_context_finished_even_with_open_tasks(self):
        self.idle("big", ctx_tokens=120_000)
        self.sw("big", "task", "add", "t")
        self.comms_tick()
        self.assertTrue(self.ended("big"))

    def test_task_done_says_what_next(self):
        self.agent("a", ctx_tokens=20_000)
        for t in "xyz":
            self.sw("a", "task", "add", t)
        self.sw("a", "task", "claim", "1")
        self.assertIn("take the next task", self.sw("a", "task", "done", "1", "--evidence", "e").stdout)
        self.q("update agent set ctx_tokens=120000")
        self.sw("a", "task", "claim", "2")
        self.assertIn("go idle", self.sw("a", "task", "done", "2", "--evidence", "e").stdout)

    def test_pr_ci_merge_to_green(self):
        self.fakes()
        self.agent("a")
        self.sw("a", "task", "add", "t1"); self.sw("a", "task", "claim", "1")
        self.sw("a", "task", "done", "1", "--evidence", "PR #7 merged")
        self.set_gh("pr", [{"number": 7, "mergedAt": "2026-11-08T10:00:00Z", "mergeCommit": {"oid": "red"}, "headRefName": "a/x"}])
        for i, (sha, concl, cr, up) in enumerate([("red", "failure", "2026-11-08T10:00:05Z", "2026-11-08T10:02:00Z"),
                                                  ("fix", "success", "2026-11-08T10:05:00Z", "2026-11-08T10:08:00Z")]):
            self.q("insert into ci(id,sha,status,conclusion,created,updated) values(?,?,'completed',?,?,?)", i + 1, sha, concl, cr, up)
        prs = lambda: [x for x in self.calls("gh") if x.startswith("pr ")]
        self.sw("a", "watchd", "--once", "--ci")
        t = json.loads(self.sw("a", "state", "--json").stdout)["tasks"][0]
        self.assertEqual((t["pr"], t["ci_conclusion"], t["merge_to_green_s"]), (7, "failure", 480))
        self.assertIn("PR #7 merged", self.sw("a", "task", "show", "1").stdout)
        self.assertEqual(len(prs()), 1)  # runs come from the ci table, not GitHub
        self.sw("a", "watchd", "--once", "--ci")
        self.assertEqual(len(prs()), 1)  # the PR list is asked for at most every 10 minutes

    def test_ci_poll_once_for_all(self):
        self.fakes()
        self.agent("a")
        self.set_gh("api", [{"databaseId": 1, "headSha": "a1", "status": "completed", "conclusion": "failure", "url": "u1",
                             "createdAt": "2026-11-08T10:00:00Z", "updatedAt": "2026-11-08T10:03:00Z"}])
        self.set_gh("run", "server, e2e\n")
        subs = lambda: [x.split()[0] for x in self.calls("gh") if x.startswith("api") or "--json jobs" in x]  # the poll's own calls
        self.sw("a", "watchd", "--once", "--ci")
        self.assertEqual(subs(), ["api", "run"])  # one request for the runs, one for the red run's jobs
        self.assertEqual(tuple(self.q("select conclusion, failed from ci where id=1")[0]), ("failure", "server, e2e"))
        self.sw("a", "watchd", "--once", "--ci")
        self.assertEqual(len(subs()), 2)  # within the minute: no call
        self.q("update meta set v='0' where k='ci_polled'")
        self.set_gh("api", None)  # rate limited
        self.sw("a", "watchd", "--once", "--ci")
        self.assertEqual(len(self.q("select 1 from ci")), 1)  # kept
        self.assertTrue(self.q("select 1 from meta where k='ci_error'"))

    def test_ci_reads_the_table(self):
        sha = lambda: subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.repo, capture_output=True, text=True).stdout.strip()
        commit = lambda: subprocess.run([*G, "commit", "-q", "--allow-empty", "-m", "c"], cwd=self.repo, check=True)
        c1 = sha(); commit(); c2 = sha(); commit(); c3 = sha()
        self.sw("a", "join")
        self.assertEqual(self.sw("a", "ci", c1, "--wait", "--timeout", "2", "--poll", "1", ok=False).stderr.count("nobody is polling"), 1)
        self.q("insert into meta(k,v) values('ci_polled',?)", str(int(time.time())))
        self.assertEqual(self.sw("a", "ci", c1, ok=False).returncode, 2)  # no run yet
        ins = lambda i, s, st, cc, t: self.q("insert into ci(id,sha,status,conclusion,url,created) values(?,?,?,?,'u',?)", i, s, st, cc, t)
        ins(1, c2, "completed", "cancelled", "2026-11-08T10:00:00Z")  # replaced by the next push
        ins(2, c3, "in_progress", None, "2026-11-08T10:01:00Z")
        self.assertEqual(self.sw("a", "ci", c1, ok=False).returncode, 2)  # c3's run includes c1, still running
        self.q("update ci set status='completed', conclusion='failure', failed='e2e' where id=2")
        r = self.sw("a", "ci", c1, ok=False)
        self.assertEqual(r.returncode, 1)
        self.assertIn("failed: e2e", r.stdout)
        ins(3, c3, "completed", "success", "2026-11-08T10:05:00Z")  # a re-run, green
        self.assertEqual(self.sw("a", "ci", c2).returncode, 0)
        self.assertEqual(self.sw("a", "ci", c3, "--wait", "--timeout", "5").returncode, 0)

    def test_block_unblock(self):
        self.fakes()
        self.agent("a"); self.agent("t-comms")
        self.sw("a", "task", "add", "t1"); self.sw("a", "task", "claim", "1")
        self.sw("b", "task", "block", "1", "q?", ok=False)
        self.sw("a", "task", "block", "1", "which db?")
        self.assertIn("#1 blocked by a: which db?", self.sw("a", "board").stdout)
        self.q("update task set lease_until=1")
        for _ in range(2):
            self.sw("a", "watchd", "--once", "--comms", "t-comms", "--max-agents", "0")
        self.assertEqual(self.q("select state,owner from task")[0]["state"], "blocked")
        self.assertEqual(len(self.q("select 1 from msg where dest='t-comms' and body like '%which db?%'")), 1)
        self.sw("b", "task", "unblock", "1", ok=False)
        self.sw("t-comms", "task", "unblock", "1", "--answer", "sqlite")
        self.assertEqual(self.q("select state,owner from task")[0]["owner"], "a")
        self.assertEqual(self.q("select state from task")[0]["state"], "claimed")
        self.assertEqual(len(self.q("select 1 from msg where dest='a' and body like '%sqlite%'")), 1)

    def test_hc_blocked_marks_task(self):
        self.fakes()
        self.set_hc({"address": "h1", "status": "blocked"})
        self.agent("a", hc="h1", status="working"); self.agent("t-comms")
        self.sw("a", "task", "add", "t1", hc="h1"); self.sw("a", "task", "claim", "1", hc="h1")
        tick = lambda: self.sw("a", "watchd", "--once", "--comms", "t-comms", "--max-agents", "0")
        tick()
        self.assertEqual(self.q("select state from task")[0]["state"], "blocked")
        self.assertEqual(len(self.q("select 1 from msg where dest='t-comms'")), 1)  # one notice, not two
        self.set_hc({"address": "h1", "status": "working"})
        tick()
        self.assertEqual(self.q("select state from task")[0]["state"], "claimed")

    def test_after_dependency(self):
        self.agent("a")
        self.sw("a", "task", "add", "first"); self.sw("a", "task", "add", "second", "--after", "1")
        self.assertIn("after #1", self.sw("a", "board").stdout)
        r = self.sw("a", "task", "claim", "2", ok=False)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("waits on #1", r.stderr)
        self.sw("a", "task", "claim", "1"); self.sw("a", "task", "done", "1", "--evidence", "e")
        self.sw("a", "task", "claim", "2")

    def test_deps_migration(self):
        c = sqlite3.connect(self.db)  # a task.after from before task.deps
        c.executescript("create table task(id integer primary key, title text, body text, state text default 'open', owner text,"
                        " lease_until int, created_by text, evidence text, after int);"
                        "insert into task(title) values('one'); insert into task(title,after) values('two',1);")
        c.close()
        self.agent("a")
        self.assertEqual([r[0] for r in self.q("select deps from task")], [None, "1"])
        self.assertNotIn("after", [r[1] for r in self.q("pragma table_info(task)")])
        self.assertIn("after #1  two", self.sw("a", "board").stdout)

    def test_deps_list_holds_until_last_done(self):
        self.fakes()
        self.agent("a")
        for t in ("one", "two", "three"):
            self.sw("a", "task", "add", t)
        self.sw("a", "task", "add", "four", "--after", "3,1")
        self.assertEqual(self.q("select deps from task where id=4")[0][0], "3,1")

        def check(ready):
            ts = json.loads(self.sw("a", "state", "--json").stdout)["tasks"]
            self.assertEqual(sorted(t["id"] for t in ts if t["state"] == "open" and not t["waiting"]), ready)
            if 4 not in ready:
                self.assertIn("waits on", self.sw("a", "task", "claim", "4", ok=False).stderr)
                self.assertIn("waits on", self.sw("a", "spawn", "t-9", "--task", "4", ok=False).stderr)
        check([1, 2, 3])
        for tid, ready in ((1, [2, 3]), (2, [3]), (3, [4])):
            self.sw("a", "task", "claim", str(tid)); self.sw("a", "task", "done", str(tid), "--evidence", "e")
            check(ready)
        self.assertIn("after: #3 done, #1 done", self.sw("a", "task", "show", "4").stdout)
        self.sw("a", "task", "claim", "4")
        self.assertIn("no task #9", self.sw("a", "task", "add", "x", "--after", "1,9", ok=False).stderr)

    def test_task_after_cycle_and_lines(self):
        self.agent("a")
        for t in ("one", "two", "three"):
            self.sw("a", "task", "add", t)
        self.sw("a", "task", "after", "2", "1")
        self.sw("a", "task", "after", "3", "2,1")
        r = self.sw("a", "task", "after", "1", "3", ok=False)
        self.assertIn("#1 → #3 → #2 → #1", r.stderr)
        self.assertIn("#1 → #1", self.sw("a", "task", "after", "1", "1", ok=False).stderr)
        self.assertIn("after #1  two", self.sw("a", "board").stdout)
        show = self.sw("a", "task", "show", "1").stdout
        self.assertIn("blocks: #2, #3", show)
        self.assertNotIn("after:", show)
        self.assertIn("after: #2 open, #1 open", self.sw("a", "task", "show", "3").stdout)
        s = {t["id"]: t for t in json.loads(self.sw("a", "state", "--json").stdout)["tasks"]}
        self.assertEqual((s[3]["deps"], s[1]["blocks"], s[3]["blocks"]), ([2, 1], [2, 3], []))
        out = self.sw("a", "task", "drop", "1").stdout
        self.assertIn("#2 waits on #1: drop it too, or `swarm task after 2 …`", out)
        self.assertIn("#3 waits on #1", out)
        self.assertIn("after #2, #1 (dropped)  three", self.sw("a", "board").stdout)  # still held back
        self.sw("a", "task", "after", "3", "")  # cleared
        self.assertEqual(self.q("select deps from task where id=3")[0][0], "")
        self.sw("a", "task", "claim", "2", ok=False)
        self.sw("a", "task", "claim", "3")
        self.assertIn("is claimed", self.sw("a", "task", "after", "3", "2", ok=False).stderr)

    def test_auto_spawn_once_within_cap(self):
        self.fakes()
        for n in ("t-comms", "t-1"):
            self.agent(n, status="working", model="haiku")
        self.sw("a", "task", "add", "do it")
        tick = lambda cap: self.sw("a", "watchd", "--once", "--comms", "t-comms", "--max-agents", str(cap), "--min-free-mem", "0")
        spawned = lambda: [(x["argv"][0], x["argv"][x["argv"].index("--model") + 1]) for x in self.launched()]
        tick(1)
        self.assertEqual(spawned(), [])  # at the cap
        tick(2)
        self.assertEqual(spawned(), [("t-2", "haiku")])
        self.assertEqual(self.q("select owner,state from task")[0]["owner"], "t-2")
        self.assertTrue(self.q("select first_claimed_at from task")[0][0])  # auto-spawn stamps the claim time
        tick(2)
        self.assertEqual(len(spawned()), 1)  # the task is claimed: no second spawn

    def fake_launch(self, log, rec, fail=False):
        real = self.mod().run  # only launch.sh is faked; git etc. run for real

        def run(cmd, **kw):
            if "launch.sh" not in cmd[0]:
                return real(cmd, **kw)
            if rec:
                log.append(rec(cmd))
            return None if fail else "hc1"
        return run

    def test_spawn_task_claims_before_launch(self):
        self.fakes()
        self.sw("a", "task", "add", "do it")
        self.sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1")
        self.assertEqual([x["task"] for x in self.launched()], [[["t-9", "claimed"]]])  # claimed by the new name before launch ran
        self.assertEqual(self.q("select hc from agent where name='t-9'")[0][0], "hc1")
        self.assertIn("live agent", self.sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1", ok=False).stderr)  # a live name is refused

    def test_spawn_launch_failure_keeps_live_agent(self):
        self.fakes(); self.set_hc({"name": "t-9", "address": "t7"})
        open(os.path.join(self.d, "launch.fail"), "w").close()
        self.sw("a", "task", "add", "do it")
        self.sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1")
        self.assertEqual(tuple(self.q("select owner,state from task")[0]), ("t-9", "claimed"))
        self.assertEqual(self.q("select hc from agent where name='t-9'")[0][0], "t7")

    def test_launch_sh_survives_failure_after_hc_run(self):
        fb = os.path.join(self.d, "lfb"); os.makedirs(fb)
        j = json.dumps({"spaces": [{"id": "s", "tabs": [{"id": "b", "terminals": [{"terminal": "t1"}]}]}]})
        for n, body in (("hc", "echo '{\"address\": \"t5\"}'"), ("herdr-app", f"[ \"$1\" = ls ] && echo '{j}' || exit 1")):
            open(os.path.join(fb, n), "w").write("#!/bin/sh\n" + body + "\n"); os.chmod(os.path.join(fb, n), 0o755)
        sh = os.path.join(os.path.dirname(__file__), "..", "relaunch", "launch.sh")
        r = subprocess.run([sh, "x", "tab", "task"], capture_output=True, text=True,
                           env={**os.environ, "PATH": fb + ":" + os.environ["PATH"], "HC_TERMINAL_ID": "t1"})
        self.assertEqual((r.returncode, r.stdout.strip().splitlines()[-1:]), (0, ["t5"]), r.stderr)

    def test_spawn_task_launch_failure_rolls_back(self):
        self.fakes()
        open(os.path.join(self.d, "launch.fail"), "w").close()
        self.sw("a", "task", "add", "do it")
        self.sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1", ok=False)
        self.assertEqual(tuple(self.q("select owner,state from task")[0]), (None, "open"))
        self.assertTrue(self.q("select ended from agent where name='t-9'")[0][0])

    @unittest.skipUnless(PY, "needs the Python module: a race or a pure function, a Lua spec instead")
    def test_auto_spawn_skips_lost_race(self):
        m = self.mod()
        launched = []
        m.run = self.fake_launch(launched, lambda cmd: cmd)
        m.hc_terminals = lambda: None
        c = m.connect()
        self.agent("t-comms", status="working")
        self.sw("a", "task", "add", "do it")
        real = m.pool
        m.pool = lambda c: (lambda r: (self.sw("t-1", "join"), self.sw("t-1", "task", "claim", "1"), r)[2])(real(c))  # a peer claims after pool()
        cwd = os.getcwd(); os.chdir(self.repo)
        try:
            m.watchd_tick(c, "t-comms", None, {"max_agents": 1, "min_free_gib": 0})
        finally:
            os.chdir(cwd)
        self.assertEqual(launched, [])
        self.assertEqual(self.q("select owner from task")[0][0], "t-1")

    def test_rules_appended_to_spawn(self):
        self.fakes()
        self.assertEqual(self.sw("a", "rules", "set", "never", "edit", "main").stdout.strip(), "never edit main")
        self.sw("a", "spawn", "t-9", "--model", "haiku", "--", "go")
        self.assertIn("never edit main", self.launched()[0]["argv"][2])

    # ---- cold-cache rule ----
    def sendmsg(self, to, text="hi"):
        return self.hook("a", "pre-tool", tool_name="SendMessage", tool_input={"to": to, "message": text})

    def test_cold_cache_cheap_cases_and_cold(self):
        self.agent("a")
        t = int(time.time())
        cold = dict(status="idle", ctx_tokens=140_000, last_active=t - 72 * 60, compacted_at=0)
        cheap = {
            "working": dict(cold, status="working"),
            "warm": dict(cold, last_active=t - 10 * 60),
            "compacted": dict(cold, compacted_at=t - 60),
            "small": dict(cold, ctx_tokens=30_000),
        }
        for n, kw in cheap.items():
            self.agent(n, **kw)
            self.assertEqual(self.sendmsg(n), {}, n)
        self.agent("cold", **cold)
        out = self.sendmsg("cold")
        self.assertEqual(out["permissionDecision"], "deny")
        self.assertIn("idle 72 min", out["permissionDecisionReason"])
        self.assertIn("140k", out["permissionDecisionReason"])
        self.assertEqual(self.q("select path from event where kind='deny-cold'")[0]["path"], "cold")
        self.assertEqual(self.sendmsg("nobody-we-know"), {})  # not a member
        # post to a cold agent is stored without a wake
        r = self.sw("a", "post", "cold", "later")
        self.assertIn("held, cold", r.stdout)
        # wait: non-urgent stays held, [urgent] wakes (exit 2)
        w = self.sw("cold", "wait", "--timeout", "2", "--poll", "0.2", ok=False)
        self.assertEqual(w.returncode, 0)

    def test_session_turns_keep_cache_warm(self):
        self.agent("a")
        t = int(time.time())
        self.fakebin = os.path.join(self.d, "fb"); os.makedirs(self.fakebin)
        hc = os.path.join(self.fakebin, "hc")
        open(hc, "w").write(f"#!/bin/sh\necho '{{\"status_ms\": {(t - 60) * 1000}}}'\n")
        os.chmod(hc, 0o755)
        kw = dict(status="idle", ctx_tokens=140_000, last_active=t - 4 * 3600, compacted_at=0)
        self.agent("comms", hc="t1", **kw)
        self.agent("nohc", **kw)
        self.assertEqual(self.sendmsg("comms"), {})
        self.assertEqual(self.sendmsg("nohc")["permissionDecision"], "deny")
        who = self.sw("a", "who").stdout
        self.assertRegex(who, r"comms idle .*idle=1m cache=warm(?! COLD)")
        self.assertRegex(who, r"nohc idle .*cache=cold COLD-GUARDED")

    def test_wait_fenced_join_rebinds_dead_hc(self):
        self.agent("a")
        t = int(time.time())
        self.fakebin = os.path.join(self.d, "fb"); os.makedirs(self.fakebin)
        hc = os.path.join(self.fakebin, "hc")
        open(hc, "w").write(f"#!/bin/sh\n[ \"$1\" = ls ] && echo '{{\"terminals\": []}}' && exit; [ \"$2\" = new ] && echo '{{\"status_ms\": {(t - 60) * 1000}}}' || echo '{{}}'\n")
        os.chmod(hc, 0o755)
        self.agent("comms", hc="dead", status="idle", ctx_tokens=140_000, last_active=t - 4 * 3600, compacted_at=0)
        self.sw("a", "post", "comms", "later")
        w = self.sw("comms", "wait", "--timeout", "2", "--poll", "0.2", ok=False)
        self.assertEqual(w.returncode, 3)  # outside Herdr while bound to "dead": fenced
        self.assertEqual(self.sw("comms", "wait", "--timeout", "1", hc="new", ok=False).returncode, 3)  # fenced: no rebind
        self.assertEqual(self.q("select hc from agent where name='comms'")[0]["hc"], "dead")
        self.sw("comms", "join", hc="new")  # hc ls doesn't show dead live: join moves it without --takeover
        w = self.sw("comms", "wait", "--timeout", "3", "--poll", "0.2", ok=False, hc="new")
        self.assertEqual(w.returncode, 2)
        self.assertIn("later", w.stderr)
        self.assertEqual(self.q("select hc from agent where name='comms'")[0]["hc"], "new")

    def test_urgent_override(self):
        self.agent("a")
        t = int(time.time())
        self.agent("cold", status="idle", ctx_tokens=140_000, last_active=t - 4000, compacted_at=0)
        self.assertEqual(self.sendmsg("cold", "[urgent] main is red"), {})
        self.sw("a", "post", "cold", "--urgent", "stop pushing")
        w = self.sw("cold", "wait", "--timeout", "3", "--poll", "0.2", ok=False)
        self.assertEqual(w.returncode, 2)
        self.assertIn("stop pushing", w.stderr)
        self.assertEqual(self.q("select data from event where kind='wake'")[0]["data"], "1 msg urgent")

    def test_wait_wakes_warm_idle(self):
        self.agent("a"); self.agent("b")
        self.sw("a", "post", "b", "ping")
        w = self.sw("b", "wait", "--timeout", "3", "--poll", "0.2", ok=False)
        self.assertEqual(w.returncode, 2)
        self.assertIn("ping", w.stderr)

    def test_prompt_hook_delivers_and_stops_waiter(self):
        self.agent("a"); self.agent("b")
        w = subprocess.Popen([SWARM, "wait", "--timeout", "10", "--poll", "0.2"],
                             env={**{k: v for k, v in os.environ.items() if k != "HC_TERMINAL_ID"}, "SWARM_DB": self.db, "SWARM_NAME": "b"},
                             stderr=subprocess.PIPE, text=True)
        time.sleep(1)
        out = self.hook("b", "prompt", prompt="hi")  # turn without a tool call: status -> working
        self.assertEqual(out, {})
        self.assertEqual(w.wait(timeout=5), 0)  # old waiter exits; no double delivery
        self.sw("a", "post", "b", "while idle")
        self.assertIn("while idle", self.hook("b", "prompt", prompt="x")["additionalContext"])
        self.assertIn("no unread", self.sw("b", "read").stdout)

    def test_newest_waiter_owns_inbox(self):
        self.agent("a"); self.agent("b")
        env = {**os.environ, "SWARM_DB": self.db, "SWARM_NAME": "b"}
        cmd = [SWARM, "wait", "--timeout", "10", "--poll", "0.2"]
        w1 = subprocess.Popen(cmd, env=env, stderr=subprocess.PIPE, text=True)
        time.sleep(0.8)
        w2 = subprocess.Popen(cmd, env=env, stderr=subprocess.PIPE, text=True)
        time.sleep(0.8)
        self.assertEqual(w1.wait(timeout=5), 0)  # superseded without ever seeing 'working'
        self.assertIn("wakes", self.sw("a", "post", "b", "ping").stdout)
        self.assertEqual(w2.wait(timeout=5), 2)
        self.assertIn("ping", w2.stderr.read())
        self.assertIn("no live waiter", self.sw("a", "post", "b", "again").stdout)

    def test_post_to_comms_has_no_sendmessage_nudge(self):
        self.agent("a"); self.agent("x-comms", status="idle", last_active=int(time.time()))
        out = self.sw("a", "post", "x-comms", "hi").stdout
        self.assertNotIn("nudge by SendMessage", out)
        self.assertIn("held", out)
        self.agent("b", status="idle", last_active=int(time.time()))
        self.assertIn("nudge by SendMessage", self.sw("a", "post", "b", "hi").stdout)

    def test_sendmessage_ref_and_hookless_waiter(self):
        self.agent("a")
        t = int(time.time())
        self.agent("cold", status="idle", ctx_tokens=140_000, last_active=t - 4000, compacted_at=0)
        out = self.sendmsg("cold [ab12]")
        self.assertEqual(out["permissionDecision"], "deny")
        self.sw("c", "join")  # no hooks: idle, ctx 0 counts as cheap
        self.sw("a", "post", "c", "inbox")
        w = self.sw("c", "wait", "--timeout", "3", "--poll", "0.2", ok=False)
        self.assertEqual(w.returncode, 2)
        self.assertIn("inbox", w.stderr)

    def test_stop_hook_records_ctx(self):
        self.agent("a")
        tr = os.path.join(self.d, "t.jsonl")
        open(tr, "w").write(json.dumps({"type": "assistant", "message": {"usage": {
            "input_tokens": 10, "cache_read_input_tokens": 90000, "cache_creation_input_tokens": 500}}}) + "\n")
        self.hook("a", "stop", transcript_path=tr)
        r = self.q("select status,ctx_tokens from agent where name='a'")[0]
        self.assertEqual((r["status"], r["ctx_tokens"]), ("idle", 90510))
        self.hook("a", "session", source="compact", transcript_path=tr)
        self.assertGreater(self.q("select compacted_at from agent where name='a'")[0][0], 0)

    def test_board_who(self):
        self.agent("a")
        self.sw("a", "task", "add", "do it")
        self.assertIn("do it", self.sw("a", "board").stdout)
        self.assertIn("a idle", self.sw("a", "who").stdout)

    def test_state_json(self):
        self.assertEqual(json.loads(self.sw("a", "state", "--json").stdout)["active"], False)
        self.assertFalse(os.path.exists(self.db))  # read-only: no db is created
        self.agent("a", model="opus", ctx_tokens=90_000)
        self.agent("b")
        self.sw("a", "task", "add", "first")
        self.sw("a", "task", "add", "second", "--after", "1")
        self.sw("a", "task", "claim", "1")
        self.sw("a", "task", "block", "1", "which db?")
        self.sw("b", "lock", "b.txt")
        self.sw("a", "post", "b", "hello")
        self.sw("b", "leave")
        before = self.q("select count(*) n from event")[0]["n"]
        s = json.loads(self.sw("a", "state", "--json").stdout)
        self.assertEqual(self.q("select count(*) n from event")[0]["n"], before)
        self.assertTrue(s["active"])
        t1, t2 = s["tasks"]
        self.assertEqual((t1["state"], t1["owner"], t1["question"]), ("blocked", "a", "which db?"))
        self.assertGreater(t1["lease_left"], 0)
        self.assertTrue(t2["waiting"])
        a, b = s["agents"]
        self.assertEqual((a["name"], a["status"], a["model"], a["ctx_tokens"], a["cache"]), ("a", "blocked", "opus", 90_000, "warm"))
        self.assertEqual(a["task"]["id"], 1)
        self.assertEqual(a["messages"][0]["body"], "hello")
        self.assertEqual((b["name"], b["status"]), ("b", "ended"))
        self.assertEqual(s["messages"][0]["dest"], "b")
        self.assertIn("block", [e["kind"] for e in s["events"]])
        self.assertIn("machine", s)
        self.sw("a", "post", "b", "x" * 5000)
        s = json.loads(self.sw("a", "state", "--json").stdout)
        self.assertEqual(len(s["messages"][0]["body"]), 500)  # long bodies (briefs) are cut

    def test_state_json_round2(self):
        self.agent("a")
        self.q("update agent set status='idle', last_active=1000 where name='a'")
        self.q("update agent set wt=? where name='a'", self.repo)
        self.hook("a", "post-tool", tool_name="Bash", tool_input={"command": "git push"}, cwd=self.repo)
        self.q("update agent set status='idle', last_active=1000 where name='a'")
        self.q("insert or replace into event(ts,agent,kind,data) values(1,'a','push','git push old')")
        self.q("insert or replace into meta(k,v) values('comms','sr-comms')")
        s = json.loads(self.sw("a", "state", "--json").stdout)
        a = s["agents"][0]
        self.assertEqual((s["comms"], a["branch"], a["cold_at"]), ("sr-comms", "main", 1000 + 55 * 60))
        pushes = [e for e in s["events"] if e["kind"] == "push"]
        self.assertEqual((pushes[0]["branch"], pushes[0]["subject"]), (None, None))  # older event
        self.assertEqual((pushes[1]["branch"], pushes[1]["subject"]), ("main", "init"))
        subprocess.run([*G, "commit", "-q", "--allow-empty", "-m", "wt work"], cwd=self.wt, check=True)
        for cmd in (f"cd {self.wt} && git push", f"git -C '{self.wt}' push", "cd ../wt; git push -u origin w2"):
            self.hook("a", "post-tool", tool_name="Bash", tool_input={"command": cmd}, cwd=self.repo)
        s = json.loads(self.sw("a", "state", "--json").stdout)
        pushes = [e for e in s["events"] if e["kind"] == "push"][:3]  # newest first
        self.assertEqual([(e["branch"], e["subject"]) for e in pushes], [("w2", "wt work")] * 3)  # the worktree's

    def test_state_json_view(self):
        self.agent("a", wt=self.wt)
        self.agent("b")
        self.sw("a", "task", "add", "t")
        self.sw("b", "lock", "b.txt")
        self.sw("a", "post", "b", "hi")
        self.sw("b", "leave")
        st = lambda *v: json.loads(self.sw("a", "state", "--json", *v).stdout)
        head = {"active", "db", "now", "view", "comms", "tasks", "agents", "conflicts", "pressure", "machine"}
        for view, extra in {"board": set(), "activity": {"messages", "events"}, "system": {"events", "locks", "running"},
                            "overview": {"messages", "events"}, "agents": set()}.items():
            s = st("--view", view)
            self.assertEqual(set(s), head | extra, view)
            a, b = s["agents"]
            self.assertNotIn("messages", a)  # per-agent messages only for --agent
            self.assertEqual("events" in a, view in ("overview", "agents", "system"), view)  # live lanes
            self.assertNotIn("events", b)  # ended and not asked for
        self.assertEqual(st("--view", "board")["tasks"][0]["title"], "t")
        a, b = st("--view", "agents", "--agent", "b")["agents"]
        self.assertEqual((b["messages"][0]["body"], a["branch"]), ("hi", "w2"))  # w2: read from the worktree's HEAD
        self.assertIn("leave", [e["kind"] for e in b["events"]])
        full = st()
        self.assertEqual(full["view"], None)
        self.assertIn("locks", full["agents"][1])  # no --view: everything, as before
        for i in range(80):
            self.q(f"insert into event(ts,agent,kind,data) values({i},'a','claim','#{i}')")
        self.assertGreater(len(st("--view", "activity")["events"]), 80)  # Activity reads further back
        self.assertEqual(len(st("--view", "overview")["events"]), 60)

    def test_state_json_running(self):
        pr = self.fake_proc()
        self.hook("a", "session")
        self.q("update agent set claude_pid=100 where name='a'")
        self.add_proc(pr, 100, 1, "claude", ["claude"])
        self.add_proc(pr, 102, 100, "cabal", ["/x/bin/cabal", "build"], rss_pages=1_000_000 // 4, age_s=125)
        self.add_proc(pr, 200, 1, "node", ["node", "/x/bin/tsc", "-b"], rss_pages=500_000 // 4)
        st = lambda *v: json.loads(self.swp("a", pr, "state", "--json", *v).stdout)
        r = st("--view", "system")["running"]
        self.assertEqual([(j["agent"], j["command"], j["elapsed_s"], j["rss_kb"]) for j in r],
                         [("a", "cabal build", 125, 1_000_000), ("other session", "tsc -b", 240, 500_000)])
        self.assertNotIn("running", st("--view", "board"))

    def test_state_json_hc_only_where_shown(self):
        t = int(time.time())
        self.fakebin = os.path.join(self.d, "fb"); os.makedirs(self.fakebin)
        log = os.path.join(self.d, "hc.log")
        open(os.path.join(self.fakebin, "hc"), "w").write(f"#!/bin/sh\necho \"$2\" >> {log}\necho '{{}}'\n")
        os.chmod(os.path.join(self.fakebin, "hc"), 0o755)
        kw = dict(status="idle", last_active=t - 4 * 3600)
        self.agent("live", hc="t-live", **kw)
        self.agent("gone", hc="t-gone", **kw)
        self.q("update agent set ended=? where name='gone'", t)
        calls = lambda: open(log).read().split() if os.path.exists(log) else []
        self.sw("a", "state", "--json", "--view", "board")
        self.assertEqual(calls(), [])  # board shows no idle timers
        self.sw("a", "state", "--json")
        self.assertEqual(calls(), ["t-live"])  # never an ended agent's terminal

    def test_state_json_old_db(self):
        c = sqlite3.connect(self.db)  # schema from before agent.wt / task.after,model,question
        c.executescript("create table agent(name text primary key, hc text, model text, cwd text, status text, last_active int,"
                        " ctx_tokens int default 0, compacted_at int default 0, started int, ended int, snap text, waiter int);"
                        "create table task(id integer primary key, title text, body text, state text, owner text, lease_until int,"
                        " created_by text, evidence text);"
                        "create table msg(id integer primary key, ts int, frm text, dest text, body text, urgent int, kind text);"
                        "create table event(id integer primary key, ts int, agent text, kind text, path text, data text);"
                        "insert into agent(name,status,last_active) values('a','idle',1);"
                        "insert into task(title,state) values('t','open');")
        c.close()
        s = json.loads(self.sw("a", "state", "--json").stdout)
        self.assertTrue(s["active"])
        self.assertEqual((s["agents"][0]["worktree"], s["tasks"][0]["waiting"]), (None, False))


    def fake_proc(self, avail_kb=20_000_000, psi=1.0):
        r = os.path.join(self.d, "proc")
        os.makedirs(os.path.join(r, "pressure"), exist_ok=True)
        open(os.path.join(r, "uptime"), "w").write("10000.0 0\n")
        open(os.path.join(r, "meminfo"), "w").write(f"MemTotal: 32000000 kB\nMemAvailable: {avail_kb} kB\n")
        for k in ("memory", "cpu"):
            open(os.path.join(r, "pressure", k), "w").write(f"some avg10={psi} avg60=0 avg300=0 total=0\n")
        return r

    def add_proc(self, r, pid, ppid, comm, argv, rss_pages=0, age_s=240, cwd=None):
        d = os.path.join(r, str(pid))
        os.makedirs(d, exist_ok=True)
        tck = os.sysconf("SC_CLK_TCK")
        f = ["S", str(ppid)] + ["0"] * 17 + [str(int((10000 - age_s) * tck)), "0", str(rss_pages)]
        open(os.path.join(d, "stat"), "w").write(f"{pid} ({comm}) " + " ".join(f))
        open(os.path.join(d, "cmdline"), "w").write("\0".join(argv) + "\0")
        open(os.path.join(d, "oom_score_adj"), "w").write("0")
        if cwd:
            os.symlink(cwd, os.path.join(d, "cwd"))

    def swp(self, who, proc, *args, stdin=None):
        env = {**os.environ, "SWARM_DB": self.db, "SWARM_NAME": who, "SWARM_PROC": proc}
        if getattr(self, "fakebin", None):
            env["PATH"] = self.fakebin + os.pathsep + env["PATH"]
        if getattr(self, "launch", None):
            env["SWARM_LAUNCH"] = self.launch
        return subprocess.run([SWARM, *args], env=env, input=stdin, capture_output=True, text=True, cwd=self.cwd[who])

    def hookp(self, who, proc, cmd):
        r = self.swp(who, proc, "hook", "pre-tool", stdin=json.dumps({"cwd": self.cwd[who], "tool_name": "Bash", "tool_input": {"command": cmd}}))
        self.assertEqual(r.returncode, 0, r.stderr)
        return json.loads(r.stdout)["hookSpecificOutput"] if r.stdout.strip() else {}

    def test_one_watchd(self):
        self.sw("a", "join")
        self.q("insert or replace into meta(k,v) values('watchd',?)", f"{os.getppid()} T1")  # a live pid
        r = self.sw("a", "watchd", "--once", ok=False)
        self.assertIn("already runs", r.stderr); self.assertIn("T1", r.stderr)
        self.sw("a", "watchd", "--once", "--takeover")
        self.assertNotIn("T1", self.q("select v from meta where k='watchd'")[0]["v"])

    def test_machine_note_and_patterns(self):
        pr = self.fake_proc()
        self.hook("a", "session"); self.hook("b", "session")
        self.q("update agent set claude_pid=100 where name='a'")
        self.add_proc(pr, 100, 1, "claude", ["claude"])
        self.add_proc(pr, 101, 100, "bash", ["bash", "-c", "x"])
        self.add_proc(pr, 102, 101, "cabal", ["/nix/store/x/bin/cabal", "build"], rss_pages=1_000_000 // 4)
        self.add_proc(pr, 200, 1, "node", ["node", "/x/bin/tsc", "-b"], rss_pages=500_000 // 4)  # not a swarm agent's
        self.add_proc(pr, 103, 101, "ghc-9.10.3", ["/s/ghc-9.10.3", "--make"], rss_pages=2_000_000 // 4)
        self.hookp("b", pr, "nix develop -c env TPG_SOCK=/m/.dev/.s.PGSQL.5432 cabal build")  # b starts one: logged
        o = self.hookp("a", pr, "nix develop -c env TPG_SOCK=/m/.dev/.s.PGSQL.5432 cabal build")
        self.assertNotIn("permissionDecision", o)
        n = o["additionalContext"]
        self.assertLessEqual(len(n.splitlines()), 6)
        self.assertIn("machine: 19.1/30.5G", n)
        self.assertRegex(n, r"running: ghc-9.10.3 --make .*\(a\)")
        self.assertIn("running: tsc -b", n); self.assertIn("(other session)", n)
        self.assertIn("started in the last 60s: b:", n)
        self.assertEqual(self.hookp("a", pr, "git commit -m 'make it'"), {})
        self.assertEqual(self.hookp("a", pr, "nix run .#dev"), {})
        for c in ("nix build .#server", "nix flake check", "spago build", "purs compile", "npx playwright test"):
            self.assertIn("machine:", self.hookp("a", pr, c)["additionalContext"], c)
        os.makedirs(os.path.join(self.repo, ".claude"))
        open(os.path.join(self.repo, ".claude", "swarm.json"), "w").write('{"heavy": ["\\\\bfoo-build\\\\b"]}')
        self.assertIn("machine:", self.hookp("a", pr, "foo-build all")["additionalContext"])

    def test_pressure_edge_oom_and_orphans(self):
        pr = self.fake_proc(avail_kb=2_000_000)  # 6% available: high
        self.hook("a", "session"); self.hook("b", "session")
        self.q("update agent set claude_pid=100 where name='a'")
        self.add_proc(pr, 100, 1, "claude", ["claude"])
        self.add_proc(pr, 102, 100, "cabal", ["cabal", "build"], rss_pages=1_000_000 // 4)
        # b is ended; its worktree holds a build reparented to init
        self.q("update agent set ended=1 where name='b'")
        self.add_proc(pr, 300, 1, "ghc-9.10.3", ["ghc-9.10.3", "--make"], rss_pages=3_000_000 // 4, cwd=self.wt)
        self.swp("a", pr, "watchd", "--once")
        ev = [r[0] for r in self.q("select kind from event where kind in ('pressure','pressure-end','orphan-kill') order by id")]
        self.assertEqual(ev, ["pressure", "orphan-kill"])
        notes = self.q("select dest,body from msg where kind='notice'")
        self.assertEqual([n[0] for n in notes], ["a"]); self.assertIn("ghc-9.10.3", notes[0][1])
        self.assertEqual(open(os.path.join(pr, "102", "oom_score_adj")).read(), "500")
        self.assertEqual(open(os.path.join(pr, "300", "oom_score_adj")).read(), "0")  # not an agent's: left alone
        # still high: no second notice (edge-triggered); leaves high: pressure-end
        self.swp("a", pr, "watchd", "--once")
        self.assertEqual(self.q("select count(*) from event where kind='pressure'")[0][0], 1)
        self.fake_proc(avail_kb=20_000_000)
        self.swp("a", pr, "watchd", "--once")
        self.assertEqual(self.q("select count(*) from event where kind='pressure-end'")[0][0], 1)

    def test_ci_red_is_one_task_closed_on_green(self):
        def commit(who):
            subprocess.run([*G, "commit", "-q", "--allow-empty", "-m", f"x\n\nSwarm-Agent: {who}"], cwd=self.repo, check=True)
        green = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.repo, capture_output=True, text=True).stdout.strip()
        commit("a"); commit("gone")
        red = subprocess.run(["git", "rev-parse", "HEAD"], cwd=self.repo, capture_output=True, text=True).stdout.strip()
        bindir = os.path.join(self.d, "bin"); os.makedirs(bindir)
        runs = [{"databaseId": 9, "headSha": red, "conclusion": "failure", "status": "completed", "url": "http://ci/9",
                 "createdAt": "2026-11-08T10:05:00Z", "updatedAt": "2026-11-08T10:08:00Z"},
                {"databaseId": 8, "headSha": green, "conclusion": "success", "status": "completed", "url": "http://ci/8",
                 "createdAt": "2026-11-08T10:00:00Z", "updatedAt": "2026-11-08T10:03:00Z"}]
        open(os.path.join(bindir, "gh"), "w").write(f"#!/bin/sh\n[ \"$1\" = api ] && echo '{json.dumps(runs)}' || echo 'step Build failed'\n")
        os.chmod(os.path.join(bindir, "gh"), 0o755)
        env = {**os.environ, "SWARM_DB": self.db, "SWARM_NAME": "a", "PATH": bindir + os.pathsep + os.environ["PATH"]}
        self.agent("a"); self.agent("gone", ended=1); self.agent("comms")
        go = lambda: subprocess.run([SWARM, "watchd", "--once", "--ci", "--comms", "comms"],
                                    env=env, capture_output=True, text=True, cwd=self.repo, check=True)
        self.sw("a", "task", "add", "earlier work")
        go(); go()  # second tick: edge-triggered
        m = self.q("select dest,body from msg where kind='system' order by id")
        self.assertEqual([x[0] for x in m], ["a"])
        self.assertIn("http://ci/9", m[0][1]); self.assertIn("swarm task claim 2", m[0][1])
        red_tasks = self.q("select id,body,state from task where title like 'main red:%'")
        self.assertEqual(len(red_tasks), 1); self.assertIn("Build failed", red_tasks[0][1])
        board = self.sw("a", "board").stdout
        self.assertLess(board.index("main red"), board.index("earlier work"))  # the red task starts first
        # a later red in the same stretch is the same task
        runs.insert(0, {**runs[0], "databaseId": 10, "createdAt": "2026-11-08T10:10:00Z"})
        open(os.path.join(bindir, "gh"), "w").write(f"#!/bin/sh\n[ \"$1\" = api ] && echo '{json.dumps(runs)}' || echo 'step Build failed'\n")
        self.q("delete from meta where k like 'ci%'")
        go()
        self.assertEqual(len(self.q("select 1 from task where title like 'main red:%'")), 1)
        self.assertEqual(len(self.q("select 1 from msg where kind='system'")), 1)
        self.assertIn("Later red: run 10", self.q("select body from task where id=2")[0][0])
        # the fixer's done keeps its claim; a re-run of the reds leaves an older green on top: still open
        self.sw("a", "task", "claim", "2")
        self.assertIn("stays yours", self.sw("a", "task", "done", "2", "--evidence", "abc").stdout)
        self.assertEqual(self.q("select state from task where id=2")[0][0], "claimed")
        rerun = [{**r, "status": "in_progress", "conclusion": None} if r["conclusion"] == "failure" else r for r in runs]
        open(os.path.join(bindir, "gh"), "w").write(f"#!/bin/sh\n[ \"$1\" = api ] && echo '{json.dumps(rerun)}' || echo 'step Build failed'\n")
        self.q("delete from meta where k like 'ci%'")
        go()
        self.assertEqual(self.q("select state from task where id=2")[0][0], "claimed")
        # green closes it, and tells its owner
        runs.insert(0, {**runs[0], "databaseId": 11, "conclusion": "success", "createdAt": "2026-11-08T10:20:00Z"})
        open(os.path.join(bindir, "gh"), "w").write(f"#!/bin/sh\n[ \"$1\" = api ] && echo '{json.dumps(runs)}' || echo 'step Build failed'\n")
        self.q("delete from meta where k like 'ci%'")
        go()
        self.assertEqual(self.q("select state,evidence from task where id=2")[0][:], ("done", f"green run 11 at {red[:7]}"))
        self.assertIn("is done; stop fixing it", self.q("select body from msg where dest='a' order by id desc limit 1")[0][0])
        # no live suspect: a new task, and comms hears of it
        self.q("update agent set ended=1 where name='a'"); self.q("delete from event where kind='ci-red'")
        runs.pop(0)
        open(os.path.join(bindir, "gh"), "w").write(f"#!/bin/sh\n[ \"$1\" = api ] && echo '{json.dumps(runs)}' || echo 'step Build failed'\n")
        self.q("delete from meta where k like 'ci%'"); self.q("delete from ci")
        go()
        self.assertEqual([x[0] for x in self.q("select dest from msg where kind='system' order by id")], ["a", "a", "comms"])
        self.assertEqual(len(self.q("select 1 from task where title like 'main red:%' and state='open'")), 1)

    # ---- swarm run ----
    def fake_remote(self, state="connected"):
        """Fake hc and ssh: the 'laptop' is a home dir here; rsync is real."""
        self.home = os.path.join(self.d, "laptop-home"); os.makedirs(self.home, exist_ok=True)
        self.fakebin = os.path.join(self.d, "fb"); os.makedirs(self.fakebin, exist_ok=True)
        self.hclog = os.path.join(self.d, "hc.log")
        m = json.dumps({"machines": [{"name": "laptop", "state": state, "target": "u@laptop"}]})
        open(os.path.join(self.fakebin, "hc"), "w").write(f"""#!{sys.executable}
import json, os, subprocess, sys
a, H, D = sys.argv[1:], {self.home!r}, {self.d!r}
open({self.hclog!r}, "a").write(" ".join(a) + "\\n")
env = {{**os.environ, "HOME": H}}
if a[:2] == ["machine", "ls"]: print({m!r})
elif a[0] == "ls": print('{{"terminals": []}}')
elif a[0] == "run":
    i = a.index("sh")
    rc = subprocess.run(a[i:], cwd=H, env=env, stdout=subprocess.DEVNULL).returncode
    open(D + "/rc", "w").write(str(rc)); print('{{"address": "laptop/t1"}}')
elif a[0] == "wait":
    if os.path.exists(D + "/lost"): sys.exit(3)
    print(json.dumps({{"ended": True, "exit_code": int(open(D + "/rc").read())}}))
elif a[0] == "exec":
    sys.stdout.write(subprocess.run(a[a.index("--timeout") + 2:], cwd=H, env=env, capture_output=True, text=True).stdout)
""")
        open(os.path.join(self.fakebin, "ssh"), "w").write(f"""#!/bin/sh
while [ "$1" = -o ] || [ "$1" = -l ]; do shift 2; done
shift; cd {self.home} && HOME={self.home} exec sh -c "$*"
""")
        for f in ("hc", "ssh"):
            os.chmod(os.path.join(self.fakebin, f), 0o755)

    def read(self, *p):
        return open(os.path.join(*p)).read()

    def test_run_remote_syncs_runs_and_brings_back(self):
        self.fake_remote()
        os.makedirs(os.path.join(self.wt, ".claude"))
        open(os.path.join(self.wt, ".claude", "swarm.json"), "w").write(json.dumps({"run": {
            "prefix": "env", "env": ["^APP_"], "set": {"T": "{dir}/target"}, "bring_back": ["out/"]}}))
        self.write("b", ".gitignore", "out/\nsecret.txt\n"); self.write("b", "secret.txt", "s")
        self.sw("b", "task", "add", "t"); self.sw("b", "task", "claim", "1")
        cmd = (f'echo "app=$APP_Y k=$K t=$T"; echo new > new.txt; echo job > a.txt; mkdir -p out; echo r > out/r.txt; '
               f'echo mine > {self.wt}/b.txt; echo theirs > b.txt; exit 3')
        os.environ["APP_Y"] = "2"
        try:
            r = self.sw("b", "run", "--on", "laptop", "--env", "K=1", "--", cmd, ok=False)
        finally:
            del os.environ["APP_Y"]
        self.assertEqual(r.returncode, 3, r.stderr)
        src = os.path.join(self.home, ".cache/swarm-run/repo/wt/src")
        self.assertIn(f"app=2 k=1 t={self.home}/.cache/swarm-run/repo/wt/target", r.stdout)
        self.assertRegex(r.stdout, r"job j1 exit 3 on laptop, 0m\d\ds \(sync [\d.]+s, back [\d.]+s\), tree [0-9a-f]{7}; log: ")
        self.assertFalse(os.path.exists(os.path.join(src, "secret.txt")))  # ignored files stay here
        self.assertEqual((self.read(self.wt, "new.txt"), self.read(self.wt, "a.txt"), self.read(self.wt, "out/r.txt")), ("new\n", "job\n", "r\n"))
        self.assertEqual(self.read(self.wt, "b.txt"), "mine\n")  # edited here during the job: kept, theirs beside the log
        self.assertEqual(self.read(self.d, "jobs", "1", "kept", "b.txt"), "theirs\n")
        self.assertIn("b.txt are in", r.stdout)
        ev = {k: json.loads(d) for k, d in self.q("select kind,data from event where kind like 'job-%'")}
        self.assertEqual((ev["job-start"]["machine"], ev["job-start"]["task"], ev["job-start"]["hc"]), ("laptop", 1, "laptop/t1"))
        self.assertEqual((ev["job-end"]["exit"], len(ev["job-end"]["tree"])), (3, 40))
        hc = self.read(self.hclog)
        self.assertIn("--label swarm-agent=b --label swarm-job=1 --label swarm-wt=repo/wt --label swarm-task=1", hc)
        self.assertIn("rm laptop/t1", hc)
        self.assertEqual([j for j in json.loads(self.sw("b", "state", "--json").stdout)["running"] if "machine" in j], [])

    def test_run_never_ran_or_lost_is_255(self):
        self.fake_remote(state="disconnected")
        r = self.sw("b", "run", "--on", "laptop", "--", "true", ok=False)
        self.assertEqual(r.returncode, 255)
        self.assertIn("laptop is disconnected; the job never ran", r.stderr)
        self.assertEqual(self.q("select count(*) from event where kind like 'job-%'")[0][0], 0)
        self.fake_remote()
        open(os.path.join(self.d, "lost"), "w").close()
        r = self.sw("b", "run", "--on", "laptop", "--", "true", ok=False)
        self.assertEqual(r.returncode, 255)
        self.assertIn("lost on laptop", r.stdout); self.assertIn("hc wait laptop/t1", r.stdout)
        self.assertEqual(json.loads(self.q("select data from event where kind='job-end'")[0][0])["exit"], "lost")

    def test_run_local_records_job(self):
        r = self.sw("b", "run", "--", "echo hi; exit 2", ok=False)
        self.assertEqual(r.returncode, 2)
        self.assertRegex(r.stdout, r"^hi\njob j1 exit 2 on this machine, .*tree [0-9a-f]{7}")
        self.assertEqual([k for (k,) in self.q("select kind from event where kind like 'job-%' order by id")], ["job-start", "job-end"])

    def test_run_note_state_and_cleanup(self):
        self.fake_remote()
        pr = self.fake_proc()
        self.agent("a")
        t = int(time.time())
        self.q("insert into meta values('machines',?)", json.dumps({
            "laptop": {"state": "connected", "ts": t, "cores": 24, "load": 3.5, "avail_kb": 80 * 2**20, "total_kb": 93 * 2**20, "psi": 0.0},
            "nas": {"state": "disconnected", "ts": t, "since": t - 600}}))
        d = ".cache/swarm-run/repo/wt"
        self.q("insert into event(ts,agent,kind,path,data) values(?,?,?,?,?)", t - 120, "a", "job-start", "1",
               json.dumps({"machine": "laptop", "hc": "laptop/t9", "wt": os.path.realpath(self.wt), "dir": d, "cmd": "cargo test -p x", "pid": 999999999}))
        n = self.hookp("a", pr, "swarm run --on laptop -- cargo test")["additionalContext"]  # swarm run is heavy
        self.assertIn("laptop: 80/93G available, load 3.5 on 24 cores, mem pressure 0%, jobs: a cargo test -p x 2m", n)
        self.assertIn("nas: disconnected since", n)
        run = json.loads(self.sw("a", "state", "--json").stdout)["running"]
        self.assertEqual([(j["machine"], j["job"], j["lost"]) for j in run if "machine" in j], [("laptop", "1", True)])  # swarm run gone, terminal gone
        # watchd's probe of each machine, only from a Herdr terminal
        env = {**os.environ, "SWARM_DB": self.db, "HC_TERMINAL_ID": "t1", "PATH": self.fakebin + os.pathsep + os.environ["PATH"]}
        subprocess.run([SWARM, "watchd", "--once"], env=env, cwd=self.repo, check=True, capture_output=True)
        lap = json.loads(self.q("select v from meta where k='machines'")[0][0])["laptop"]
        self.assertEqual(lap["state"], "connected"); self.assertGreater(lap["cores"], 0); self.assertGreater(lap["total_kb"], 0)
        # a landed worktree's dirs go on every machine its jobs used
        os.makedirs(os.path.join(self.home, d, "src"))
        self.idle("e", wt=self.wt)
        self.comms_tick()
        self.assertTrue(self.ended("e"))
        self.assertIn(f"exec --on laptop --timeout 120 rm -rf {d}", self.read(self.hclog))
        self.assertFalse(os.path.exists(os.path.join(self.home, d)))


if __name__ == "__main__":
    unittest.main()
