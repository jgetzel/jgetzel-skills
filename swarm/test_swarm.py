import argparse
import sys; sys.dont_write_bytecode = True
import json, os, sqlite3, subprocess, sys, tempfile, time, unittest

SWARM = os.path.join(os.path.dirname(os.path.abspath(__file__)), "swarm")
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

    def sw(self, who, *args, stdin=None, ok=True):
        env = {**os.environ, "SWARM_DB": self.db, "SWARM_NAME": who}
        env.pop("HC_TERMINAL_ID", None)  # an agent's own terminal would make `hc ls` part of the test
        r = subprocess.run([sys.executable, SWARM, *args], env=env, input=stdin, capture_output=True,
                           text=True, cwd=self.cwd.get(who, self.repo))
        if ok:
            self.assertEqual(r.returncode, 0, r.stderr)
        return r

    def hook(self, who, ev, **payload):
        payload.setdefault("cwd", self.cwd[who])
        r = self.sw(who, "hook", ev, stdin=json.dumps(payload))
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
        self.assertIn("lease", self.sw("a", "read").stdout)
        # dead agent: hc terminal gone releases everything
        self.sw("a", "task", "claim", "1")
        self.sw("a", "lock", "b.txt")
        self.q("update agent set hc='t99' where name='a'")
        sys.path.insert(0, os.path.dirname(SWARM))
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_mod", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_mod", ld))
        ld.exec_module(m)
        os.environ["SWARM_DB"] = self.db
        c = m.connect()
        out = m.reap(c, live_addrs={"t1"})
        self.assertIn("agent a", out)
        self.assertEqual(self.q("select state from task")[0]["state"], "open")
        self.assertEqual(self.q("select * from lock"), [])
        self.assertIsNotNone(self.q("select ended from agent where name='a'")[0]["ended"])

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

    def test_handoff_nudge_once_until_compaction(self):
        self.agent("b")
        tr = os.path.join(self.cwd["b"], "t.jsonl")
        def usage(n):
            open(tr, "w").write(json.dumps({"type": "assistant", "message": {"usage": {"input_tokens": n}}}) + "\n")
        post = lambda: self.hook("b", "post-tool", tool_name="Read", tool_input={}, transcript_path=tr)
        usage(100_000)
        self.assertEqual(post(), {})
        usage(160_000)
        self.assertIn("relaunch", post()["additionalContext"])
        self.assertEqual(post(), {})
        self.q("update agent set compacted_at=? where name='b'", int(time.time()) + 5)
        self.assertIn("relaunch", post()["additionalContext"])

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

    def test_block_unblock(self):
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_mod4", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_mod4", ld))
        ld.exec_module(m)
        os.environ["SWARM_DB"] = self.db
        m.hc_terminals = lambda: None
        c = m.connect()
        self.agent("a"); self.agent("t-comms")
        self.sw("a", "task", "add", "t1"); self.sw("a", "task", "claim", "1")
        self.sw("b", "task", "block", "1", "q?", ok=False)
        self.sw("a", "task", "block", "1", "which db?")
        self.assertIn("#1 blocked by a: which db?", self.sw("a", "board").stdout)
        self.q("update task set lease_until=1")
        self.assertEqual(m.pool(c), [])
        m.reap(c, set(), comms="t-comms")
        self.assertEqual(self.q("select state,owner from task")[0]["state"], "blocked")
        cwd = os.getcwd(); os.chdir(self.repo)
        try:
            for _ in range(2):
                m.watchd_tick(c, "t-comms", None, {})
        finally:
            os.chdir(cwd)
        self.assertEqual(len(self.q("select 1 from msg where dest='t-comms' and body like '%which db?%'")), 1)
        self.sw("b", "task", "unblock", "1", ok=False)
        self.sw("t-comms", "task", "unblock", "1", "--answer", "sqlite")
        self.assertEqual(self.q("select state,owner from task")[0]["owner"], "a")
        self.assertEqual(self.q("select state from task")[0]["state"], "claimed")
        self.assertEqual(len(self.q("select 1 from msg where dest='a' and body like '%sqlite%'")), 1)

    def test_hc_blocked_marks_task(self):
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_mod5", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_mod5", ld))
        ld.exec_module(m)
        os.environ["SWARM_DB"] = self.db
        st = {"status": "blocked"}
        m.hc_terminals = lambda: [{"address": "h1", "state": "live", **st}]
        c = m.connect()
        self.agent("a", hc="h1", status="working"); self.agent("t-comms")
        self.sw("a", "task", "add", "t1"); self.sw("a", "task", "claim", "1")
        cwd = os.getcwd(); os.chdir(self.repo)
        try:
            m.watchd_tick(c, "t-comms", None, {})
            self.assertEqual(self.q("select state from task")[0]["state"], "blocked")
            self.assertEqual(len(self.q("select 1 from msg where dest='t-comms'")), 1)  # one notice, not two
            st["status"] = "working"
            m.watchd_tick(c, "t-comms", None, {})
        finally:
            os.chdir(cwd)
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

    def test_auto_spawn_once_within_cap(self):
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_mod3", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_mod3", ld))
        ld.exec_module(m)
        os.environ["SWARM_DB"] = self.db
        spawned = []
        m.cmd_spawn = lambda c, a: spawned.append((a.name, a.model))
        m.hc_terminals = lambda: None
        c = m.connect()
        for n in ("t-comms", "t-1"):
            self.agent(n, status="working", model="haiku")
        self.sw("a", "task", "add", "do it")
        cwd = os.getcwd(); os.chdir(self.repo)
        try:
            opts = {"max_agents": 1, "min_free_gib": 0}
            m.watchd_tick(c, "t-comms", None, opts)
            self.assertEqual(spawned, [])  # at the cap
            opts["max_agents"] = 2
            m.watchd_tick(c, "t-comms", None, opts)
            self.assertEqual(spawned, [("t-2", "haiku")])
            self.assertEqual(self.q("select owner,state from task")[0]["owner"], "t-2")
            m.watchd_tick(c, "t-comms", None, opts)
            self.assertEqual(len(spawned), 1)  # the task is claimed: no second spawn
        finally:
            os.chdir(cwd)

    def test_auto_spawn_waits_one_interval(self):
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_mod6", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_mod6", ld))
        ld.exec_module(m)
        os.environ["SWARM_DB"] = self.db
        spawned = []
        m.cmd_spawn = lambda c, a: spawned.append(a.name)
        m.hc_terminals = lambda: None
        c = m.connect()
        self.agent("t-comms", status="working")
        self.sw("a", "task", "add", "do it")
        cwd = os.getcwd(); os.chdir(self.repo)
        try:
            opts = {"max_agents": 1, "min_free_gib": 0}
            m.watchd_tick(c, "t-comms", None, opts)
            self.assertEqual(spawned, [])  # first sight of the task: no spawn
            self.sw("t-1", "join"); self.sw("t-1", "task", "claim", "1")  # an explicit spawn takes it
            m.watchd_tick(c, "t-comms", None, opts)
            self.assertEqual(spawned, [])
        finally:
            os.chdir(cwd)

    def test_rules_appended_to_spawn(self):
        import importlib.machinery, importlib.util
        ld = importlib.machinery.SourceFileLoader("swarm_mod7", SWARM)
        m = importlib.util.module_from_spec(importlib.util.spec_from_loader("swarm_mod7", ld))
        ld.exec_module(m)
        os.environ["SWARM_DB"] = self.db
        seen = []
        m.run = lambda cmd, **kw: seen.append(cmd[3]) or "hc1"
        c = m.connect()
        self.assertEqual(self.sw("a", "rules", "set", "never", "edit", "main").stdout.strip(), "never edit main")
        m.cmd_spawn(c, argparse.Namespace(name="t-9", model="haiku", task=["go"]))
        self.assertIn("never edit main", seen[0])

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
        w = subprocess.Popen([sys.executable, SWARM, "wait", "--timeout", "10", "--poll", "0.2"],
                             env={**os.environ, "SWARM_DB": self.db, "SWARM_NAME": "b"},
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
        cmd = [sys.executable, SWARM, "wait", "--timeout", "10", "--poll", "0.2"]
        w1 = subprocess.Popen(cmd, env=env, stderr=subprocess.PIPE, text=True)
        time.sleep(0.8)
        w2 = subprocess.Popen(cmd, env=env, stderr=subprocess.PIPE, text=True)
        time.sleep(0.8)
        self.assertEqual(w1.wait(timeout=5), 0)  # superseded without ever seeing 'working'
        self.assertIn("wakes", self.sw("a", "post", "b", "ping").stdout)
        self.assertEqual(w2.wait(timeout=5), 2)
        self.assertIn("ping", w2.stderr.read())
        self.assertIn("no live waiter", self.sw("a", "post", "b", "again").stdout)

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
        return subprocess.run([sys.executable, SWARM, *args], env=env, input=stdin, capture_output=True, text=True, cwd=self.cwd[who])

    def hookp(self, who, proc, cmd):
        r = self.swp(who, proc, "hook", "pre-tool", stdin=json.dumps({"cwd": self.cwd[who], "tool_name": "Bash", "tool_input": {"command": cmd}}))
        self.assertEqual(r.returncode, 0, r.stderr)
        return json.loads(r.stdout)["hookSpecificOutput"] if r.stdout.strip() else {}

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


if __name__ == "__main__":
    unittest.main()
