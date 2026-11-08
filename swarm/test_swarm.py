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


if __name__ == "__main__":
    unittest.main()
