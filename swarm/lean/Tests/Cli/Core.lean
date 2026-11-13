import Tests.Cli.Fixture

/-! cli_core_spec.lua: tasks, terminal fencing, locks, messages, context notes, conflicts, roles. -/

namespace SwarmLean.Tests.Cli.Core
open SwarmLean.Tests.Cli
open Lean (Json toJson)

def state (t : T) : IO Json := do
  match Json.parse (← t.sw "a" ["state", "--json"]).stdout with
  | .ok j => return j
  | .error e => fail s!"state --json: {e}"
def count (s sub : String) : Nat := (s.splitOn sub).length - 1
def sid (p : String) : IO String := do
  return s!"{p}{← IO.Process.getPID}{← IO.monoNanosNow}{← IO.rand 0 1000000000}"
def nth (j : Json) (i : Nat) : Json := ((j.getArrVal? i).toOption).getD .null
def num (j : Json) : Float := match j with | .num n => n.toFloat | _ => -1
def okc (hc : String) : Opts := { hc := some hc }
def nok (hc : String) : Opts := { hc := some hc, ok := false }
def emptyObj : Json := Json.mkObj []

-- ---- tasks ----
def test_task_timing_columns (t : T) : IO Unit := do
  t.sw_ "a" ["task", "add", "t1"]
  t.sw_ "a" ["task", "claim", "1"]
  t.sw_ "a" ["task", "block", "1", "why"]
  t.sw_ "a" ["task", "unblock", "1"]
  has (← t.sw "a" ["task", "show", "1"]).stdout "claims 1, releases 0, held by a"
  t.sw_ "a" ["task", "done", "1", "--evidence", "e"]
  let r ← t.q1 "select created_at, first_claimed_at, done_at from task"
  unless num (r.f "created_at") ≤ num (r.f "first_claimed_at") ∧ num (r.f "first_claimed_at") ≤ num (r.f "done_at") do
    fail (repr r)
  let s := nth ((← state t).f "tasks") 0
  eq (json% [$(s.f "claims"), $(s.f "holders"), $(decide (num (s.f "blocked_s") ≥ 0))]) (json% [1, ["a"], true])
  -- an older db: columns null, numbers come from the events
  t.q_ "update task set created_at=null, first_claimed_at=null, done_at=null"
  t.q_ "update event set ts=ts-100 where kind='task-add'"
  let s := nth ((← state t).f "tasks") 0
  unless num (s.f "queue_wait_s") ≥ 100 do fail s!"{repr (s.f "queue_wait_s")}"

def test_timing_from_auto_spawn_event (t : T) : IO Unit := do
  t.sw_ "a" ["task", "add", "t1"]
  t.q_ "update task set state='done', owner='t-2', created_at=null"
  t.q_ "update event set ts=100 where kind='task-add'"
  t.q_ "insert into event(ts,agent,kind,data) values(160,'t-2','spawn','auto #1'),(400,'t-2','done','#1 e'),(5,'a','spawn','t-3')"
  let s := nth ((← state t).f "tasks") 0
  eq (json% [$(s.f "queue_wait_s"), $(s.f "work_s"), $(s.f "holders")]) (json% [60, 240, ["t-2"]])

def test_task_show_and_claim_print_body (t : T) : IO Unit := do
  t.sw_ "a" ["task", "add", "t1", "--body", "build X and Y"]
  t.sw_ "a" ["task", "add", "t2"]
  has (← t.sw "a" ["board"]).stdout "[body: task show]"
  has (← t.sw "b" ["task", "show", "1"]).stdout "build X and Y"
  has (← t.sw "a" ["task", "claim", "1"]).stdout "build X and Y"
  has (← t.sw "a" ["task", "show", "2"]).stdout "(no body)"

def test_release_reopens (t : T) : IO Unit := do
  t.sw_ "a" ["task", "add", "t1"]
  t.sw_ "a" ["task", "claim", "1"]
  unless (← t.sw "b" ["task", "release", "1"] { ok := false }).code ≠ 0 do fail "b released a's claim"
  t.sw_ "a" ["task", "release", "1"]
  eq ((← t.q1 "select state,owner from task").f "state") "open"
  t.sw_ "b" ["task", "claim", "1"]
  eq ((← t.q1 "select count(*) n from event where kind='release'").f "n") 1

def test_lock_denial_logged (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["lock", "a.txt"]
  has ((← t.edit "b" "a.txt").f "permissionDecisionReason") "locked"
  eq ((← t.q1 "select path,data from event where kind='deny-lock'").f "data") "a"

def test_claim_lease_done (t : T) : IO Unit := do
  t.sw_ "a" ["task", "add", "t1"]
  t.sw_ "a" ["task", "claim", "1"]
  unless (← t.sw "b" ["task", "claim", "1"] { ok := false }).code ≠ 0 do fail "b claimed a's task"
  eq (← t.sw "a" ["task", "done", "1"] { ok := false }).code 2
  t.sw_ "a" ["task", "renew", "1", "--lease", "3h"]
  for ev in ["", "  "] do  -- done needs evidence (swarm/model: doneHasEvidence)
    let r ← t.sw "a" ["task", "done", "1", "--evidence", ev] { ok := false }
    eq r.code 1
    has r.stderr "evidence"
  eq ((← t.q1 "select state from task").f "state") "claimed"
  t.sw_ "a" ["task", "done", "1", "--evidence", "sha abc"]
  eq ((← t.q1 "select state,evidence from task").f "state") "done"

def test_reaping (t : T) : IO Unit := do
  t.sw_ "a" ["task", "add", "t1"]
  t.sw_ "a" ["task", "claim", "1"]
  t.sw_ "b" ["join"]
  t.sw_ "a" ["lock", "a.txt"]
  t.q_ "update task set lease_until=1"
  t.q_ "update lock set lease_until=1"
  t.q_ "update agent set status='working' where name='a'"
  t.sw_ "a" ["watchd", "--once"]
  eq ((← t.q1 "select state from task").f "state") "claimed"  -- live working owner: claim stays
  t.q_ "update agent set ended=1 where name='a'"
  t.sw_ "a" ["watchd", "--once"]
  eq ((← t.q1 "select state from task").f "state") "open"
  eq (← t.q "select * from lock") (Json.arr #[])
  has (← t.sw "a" ["read"] { ok := false }).stderr "was ended"  -- ended: only join returns it
  t.sw_ "a" ["join"]
  has (← t.sw "a" ["read"]).stdout "lease"
  -- dead agent: hc terminal gone releases everything
  t.sw_ "a" ["task", "claim", "1"]
  t.sw_ "a" ["lock", "b.txt"]
  t.q_ "update agent set hc='t99' where name='a'"
  t.fakes; t.setHc [json% {"address": "t1"}]
  t.sw_ "a" ["watchd", "--once"]
  eq ((← t.q1 "select count(*) n from event where kind='reap' and data='agent gone'").f "n") 1
  eq ((← t.q1 "select state from task").f "state") "open"
  eq (← t.q "select * from lock") (Json.arr #[])
  unless (← t.q1 "select ended from agent where name='a'").f "ended" != .null do fail "agent a not ended"

-- ---- fencing on the bound terminal (sw-ownership §7.2) ----
def test_other_terminal_hook_and_wait_dont_rebind (t : T) : IO Unit := do
  t.sw_ "a" ["join"] (okc "t1")
  t.q_ "update agent set status='idle'"
  let out ← t.hook "a" "post-tool" (json% {"tool_name": "Bash", "tool_input": {"command": "ls"}}) (some "t2")
  has (out.f "additionalContext") "a is bound to t1; this terminal is t2. `swarm join --takeover`"
  eq (← t.hook "a" "prompt" emptyObj (some "t2")) emptyObj  -- said once per terminal
  eq (← t.q1 "select hc,status from agent") (json% {"hc": "t1", "status": "idle"})  -- wrote nothing
  let w ← t.sw "a" ["wait", "--timeout", "1"] (nok "t2")
  eq (json% [$(w.code), $(strip w.stderr)])
    (json% [3, "a is bound to t1; this terminal is t2. `swarm join --takeover` moves it here."])
  eq ((← t.q1 "select hc from agent").f "hc") "t1"
  has (← t.sw "a" ["task", "add", "x"] (nok "t2")).stderr "bound to t1"
  t.sw_ "a" ["task", "add", "x"] (okc "t1")
  t.sw_ "u" ["join"]  -- unbound row (outside Herdr): wait binds it
  t.sw_ "u" ["wait", "--timeout", "1"] (okc "t3")
  eq ((← t.q1 "select hc from agent where name='u'").f "hc") "t3"

def test_ended_agent_not_revived (t : T) : IO Unit := do
  t.sw_ "a" ["join"] (okc "t1")
  t.sw_ "a" ["leave"] (okc "t1")
  has ((← t.hook "a" "prompt" emptyObj (some "t1")).f "additionalContext") "a was ended at"
  discard <| t.hook "a" "stop" emptyObj (some "t1")
  let w ← t.sw "a" ["wait", "--timeout", "1"] (nok "t1")
  eq w.code 3; has w.stderr "swarm join` to return"
  eq (← t.q1 "select status, ended is not null e from agent") (json% {"status": "ended", "e": 1})
  has (← t.sw "a" ["lock", "a.txt"] (nok "t1")).stderr "swarm join` to return"
  t.sw_ "a" ["join"] (okc "t1")
  eq (← t.q1 "select status,ended from agent") (json% {"status": "idle"})

def test_join_refused_on_live_binding_takeover_moves_and_logs (t : T) : IO Unit := do
  t.liveHc ["t1", "t2"]
  t.sw_ "a" ["join"] (okc "t1")
  t.sw_ "a" ["task", "add", "t"] (okc "t1"); t.sw_ "a" ["task", "claim", "1"] (okc "t1")
  let err := (← t.sw "a" ["join"] (nok "t2")).stderr
  has err "a is bound to t1; this terminal is t2. `swarm join --takeover`"
  eq ((← t.q1 "select hc from agent").f "hc") "t1"
  -- a restart: the predecessor t1 is still live, the successor takes over from t2
  t.sw_ "a" ["join", "--takeover"] (okc "t2")
  eq ((← t.q1 "select hc from agent").f "hc") "t2"
  eq ((← t.q1 "select data from event where kind='takeover'").f "data") "t1 -> t2"
  for cmd in [["task", "done", "1", "--evidence", "x"], ["read"], ["lock", "b.txt"], ["post", "@all", "hi"]] do
    has (← t.sw "a" cmd (nok "t1")).stderr "a is bound to t2; this terminal is t1" (cmd.headD "")
  has ((← t.hook "a" "pre-tool" (json% {"tool_name": "Bash", "tool_input": {"command": "ls"}}) (some "t1")).f
    "additionalContext") "bound to t2"
  eq (← t.q1 "select state,owner from task") (json% {"state": "claimed", "owner": "a"})  -- the claim moved with the name
  t.sw_ "a" ["task", "done", "1", "--evidence", "x"] (okc "t2")
  -- a binding whose terminal hc ls doesn't show live moves without --takeover
  t.sw_ "b" ["join"] (okc "t9")
  t.sw_ "b" ["join"] (okc "t2")
  eq ((← t.q1 "select hc from agent where name='b'").f "hc") "t2"

def test_takeover_then_predecessor_death_keeps_agent_claims_locks (t : T) : IO Unit := do
  t.fakes
  t.sw_ "a" ["join"] (okc "t1")
  t.sw_ "a" ["task", "add", "t"] (okc "t1"); t.sw_ "a" ["task", "claim", "1"] (okc "t1")
  t.sw_ "a" ["lock", "a.txt"] (okc "t1")
  t.sw_ "a" ["join", "--takeover"] (okc "t2")
  t.setHc [json% {"address": "t2"}]  -- the predecessor's terminal t1 is gone; only t2 is live
  t.sw_ "a" ["watchd", "--once"]
  eq (← t.q1 "select hc,ended from agent") (json% {"hc": "t2"})
  eq ((← t.q1 "select state from task").f "state") "claimed"
  eq ((← t.q1 "select agent from lock").f "agent") "a"

def test_second_lock_on_held_path_refused (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["lock", "a.txt"]
  has (← t.sw "b" ["lock", "a.txt"] { ok := false }).stderr "locked by a"
  eq (← t.q "select path,agent from lock") (json% [{"path": "a.txt", "agent": "a"}])

def test_concurrent_lock_waits_not_double_writes (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  let peer ← Sqlite.Conn.open t.db false
  discard <| peer.exec "begin immediate"
  let now := (← Sqlite.now).toNat
  discard <| peer.exec s!"insert into lock(path,agent,since,lease_until) values('a.txt','a',{now},{now + 3600})"
  let bin ← swarmBin
  let child ← IO.Process.spawn
    { cmd := bin, args := #["lock", "a.txt"], cwd := some t.repo, stdin := .null, stdout := .piped, stderr := .piped,
      env := #[("SWARM_DB", some t.db), ("SWARM_NAME", some "b"), ("HC_TERMINAL_ID", none)] }
  IO.sleep 1000
  unless (← child.tryWait).isNone do fail "lock did not wait on the peer's transaction"  -- still running
  discard <| peer.exec "commit"
  let code ← child.wait
  unless code ≠ 0 do fail "lock succeeded on a held path"
  eq (← t.q "select path,agent from lock") (json% [{"path": "a.txt", "agent": "a"}])

/-- A peer holds the write lock past the 10 s busy handler: `wait` tries its write again rather than exit 1, and reads
go through meanwhile (board #137). -/
def test_wait_outlasts_a_busy_db (t : T) : IO Unit := do
  t.agent "a"
  let peer ← Sqlite.Conn.open t.db false
  discard <| peer.exec "begin immediate"
  let child ← IO.Process.spawn
    { cmd := ← swarmBin, args := #["wait", "--timeout", "1"], cwd := some t.repo, stdin := .null, stdout := .null,
      stderr := .piped, env := #[("SWARM_DB", some t.db), ("SWARM_NAME", some "a"), ("HC_TERMINAL_ID", none)] }
  has (← t.sw "a" ["who"]).stdout "a"  -- a read takes no write lock
  IO.sleep 11500
  unless (← child.tryWait).isNone do fail "wait did not wait out the held lock"
  discard <| peer.exec "commit"
  let err ← child.stderr.readToEnd
  eq (json% [$((← child.wait).toNat), $err]) (json% [0, ""])
  unless (← t.q1 "select waiter from agent where name='a'").f "waiter" != .null do fail "wait did not record its pid"

def test_drop_claimed_only_by_owner_or_comms (t : T) : IO Unit := do
  for i in [0:3] do t.sw_ "a" ["task", "add", s!"t{i}"]
  t.sw_ "a" ["task", "claim", "1"]
  t.sw_ "a" ["task", "claim", "2"]
  t.q_ "insert or replace into meta(k,v) values('comms','x-comms')"  -- the communicator is the address, not the name
  has (← t.sw "b" ["task", "drop", "1"] { ok := false }).stderr "only it or the communicator"
  t.sw_ "b" ["task", "drop", "3"]  -- open: anyone
  t.sw_ "a" ["task", "drop", "1"]
  t.sw_ "x-comms" ["task", "drop", "2"]
  eq (← t.q "select state from task order by id")
    (json% [{"state": "dropped"}, {"state": "dropped"}, {"state": "dropped"}])

-- ---- messages ----
def test_cursor (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["post", "b", "hello"]
  t.sw_ "a" ["post", "@all", "all"]
  has (← t.sw "b" ["read"]).stdout "hello"
  has (← t.sw "b" ["read"]).stdout "no unread"
  has (← t.sw "a" ["read"]).stdout "no unread"  -- own @all not echoed
  t.sw_ "a" ["post", "b", "again"]
  has (← t.sw "b" ["read"]).stdout "again"

def test_post_delivery_in_post_tool (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["post", "b", "look at X"]
  let out ← t.hook "b" "post-tool" (json% {"tool_name": "Read", "tool_input": {}})
  has (out.f "additionalContext") "look at X"
  eq (← t.hook "b" "post-tool" (json% {"tool_name": "Read", "tool_input": {}})) emptyObj

-- board #136: the hook records context (watchd's compaction pass reads it) and adds no note; claims stop at the nudge
def test_ctx_recorded_and_claim_refusal (t : T) : IO Unit := do
  t.agent "b"
  let tr := (← t.cwdOf "b") ++ "/t.jsonl"
  put tr ((json% {"type": "assistant", "message": {"usage": {"input_tokens": 330000}}}).compress ++ "\n")
  eq (← t.hook "b" "post-tool" (json% {"tool_name": "Read", "tool_input": {}, "transcript_path": $tr})) emptyObj
  eq ((← t.q1 "select ctx_tokens c from agent where name='b'").f "c").i 330000
  t.sw_ "b" ["task", "add", "t1"]
  let r ← t.sw "b" ["task", "claim", "1"] { ok := false }
  unless r.code ≠ 0 do fail "claim allowed at high ctx"
  has r.stderr "`swarm compact`"
  t.sw_ "human" ["limits", "--ctx-nudge", "0"]  -- off: no fence
  has (← t.sw "b" ["task", "claim", "1"]).stdout "claimed #1"

def test_comms_ctx_recorded_from_commands (t : T) : IO Unit := do
  t.agent "x-comms"
  t.q_ "insert or replace into meta(k,v) values('comms','x-comms')"
  let s ← sid "c"
  let home := t.d ++ "/home/.claude/projects/p"
  discard <| t.exec ["mkdir", "-p", home]
  put (home ++ "/" ++ s ++ ".jsonl")
    ((json% {"type": "assistant", "message": {"usage": {"input_tokens": 360000}}}).compress ++ "\n")
  let env := [("HOME", some (t.d ++ "/home")), ("CLAUDE_CODE_SESSION_ID", some s)]
  hasnt (← t.sw "x-comms" ["board"] { env, ok := false }).stdout "Context is"
  eq ((← t.q1 "select ctx_tokens c from agent where name='x-comms'").f "c").i 360000

-- board #136: `swarm compact` types an unwrapped /compact with the agent's task, worktree and --keep into its terminal
def test_compact_types_into_own_terminal (t : T) : IO Unit := do
  t.fakes
  discard <| t.fake "hc" s!"#!/bin/sh\necho \"[$HC_TERMINAL_ID] $*\" >> {t.d}/hc.log\n"
  t.agent "a" [("hc", "h1")]
  t.sw_ "a" ["task", "add", "the thing"] { hc := some "h1" }; t.sw_ "a" ["task", "claim", "1"] { hc := some "h1" }
  has (← t.sw "a" ["compact", "--keep", "the plan"] { hc := some "h1" }).stdout "runs when this turn ends"
  let c := (← t.calls "hc").getLastD ""
  has c "[] send h1 /compact Keep what swarm agent a needs"; has c "task #1 (the thing)"; has c "the plan"
  has c (← t.cwdOf "a")
  -- another terminal is fenced
  unless (← t.sw "a" ["compact"] { hc := some "h2", ok := false }).code ≠ 0 do fail "compact from another terminal"

def test_burst_capped_rest_stays_unread (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  for i in [0:40] do t.sw_ "a" ["post", "b", s!"m{i} {"".pushn 'y' 400}"]
  let ctx := ((← t.hook "b" "post-tool" (json% {"tool_name": "Read", "tool_input": {}})).f "additionalContext").s?.getD ""
  unless ctx.utf8ByteSize < 10000 do fail s!"{ctx.utf8ByteSize}"
  has ctx "more unread"
  let shown := count ctx " yyyy"
  let left := (← t.sw "b" ["read"]).stdout
  eq (shown + count left " yyyy") 40

def test_new_agent_skips_older_broadcasts (t : T) : IO Unit := do
  t.agent "a"
  t.sw_ "a" ["post", "@all", "old rule from another run"]
  t.agent "b"  -- joins after it
  t.sw_ "a" ["post", "@all", "new rule"]
  t.sw_ "a" ["post", "b", "for you"]
  let out := (← t.sw "b" ["read"]).stdout
  hasnt out "old rule"
  has out "new rule"; has out "for you"
  t.sw_ "b" ["leave"]; t.sw_ "a" ["post", "@all", "while b was away"]
  t.agent "b"  -- a rejoin keeps its cursor
  has (← t.sw "b" ["read"]).stdout "while b was away"

def test_post_compact_ctx (t : T) : IO Unit := do
  let tr := t.d ++ "/t.jsonl"
  put tr ((json% {"type": "assistant", "message": {"usage": {"input_tokens": 1, "cache_read_input_tokens": 200000}}}).compress
    ++ "\n" ++ (json% {"type": "system", "compactMetadata": {"postTokens": 9000}}).compress ++ "\n")
  t.agent "a"
  discard <| t.hook "a" "session" (json% {"source": "compact", "transcript_path": $tr})
  eq ((← t.q1 "select ctx_tokens from agent where name='a'").f "ctx_tokens") 40000

-- ---- conflicts ----
def test_compatible_appends_are_silent (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  discard <| t.edit "a" "e.txt"; discard <| t.edit "b" "e.txt"
  t.write "a" "e.txt" "mod (p, q, c)\n"
  t.write "b" "e.txt" "mod (p, q, d)\n"
  t.tick
  eq ((← t.q1 "select count(*) n from msg where kind='notice'").f "n") 0
  eq ((← t.q1 "select count(*) n from event where kind='conflict-compat'").f "n") 1

def test_same_token_episode (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  discard <| t.edit "a" "a.txt"; discard <| t.edit "b" "a.txt"
  t.write "a" "a.txt" "y"; t.write "b" "a.txt" "z"
  t.tick
  for (me, peer) in [("a", "b"), ("b", "a")] do
    let n ← t.notices me
    eq n.size 1
    has ((n[0]!).f "body") s!"conflicts with {peer}'s"
    has ((n[0]!).f "body") "a.txt (your lines 1–1"
  t.tick
  eq (← t.notices "a").size 1  -- same episode: silent
  t.write "b" "a.txt" "x"  -- revert one side
  t.tick
  eq (← t.q "select * from conflict") (Json.arr #[])
  t.write "b" "a.txt" "w"
  t.tick
  eq (← t.notices "a").size 2  -- a new episode

def test_fresh_worktree_off_origin_main_is_silent (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  discard <| t.edit "b" "a.txt"
  t.write "b" "a.txt" "z"  -- b's own uncommitted edit, off the old main
  t.land "a.txt" "y"
  t.setCwd "c" (t.d ++ "/wt3")
  discard <| t.git t.repo ["worktree", "add", "-q", "-b", "c/x", t.d ++ "/wt3", "origin/main"]
  t.agent "c"
  t.tick
  eq ((← t.q1 "select count(*) n from msg where kind='notice'").f "n") 0

def test_merge_origin_main_is_silent (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  let mut L := ""
  for i in [0:9] do L := L ++ s!"l{i}\n"
  let sub (s a b : String) := s.replace a b
  t.write "a" "e.txt" L
  discard <| t.git t.repo ["commit", "-qam", "lines"]
  discard <| t.git t.wt ["merge", "-q", "main"]
  t.land "e.txt" (sub L "l0" "main0")
  let c := t.d ++ "/wt3"
  t.setCwd "c" c
  discard <| t.git t.repo ["worktree", "add", "-q", "-b", "c/x", c, "main"]
  t.agent "c"
  discard <| t.edit "b" "e.txt"; discard <| t.edit "c" "e.txt"
  discard <| t.git c ["merge", "-q", "origin/main"]
  t.write "c" "e.txt" (sub (sub L "l0" "main0") "l8" "c8")  -- c's own edit: line 8
  t.write "b" "e.txt" (sub L "l0" "b0")  -- b edits line 0, which main changed: b vs main, not vs c
  t.tick
  eq ((← t.q1 "select count(*) n from msg where kind='notice'").f "n") 0
  t.write "b" "e.txt" (sub L "l8" "b8")  -- now b's own change overlaps c's
  t.tick
  has (((← t.notices "c")[0]!).f "body") "conflicts with b's"

def test_shared_tree_notice_once (t : T) : IO Unit := do
  t.setCwd "c" t.repo
  t.agent "a"; t.agent "c"
  eq (← t.edit "a" "a.txt") emptyObj
  let out ← t.edit "c" "a.txt"
  has (out.f "additionalContext") "also a's worktree"
  has (((← t.notices "a")[0]!).f "body") "also edits in"
  eq (← t.edit "c" "a.txt") emptyObj
  discard <| t.edit "a" "b.txt"
  eq (← t.notices "a").size 1

-- ---- roles (sw-roles §3, PR 1) ----
def test_role_set_change_print_and_logged (t : T) : IO Unit := do
  t.sw_ "a" ["join"] (okc "t1")
  eq (strip (← t.sw "a" ["role"] (okc "t1")).stdout) "(none)"
  t.sw_ "a" ["role", "model", "checker"] (okc "t1")
  eq (strip (← t.sw "a" ["role"] (okc "t1")).stdout) "model checker"
  t.sw_ "a" ["role", "reviewer\nof   PRs " ++ "".pushn 'x' 100] (okc "t1")  -- one line, cut at 80
  let r := ((← t.q1 "select role from agent").f "role").s?.getD ""
  eq (json% [$(r.contains '\n'), $(r.utf8ByteSize), $(r.take 15)]) (json% [false, 80, "reviewer of PRs"])
  eq (← t.q "select * from event where kind='role'").size 2
  eq ((← t.q1 "select data from event where kind='role' order by id limit 1").f "data") "model checker"
  -- a write from another terminal is fenced
  has (← t.sw "a" ["role", "planner"] (nok "t2")).stderr "a is bound to t1; this terminal is t2"
  eq ((← t.q1 "select role from agent").f "role") r

def test_role_same_text_names_peer_and_survives_takeover (t : T) : IO Unit := do
  t.liveHc ["t1", "t2", "t3"]
  t.sw_ "a" ["join"] (okc "t1"); t.sw_ "b" ["join"] (okc "t3")
  eq (strip (← t.sw "a" ["role", "reviewer"] (okc "t1")).stdout) ""
  eq (strip (← t.sw "b" ["role", "Reviewer"] (okc "t3")).stdout) "a also declares 'Reviewer'"
  t.sw_ "a" ["join", "--takeover"] (okc "t2")
  eq ((← t.q1 "select role from agent where name='a'").f "role") "reviewer"
  t.sw_ "a" ["role", "planner"] (okc "t2")
  t.sw_ "a" ["leave"] (okc "t2"); t.sw_ "a" ["join"] (okc "t2")  -- kept like model, past an end
  eq ((← t.q1 "select role from agent where name='a'").f "role") "planner"

def test_role_shown_in_who_board_state (t : T) : IO Unit := do
  t.sw_ "a" ["join"]; t.sw_ "b" ["join"]
  t.sw_ "a" ["role", "model checker"]
  t.sw_ "a" ["task", "add", "t1"]; t.sw_ "a" ["task", "claim", "1"]; t.sw_ "b" ["task", "add", "t2"]
  has (← t.sw "b" ["who"]).stdout "a idle role=model checker ctx="
  has (← t.sw "b" ["who"]).stdout "b idle ctx="
  let board := (← t.sw "b" ["board"]).stdout
  has board "#1 claimed a (model checker) lease"; has board "#2 open    -  "
  let st ← match Json.parse (← t.sw "b" ["state", "--json"]).stdout with
    | .ok j => pure j | .error e => fail s!"state --json: {e}"
  let mut roles : List (String × Json) := []
  for x in ((st.f "agents").getArr?.toOption.getD #[]) do
    if x.f "role" != .null then roles := roles ++ [((x.f "name").s?.getD "", x.f "role")]
  eq (Json.mkObj roles) (json% {"a": "model checker"})

def tests : List Case := [
  ("test_task_timing_columns", test_task_timing_columns),
  ("test_timing_from_auto_spawn_event", test_timing_from_auto_spawn_event),
  ("test_task_show_and_claim_print_body", test_task_show_and_claim_print_body),
  ("test_release_reopens", test_release_reopens),
  ("test_lock_denial_logged", test_lock_denial_logged),
  ("test_claim_lease_done", test_claim_lease_done),
  ("test_reaping", test_reaping),
  ("test_other_terminal_hook_and_wait_dont_rebind", test_other_terminal_hook_and_wait_dont_rebind),
  ("test_ended_agent_not_revived", test_ended_agent_not_revived),
  ("test_join_refused_on_live_binding_takeover_moves_and_logs", test_join_refused_on_live_binding_takeover_moves_and_logs),
  ("test_takeover_then_predecessor_death_keeps_agent_claims_locks", test_takeover_then_predecessor_death_keeps_agent_claims_locks),
  ("test_second_lock_on_held_path_refused", test_second_lock_on_held_path_refused),
  ("test_concurrent_lock_waits_not_double_writes", test_concurrent_lock_waits_not_double_writes),
  ("test_wait_outlasts_a_busy_db", test_wait_outlasts_a_busy_db),
  ("test_drop_claimed_only_by_owner_or_comms", test_drop_claimed_only_by_owner_or_comms),
  ("test_cursor", test_cursor),
  ("test_post_delivery_in_post_tool", test_post_delivery_in_post_tool),
  ("test_ctx_recorded_and_claim_refusal", test_ctx_recorded_and_claim_refusal),
  ("test_comms_ctx_recorded_from_commands", test_comms_ctx_recorded_from_commands),
  ("test_compact_types_into_own_terminal", test_compact_types_into_own_terminal),
  ("test_burst_capped_rest_stays_unread", test_burst_capped_rest_stays_unread),
  ("test_new_agent_skips_older_broadcasts", test_new_agent_skips_older_broadcasts),
  ("test_post_compact_ctx", test_post_compact_ctx),
  ("test_compatible_appends_are_silent", test_compatible_appends_are_silent),
  ("test_same_token_episode", test_same_token_episode),
  ("test_fresh_worktree_off_origin_main_is_silent", test_fresh_worktree_off_origin_main_is_silent),
  ("test_merge_origin_main_is_silent", test_merge_origin_main_is_silent),
  ("test_shared_tree_notice_once", test_shared_tree_notice_once),
  ("test_role_set_change_print_and_logged", test_role_set_change_print_and_logged),
  ("test_role_same_text_names_peer_and_survives_takeover", test_role_same_text_names_peer_and_survives_takeover),
  ("test_role_shown_in_who_board_state", test_role_shown_in_who_board_state)]

end SwarmLean.Tests.Cli.Core
