import Tests.Cli.Fixture

/-! cli_scale_spec: the write commands stay fast on a big db (board #138: a write-back quadratic in a table's rows made
hook post-tool take 82 s on 12.6k events, holding the write lock). Each command's best of three is under a second on
20k events, 500 tasks, 400 agents; each view of state --json under 300 ms (board #139). -/

namespace SwarmLean.Tests.Cli.Scale
open SwarmLean.Tests.Cli

def now : IO Int := return ((← SwarmLean.Sqlite.now).toNat : Int)

/-- `n` rows of `select` (over `i`, 1..n) inserted into `into`. -/
def gen (t : T) (n : Nat) (into select : String) : IO Unit :=
  t.q_ s!"with recursive c(i) as (select 1 union all select i+1 from c where i<{n}) insert into {into} {select} from c"

/-- The db of a long-running swarm, with `a` joined. -/
def big (t : T) : IO Unit := do
  t.agent "a"
  let n ← now
  gen t 400 "agent(name, status, last_active, cwd)" s!"select 'ag'||i, case when i%2 then 'idle' else 'working' end, {n}-i, '/w/'||i"
  gen t 500 "task(title, body, state, owner, lease_until, created_by)"
    s!"select 'task '||i, 'body of task '||i, case when i%5=0 then 'claimed' when i%5=1 then 'open' else 'done' end, case when i%5=0 then 'ag'||i else null end, {n}+3600, 'a'"
  gen t 600 "msg(ts, frm, dest, body, kind)" s!"select {n}-i, 'ag'||(i%400), 'ag'||((i+1)%400), 'message '||i, 'msg'"
  gen t 340 "workspace(path, branch, agent)" "select '/w/'||i, 'ag'||i||'/1', 'ag'||i"
  gen t 20000 "event(ts, agent, kind, path, data)" s!"select {n}-20000+i, 'ag'||(i%400), 'tool', '/w/'||(i%340)||'/f.lean', 'event '||i"

/-- The best of three runs of `act` (load on the machine slows a run, never speeds one), in ms. -/
def best3 (act : Nat → IO Unit) : IO Nat := do
  let mut b := 1000000
  for i in [0:3] do
    let t0 ← IO.monoMsNow
    act i
    b := min b ((← IO.monoMsNow) - t0)
  return b

def under1s (what : String) (ms : Nat) : IO Unit := do
  if ms ≥ 1000 then fail s!"{what} took {ms} ms on a big db (best of three)"

def test_write_commands_fast_on_a_big_db (t : T) : IO Unit := do
  big t
  under1s "hook post-tool" (← best3 fun _ => discard <| t.hook "a" "post-tool")
  under1s "post" (← best3 fun i => t.sw_ "a" ["post", "@all", s!"hi {i}"])
  let opens ← t.q "select id from task where state='open' order by id limit 3"
  under1s "task claim" (← best3 fun i => t.sw_ "a" ["task", "claim", toString ((opens[i]!.f "id").i)])
  -- watchd's reap: a lapsed claim of an agent that is gone is reopened
  t.fakes
  under1s "watchd --once (reap)" (← best3 fun i => do
    let id := (opens[i]!.f "id").i
    t.q_ "update task set owner='gone', lease_until=1 where id=?" [.int id]
    t.tick
    eq ((← t.q1 "select state from task where id=?" [.int id]).f "state") "open" "the lapsed claim was not reaped")

-- board #139: state --json, which the panel runs every 3 s, scanned the events once per task and per agent (2-4 s on a
-- db this size); each view's best of three is under 300 ms
def test_state_fast_on_a_big_db (t : T) : IO Unit := do
  big t
  t.fakes
  let n ← now
  -- each task's life in events (what task timing reads), and half the agents ended
  gen t 6000 "event(ts, agent, kind, data)"
    s!"select {n}-6000+i, 'ag'||(i%400), case i%3 when 0 then 'task-add' when 1 then 'claim' else 'done' end, '#'||(i%500+1)"
  t.q_ s!"update agent set ended={n}-60 where name like 'ag%' and rowid%2=0"
  for v in [[], ["--view", "summary"], ["--view", "board"], ["--view", "overview"], ["--view", "agents"], ["--view", "board", "--task", "7"]] do
    let ms ← best3 fun _ => t.sw_ "a" (["state", "--json"] ++ v)
    if ms ≥ 300 then fail s!"state --json {" ".intercalate v} took {ms} ms on a big db (best of three)"

def tests : List Case := [("write_commands_fast_on_a_big_db", test_write_commands_fast_on_a_big_db),
  ("state_fast_on_a_big_db", test_state_fast_on_a_big_db)]

end SwarmLean.Tests.Cli.Scale
