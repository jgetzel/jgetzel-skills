-- The panel's CLI (board #40, swarm/herdr/REDESIGN.md §3 and §4): `human`, the user's name, has the communicator's
-- rights (end, release another's task, drop, unblock); `swarm away` and `--back`; `state --json --task N`.
local json = require "swarm.json"
local T = {}

local function comms(t, name)
  t:agent(name or "c")
  t:q("insert or replace into meta(k,v) values('comms',?)", name or "c")
end
local function tick(t) t:sw("a", "watchd", "--once", "--comms", "c", "--max-agents", "0") end
local function state(t, ...) return json.decode(t:sw("human", "state", "--json", ...).stdout) end
local function msgs_to(t, who) return t:q("select frm, body, urgent from msg where dest=? order by id", who) end

function T.test_human_ends_agents(t)
  t:fakes()
  t:agent("e", { status = "idle" })
  t:has(t:sw("x", "end", "e", { ok = false }).stderr, "only the communicator or the user")
  t:sw("human", "end", "e", "--force")
  t:eq(t:q1("select status from agent where name='e'").status, "ended")
  t:eq(t:q1("select data from event where kind='end'").data, "forced by human")
  t:eq(#t:q("select 1 x from agent where name='human'"), 0)  -- the user is never an agent row
end

function T.test_human_is_reserved(t)
  t:has(t:sw("human", "join", { ok = false }).stderr, "'human' is the user's name")
end

function T.test_release_of_anothers_task(t)
  comms(t)
  t:agent("e"); t:agent("f")
  t:sw("e", "task", "add", "x"); t:sw("e", "task", "claim", "1")
  t:has(t:sw("f", "task", "release", "1", { ok = false }).stderr, "not claimed by you")  -- a peer can't
  t:has(t:sw("human", "task", "release", "1").stdout, "released #1 from e")
  t:eq(t:q1("select state, owner from task"), { state = "open" })
  t:eq(msgs_to(t, "e"), { { frm = "human", body = "the user released #1: stop work on it", urgent = 1 } })
  local ev = t:q1("select agent, data from event where kind='release'")
  t:eq(ev, { agent = "human", data = "#1 from e" })
  -- the communicator may too, a blocked task as well; its question goes with it
  t:sw("f", "task", "claim", "1"); t:sw("f", "task", "block", "1", "which db?")
  t:sw("c", "task", "release", "1")
  t:eq(t:q1("select state, question from task"), { state = "open" })
  t:eq(msgs_to(t, "f")[1].body, "c released #1: stop work on it")
  t:has(t:sw("human", "task", "release", "1", { ok = false }).stderr, "task #1 is not claimed")
end

function T.test_human_drops_and_unblocks(t)
  t:agent("e")
  t:sw("e", "task", "add", "x"); t:sw("e", "task", "add", "y")
  t:sw("e", "task", "claim", "1"); t:sw("e", "task", "block", "1", "which db?")
  t:sw("human", "task", "unblock", "1", "--answer", "sqlite")
  t:eq(t:q1("select state, answer from task where id=1"), { state = "claimed", answer = "sqlite" })
  t:eq(msgs_to(t, "e")[1].frm, "human")
  t:sw("e", "task", "claim", "2")
  t:sw("human", "task", "drop", "2")
  t:eq(t:q1("select state from task where id=2").state, "dropped")
  t:eq(t:q1("select agent from event where kind='drop'").agent, "human")
end

function T.test_away_queues_questions(t)
  t:fakes()
  comms(t)
  t:agent("e")
  t:sw("e", "task", "add", "x"); t:sw("e", "task", "claim", "1")
  t:has(t:sw("human", "away", "lunch").stdout, "away: lunch")
  t:has(t:sw("human", "away").stdout, "already away since")  -- the first since stays
  local told = msgs_to(t, "c")
  t:eq(#told, 1)  -- told once
  t:has(told[1].body, "the user is away since"); t:has(told[1].body, "(lunch)"); t:eq(told[1].urgent, 0)
  local s = state(t)
  t:eq(s.away.note, "lunch")
  -- rule 1: task block tells the agent; watchd's notice isn't urgent
  t:has(t:sw("e", "task", "block", "1", "which db?").stdout, "the user is away: park this")
  tick(t)
  local n = msgs_to(t, "c")[2]
  t:has(n.body, "is blocked on #1"); t:has(n.body, "The user is away"); t:eq(n.urgent, 0)
  -- rule 2: the communicator's read and board remind it
  t:has(t:sw("c", "read").stdout, "don't ask them")
  t:has(t:sw("c", "board").stdout, "the user is away since")
  t:hasnt(t:sw("e", "board").stdout, "the user is away since")  -- only the communicator
end

function T.test_not_away_block_is_urgent(t)
  t:fakes()
  comms(t)
  t:agent("e")
  t:sw("e", "task", "add", "x"); t:sw("e", "task", "claim", "1")
  t:has(t:sw("e", "task", "block", "1", "which db?").stdout, "watchd tells the communicator")
  tick(t)
  t:eq(msgs_to(t, "c")[1].urgent, 1)
  t:hasnt(t:sw("c", "read").stdout, "the user is away")
end

function T.test_away_hc_prompt_not_urgent(t)
  t:fakes()
  t:set_hc({ address = "h1", status = "blocked" })
  comms(t)
  t:agent("a", { hc = "h1", status = "working" })
  t:sw("a", "task", "add", "t1", { hc = "h1" }); t:sw("a", "task", "claim", "1", { hc = "h1" })
  t:sw("human", "away")
  tick(t)
  local m = t:q("select body, urgent from msg where dest='c' and frm='swarm'")
  t:eq(#m, 1)
  t:has(m[1].body, "a prompt or question needs the human"); t:eq(m[1].urgent, 0)
end

function T.test_back_digest(t)
  t:fakes()
  comms(t)
  t:agent("e"); t:agent("g")
  for _, x in ipairs({ "x", "y", "z" }) do t:sw("e", "task", "add", x) end
  t:has(t:sw("human", "away", "--back").stdout, "you were not away")
  t:sw("human", "away")
  t:sw("e", "task", "claim", "1"); t:sw("e", "task", "block", "1", "which db?")
  t:sw("g", "task", "claim", "3"); t:sw("g", "task", "block", "3", "which port?")
  t:q("update event set ts=ts-60 where kind='block' and data like '#3 %'")  -- #3 asked first
  t:sw("e", "task", "claim", "2"); t:sw("e", "task", "done", "2", "--evidence", "abc123")
  t:q("update task set pr=12, merged_at=? where id=2", os.time())
  t:q("insert into ci(id,sha,status,conclusion,url,created,updated,workflow) values(1,'deadbeef00','completed','success','u','2026-11-11T10:00:00Z','x','ci')")
  t:agent("h"); t:sw("h", "leave")
  local out = t:sw("human", "away", "--back").stdout
  t:has(out, "2 questions wait, oldest first:")
  assert(out:find("#3 g", 1, true) < out:find("#1 e", 1, true), "oldest first: " .. out)
  t:has(out, "finished: #2 y"); t:has(out, "merged: PR #12 (#2)"); t:has(out, "main CI: success deadbee")
  t:has(out, "ended: h")
  local m = msgs_to(t, "c")
  t:eq(m[#m], { frm = "human", body = "the user is back: 2 questions wait (#3, #1)", urgent = 1 })
  t:eq(t:q1("select v from meta where k='away'"), nil)
  -- state --json keeps the digest for the panel's card until the next away
  local s = state(t)
  t:eq(s.away, nil)
  t:eq(#s.back.questions, 2); t:eq(s.back.questions[1].id, 3); t:eq(s.back.done[1].id, 2)
  t:eq(s.back.ended[1].name, "h"); t:eq(s.back.ci.conclusion, "success")
  t:sw("human", "away")
  t:eq(state(t).back, nil)
end

function T.test_state_task(t)
  t:agent("e")
  t:sw("e", "task", "add", "x", "--body", "do x"); t:sw("e", "task", "add", "y")
  t:sw("e", "task", "claim", "1")
  t:sw("e", "post", "e", "about #1 and #12")
  t:sw("e", "post", "e", "about #12 only")
  local s = state(t, "--task", "1")
  t:eq(s.task.id, 1); t:eq(s.task.body, "do x")
  local kinds = {}
  for i, e in ipairs(s.task.events) do kinds[i] = e.kind end
  t:eq(kinds, { "task-add", "claim" })
  t:eq(#s.task.messages, 1); t:has(s.task.messages[1].body, "#1 and")
  t:eq(state(t, "--task", "9").task, nil)
end

return T
