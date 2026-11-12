-- The Stop hook (board #90): blocks a stop until the agent is endable or has declared why it waits. Harness: cli.lua.
local json, util = require "swarm.json", require "swarm.util"
local T = {}

local function stop(t, who, p)
  p = p or {}
  p.cwd = p.cwd or t.cwd[who] or t.repo
  local r = t:sw(who, "hook", "stop", { stdin = json.encode(p) })
  if util.strip(r.stdout) == "" then return nil end
  local o = json.decode(r.stdout)
  t:eq(o.decision, "block")
  return o.reason
end
local function claim(t, who) t:sw(who, "task", "add", "x"); t:sw(who, "task", "claim", "1") end

function T.test_endable_stops_through(t)
  t:agent("a")
  t:eq(stop(t, "a"), nil)
  t:eq(t:sw("a", "endable", "--why", { ok = true }).stdout, "")
end

function T.test_claim_blocks_with_the_three_ways_out(t)
  t:agent("a"); claim(t, "a")
  local r = stop(t, "a")
  t:has(r, "claim held (#1)")
  t:has(r, "swarm task release"); t:has(r, "swarm task block"); t:has(r, "swarm stay")
  local e = t:sw("a", "endable", "--why", { ok = false })
  t:eq(e.code, 1); t:has(e.stdout, "claim held (#1)")
end

function T.test_lock_blocks(t)
  t:agent("a"); t:sw("a", "lock", "a.txt")
  t:has(stop(t, "a"), "lock held")
end

function T.test_blocked_task_and_stay_allow(t)
  t:agent("a"); claim(t, "a")
  t:sw("a", "task", "block", "1", "which one?")
  t:eq(stop(t, "a"), nil)
  t:agent("b"); t:sw("b", "stay", "reviews")
  t:eq(stop(t, "b"), nil)
end

function T.test_release_then_stop_is_endable(t)
  t:agent("a"); claim(t, "a")
  t:has(stop(t, "a"), "claim held")
  t:sw("a", "task", "release", "1")
  t:eq(stop(t, "a"), nil)
end

function T.test_dirty_worktree_lists_files(t)
  t:agent("a", { wt = t.wt })
  t.cwd.a = t.wt
  t:write("a", "new.txt", "x")
  local r = stop(t, "a")
  t:has(r, "dirty worktree"); t:has(r, "new.txt")
end

function T.test_own_background_job_allows_but_swarm_wait_does_not(t)
  t:agent("a"); claim(t, "a")
  t:eq(stop(t, "a", { background_tasks = { { status = "running", command = "make test" } } }), nil)
  t:has(stop(t, "a", { background_tasks = { { status = "running", command = "swarm wait --timeout 60" } } }), "claim held")
end

function T.test_error_turn_allows(t)
  t:agent("a"); claim(t, "a")
  local tr = t.d .. "/e.jsonl"
  local f = assert(io.open(tr, "w"))
  f:write(json.encode({ type = "assistant", isApiErrorMessage = true, message = { content = "rate limit" } }), "\n"); f:close()
  t:eq(stop(t, "a", { transcript_path = tr }), nil)
end

function T.test_comms_is_exempt(t)
  t:agent("comms"); claim(t, "comms")
  t:q("insert or replace into meta(k,v) values('comms','comms')")
  t:eq(stop(t, "comms"), nil)
end

function T.test_context_too_high_says_hand_off(t)
  t:agent("a"); claim(t, "a")
  local tr = t.d .. "/c.jsonl"
  local f = assert(io.open(tr, "w"))
  f:write(json.encode({ type = "assistant", message = { usage = { input_tokens = 600000 } } }), "\n"); f:close()
  local r = stop(t, "a", { transcript_path = tr })
  t:has(r, "hand off"); t:hasnt(r, "(a) finish")
end

function T.test_cap_two_blocks_per_chain_then_allow_and_tell_comms(t)
  t:agent("a"); t:agent("comms"); claim(t, "a")
  t:q("insert or replace into meta(k,v) values('comms','comms')")
  t:has(stop(t, "a"), "claim held")
  t:has(stop(t, "a", { stop_hook_active = true }), "claim held")
  t:eq(stop(t, "a", { stop_hook_active = true }), nil)
  t:eq(#t:q("select 1 x from event where kind='stop-cap'"), 1)
  t:has(t:sw("comms", "read").stdout, "stop hook let it go")
  t:has(stop(t, "a"), "claim held")  -- a new chain blocks again
end

return T
