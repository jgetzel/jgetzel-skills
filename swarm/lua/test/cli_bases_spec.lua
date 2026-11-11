-- Per-task bases (sw-bases, board #3): base_for, .claude/swarm.json base, task add --base, and the checks that used to
-- say main: lifecycle's landed check, the sweep, the conflict snapshot, CI. Harness: cli.lua.
local util = require "swarm.util"
local bases = require "swarm.bases"
local lfs = require "lfs"
local T = {}

local OLD = os.time() - 3600
local function exists(p) return lfs.attributes(p) ~= nil end
local function put(path, text) local f = assert(io.open(path, "w")); f:write(text); f:close() end
local function ended(t, name) return t:q1("select ended from agent where name=?", name).ended ~= nil end
local function comms_tick(t) t:sw("a", "watchd", "--once", "--comms", "comms", "--max-agents", "0") end
local function idle(t, name, kw)
  local o = { status = "idle", last_active = OLD, waiter = require("posix.unistd").getpid() }
  for k, v in pairs(kw or {}) do o[k] = v end
  t:agent(name, o)
end
local function old_wt(t, path)
  local gd = util.strip(t:git(path, "rev-parse", "--absolute-git-dir"))
  for _, p in ipairs({ path, gd .. "/logs/HEAD" }) do lfs.touch(p, OLD, OLD) end
end
-- w2 gets a commit and main fast-forwards to it; `formal` stays where main was
local function land_on_main_only(t)
  t:git(t.repo, "branch", "formal")
  t:write("b", "new.txt", "wip")
  t:git(t.wt, "add", ".")
  t:git(t.wt, "commit", "-qm", "wip")
  t:git(t.repo, "merge", "-q", "--ff-only", "w2")
end
local function done_task(t, owner, base)
  t:sw("a", "task", "add", "t", "--base", base)
  t:q("update task set state='done', owner=?, evidence='x' where id=1", owner)
end

function T.test_base_for_task_then_repo_then_main(t)
  t:eq(bases.default(t.repo), "main")
  t:eq(bases.base_for({}, t.repo), "main")
  lfs.mkdir(t.repo .. "/.claude")
  put(t.repo .. "/.claude/swarm.json", '{"base": "formal"}')
  t:eq(bases.default(t.repo), "formal")
  t:eq(bases.base_for({}, t.repo), "formal")
  t:eq(bases.base_for({ base = "dev" }, t.repo), "dev")
  put(t.repo .. "/.claude/swarm.json", '{"ci": {}}')  -- no base key
  t:eq(bases.default(t.repo), "main")
end

function T.test_task_add_base_stored_and_shown(t)
  t:sw("a", "task", "add", "plain")
  t:sw("a", "task", "add", "on formal", "--base", "formal")
  t:eq(t:q1("select base from task where id=1").base, nil)
  t:eq(t:q1("select base from task where id=2").base, "formal")
  t:hasnt(t:sw("a", "task", "show", "1").stdout, "base:")
  t:has(t:sw("a", "task", "show", "2").stdout, "base: formal")
end

function T.test_ref_prefers_the_remote_branch(t)
  t:eq(bases.ref("main", t.repo), "main")  -- no origin
  t:git(t.repo, "update-ref", "refs/remotes/origin/main", "HEAD")
  t:eq(bases.ref("main", t.repo), "origin/main")
  t:eq(bases.ref("formal", t.repo), "formal")  -- origin lacks it
end

-- lifecycle: an agent whose task is on `formal` is not done while its work is only on main
function T.test_agent_kept_until_work_is_on_its_tasks_base(t)
  land_on_main_only(t)
  idle(t, "e", { wt = t.wt })
  done_task(t, "e", "formal")
  comms_tick(t)
  assert(not ended(t, "e"), "on main, not on formal")
  assert(exists(t.wt))
  t:git(t.repo, "branch", "-f", "formal", "w2")
  comms_tick(t)
  assert(ended(t, "e"))
end

function T.test_agent_without_task_uses_the_repo_base(t)
  land_on_main_only(t)
  idle(t, "e", { wt = t.wt })
  lfs.mkdir(t.repo .. "/.claude")
  put(t.repo .. "/.claude/swarm.json", '{"base": "formal"}')
  comms_tick(t)
  assert(not ended(t, "e"), "the repo's base is formal")
  t:git(t.repo, "branch", "-f", "formal", "w2")
  comms_tick(t)
  assert(ended(t, "e"))
end

function T.test_agent_on_main_task_still_ended_on_main(t)
  land_on_main_only(t)
  idle(t, "e", { wt = t.wt })
  done_task(t, "e", "main")
  comms_tick(t)
  assert(ended(t, "e"))
end

-- the sweep protects every base a task names, and main
function T.test_sweep_removes_work_landed_on_a_task_base(t)
  t:git(t.repo, "branch", "formal")
  t:write("b", "new.txt", "wip")
  t:git(t.wt, "add", ".")
  t:git(t.wt, "commit", "-qm", "wip")
  t:git(t.repo, "branch", "-f", "formal", "w2")  -- on formal only
  old_wt(t, t.wt)
  t:fakes()
  comms_tick(t)
  assert(exists(t.wt), "no task names formal: not landed")
  t:sw("a", "task", "add", "t", "--base", "formal")
  comms_tick(t)
  assert(not exists(t.wt), "formal is a base now")
end

-- the conflict snapshot: work for different bases can't meet
function T.test_conflict_only_between_agents_on_the_same_base(t)
  t:git(t.repo, "branch", "formal")
  t:agent("a"); t:agent("b")
  t:sw("a", "task", "add", "t", "--base", "formal")
  t:sw("b", "task", "claim", "1")
  t:edit("a", "a.txt"); t:edit("b", "a.txt")
  t:write("a", "a.txt", "y"); t:write("b", "a.txt", "z")
  t:tick()
  t:eq(t:q1("select count(*) n from msg where kind='notice'").n, 0)
  t:q("update task set state='open', owner=null where id=1")
  t:tick()
  t:eq(t:q1("select count(*) n from msg where kind='notice'").n, 2)
end

-- CI follows the repo's base, and a base other than main that origin lacks has none
function T.test_ci_polls_only_a_base_with_a_remote(t)
  t:fakes()
  t:agent("a")
  t:set_gh("api", { { databaseId = 1, headSha = "a1", status = "completed", conclusion = "success", url = "u1",
                      createdAt = "2026-11-08T10:00:00Z", updatedAt = "2026-11-08T10:03:00Z", event = "push" } })
  lfs.mkdir(t.repo .. "/.claude")
  put(t.repo .. "/.claude/swarm.json", '{"base": "formal"}')
  t:sw("a", "watchd", "--once", "--ci")
  t:eq(#t:calls("gh"), 0, "formal is local only")
  t:git(t.repo, "update-ref", "refs/remotes/origin/formal", "HEAD")
  t:q("delete from meta where k='ci_polled'")
  t:sw("a", "watchd", "--once", "--ci")
  assert(t:calls("gh")[1]:find("branch=formal", 1, true), "polls the repo's base")
end

return T
