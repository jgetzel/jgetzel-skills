-- Differential tests of swarm/model/SwarmModel/Env.lean: each environment assumption against the real tool, in a
-- scratch repo, through the Lua the swarm runs where there is one. A case carries its assumption's name; check.sh
-- refuses an assumption with no case here. hc_ls_live, hc_run_starts and hc_kill_ends start a terminal in your hc: they run only
-- with SWARM_TEST_HC=1. gh_checks and gh_state ask GitHub about this repo's latest PRs: they run only with
-- SWARM_TEST_GH=1.
local proc, util, watchd, machine, agents = require "swarm.proc", require "swarm.util", require "swarm.watchd",
  require "swarm.machine", require "swarm.agents"
local stdlib, unistd, signal, wait = require "posix.stdlib", require "posix.unistd", require "posix.signal",
  require "posix.sys.wait"
local lfs = require "lfs"

local d = stdlib.realpath(stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-env-XXXXXX"))
for k, v in pairs({ GIT_CONFIG_NOSYSTEM = "1", GIT_CONFIG_GLOBAL = "/dev/null", GIT_AUTHOR_NAME = "t",
    GIT_AUTHOR_EMAIL = "t@t", GIT_COMMITTER_NAME = "t", GIT_COMMITTER_EMAIL = "t@t" }) do stdlib.setenv(k, v) end
local PATH0 = os.getenv("PATH")
os.execute("mkdir -p " .. d .. "/bin && printf '#!/bin/sh\\nexit 1\\n' > " .. d .. "/bin/gh && chmod +x " .. d .. "/bin/gh")
stdlib.setenv("PATH", d .. "/bin:" .. os.getenv("PATH"))  -- landed_ref's gh finds no merged PR: only git's answers count

local function git(cwd, ...)
  local out, err, code = proc.exec({ "git", "-C", cwd, ... })
  assert(code == 0, table.concat({ ... }, " ") .. ": " .. err)
  return util.strip(out)
end
local function gx(cwd, ...) return (proc.gx({ "-C", cwd, ... })) end
local function write(p, s) local f = assert(io.open(p, "w")); f:write(s); f:close() end
local function set(l) local r = {} for _, x in ipairs(l) do r[x] = true end return r end
local function subset(a, b) for x in pairs(a) do if not b[x] then return false end end return true end
-- what a commit holds, in the model's reading: its files, by content
local function files(cwd, rev) return set(util.splitlines(git(cwd, "ls-tree", "-r", rev))) end
-- the repo's durable state (Env's Git.durable): worktrees with branch and HEAD, branch tips, commits, and each status
local function durable(cwd)
  local s = { git(cwd, "worktree", "list", "--porcelain"), git(cwd, "for-each-ref", "refs/heads"), git(cwd, "rev-list", "--all") }
  for _, l in ipairs(util.splitlines(s[1])) do
    local p = l:match("^worktree (.*)")
    if p then s[#s + 1] = p .. ":" .. git(p, "status", "--porcelain") end
  end
  return table.concat(s, "\n")
end
local function listed(main)  -- the sweep's parse of `worktree list`
  local r = {}
  for _, l in ipairs(util.splitlines(proc.run({ "git", "worktree", "list", "--porcelain" }, main))) do
    if util.startswith(l, "worktree ") then r[stdlib.realpath(l:sub(10)) or l:sub(10)] = true end
  end
  return r
end
local function clean(wt)  -- the sweep's and landed's reading of status
  local st = proc.run({ "git", "-C", wt, "status", "--porcelain" })
  return st ~= nil and util.strip(st) == ""
end
local function spawn(cwd, ...)  -- a child running argv in cwd; its pid
  local argv = { ... }
  local pid = unistd.fork()
  if pid == 0 then
    if cwd then unistd.chdir(cwd) end
    unistd.execp(argv[1], { select(2, unpack(argv)) })
    unistd._exit(127)
  end
  return pid
end
local function kill0(pid) return signal.kill(pid, 0) == 0 end  -- as state.lua, msgs.lua and watchd.lua ask

local repo = d .. "/repo"
git(d, "init", "-q", "-b", "main", repo)
write(repo .. "/base", "base\n")
git(repo, "add", "-A"); git(repo, "commit", "-q", "-m", "c0")

-- ---------- ancestor_reach, same_content_reach ----------
-- A random history: commits that each add a fresh file, squash merges, fast-forwards, on main and three branches.
-- What git answers is checked against the parents the test recorded, and what landed_ref answers against the files.
math.randomseed(34)
local brs = { "main", "b1", "b2", "b3" }
local sha, par, tip = { git(repo, "rev-parse", "HEAD") }, { 0 }, {}
for _, b in ipairs(brs) do
  tip[b] = 1
  if b ~= "main" then git(repo, "branch", b) end
end
local squashes = 0
for i = 1, 24 do
  local b, s = brs[math.random(#brs)], brs[math.random(#brs)]
  local op = math.random(4)
  git(repo, "checkout", "-q", b)
  if op <= 2 or s == b then
    write(repo .. "/f" .. i, "patch " .. i .. "\n")
    git(repo, "add", "-A"); git(repo, "commit", "-q", "-m", "c" .. i)
  elseif op == 3 then
    git(repo, "merge", "-q", "--squash", s)
    if gx(repo, "diff", "--cached", "--quiet") == 0 then goto continue end
    git(repo, "commit", "-q", "-m", "squash " .. s)
    squashes = squashes + 1
  else
    if gx(repo, "merge", "-q", "--ff-only", s) ~= 0 then goto continue end
    tip[b] = tip[s]
    goto continue
  end
  sha[#sha + 1] = git(repo, "rev-parse", "HEAD"); par[#sha] = tip[b]; tip[b] = #sha
  ::continue::
end
git(repo, "checkout", "-q", "--detach", "main")
assert(squashes > 0, "the history has a squash merge")
local function anc(k, t)  -- k an ancestor of t, by the recorded parents
  while t ~= 0 do if t == k then return true end; t = par[t] end
  return false
end
local cases, tipfiles = { ancestor = 0, squash = 0, neither = 0 }, {}
for _, b in ipairs(brs) do tipfiles[b] = files(repo, b) end
for k = 1, #sha do
  local kf = files(repo, sha[k])
  for _, b in ipairs(brs) do
    local ga = gx(repo, "merge-base", "--is-ancestor", sha[k], b) == 0
    assert(ga == anc(k, tip[b]), ("ancestor_reach: git's --is-ancestor %d %s is ancestry"):format(k, b))
    local holds = subset(kf, tipfiles[b])
    if ga then assert(holds, ("ancestor_reach: %s holds ancestor %d's files"):format(b, k)) end
    local landed = watchd.landed_ref(repo, sha[k], b)
    if landed then assert(holds, ("same_content_reach: landed_ref(%d, %s) means %s holds its files"):format(k, b, b)) end
    local kind = ga and "ancestor" or landed and "squash" or "neither"
    cases[kind] = cases[kind] + 1
  end
end
assert(cases.squash > 0 and cases.neither > 0, "the history has squash-landed and unlanded commits")

-- ---------- status_clean, listed_on ----------
local wt1, wt2, wt3 = d .. "/wt1", d .. "/wt2", d .. "/wt3"
git(repo, "worktree", "add", "-q", "-b", "w1", wt1, "main")
git(repo, "worktree", "add", "-q", "-b", "w2", wt2, "main")
git(repo, "worktree", "add", "-q", "-b", "w3", wt3, "main")
assert(listed(repo)[wt1] and listed(repo)[wt2] and listed(repo)[wt3], "listed_on: an added worktree is listed")
assert(clean(wt1), "status_clean: a fresh worktree is clean")
write(wt1 .. "/new", "x\n")
assert(not clean(wt1), "status_clean: an untracked file is unclean")
os.execute("mkdir -p " .. wt1 .. "/sub")
os.remove(wt1 .. "/new"); write(wt1 .. "/sub/new", "x\n")
assert(not clean(wt1), "status_clean: an untracked file in a new directory is unclean")
git(wt1, "add", "-A"); git(wt1, "commit", "-q", "-m", "w1")
assert(clean(wt1), "status_clean: committed is clean")
write(wt1 .. "/base", "changed\n")
assert(not clean(wt1), "status_clean: a changed tracked file is unclean")
git(wt1, "checkout", "-q", "--", "base")
assert(clean(wt1))

-- ---------- wt_remove ----------
write(wt2 .. "/untracked", "x\n")
local before = durable(repo)
assert(gx(repo, "worktree", "remove", wt2) ~= 0, "wt_remove: a dirty worktree is refused")
assert(durable(repo) == before and lfs.attributes(wt2 .. "/untracked"), "wt_remove: a refused remove changes nothing")
local heads, commits = git(repo, "for-each-ref", "refs/heads"), git(repo, "rev-list", "--all")
assert(gx(repo, "worktree", "remove", wt1) == 0, "wt_remove: a clean worktree is removed")
assert(not lfs.attributes(wt1), "wt_remove: its directory goes")
assert(not listed(repo)[wt1] and listed(repo)[wt2] and listed(repo)[wt3], "listed_on: a removed worktree is not listed, the rest are")
assert(git(repo, "for-each-ref", "refs/heads") == heads and git(repo, "rev-list", "--all") == commits,
  "wt_remove: every branch (its own too) and commit stays")
assert(git(wt2, "status", "--porcelain") == "?? untracked" and clean(wt3), "wt_remove: other worktrees stay as they were")

-- ---------- del_ref ----------
-- watchd.delete_branch: `branch -d` when merged into the main checkout's HEAD, else `update-ref -d` guarded by the tip
-- the sweep checked
local a = git(repo, "rev-parse", "w1")
git(repo, "branch", "-f", "w1", "b2")  -- w1 moved since the check, to work not in HEAD
local refs = git(repo, "for-each-ref", "refs/heads")
assert(gx(repo, "merge-base", "--is-ancestor", "w1", "HEAD") ~= 0)
watchd.delete_branch(repo, "w1", a, {})
assert(git(repo, "for-each-ref", "refs/heads") == refs, "del_ref: a branch that moved since the check is kept")
watchd.delete_branch(repo, "main", git(repo, "rev-parse", "main"), { main = true })
assert(git(repo, "for-each-ref", "refs/heads") == refs, "del_ref: a protected branch is kept")
watchd.delete_branch(repo, "w1", git(repo, "rev-parse", "w1"), {})
assert(gx(repo, "rev-parse", "-q", "--verify", "refs/heads/w1") ~= 0, "del_ref: the checked tip is deleted")
assert(git(repo, "for-each-ref", "refs/heads") == refs:gsub("[^\n]*refs/heads/w1\n?", ""):gsub("\n$", ""),
  "del_ref: no other branch goes")

-- ---------- touched_recent ----------
assert(watchd.SWEEP_IDLE == 1800, "touched_recent: Env.sweepIdle is watchd.SWEEP_IDLE")
local function last(wt)  -- sweep_worktrees' reading
  local gd = git(wt, "rev-parse", "--absolute-git-dir")
  local l = 0
  for _, p in ipairs({ wt, util.join(gd, "logs", "HEAD") }) do l = math.max(l, lfs.attributes(p, "modification") or 0) end
  return l
end
local function recent(wt) return util.now() - last(wt) < watchd.SWEEP_IDLE end
os.execute("mkdir -p " .. wt3 .. "/sub"); write(wt3 .. "/sub/x", "1\n")
git(wt3, "add", "-A"); git(wt3, "commit", "-q", "-m", "w3")
assert(recent(wt3), "touched_recent: a commit touches it")
local old = util.now() - 1860
lfs.touch(wt3, old, old); lfs.touch(git(wt3, "rev-parse", "--absolute-git-dir") .. "/logs/HEAD", old, old)
assert(not recent(wt3), "touched_recent: 31 min untouched is not recent")
write(wt3 .. "/sub/x", "2\n")  -- the model's edit makes it recent; the directory's mtime doesn't move for a nested file
assert(not recent(wt3) and not clean(wt3), "touched_recent: a nested edit leaves it not recent, but unclean, so unswept")
git(wt3, "commit", "-q", "-am", "w3 again")
assert(recent(wt3), "touched_recent: the commit touches logs/HEAD")

-- ---------- kill0_alive, cwds_proc ----------
local pid = spawn(wt3, "sleep", "30")
unistd.sleep(1)  -- exec'd: its cwd is wt3
assert(kill0(pid), "kill0_alive: a live process answers kill 0")
local cw = assert(machine.cwds(), "cwds_proc: machine.cwds answers")
assert(cw[pid] and watchd.inside(stdlib.realpath(cw[pid]), wt3), "cwds_proc: a process in a worktree is seen inside it")
signal.kill(pid, signal.SIGTERM)
unistd.sleep(1)
assert(kill0(pid), "kill0_alive: a zombie (dead, not yet reaped) still answers kill 0: alive means in the process table")
wait.wait(pid)
assert(not kill0(pid), "kill0_alive: a reaped process doesn't")
for p, c in pairs(machine.cwds() or {}) do
  assert(not watchd.inside(stdlib.realpath(c) or c, wt3), "cwds_proc: no process left inside, but " .. p)
end

-- ---------- now_mono ----------
local t0, prev = util.now(), util.now()
for _ = 1, 100000 do local t = util.now(); assert(t >= prev, "now_mono: os.time() never goes back"); prev = t end
unistd.sleep(1)
assert(util.now() > t0, "now_mono: it moves on")

-- ---------- hc_ls_live, hc_run_starts, hc_kill_ends ----------
if os.getenv("SWARM_TEST_HC") == "1" then
  local json = require "swarm.json"
  stdlib.setenv("XDG_STATE_HOME", nil)  -- run.lua points it at a scratch dir; hc keeps its socket under the real one
  local function live(addr)
    for _, x in ipairs(assert(agents.hc_terminals(), "hc_ls_live: hc ls answers")) do
      if x.address == addr then return x.state == "live" end
    end
    return false
  end
  local pidf = d .. "/hc-run.pid"  -- started as `--restart` starts a watchd (watchd.restart's flags)
  local out, err, code = proc.exec({ "hc", "run", "--json", "--bg", "--no-parent", "--no-notify", "--name",
    "swarm-env-" .. unistd.getpid(), "--cwd", wt3, "--", "sh", "-c", 'echo $$ > "$0"; exec sleep 300', pidf })
  assert(code == 0, "hc run: " .. err)
  local addr = json.decode(out).address
  local here = os.getenv("HC_TERMINAL_ID")
  assert(live(addr), "hc_ls_live: a started terminal is listed live")
  local pid
  for _ = 1, 100 do
    pid = tonumber(util.slurp(pidf) or "")
    if pid then break end
    require("posix.time").nanosleep({ tv_sec = 0, tv_nsec = 100000000 })
  end
  assert(pid and signal.kill(pid, 0) == 0, "hc_run_starts: the program it was given runs")
  assert(live(addr), "hc_run_starts: in the live terminal it printed")
  local g = durable(repo)
  proc.run({ "hc", "kill", addr })
  assert(not live(addr), "hc_kill_ends: a killed terminal is not listed live")
  assert(not here or live(here), "hc_kill_ends: no other terminal ends")
  assert(durable(repo) == g, "hc_kill_ends: the repo's durable state stays")
  proc.run({ "hc", "rm", addr })
else
  io.stderr:write("env_spec: hc_ls_live, hc_run_starts, hc_kill_ends skipped (SWARM_TEST_HC=1 runs them)\n")
end

-- ---------- gh_checks, gh_state ----------
-- What ci.pr_watch reads from `gh pr list` against what GitHub's REST API says of the same PRs: their check runs and
-- commit statuses, and whether they are merged (the merge commit then on the base, by git).
if os.getenv("SWARM_TEST_GH") == "1" then
  local json, ci = require "swarm.json", require "swarm.ci"
  local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
  local top = util.strip(proc.run({ "git", "rev-parse", "--show-toplevel" }, here) or "")
  stdlib.setenv("PATH", PATH0)
  local function api(path, jq) return json.decode(assert(proc.run({ "gh", "api", path, "--jq", jq }, top), "gh api " .. path)) end
  local prs = json.decode(assert(proc.run({ "gh", "pr", "list", "--state", "all", "--limit", "6", "--json",
    "number,headRefOid,baseRefName,state,mergeCommit,statusCheckRollup" }, top), "gh pr list answers"))
  local n = 0
  for _, pr in ipairs(prs) do
    if pr.state == "OPEN" or pr.state == "MERGED" then
      n = n + 1
      local sha = pr.headRefOid
      local runs = api("repos/{owner}/{repo}/commits/" .. sha .. "/check-runs?per_page=100", "[.check_runs[] | {status, conclusion}]")
      local sts = api("repos/{owner}/{repo}/commits/" .. sha .. "/status", "[.statuses[] | .state]")
      local want, red = (#runs + #sts > 0) and "green" or "pending", false
      for _, r in ipairs(runs) do
        if r.status ~= "completed" then want = "pending"
        elseif r.conclusion ~= "success" and r.conclusion ~= "neutral" and r.conclusion ~= "skipped" then red = true end
      end
      for _, st in ipairs(sts) do
        if st == "pending" then want = "pending" elseif st ~= "success" then red = true end
      end
      if want == "green" and red then want = "red" end
      assert(ci.verdict(pr.statusCheckRollup) == want, ("gh_checks: PR #%d: the rollup reads %s, its check runs and statuses %s"):format(
        pr.number, ci.verdict(pr.statusCheckRollup), want))
      local merged = api("repos/{owner}/{repo}/pulls/" .. pr.number, ".merged")
      assert((pr.state == "MERGED") == merged, ("gh_state: PR #%d is %s, and merged is %s"):format(pr.number, pr.state, tostring(merged)))
      if merged then
        proc.run({ "git", "fetch", "-q", "origin", pr.baseRefName }, top)
        assert(proc.gx({ "merge-base", "--is-ancestor", pr.mergeCommit.oid, "origin/" .. pr.baseRefName }, top) == 0,
          ("gh_state: PR #%d's merge commit is on %s"):format(pr.number, pr.baseRefName))
      end
    end
  end
  assert(n > 0, "gh_checks: the repo has an open or merged PR")
  stdlib.setenv("PATH", d .. "/bin:" .. PATH0)
else
  io.stderr:write("env_spec: gh_checks, gh_state skipped (SWARM_TEST_GH=1 runs them)\n")
end

os.execute("rm -rf " .. d)
