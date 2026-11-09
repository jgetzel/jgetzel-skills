-- main's CI: watchd's poll into the ci table, the red-run task, merge-to-green per task; cmd ci reads the table.
local util, db, proc, json = require "swarm.util", require "swarm.db", require "swarm.proc", require "swarm.json"
local msgs, agents = require "swarm.msgs", require "swarm.agents"
local lfs, ptime = require "lfs", require "posix.time"
local d, now = util.d, util.now
local M = {}

-- "2026-11-08T10:00:00Z" as epoch seconds (UTC), as Python's fromisoformat(...).timestamp().
local function ts(s)
  local y, mo, dd, h, mi, se = s:match("^(%d+)-(%d+)-(%d+)T(%d+):(%d+):(%d+)")
  y, mo, dd = tonumber(y), tonumber(mo), tonumber(dd)
  if mo <= 2 then y = y - 1 end
  local era, mp = math.floor(y / 400), (mo + 9) % 12
  local yoe = y - era * 400
  local doe = yoe * 365 + math.floor(yoe / 4) - math.floor(yoe / 100) + math.floor((153 * mp + 2) / 5) + dd - 1
  return (era * 146097 + doe - 719468) * 86400 + tonumber(h) * 3600 + tonumber(mi) * 60 + tonumber(se)
end
M.ts = ts

-- True, and stamps the time, if `key` was last stamped `every` seconds ago or never.
function M.due(c, key, every)
  local r = c:one("select v from meta where k=?", key)
  if r and now() - tonumber(r.v) < every then return false end
  c:exec("insert or replace into meta(k,v) values(?,?)", key, d(now()))
  return true
end

-- For done tasks without merge data: find the PR (evidence 'PR #N' / 'pull/N', else the merged PR from the owner's
-- branch), its merged_at, and the first completed main CI run on the merge commit; if red, the next green run.
function M.pr_ci(c, repo)
  local todo = c:all("select * from task where state='done' and merged_at is null and done_at>?", now() - 86400)
  if #todo == 0 or not M.due(c, "pr_polled", 600) then return end  -- every gh call counts against the API limit
  local prs = json.decode(proc.run({ "gh", "pr", "list", "--state", "merged", "--limit", "100", "--json",
    "number,mergedAt,mergeCommit,headRefName" }, repo) or "[]")
  if type(prs) ~= "table" then return end
  local runs = {}
  for _, x in ipairs(c:all("select * from ci order by created")) do
    runs[#runs + 1] = { headSha = x.sha, conclusion = x.conclusion, status = x.status, createdAt = x.created, updatedAt = x.updated }
  end
  local function completed(f)
    for _, x in ipairs(runs) do
      if x.status == "completed" and f(x) then return x end
    end
  end
  for _, r in ipairs(todo) do
    local ev, num = r.evidence or "", nil
    local a, b = ev:match("PR #(%d+)"), ev:match("pull/(%d+)")
    local pa, pb = ev:find("PR #%d"), ev:find("pull/%d")
    num = tonumber((pa and (not pb or pa < pb)) and a or b)
    local pr
    for _, x in ipairs(prs) do
      if num and x.number == num then pr = x; break end
    end
    if not pr then
      for _, x in ipairs(prs) do
        if util.startswith(x.headRefName, tostring(r.owner) .. "/") and ts(x.mergedAt) >= (r.first_claimed_at or 0)
            and (not pr or x.mergedAt > pr.mergedAt) then
          pr = x
        end
      end
    end
    if pr then
      local merged = ts(pr.mergedAt)
      local oid = pr.mergeCommit and pr.mergeCommit.oid
      local mine = completed(function(x) return x.headSha == oid end)
      if not mine then  -- CI not finished; ci_conclusion stays null
        c:exec("update task set pr=?, merged_at=? where id=?", pr.number, merged, r.id)
      else
        local green = mine
        if mine.conclusion ~= "success" then
          green = completed(function(x) return x.createdAt > mine.createdAt and x.conclusion == "success" end)
        end
        c:exec("update task set pr=?, merged_at=?, ci_conclusion=?, ci_green_at=? where id=?",
          pr.number, merged, mine.conclusion, green and ts(green.updatedAt) or nil, r.id)
      end
    end
  end
end

-- The one place the swarm asks GitHub about main's CI: a run list a minute into the ci table, and each red run's
-- failed jobs once. Agents read the table (`swarm ci`), so N agents cost one poll, not N.
function M.ci_poll(c, repo, every)
  local err = c:one("select v from meta where k='ci_error'")
  if err and now() - tonumber(err.v) < 300 then return end  -- refused: GitHub's secondary limit grows with retries
  if not M.due(c, "ci_polled", every or 60) then return end
  -- The runs endpoint itself: one request, where `gh run list` first lists every workflow (a second request)
  local out = proc.run({ "gh", "api", "repos/{owner}/{repo}/actions/runs?branch=main&per_page=20", "--jq",
    "[.workflow_runs[] | {databaseId: .id, headSha: .head_sha, status, conclusion, url: .html_url,"
    .. " createdAt: .created_at, updatedAt: .updated_at}]" }, repo)
  local runs = out and out ~= "" and json.decode(out) or nil
  if type(runs) ~= "table" then  -- rate limited or offline: keep what's stored, try again next minute
    c:exec("insert or replace into meta(k,v) values('ci_error',?)", d(now()))
    return
  end
  c:exec("delete from meta where k='ci_error'")
  for _, r in ipairs(runs) do
    c:exec("insert into ci(id,sha,status,conclusion,url,created,updated) values(?,?,?,?,?,?,?) on conflict(id) do update set "
      .. "status=excluded.status, conclusion=excluded.conclusion, updated=excluded.updated",
      r.databaseId, r.headSha, r.status, (r.conclusion ~= "" and r.conclusion or nil), r.url, r.createdAt, r.updatedAt)
  end
  for _, r in ipairs(c:all("select id from ci where conclusion='failure' and failed is null")) do
    local jobs = proc.run({ "gh", "run", "view", d(r.id), "--json", "jobs", "--jq",
      '[.jobs[] | select(.conclusion=="failure") | .name] | join(", ")' }, repo)
    if jobs then c:exec("update ci set failed=? where id=?", util.strip(jobs), r.id) end
  end
end

function M.ci_check(c, repo, comms)
  local runs = c:all("select * from ci where status='completed' and conclusion!='cancelled' order by created desc limit 10")
  if #runs == 0 then return end
  local red = runs[1]
  local RED = require("swarm.tasks").RED_TASK
  local open_red = c:all("select id,title,owner from task where title like ? and state in ('open','claimed','blocked')", RED .. "%")
  if red.conclusion == "success" then
    for _, t in ipairs(open_red) do  -- only a run at least as new as the red one: a re-run in progress leaves an older green on top
      local n = t.title:match("^" .. RED:gsub("%p", "%%%0") .. "run (%d+)")
      if not (n and red.id < tonumber(n)) then
        c:exec("update task set state='done', evidence=?, lease_until=null, done_at=? where id=?",
          ("green run %s at %s"):format(d(red.id), red.sha:sub(1, 7)), now(), t.id)
        db.log(c, "swarm", "done", nil, ("#%s green run %s"):format(d(t.id), d(red.id)))
        if t.owner then
          msgs.post(c, "swarm", t.owner, ("main is green (run %s): #%s is done; stop fixing it."):format(d(red.id), d(t.id)),
            false, "system")
        end
      end
    end
    return
  end
  if red.conclusion ~= "failure" and red.conclusion ~= "timed_out" and red.conclusion ~= "startup_failure" then return end
  if c:one("select 1 from event where kind='ci-red' and data=?", d(red.id)) then return end
  db.log(c, "swarm", "ci-red", nil, d(red.id))
  local failed = red.failed and red.failed ~= "" and red.failed
  if #open_red > 0 then  -- one fixer per red stretch: a later red goes into its body, and its fixer waits for a green run
    c:exec("update task set body=body || ? where id=?",
      ("\nLater red: run %s at %s"):format(d(red.id), red.sha:sub(1, 7)) .. (failed and (" (" .. failed .. ")") or ""), open_red[1].id)
    return
  end
  local green
  for _, r in ipairs(runs) do
    if r.conclusion == "success" then green = r; break end
  end
  local rng = green and (green.sha .. ".." .. red.sha) or ("-20 " .. red.sha)
  local argv = { "git", "log", "--format=%B%x1e" }
  for _, x in ipairs(util.split(rng)) do argv[#argv + 1] = x end
  local set, names = {}, {}
  for _, l in ipairs(util.splitlines(proc.run(argv, repo) or "")) do
    local n = l:match("^Swarm%-Agent:%s*(%S+)")
    if n and not set[n] then set[n] = true; names[#names + 1] = n end
  end
  table.sort(names)
  local lines = util.splitlines(proc.run({ "gh", "run", "view", d(red.id), "--log-failed" }, repo) or "")
  local tail = table.concat(lines, "\n", math.max(1, #lines - 29), #lines)
  local about = ("main CI is red (run %s %s), commits %s, authors: %s."):format(d(red.id), red.url or "None", rng,
    #names > 0 and table.concat(names, ", ") or "none")
  local title = RED .. "run " .. d(red.id) .. (failed and (" (" .. failed .. ")") or "")
  c:exec("insert into task(title,body,created_by,created_at) values(?,?,?,?)", title,
    about .. " Fix forward on main; watchd marks this done on the next green run.\n" .. tail, "swarm", now())
  local tid = c:last_id()
  db.log(c, "swarm", "task-add", nil, ("#%s %s"):format(d(tid), title))
  local live = {}
  for _, x in ipairs(agents.live_agents(c)) do live[x.name] = true end
  local msg = ("%s Task #%s is its one fix: `swarm task claim %s` if your commit broke it, then fix forward; "
    .. "if someone holds it, leave it to them."):format(about, d(tid), d(tid))
  local suspects = 0
  for _, n in ipairs(names) do
    if live[n] then suspects = suspects + 1; msgs.post(c, "swarm", n, msg, true, "system") end
  end
  if suspects == 0 and comms then  -- nobody who committed is live: the board's task gets a fresh agent
    msgs.post(c, "swarm", comms, msg .. " No live agent has commits in it.", true, "system")
  end
end

-- The newest main CI run that includes `sha` (its head is sha or a descendant), skipping cancelled ones, which a
-- newer push replaced: state (success/failure/pending), row; pending with no row if none is known yet.
function M.ci_for(c, sha, cwd)
  for _, r in ipairs(c:all("select * from ci order by created desc")) do
    if r.sha == sha or proc.gx({ "merge-base", "--is-ancestor", sha, r.sha }, cwd) == 0 then
      if r.status ~= "completed" then return "pending", r end
      if r.conclusion ~= "cancelled" then
        return r.conclusion == "success" and "success" or "failure", r
      end
    end
  end
  return "pending", nil
end

-- main's CI for a commit, from what watchd polled: never asks GitHub itself. Exit 0 green, 1 red, 2 pending,
-- 124 timed out waiting.
function M.cmd_ci(c, a)
  local cwd = lfs.currentdir()
  local sha = proc.git({ "rev-parse", a.sha }, cwd) or a.sha
  local deadline, fetched, warned = now() + a.timeout, 0, false
  local state, r
  while true do
    local polled = c:one("select v from meta where k='ci_polled'")
    if (not polled or now() - tonumber(polled.v) > 300) and not warned then
      warned = true
      io.stderr:write("swarm ci: nobody is polling CI (the communicator runs `swarm watchd --ci`); tell it.\n")
    end
    state, r = M.ci_for(c, sha, cwd)
    if state ~= "pending" or not a.wait then break end
    if now() >= deadline then
      io.stderr:write(("%s: still pending after %ss\n"):format(sha:sub(1, 7), d(a.timeout)))
      util.exit(124)
    end
    if now() - fetched >= 60 then  -- a newer run's head must be local for the ancestry check; git, not the API
      proc.run({ "git", "fetch", "-q", "origin" }, cwd)
      fetched = now()
    end
    ptime.nanosleep({ tv_sec = math.floor(a.poll), tv_nsec = math.floor((a.poll % 1) * 1e9) })
  end
  if not r then
    print(("%s: no main CI run includes it yet"):format(sha:sub(1, 7)))
  else
    local failed = r.failed and r.failed ~= "" and ("; failed: " .. r.failed) or ""
    print(("%s: %s (run %s at %s %s%s)"):format(sha:sub(1, 7), state, d(r.id), r.sha:sub(1, 7), r.url or "", failed))
  end
  util.exit(state == "success" and 0 or state == "failure" and 1 or 2)
end

return M
