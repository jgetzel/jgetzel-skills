-- Evidence for a swarm retro, read from the swarm db: who did what, where time and attention went.
-- Run through the swarm-report launcher. See --help. Read-only.
local lfs = require "lfs"
local argparse = require "argparse"
local utf8 = require "lua-utf8"
local json = require "swarm.json"
local util = require "swarm.util"
local db = require "swarm.db"
local proc = require "swarm.proc"

-- conflict/shared-tree come from watchd's trial merges; conflict-compat is a line conflict whose tokens merge (no notice sent);
-- conflict-stale is a pair skipped because one agent's own changes conflict with main;
-- overlap is the pre-sw-locks touch notice, kept so old dbs still report
local CONFLICTS = { conflict = 1, ["conflict-compat"] = 1, ["shared-tree"] = 1, ["conflict-error"] = 1, ["conflict-stale"] = 1, overlap = 1 }
local FRICTION = { conflict = 1, ["shared-tree"] = 1, overlap = 1, reap = 1, compact = 1, ["ci-red"] = 1, blocked = 1 }  -- push is counted, not listed
local COLD_IDLE = 55 * 60  -- as swarm: the prompt cache is warm this long
local SOURCES = { { "inbox", "swarm messages" }, { "machine", "machine:" }, { "conflict", "worktree" }, { "digest", "idle" } }
local NULL = json.null

local M = {}

local function pick(row, keys)  -- the keys of row, a missing one as JSON null
  local o = {}
  for _, k in ipairs(keys) do
    local v = row[k]
    if v == nil then v = NULL end
    o[k] = v
  end
  return o
end

local function count(xs, f)  -- {key = n} over xs, f(x) -> key or nil to skip
  local n = {}
  for _, x in ipairs(xs) do
    local k = f(x)
    if k ~= nil then n[k] = (n[k] or 0) + 1 end
  end
  return n
end

local function pct(xs, p)
  if #xs == 0 then return nil end
  table.sort(xs)
  return xs[math.min(#xs, math.floor(p * #xs) + 1)]
end

local function span(s)
  s = math.floor(s or 0)
  if s >= 3600 then return ("%dh%02dm"):format(math.floor(s / 3600), math.floor(s % 3600 / 60)) end
  return ("%dm%02ds"):format(math.floor(s / 60), s % 60)
end

local function sorted_keys(t)
  local ks = {}
  for k in pairs(t) do ks[#ks + 1] = k end
  table.sort(ks)
  return ks
end

function M.dbpath(a)
  if a then return a end
  return db.dbpath()
end

-- Per-task timing from the CLI's own `swarm state --json`, so the report and `swarm state` agree.
function M.state_tasks(path)
  local cli = os.getenv("SWARM_RETRO_HERE") .. "/../swarm/swarm"
  local out, err, code = proc.exec({ cli, "state", "--json" }, { env = { SWARM_DB = path } })
  if code ~= 0 then util.die("swarm-report: swarm state --json failed: " .. util.strip(err)) end
  return json.decode(out).tasks or {}
end

local function lines(f, n)  -- iterator over the first n lines (all if nil) of file f
  local fh = io.open(f)
  local i = 0
  return function()
    i = i + 1
    local l = fh and (not n or i <= n) and fh:read("*l") or nil
    if not l and fh then fh:close(); fh = nil end
    return l
  end
end

function M.transcripts(name, cwd)
  if not cwd or cwd == "" then return {} end
  local d = (os.getenv("HOME") or "") .. "/.claude/projects/" .. cwd:gsub("[^A-Za-z0-9]", "-")
  local esc, hit = name:gsub("%p", "%%%0"), {}
  if not lfs.attributes(d, "mode") then return hit end
  for f in lfs.dir(d) do
    if f:match("%.jsonl$") then
      for line in lines(d .. "/" .. f, 40) do  -- the record sits near the top
        local m = line:match('"type":"agent%-name","agentName":"([^"]+)"')
        if m then
          if m == name or m:match("^" .. esc .. "%-%d+$") then hit[#hit + 1] = d .. "/" .. f end
          break
        end
      end
    end
  end
  table.sort(hit, function(a, b) return lfs.attributes(a, "modification") < lfs.attributes(b, "modification") end)
  return hit
end

-- Bytes of hook-injected context (additionalContext, as hook_additional_context attachments) per source.
function M.hook_bytes(files)
  local n = {}
  for _, f in ipairs(files) do
    for line in lines(f) do
      if line:find('"hook_additional_context"', 1, true) then
        local a = (json.decode(line) or {}).attachment or {}
        local cs = type(a.content) == "string" and { a.content } or a.content or {}
        for _, c in ipairs(cs) do
          local src = "other"
          for _, s in ipairs(SOURCES) do
            if c:sub(1, 80):find(s[2], 1, true) then src = s[1]; break end
          end
          n[src] = (n[src] or 0) + (utf8.len(c) or #c)
        end
      end
    end
  end
  return n
end

-- Bytes of the spawn prompt (brief + roster + task + repo rules): the first user message of the first transcript.
function M.brief_size(files, default)
  if files[1] then
    for line in lines(files[1]) do
      if line:find('"type":"user"', 1, true) then
        local m = ((json.decode(line) or {}).message or {}).content
        if type(m) == "string" then return utf8.len(m) or #m end
      end
    end
  end
  return default
end

-- Wakes after >= COLD_IDLE of that agent's silence with no compaction in between (the wake re-sent its context uncached).
function M.cold_wakes(ev)
  local n, last, comp = 0, {}, {}
  for _, e in ipairs(ev) do
    local a = e.agent or ""
    if e.kind == "wake" and last[a] and e.ts - last[a] >= COLD_IDLE and (comp[a] or -1) < last[a] then n = n + 1 end
    if e.kind == "compact" then comp[a] = e.ts end
    last[a] = e.ts
  end
  return n
end

local function brief_bytes()
  local a = lfs.attributes(os.getenv("SWARM_RETRO_HERE") .. "/../swarm/brief.md")
  return a and a.size or 0
end

local function sh(...)
  local out, _, code = proc.exec({ ... })
  return code == 0 and out or ""
end

-- Landed commits per agent-hour and files two or more agents changed, from Swarm-Agent: lines anywhere in the message.
function M.git_evidence(since, ref)
  since = since or 0
  local args = { "git", "log", ref or "origin/main" }
  if since ~= 0 then args[#args + 1] = "--since=" .. ("%d"):format(since) end
  for _, x in ipairs({ "--name-only", "--format=%x01%H%x00%ct%x00%B%x00" }) do args[#args + 1] = x end
  local hours, files, commits, order = {}, {}, {}, {}
  local blks = util.split(sh(unpack(args)), "\1")
  for i = 2, #blks do
    local p = util.split(blks[i], "\0")
    local sha, ct, body, rest = p[1], tonumber(p[2]), p[3], p[4]
    -- squash merges put the line in its own paragraph, so a trailer parse misses it
    local agent = ("\n" .. body):match("\nSwarm%-Agent:%s*(%S+)") or "(none)"
    commits[#commits + 1] = { ct, sha, agent }
    local k = os.date("%Y-%m-%d %H:00", ct) .. "\0" .. agent
    if not hours[k] then hours[k] = 0; order[#order + 1] = k end
    hours[k] = hours[k] + 1
    for _, f in ipairs(util.split(util.strip(rest), "\n")) do
      if f ~= "" then
        files[f] = files[f] or {}
        files[f][agent] = true
      end
    end
  end
  table.sort(order)
  local cph, none = json.array(), 0
  for _, k in ipairs(order) do
    local h, a = k:match("^(.-)%z(.*)$")
    if a == "(none)" then none = none + hours[k] else cph[#cph + 1] = { hour = h, agent = a, n = hours[k] } end
  end
  local multi = {}
  for f, as in pairs(files) do
    local l, n = sorted_keys(as), 0
    for _, a in ipairs(l) do if a ~= "(none)" then n = n + 1 end end
    if n > 1 then multi[f] = json.array(l) end
  end
  return { commits_per_hour = cph, not_swarm_commits = none, multi_agent_files = multi, _commits = commits }
end

-- Failed main runs and the agent whose later green run's commit fixed it (needs gh).
function M.red_runs(commits, since)
  local runs = json.decode(sh("gh", "run", "list", "--branch", "main", "--limit", "100", "--json", "conclusion,headSha,createdAt,databaseId"))
  local by, keep = {}, {}
  for _, c in ipairs(commits) do by[c[2]] = c[3] end
  local from = os.date("!%Y-%m-%dT%H:%M:%S", since or 0)
  for _, r in ipairs(type(runs) == "table" and runs or {}) do
    if r.createdAt >= from then keep[#keep + 1] = r end
  end
  table.sort(keep, function(a, b) return a.createdAt < b.createdAt end)
  local out = json.array()
  for i, r in ipairs(keep) do
    if r.conclusion == "failure" then
      local fix
      for j = i + 1, #keep do
        if keep[j].conclusion == "success" then fix = keep[j]; break end
      end
      out[#out + 1] = { run = r.databaseId, broke = by[r.headSha] or "?", fixed_by = fix and (by[fix.headSha] or "?") or NULL }
    end
  end
  return out
end

-- `swarm run` jobs per machine ('here' = local): count, minutes, exit codes, lost and unfinished, sync and bring-back seconds.
function M.jobs(ev)
  local function data(e)
    return (e.data or ""):sub(1, 1) == "{" and json.decode(e.data) or {}
  end
  local ends, out = {}, {}
  for _, e in ipairs(ev) do
    if e.kind == "job-end" then ends[e.path] = data(e) end
  end
  for _, e in ipairs(ev) do
    if e.kind == "job-start" then
      local s, x = data(e), ends[e.path]
      local mname = s.machine or "here"
      out[mname] = out[mname] or { jobs = 0, minutes = 0, exits = {}, lost = 0, unfinished = 0, sync_s = 0, back_s = 0 }
      local m = out[mname]
      m.jobs = m.jobs + 1
      if x == nil then
        m.unfinished = m.unfinished + 1
      else
        m.minutes = m.minutes + math.floor((x.s or 0) / 60 * 10 + 0.5) / 10
        if x.exit == "lost" then
          m.lost = m.lost + 1
        else
          local k = tostring(x.exit)
          m.exits[k] = (m.exits[k] or 0) + 1
        end
        m.sync_s = m.sync_s + (x.sync_s or 0)
        m.back_s = m.back_s + (x.back_s or 0)
      end
    end
  end
  return out
end

local EVK = { "ts", "agent", "kind", "path", "data" }
local TASK_KEYS = { "id", "title", "state", "owner", "evidence", "queue_wait_s", "work_s", "total_s", "blocked_s", "claims", "releases",
  "holders", "merge_to_green_s", "ci_conclusion" }

-- c: read-only db; state: the tasks list of `swarm state --json`
function M.report(c, since, git, state)
  if since == nil then  -- default window: the swarm's start
    since = c:one("select coalesce(min(started),0) m from agent").m
  end
  local ev = c:all("select * from event where ts>=? order by ts, id", since)
  local out = { since = since, agents = json.array(c:all(
    "select name,model,cwd,started,ended,ctx_tokens,status from agent where coalesce(started,0)>=? or ended is null", since)) }
  local tasks, works, qw, m2g, red, blocked, reclaimed = json.array(), {}, {}, {}, json.array(), 0, json.array()
  for _, t in ipairs(state or {}) do
    local r = pick(t, TASK_KEYS)
    r.took = t.work_s ~= nil and span(t.work_s) or NULL
    tasks[#tasks + 1] = r
    if t.work_s ~= nil then works[#works + 1] = t.work_s end
    if t.queue_wait_s ~= nil then qw[#qw + 1] = t.queue_wait_s end
    if t.merge_to_green_s ~= nil then m2g[#m2g + 1] = t.merge_to_green_s end
    if t.ci_conclusion == "failure" then red[#red + 1] = t.id end
    blocked = blocked + (t.blocked_s or 0)
    if (t.claims or 0) > 1 then reclaimed[#reclaimed + 1] = { id = t.id, claims = t.claims, holders = t.holders or json.array() } end
  end
  local longest = {}
  for i, t in ipairs(tasks) do
    if t.work_s ~= NULL and t.work_s ~= nil then longest[#longest + 1] = { i, t } end
  end
  table.sort(longest, function(a, b) if a[2].work_s ~= b[2].work_s then return a[2].work_s > b[2].work_s end return a[1] < b[1] end)
  local top = json.array()
  for i = 1, math.min(5, #longest) do
    local t = longest[i][2]
    top[i] = { id = t.id, title = t.title, work_s = t.work_s }
  end
  local qmax
  for _, x in ipairs(qw) do if not qmax or x > qmax then qmax = x end end
  out.task_durations = { n_done = #works, work_median_s = pct(works, .5), work_p90_s = pct(works, .9), longest = top,
    queue_wait_median_s = pct(qw, .5), queue_wait_max_s = qmax, merge_to_green_median_s = pct(m2g, .5),
    red_after_merge = red, blocked_total_s = blocked, reclaimed = reclaimed }
  out.tasks = tasks
  local byagent = {}
  for _, e in ipairs(ev) do
    local a = e.agent or "watchd"
    byagent[a] = byagent[a] or {}
    byagent[a][e.kind] = (byagent[a][e.kind] or 0) + 1
  end
  out.events = byagent
  local b = brief_bytes()
  local hs, total_brief = {}, 0
  for _, a in ipairs(out.agents) do  -- transcripts: files whose agent-name record is this agent or a relaunched successor (name-2)
    local n = a.name
    a.transcripts = json.array(M.transcripts(n, a.cwd))
    a.hook_bytes = M.hook_bytes(a.transcripts)
    a.brief_bytes = M.brief_size(a.transcripts, b)
    local q = function(sql, ...) return c:one(sql, ...).n end
    a.msgs_sent = q("select count(*) n from msg where frm=? and ts>=?", n, since)
    a.msgs_to_all = q("select count(*) n from msg where frm=? and dest='@all' and ts>=?", n, since)
    a.msgs_recv = q("select count(*) n from msg where (dest=? or dest='@all') and frm!=? and coalesce(kind,'') not in ('system','notice') and ts>=?", n, n, since)
    a.tasks_done_no_evidence = q("select count(*) n from task where owner=? and state='done' and coalesce(evidence,'')=''", n)
    for k, v in pairs(a.hook_bytes) do hs[k] = (hs[k] or 0) + v end
    total_brief = total_brief + a.brief_bytes
    for _, k in ipairs({ "model", "cwd", "started", "ended", "ctx_tokens" }) do if a[k] == nil then a[k] = NULL end end
  end
  local hook_total = 0
  for _, v in pairs(hs) do hook_total = hook_total + v end
  out.always_loaded = { brief_md_bytes = b, agents = #out.agents, brief_total = total_brief, cold_wakes = M.cold_wakes(ev),
    hook_total = hook_total, hook_by_source = hs }
  out.friction, out.conflicts, out.idle_with_open_tasks = json.array(), json.array(), json.array()
  for _, e in ipairs(ev) do
    if FRICTION[e.kind] then table.insert(out.friction, pick(e, EVK)) end
    if CONFLICTS[e.kind] then table.insert(out.conflicts, pick(e, EVK)) end
    if e.kind == "digest" then table.insert(out.idle_with_open_tasks, { ts = e.ts, agent = e.agent or NULL }) end
  end
  local ps, start, eps, tot, maxh, kills, heavy = 0, nil, 0, 0, 0, 0, {}
  for _, e in ipairs(ev) do
    if e.kind == "pressure" then start = e.ts
    elseif e.kind == "pressure-end" and start then eps = eps + 1; tot = tot + e.ts - start; start = nil
    elseif e.kind == "heavy-count" then maxh = math.max(maxh, tonumber(e.data) or 0)
    elseif e.kind == "orphan-kill" then kills = kills + 1
    elseif e.kind == "heavy-start" and e.agent then heavy[e.agent] = (heavy[e.agent] or 0) + 1 end
  end
  out.pressure = { episodes = eps + (start and 1 or 0), total_s = tot, ongoing = start ~= nil, max_concurrent_heavy = maxh,
    orphan_kills = kills, heavy_starts = heavy }
  out.jobs = M.jobs(ev)
  if git ~= false then
    local g = M.git_evidence(since)
    out.red_main_runs = M.red_runs(g._commits, since)
    g._commits = nil
    for k, v in pairs(g) do out[k] = v end
  end
  out.messages = json.array(c:all("select frm, count(*) n, sum(urgent) urgent from msg where ts>=? group by frm", since))
  out.locks = json.array(c:all("select path,agent,reason from lock"))
  return out
end

local function show(r)
  local function t(s) return s and s ~= NULL and s ~= 0 and os.date("%H:%M", s) or "-" end
  local function f(x) return x ~= nil and x ~= NULL and span(x) or "-" end
  local function s(v) return (v == nil or v == NULL) and "None" or tostring(v) end
  local function kv(d, sep) local o = {} for _, k in ipairs(sorted_keys(d)) do o[#o + 1] = k .. "=" .. s(d[k]) end return table.concat(o, sep or ", ") end
  print("## agents")
  for _, a in ipairs(r.agents) do
    print(("- %s %s %s-%s %s ctx=%dk msgs sent/recv=%d/%d (@all %d) done-without-evidence=%d"):format(a.name,
      a.model ~= NULL and a.model or "?", t(a.started), t(a.ended), s(a.status), math.floor((a.ctx_tokens ~= NULL and a.ctx_tokens or 0) / 1000),
      a.msgs_sent, a.msgs_recv, a.msgs_to_all, a.tasks_done_no_evidence))
    for _, p in ipairs(a.transcripts) do print("    transcript: " .. p) end
  end
  local al, per = r.always_loaded, {}
  for _, x in ipairs(r.agents) do
    local n = 0
    for _, v in pairs(x.hook_bytes) do n = n + v end
    per[#per + 1] = x.name .. "=" .. n
  end
  print(("\n## always-loaded context\n- spawn prompts (swarm/brief.md %d B + roster, task, rules) x %d agents = %d B; cold-cache wakes re-sending context uncached: %d"
    .. "\n- hook-injected text: %d B (%s); per agent: %s"):format(al.brief_md_bytes, al.agents, al.brief_total, al.cold_wakes,
    al.hook_total, kv(al.hook_by_source), #per > 0 and table.concat(per, ", ") or "-"))
  print("\n## tasks")
  for _, k in ipairs(r.tasks) do
    print(("- #%s %s %s %s: %s"):format(s(k.id), s(k.state), k.owner ~= NULL and k.owner or "-", k.took ~= NULL and k.took or "-", s(k.title))
      .. (k.evidence ~= NULL and k.evidence ~= "" and ("\n    evidence: " .. k.evidence) or ""))
  end
  local d, ids = r.task_durations, {}
  for _, i in ipairs(d.red_after_merge) do ids[#ids + 1] = "#" .. i end
  print(("\n## task durations\n- %d done: work median %s, p90 %s; queue wait median %s, max %s; blocked total %s; merge to green CI median %s, red after merge: %s")
    :format(d.n_done, f(d.work_median_s), f(d.work_p90_s), f(d.queue_wait_median_s), f(d.queue_wait_max_s), f(d.blocked_total_s),
      f(d.merge_to_green_median_s), #ids > 0 and table.concat(ids, ", ") or "none"))
  for _, k in ipairs(d.longest) do print(("- longest: #%s %s %s"):format(s(k.id), f(k.work_s), s(k.title))) end
  for _, k in ipairs(d.reclaimed) do print(("- reclaimed: #%s claimed %dx by %s"):format(s(k.id), k.claims, table.concat(k.holders, ", "))) end
  print("\n## events per agent")
  local names = sorted_keys(r.events)
  table.sort(names, function(a, b) if (a == "watchd") ~= (b == "watchd") then return a == "watchd" end return a < b end)
  for _, a in ipairs(names) do print("- " .. a .. ": " .. kv(r.events[a])) end
  print("\n## friction")
  for _, e in ipairs(r.friction) do
    print((("- %s %s %s %s %s"):format(t(e.ts), s(e.agent), e.kind, e.path ~= NULL and e.path or "", e.data ~= NULL and e.data or ""):gsub("%s+$", "")))
  end
  local function section(title, key, keys)
    print("\n## " .. title)
    for _, x in ipairs(r[key] or {}) do
      local o = {}
      for _, k in ipairs(keys) do o[#o + 1] = k .. "=" .. s(x[k]) end
      print("- " .. table.concat(o, " "))
    end
  end
  section("landed commits per hour", "commits_per_hour", { "hour", "agent", "n" })
  print("- not swarm: " .. (r.not_swarm_commits or 0))
  section("red main runs", "red_main_runs", { "run", "broke", "fixed_by" })
  section("conflict, conflict-compat and shared-tree events", "conflicts", EVK)
  section("watchd digests (idle with open tasks)", "idle_with_open_tasks", { "ts", "agent" })
  local p = r.pressure
  print(("\n## resources\n- pressure episodes: %d (%s total%s)\n- max concurrent heavy: %d\n- orphan kills: %d\n- heavy starts per agent: %s")
    :format(p.episodes, span(p.total_s), p.ongoing and ", ongoing" or "", p.max_concurrent_heavy, p.orphan_kills,
      next(p.heavy_starts) and kv(p.heavy_starts) or "-"))
  print("\n## swarm run jobs")
  for _, k in ipairs(sorted_keys(r.jobs)) do
    local m = r.jobs[k]
    print(("- %s: %d jobs, %.0f min, exits %s, lost %d, unfinished %d, sync %.0fs, back %.0fs"):format(k, m.jobs, m.minutes,
      next(m.exits) and kv(m.exits, ",") or "-", m.lost, m.unfinished, m.sync_s, m.back_s))
  end
  print("\n## files changed by 2+ agents")
  for _, fl in ipairs(sorted_keys(r.multi_agent_files or {})) do print("- " .. fl .. ": " .. table.concat(r.multi_agent_files[fl], ", ")) end
  print("\n## messages sent")
  for _, m in ipairs(r.messages) do print(("- %s: %d (%d urgent)"):format(s(m.frm), m.n, m.urgent or 0)) end
  if #r.locks > 0 then
    print("\n## locks still held")
    for _, k in ipairs(r.locks) do print(("- %s %s %s"):format(k.path, k.agent, k.reason or "")) end
  end
end

-- Pretty JSON, Python's indent=1 with sorted keys (Lua tables keep no order).
local ARR = getmetatable(json.array())
local function enc(v, ind)
  if type(v) ~= "table" then return json.encode(v) end
  local pad, inner = ("\n"):rep(1) .. (" "):rep(ind), ("\n") .. (" "):rep(ind + 1)
  local o = {}
  if getmetatable(v) == ARR then
    if #v == 0 then return "[]" end
    for _, x in ipairs(v) do o[#o + 1] = enc(x, ind + 1) end
    return "[" .. inner .. table.concat(o, "," .. inner) .. pad .. "]"
  end
  for _, k in ipairs(sorted_keys(v)) do o[#o + 1] = json.encode(tostring(k)) .. ": " .. enc(v[k], ind + 1) end
  if #o == 0 then return "{}" end
  return "{" .. inner .. table.concat(o, "," .. inner) .. pad .. "}"
end

local function parse_since(s)
  local y, mo, d, h, mi, se = s:match("^(%d+)-(%d+)-(%d+)[T ]?(%d*):?(%d*):?(%d*)$")
  if not y then util.die("swarm-report: bad --since '" .. s .. "' (use 2026-11-07T08:00)") end
  return os.time({ year = y, month = mo, day = d, hour = tonumber(h) or 0, min = tonumber(mi) or 0, sec = tonumber(se) or 0 })
end

local function main()
  local ap = argparse("swarm-report", "Evidence for a swarm retro, read from the swarm db: who did what, where time and attention went.\n"
    .. "Default db: <git-common-dir>/swarm/swarm.db (or $SWARM_DB). Sections: agents, tasks (claim -> done time, evidence), event counts "
    .. "per agent (conflicts, shared trees, reaps, compactions, pushes, ci-red are the friction signals), messages, locks. Read-only.")
  ap:option("--db")
  ap:option("--since", "ISO start, e.g. 2026-11-07T08:00")
  ap:flag("--json")
  local a = ap:parse()
  local path = M.dbpath(a.db)
  if not lfs.attributes(path, "mode") then util.die("swarm-report: no db at " .. path) end
  local c, err = db.open_ro(path)
  if not c then util.die("swarm-report: can't open " .. path .. ": " .. tostring(err)) end
  local r = M.report(c, a.since and parse_since(a.since) or nil, true, M.state_tasks(path))
  if a.json then print(enc(r, 0)) else show(r) end
end

local ok, e = pcall(main)
if not ok then
  if type(e) == "table" and e.exit then os.exit(e.exit) end
  io.stderr:write(tostring(e) .. "\n")
  os.exit(1)
end
