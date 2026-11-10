-- Worktrees and the conflict tick: edits, clash, real_hunk, snapshot, trial_merge, conflict_tick.
local util, proc, db, json, re = require "swarm.util", require "swarm.proc", require "swarm.db", require "swarm.json",
  require "swarm.re"
local difflib, locks, msgs = require "swarm.difflib", require "swarm.locks", require "swarm.msgs"
local stdlib, lfs = require "posix.stdlib", require "lfs"
local utf8 = require "lua-utf8"
local M = {}

local TOK = [[\w+|[^\w\s]|\n]]
local HUNK = [[^<<<<<<< .*?\n(.*?)^\|\|\|\|\|\|\| .*?\n(.*?)^=======\n(.*?)^>>>>>>> ]]

-- Base-token spans one side changed, half-open; i1 == i2 is an insertion at i1.
function M.edits(base, side)
  local r = {}
  for _, o in ipairs(difflib.SequenceMatcher(base, side):get_opcodes()) do
    if o[1] ~= "equal" then r[#r + 1] = { o[2], o[3] } end
  end
  return r
end

-- Two spans clash if both change a common base token, or one inserts strictly inside the other's change.
function M.clash(a, b)
  local a1, a2, b1, b2 = a[1], a[2], b[1], b[2]
  if a1 == a2 and b1 == b2 then return false end
  if a1 == a2 then return b1 < a1 and a1 < b2 end
  if b1 == b2 then return a1 < b1 and b1 < a2 end
  return a1 < b2 and b1 < a2
end

function M.real_hunk(base, ours, theirs)
  local b = re.findall(TOK, base)
  local eb = M.edits(b, re.findall(TOK, theirs))
  for _, x in ipairs(M.edits(b, re.findall(TOK, ours))) do
    for _, y in ipairs(eb) do
      if M.clash(x, y) then return true end
    end
  end
  return false
end

assert(not M.real_hunk("module L (a, b) where\n", "module L (a, b, c) where\n", "module L (a, b, d) where\n"))
assert(M.real_hunk("x = f a\n", "x = g a\n", "x = h a\n"))

-- {{path, branch}} of the repo's worktrees that are on a branch
function M.worktrees()
  local wts, cur = {}, nil
  for _, l in ipairs(util.splitlines(proc.run({ "git", "worktree", "list", "--porcelain" }))) do
    if util.startswith(l, "worktree ") then
      cur = stdlib.realpath(l:sub(10)) or l:sub(10)
    elseif util.startswith(l, "branch refs/heads/") and cur then
      wts[#wts + 1] = { cur, l:sub(19) }
    end
  end
  return wts
end

-- Every worktree name owns: its branch is <name>/…, or its directory ends in -<name> or -<name>-…
function M.owned_wts(name, wts)
  local res = {}
  for _, pb in ipairs(wts) do
    local b = util.basename(pb[1])
    if util.startswith(pb[2], name .. "/") or b:sub(-#name - 1) == "-" .. name or b:find("-" .. name .. "-", 1, true) then
      res[#res + 1] = pb[1]
    end
  end
  return res
end

-- {agent: worktree} for live agents: agent.wt, else the worktree whose branch is <name>/…
function M.wt_map(c)
  local wts = M.worktrees()
  local res = {}
  for _, a in ipairs(require("swarm.agents").live_agents(c)) do
    local w = a.wt
    if not w or w == "" then
      w = nil
      for _, pb in ipairs(wts) do
        if util.startswith(pb[2], a.name .. "/") then w = pb[1]; break end
      end
    end
    if w then res[a.name] = w end
  end
  return res
end

local function rmtree(d)
  for f in lfs.dir(d) do
    if f ~= "." and f ~= ".." then
      local p = d .. "/" .. f
      if lfs.attributes(p, "mode") == "directory" then rmtree(p) else os.remove(p) end
    end
  end
  lfs.rmdir(d)
end

-- Commit wt's working state (tracked + untracked, not ignored) as an unreferenced commit; reads wt only.
-- Returns {head, tree, commit, files} or nil.
function M.snapshot(wt, base)
  local head = proc.git({ "-C", wt, "rev-parse", "HEAD" })
  local idx = proc.git({ "-C", wt, "rev-parse", "--path-format=absolute", "--git-path", "index" })
  if not head or head == "" or not idx or idx == "" then return nil end
  local d = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-snap-XXXXXX")
  if not d then return nil end
  local tmp = d .. "/index"
  local src = util.slurp(idx)
  if src then  -- keeps the index mtime, or git trusts stale stat data (racy git); rename-replaced, so the read is whole
    local f = io.open(tmp, "wb")
    f:write(src); f:close()
    local at = lfs.attributes(idx)  -- whole seconds: an earlier index mtime only makes git rehash more
    if at then lfs.touch(tmp, at.access, at.modification) end
  end
  local env = { GIT_INDEX_FILE = tmp, GIT_OPTIONAL_LOCKS = "0", GIT_AUTHOR_NAME = "swarm", GIT_AUTHOR_EMAIL = "swarm@swarm",
    GIT_COMMITTER_NAME = "swarm", GIT_COMMITTER_EMAIL = "swarm@swarm" }
  local function g(...)
    return util.strip(proc.run({ "git", "-C", wt, ... }, nil, nil, env) or "")
  end
  g("add", "-A")
  local tree = g("write-tree")
  local commit = tree ~= "" and g("commit-tree", tree, "-p", head, "-m", "swarm snapshot") or ""
  rmtree(d)
  if commit == "" then return nil end
  local mb = base and proc.git({ "-C", wt, "merge-base", base, commit })
  local files = json.array()
  if mb and mb ~= "" then
    for _, f in ipairs(util.split(proc.run({ "git", "-C", wt, "diff", "--name-only", "-z", mb, commit }) or "", "\0")) do
      if f ~= "" then files[#files + 1] = f end
    end
  end
  return { head = head, tree = tree, commit = commit, files = files }
end

-- Tree of commit's own changes (since its merge-base with base) replayed onto base; nil if they conflict with base.
function M.onto(wt, base, commit)
  local mb = proc.git({ "-C", wt, "merge-base", base, commit })
  if not mb or mb == "" then return nil end
  local out, _, code = proc.exec({ "git", "-C", wt, "merge-tree", "--write-tree", "--no-messages", "--merge-base=" .. mb,
    base, commit })
  return code == 0 and out:match("%S+") or nil
end

-- Merge two trees that are each one agent's own changes on base, so commits merged in from base are no one's.
-- nil if git failed; else a list of {path, {{ours, theirs} real hunk texts}} by path, and a flag for line-only conflicts.
function M.trial_merge(cwd, base, ca, cb)
  local out, _, code = proc.exec({ "git", "-c", "merge.conflictStyle=diff3", "--attr-source=" .. base, "merge-tree",
    "--write-tree", "--name-only", "--no-messages", "--merge-base=" .. base, ca, cb }, { cwd = cwd })
  if code ~= 1 then
    if code ~= 0 then return nil, false end
    return {}, false
  end
  local lines = util.splitlines(out)
  local tree, files, seen = lines[1], {}, {}
  for i = 2, #lines do
    local f = lines[i]
    if f ~= "" and not seen[f] then seen[f] = true; files[#files + 1] = f end
  end
  table.sort(files)
  local real, compat = {}, false
  for _, f in ipairs(files) do
    local text = proc.git({ "show", tree .. ":" .. f }, cwd) or ""
    if not utf8.len(text) then text = "" end  -- not UTF-8 (binary): no hunks, so it counts as real
    local hunks, bad = 0, {}
    for m in re.finditer(HUNK, text, re.S + re.M) do
      hunks = hunks + 1
      if M.real_hunk(m[2], m[1], m[3]) then bad[#bad + 1] = { m[1], m[3] } end
    end
    if #bad > 0 or hunks == 0 then  -- no diff3 hunks: a rename or file/directory conflict, which counts as real
      real[#real + 1] = { f, #bad > 0 and bad or { { "", "" } } }
    else
      compat = true
    end
  end
  return real, compat
end

function M.line_range(cwd, commit, path, text)
  text = text:gsub("^\n+", ""):gsub("\n+$", "")
  local f = proc.git({ "show", commit .. ":" .. path }, cwd) or ""
  local i = text ~= "" and f:find(text, 1, true)
  if not i then return "?" end
  local _, n = f:sub(1, i - 1):gsub("\n", "")
  local _, k = text:gsub("\n", "")
  return ("%d–%d"):format(n + 1, n + 1 + k)
end

local function sorted_keys(t)
  local r = {}
  for k in pairs(t) do r[#r + 1] = k end
  table.sort(r)
  return r
end

function M.conflict_tick(c, t)
  local wts = M.wt_map(c)
  -- origin/main, unless local main is ahead: a stale local main counts merged-in PRs as the agent's own edits
  local have = {}
  for _, b in ipairs({ "origin/main", "main", "master" }) do
    if proc.git({ "rev-parse", "--verify", "-q", b }) then have[#have + 1] = b end
  end
  if have[1] == "origin/main" and have[2] == "main" and proc.gx({ "merge-base", "--is-ancestor", "origin/main", "main" }) == 0 then
    table.remove(have, 1)
  end
  local base = have[1] and proc.git({ "rev-parse", have[1] }) or nil
  local snaps, bywt, ontos = {}, {}, {}
  for _, n in ipairs(sorted_keys(wts)) do
    local w = wts[n]
    if bywt[w] == nil then bywt[w] = M.snapshot(w, base) or false end
    if bywt[w] then
      snaps[n] = bywt[w]
      c:exec("update agent set snap=? where name=?", json.encode(bywt[w]), n)
    end
  end
  local notes, order = {}, {}
  local names = sorted_keys(snaps)
  local cand, candl = {}, {}
  for i, a in ipairs(names) do
    for k = i + 1, #names do
      local b = names[k]
      if wts[a] ~= wts[b] then
        local fa = {}
        for _, f in ipairs(snaps[a].files) do fa[f] = true end
        for _, f in ipairs(snaps[b].files) do
          if fa[f] then cand[a .. "\0" .. b] = true; candl[#candl + 1] = { a, b }; break end
        end
      end
    end
  end
  for _, r in ipairs(c:all("select distinct a,b from conflict")) do
    if not cand[r.a .. "\0" .. r.b] then  -- no longer overlapping, or an agent is gone
      c:exec("delete from conflict where a=? and b=?", r.a, r.b)
    end
  end
  for _, ab in ipairs(candl) do  -- names are sorted, so this is sorted(cand)
    local a, b = ab[1], ab[2]
    local key = snaps[a].tree .. snaps[b].tree .. base
    local old = c:one("select key from pairkey where a=? and b=?", a, b)
    if not (old and old.key == key) then
      for _, n in ipairs({ a, b }) do
        if ontos[n] == nil then ontos[n] = M.onto(wts[n], base, snaps[n].commit) or false end
      end
      if not (ontos[a] and ontos[b]) then  -- an agent's work conflicts with base itself; it must merge base first
        c:exec("insert or replace into pairkey values(?,?,?)", a, b, key)
        db.log(c, a, "conflict-stale", b)
      else
        local real, compat = M.trial_merge(wts[a], base, ontos[a], ontos[b])
        if not real then
          db.log(c, a, "conflict-error", b)
        else
          c:exec("insert or replace into pairkey values(?,?,?)", a, b, key)
          local inreal = {}
          for _, x in ipairs(real) do inreal[x[1]] = true end
          local had = {}
          for _, r in ipairs(c:all("select path from conflict where a=? and b=?", a, b)) do
            had[r.path] = true
            if not inreal[r.path] then c:exec("delete from conflict where a=? and b=? and path=?", a, b, r.path) end
          end
          if compat then db.log(c, a, "conflict-compat", b) end
          for _, x in ipairs(real) do
            local p, hunks = x[1], x[2]
            if not had[p] then
              c:exec("insert into conflict values(?,?,?,?)", a, b, p, t)
              db.log(c, a, "conflict", p, b)
              local function ranges(n, side)
                local s, l = {}, {}
                for _, h in ipairs(hunks) do s[M.line_range(wts[n], snaps[n].commit, p, h[side])] = true end
                for k in pairs(s) do l[#l + 1] = k end
                table.sort(l)
                return table.concat(l, ", ")
              end
              local ha, hb = ranges(a, 1), ranges(b, 2)
              for _, v in ipairs({ { a, b, ha, hb }, { b, a, hb, ha } }) do
                local me_, o, mine, theirs = v[1], v[2], v[3], v[4]
                if not notes[me_] then notes[me_] = {}; order[#order + 1] = me_ end
                table.insert(notes[me_], ("Your uncommitted work conflicts with %s's (%s) in %s (your lines %s, "
                  .. "theirs %s). Whoever lands first wins; the other rebases onto it. Message %s only if "
                  .. "the two changes can't both stand."):format(o, locks.task_of(c, o), p, mine, theirs, o))
              end
            end
          end
        end
      end
    end
  end
  for _, n in ipairs(order) do
    msgs.post(c, "swarm", n, table.concat(notes[n], "\n"), false, "notice")
  end
  -- Bash edits to another agent's lock, from the snapshot; only in trees one agent owns
  for _, n in ipairs(names) do
    local same = 0
    for _, w in pairs(wts) do if w == wts[n] then same = same + 1 end end
    if same <= 1 then
      for _, p in ipairs(snaps[n].files) do
        local lk = locks.lock_holder(c, n, p, t)
        if lk and not c:one("select 1 x from event where kind='lock-violation' and agent=? and path=?", n, p) then
          db.log(c, n, "lock-violation", p, lk.agent)
          msgs.post(c, "swarm", n, ("%s edited %s, locked by %s: violation. Revert it or ask %s."):format(n, p, lk.agent, lk.agent),
            false, "system")
          msgs.post(c, "swarm", lk.agent, ("%s edited your locked path %s."):format(n, p), false, "system")
        end
      end
    end
  end
  -- a lock is released once the holder's work on it lands (it matched, and no longer does)
  for _, lk in ipairs(c:all("select * from lock")) do
    if snaps[lk.agent] then
      local hit = false
      for _, f in ipairs(snaps[lk.agent].files) do
        if locks.covers(f, lk.path) then hit = true; break end
      end
      local seen = lk.seen and lk.seen ~= 0
      if hit and not seen then
        c:exec("update lock set seen=1 where path=?", lk.path)
      elseif not hit and seen then
        c:exec("delete from lock where path=?", lk.path)
        db.log(c, lk.agent, "unlock", lk.path, "landed")
      end
    end
  end
end

return M
