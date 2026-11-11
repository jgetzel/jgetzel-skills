-- Workspaces (sw-bases): the worktrees swarm creates for a task, recorded as workspace(path, branch, base, agent, ro).
-- ro=0 is the agent's own; ro=1 a read-only attachment (`swarm spawn --attach`). Replaces conflict.owned_wts's guessing.
local util, proc, bases = require "swarm.util", require "swarm.proc", require "swarm.bases"
local stdlib, lfs = require "posix.stdlib", require "lfs"
local M = {}

local function real(p) return stdlib.realpath(p) or p end

-- the main checkout: the first worktree git lists
function M.main(cwd)
  local m = (proc.run({ "git", "worktree", "list", "--porcelain" }, cwd) or ""):match("^worktree ([^\n]*)")
  return m and real(m)
end

-- `git worktree add ../<repo>-<agent> -b <agent>/<task> <base ref>`, recorded. Returns path, branch, base.
function M.create(c, name, task, cwd)
  local main = M.main(cwd) or util.die("not in a git repo: no worktree to make")
  local base = bases.base_for(task, main)
  bases.fetch(base, main)
  local path = util.join(util.dirname(main), util.basename(main) .. "-" .. name)
  if lfs.attributes(path) then path = path .. "-" .. task.id end  -- a predecessor's worktree is still there
  local branch = ("%s/%s"):format(name, task.id)
  if proc.git({ "rev-parse", "--verify", "-q", "refs/heads/" .. branch }, main) then branch = branch .. "-" .. util.now() end
  local code, err = proc.gx({ "-C", main, "worktree", "add", "-q", path, "-b", branch, bases.ref(base, main) })
  if code ~= 0 then util.die("git worktree add failed: " .. err) end
  path = real(path)
  c:exec("insert or replace into workspace(path,branch,base,agent,ro) values(?,?,?,?,0)", path, branch, base, name)
  return path, branch, base
end

-- a launch that failed leaves nothing behind: the fresh worktree and its branch, or the link
function M.discard(c, name, path, branch, created)
  c:exec("delete from workspace where agent=? and path=?", name, path)
  if created then
    local main = M.main(path)
    proc.gx({ "-C", main, "worktree", "remove", "--force", path })
    proc.gx({ "-C", main, "branch", "-D", branch })
  end
end

-- link name read-only to a recorded workspace
function M.attach(c, name, path)
  path = real(path)
  local w = c:one("select * from workspace where path=? and ro=0", path) or util.die(path .. " is not a swarm workspace")
  c:exec("insert or replace into workspace(path,branch,base,agent,ro) values(?,?,?,?,1)", path, w.branch, w.base, name)
  return path, w.branch, w.base
end

-- the worktrees name owns that still exist: nil when none was ever recorded for it (it predates the table)
function M.owned(c, name, wts)
  local ok, rows = pcall(c.all, c, "select path from workspace where agent=? and ro=0", name)  -- state reads dbs older than the table
  if not ok or #rows == 0 then return nil end
  local live, res = {}, {}
  for _, pb in ipairs(wts) do live[pb[1]] = true end
  for _, r in ipairs(rows) do if live[r.path] then res[#res + 1] = r.path end end
  return res
end

-- the base branch `cmd` would check out in an agent's workspace (`git checkout main`, `git switch formal`), or nil
function M.base_checkout(c, name, cmd, cwd)
  if not c:one("select 1 from workspace where agent=?", name) then return nil end
  local re = require "swarm.re"
  local m = re.search([[\bgit\s+(?:checkout|switch)\s+(?:-[qf]\s+)*([^\s;&|-][^\s;&|]*)\s*(?:$|[;&|])]], cmd)
  if not m then return nil end
  for _, b in ipairs(bases.protected(c, cwd)) do if m[1] == b or m[1] == "origin/" .. b then return b end end
end

-- agents' workspaces with a base checked out (they slipped past the hook): {{agent, path, base}}
function M.base_out(c, wts)
  local prot, out = {}, {}
  for _, b in ipairs(bases.protected(c, M.main())) do prot[b] = true end
  for _, w in ipairs(c:all("select agent, path from workspace where ro=0")) do
    for _, pb in ipairs(wts) do
      if pb[1] == w.path and prot[pb[2]] then out[#out + 1] = { w.agent, w.path, pb[2] } end
    end
  end
  return out
end

return M
