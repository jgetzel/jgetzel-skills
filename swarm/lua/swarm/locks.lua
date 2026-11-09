-- Lock lookups for the hook: repo_rel, covers, lock_holder (sr-45's P5 adds cmd lock/unlock here).
local util, proc = require "swarm.util", require "swarm.proc"
local stdlib, fnmatch, lfs = require "posix.stdlib", require "posix.fnmatch", require "lfs"
local M = {}

local function isdir(p) return (lfs.attributes(p, "mode")) == "directory" end

-- (toplevel, repo-relative path) for an absolute or cwd-relative path, or nil outside a repo.
-- shortcut: ".." is folded lexically before symlinks resolve; upgrade if a symlinked dir/.. ever matters.
function M.repo_rel(path, cwd)
  local parts = {}
  for seg in util.join(cwd or ".", path):gmatch("[^/]+") do
    if seg == ".." then parts[#parts] = nil elseif seg ~= "." then parts[#parts + 1] = seg end
  end
  local p = "/" .. table.concat(parts, "/")
  local d, tail = util.dirname(p), ""  -- the deepest existing directory holds the repo
  while d ~= "/" and not isdir(d) do
    tail = "/" .. util.basename(d) .. tail
    d = util.dirname(d)
  end
  local real = stdlib.realpath(d)
  if not real then return nil end
  p = (real == "/" and "" or real) .. tail .. "/" .. util.basename(p)
  local top = proc.git({ "rev-parse", "--show-toplevel" }, real)
  if not top then return nil end
  top = stdlib.realpath(top) or top
  if p == top then return top, "." end
  if util.startswith(p, top .. "/") then return top, p:sub(#top + 2) end
  return nil
end

-- Whether lock pattern pat covers path: a glob, or a directory prefix (`migrations/`).
function M.covers(path, pat)
  return fnmatch.fnmatch(pat, path, 0) == true or util.startswith(path, pat:gsub("/+$", "") .. "/")
end

function M.lock_holder(c, me, path, t)
  for _, r in ipairs(c:all("select l.* from lock l join agent a on a.name=l.agent "
      .. "where l.agent!=? and l.lease_until>? and a.ended is null", me, t)) do
    if M.covers(path, r.path) then return r end
  end
  return nil
end

function M.task_of(c, name)
  local r = c:one("select id,title from task where owner=? and state in ('claimed','blocked') order by id limit 1", name)
  return r and ("task #%d: %s"):format(r.id, r.title) or "no claimed task"
end

return M
