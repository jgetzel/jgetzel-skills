-- The branch a task's work lands on (sw-bases): the task's own --base, else the repo's `base` in .claude/swarm.json,
-- else main. Ref names for git are resolved here: origin/<b> when origin has <b>, else the local branch.
local util, proc, json = require "swarm.util", require "swarm.proc", require "swarm.json"
local M = {}

-- the repo's default base name: .claude/swarm.json {"base": "formal"}, else "main"
function M.default(cwd)
  local top = proc.git({ "rev-parse", "--show-toplevel" }, cwd)
  local ok, cfg = pcall(json.decode, top and util.slurp(util.join(top, ".claude", "swarm.json")) or "")
  local b = ok and type(cfg) == "table" and cfg.base
  return type(b) == "string" and b ~= "" and b or "main"
end

-- base_for(task): a branch name
function M.base_for(task, cwd)
  local b = task and task.base
  return type(b) == "string" and b ~= "" and b or M.default(cwd)
end

-- a base's remote ref, if origin has it
local function remote_ref(b, cwd)
  local r = "origin/" .. b
  return proc.git({ "rev-parse", "--verify", "-q", "refs/remotes/" .. r }, cwd) and r or nil
end
M.remote_ref = remote_ref

-- the ref git compares against: origin/<b> when origin has it, else <b>
function M.ref(b, cwd) return remote_ref(b, cwd) or b end

-- bring origin's <b> up to date (a base with no remote branch just fails quietly)
function M.fetch(b, cwd)
  if util.strip(proc.git({ "remote", "get-url", "origin" }, cwd) or "") ~= "" then
    proc.run({ "git", "fetch", "-q", "origin", b }, cwd)
  end
end

local function uniq(l)
  local seen, r = {}, {}
  for _, x in ipairs(l) do if not seen[x] then seen[x] = true; r[#r + 1] = x end end
  return r
end

-- the bases an agent's work must be on: those of the tasks it owns (a done task keeps its owner), else the default
function M.of_agent(c, name, cwd)
  local l = {}
  for _, t in ipairs(c:all("select base from task where owner=?", name)) do l[#l + 1] = M.base_for(t, cwd) end
  return #l > 0 and uniq(l) or { M.default(cwd) }
end

-- what the sweep protects: main, the default and every base a task names
function M.protected(c, cwd)
  local l = { "main", M.default(cwd) }
  for _, t in ipairs(c:all("select distinct base from task where base is not null")) do l[#l + 1] = M.base_for(t, cwd) end
  return uniq(l)
end

function M.refs(names, cwd)
  local l = {}
  for _, b in ipairs(names) do l[#l + 1] = M.ref(b, cwd) end
  return uniq(l)
end

return M
