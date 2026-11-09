-- Worktrees and the conflict tick (P5 ports the rest).
local util, proc = require "swarm.util", require "swarm.proc"
local stdlib = require "posix.stdlib"
local M = {}

-- {agent: worktree} for live agents: agent.wt, else the worktree whose branch is <name>/…
function M.wt_map(c)
  local wts, cur = {}, nil
  for _, l in ipairs(util.splitlines(proc.run({ "git", "worktree", "list", "--porcelain" }))) do
    if util.startswith(l, "worktree ") then
      cur = stdlib.realpath(l:sub(10)) or l:sub(10)
    elseif util.startswith(l, "branch refs/heads/") and cur then
      wts[#wts + 1] = { cur, l:sub(19) }
    end
  end
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

return M
