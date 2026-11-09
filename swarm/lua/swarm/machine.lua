-- This machine's memory and pressure, from /proc (SWARM_PROC in tests). Linux only for now (sw-lua §8).
local util = require "swarm.util"
local M = {}

M.PROC = os.getenv("SWARM_PROC") or "/proc"

-- MemAvailable and MemTotal in KiB and {memory, cpu} PSI some avg10, or nil without /proc/meminfo.
function M.mem_psi()
  local s = util.slurp(M.PROC .. "/meminfo")
  if not s then return nil end
  local mi = {}
  for k, v in s:gmatch("([^\n:]+):%s*(%d+)") do mi[k] = tonumber(v) end
  local psi = {}
  for _, r in ipairs({ "memory", "cpu" }) do
    psi[r] = tonumber((util.slurp(M.PROC .. "/pressure/" .. r) or ""):match("some avg10=([%d.]+)")) or 0
  end
  return mi.MemAvailable, mi.MemTotal, psi
end

function M.pressure_high(avail, total, psi)
  return psi.memory > 10 or avail < 0.15 * total
end

function M.machine_line(avail, total, psi)
  return ("machine: %.1f/%.1fG mem available, pressure10 mem %g%% cpu %g%%"):format(
    avail / 1048576, total / 1048576, psi.memory, psi.cpu)
end

return M
