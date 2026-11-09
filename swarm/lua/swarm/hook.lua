-- Hooks (P4 ports hook() itself): the context-size notes, which the communicator gets from its commands.
local util, json, db = require "swarm.util", require "swarm.json", require "swarm.db"
local agents = require "swarm.agents"
local glob = require "posix.glob"
local M = {}

M.CTX_WARN = 350000  -- tokens; warn here, then every +100k; at 550k say hand off

local function tail_lines(path)  -- the transcript's last 300 KB as lines, or nil
  local f = path and io.open(path, "rb")
  if not f then return nil end
  local size = f:seek("end")
  f:seek("set", math.max(0, size - 300000))
  local s = f:read("*a")
  f:close()
  return util.splitlines(s)
end

-- Context size from the last assistant usage in the transcript.
function M.ctx_from(path)
  local lines = tail_lines(path)
  if not lines then return nil end
  for i = #lines, 1, -1 do
    local j = json.decode(lines[i])
    local u = type(j) == "table" and type(j.message) == "table" and j.message.usage
    if type(u) == "table" and next(u) ~= nil and j.type == "assistant" then
      local k = 0
      for _, key in ipairs({ "input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens" }) do
        k = k + (tonumber(u[key]) or 0)
      end
      return k
    end
  end
  return nil
end

function M.ctx_advice(k, comms)
  if comms then  -- the communicator holds the swarm's state, so a handoff carries it over
    if k >= 550000 then
      return "finish the current step, then hand off with the relaunch skill, same model, and pass on the swarm "
        .. "(board, watchd PID, open threads)."
    end
    return "wrap up this step; at ~550k hand off with the relaunch skill, same model, and pass on the swarm "
      .. "(board, watchd PID, open threads)."
  end
  if k >= 550000 then
    return "hand off now with the relaunch skill, same model, and post the successor's name, "
      .. "or `swarm task release` if the task is barely started."
  end
  return "finish this task, then go idle (watchd ends you and a fresh agent takes the next task); don't claim another."
end

local function tmpdir()  -- tempfile.gettempdir()
  return agents.env("TMPDIR") or agents.env("TEMP") or agents.env("TMP") or "/tmp"
end

-- Context-size note. Shares the repo hook's step marker (claude-ctx-<session_id>) so only one of the two fires per step.
function M.handoff_nudge(c, name, p, comms)
  local k = M.ctx_from(p.transcript_path)
  if not k or k == 0 then return nil end
  c:exec("update agent set ctx_tokens=? where name=?", k, name)
  local step = math.floor((k - (M.CTX_WARN - 100000)) / 100000)  -- 1 at 350k, 2 at 450k, ...
  if step < 1 then return nil end
  local sid = p.session_id
  local mark = util.join(tmpdir(), "claude-ctx-" .. ((sid and sid ~= "") and sid or "x"))
  local last = tonumber(util.slurp(mark) or "") or 0
  if step <= last then return nil end
  local f = io.open(mark, "w")
  if f then f:write(util.d(step)); f:close() end
  db.log(c, name, "ctx-note", nil, util.d(k))
  return ("Context is ~%dk tokens: %s"):format(math.floor(k / 1000), M.ctx_advice(k, comms))
end

-- The communicator is a normal session with no swarm hooks: read/wait/board/who stand in for post-tool.
function M.comms_nudge(c, cmd)
  local name, sid = agents.env("SWARM_NAME"), agents.env("CLAUDE_CODE_SESSION_ID")
  if not (name and sid) or not agents.is_comms(c, name) then return end
  local home = os.getenv("HOME") or ""
  local tr = (glob.glob(home .. "/.claude/projects/*/" .. sid .. ".jsonl", 0) or {})[1]
  local n = M.handoff_nudge(c, name, { transcript_path = tr, session_id = sid }, true)
  if n then
    if cmd == "wait" then io.stderr:write(n .. "\n") else print(n) end
  end
end

return M
