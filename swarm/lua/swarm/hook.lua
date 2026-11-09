-- Hooks: stdin JSON in, stdout JSON out; the context-size notes (the communicator gets those from its commands).
local util, json, db = require "swarm.util", require "swarm.json", require "swarm.db"
local agents, msgs, proc = require "swarm.agents", require "swarm.msgs", require "swarm.proc"
local machine, locks, re = require "swarm.machine", require "swarm.locks", require "swarm.re"
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

-- Context after the latest compaction: the boundary's postTokens plus ~31k of system prompt and tools.
function M.post_compact(path)
  local lines = tail_lines(path)
  for i = #(lines or {}), 1, -1 do
    local j = json.decode(lines[i])
    local m = type(j) == "table" and j.compactMetadata
    if type(m) == "table" and tonumber(m.postTokens) and m.postTokens ~= 0 then return m.postTokens + 31000 end
  end
  return nil
end

-- The hook's JSON answer; keys in Python's order.
local function emit(event, ctx, deny)
  local o = { '"hookEventName": ' .. json.encode(event) }
  if deny then
    o[#o + 1] = '"permissionDecision": "deny"'
    o[#o + 1] = '"permissionDecisionReason": ' .. json.encode(deny)
  end
  if ctx and ctx ~= "" then o[#o + 1] = '"additionalContext": ' .. json.encode(ctx) end
  print('{"hookSpecificOutput": {' .. table.concat(o, ", ") .. "}}")
end

local EDIT_TOOLS = { Edit = true, Write = true, MultiEdit = true, NotebookEdit = true }
local EVENTS = { ["pre-tool"] = "PreToolUse", ["post-tool"] = "PostToolUse", prompt = "UserPromptSubmit", session = "SessionStart" }

local function set_null(c, name, col)  -- touch drops nil values; a missing figure must clear the old one
  c:exec("update agent set " .. col .. "=null where name=?", name)
end

local function pre_tool(c, name, cwd, tool, ti)
  local t = util.now()
  if tool == "SendMessage" then
    local to = tostring(ti.to or ""):gsub(" %[.*$", "")
    local tgt = c:one("select * from agent where name=? and ended is null", to)
    if tgt and not util.startswith((tostring(ti.message or ""):gsub("^%s+", "")), "[urgent]") then
      local why = agents.cold_reason(tgt, t)
      if why then
        db.log(c, name, "deny-cold", tgt.name, util.cut(why, 120))
        return emit("PreToolUse", nil, why .. " Use `swarm post " .. tgt.name .. " …`: it reads the message "
          .. "when it next wakes. If it truly can't wait, resend starting with `[urgent]`.")
      end
    end
  elseif tool == "Bash" then
    local cmd = tostring(ti.command or "")
    if machine.is_heavy(cmd, cwd) then  -- information at decision time: context only, never a deny or a rewrite
      emit("PreToolUse", machine.machine_note(c, name))
      db.log(c, name, "heavy-start", nil, util.cut(cmd, 80))
    end
  elseif EDIT_TOOLS[tool] then
    local fp = ti.file_path
    if fp == nil or fp == "" then fp = ti.notebook_path end
    local top, path = locks.repo_rel(fp or "", cwd)
    if not top then return end
    local lk = locks.lock_holder(c, name, path, t)
    if lk then
      db.log(c, name, "deny-lock", path, lk.agent)
      return emit("PreToolUse", nil, ("%s is locked by %s since %s%s. Ask it with SendMessage."):format(
        path, lk.agent, util.hhmm(lk.since), (lk.reason and lk.reason ~= "") and (" (" .. lk.reason .. ")") or ""))
    end
    c:exec("update agent set wt=? where name=?", top, name)
    for _, o in ipairs(c:all("select name from agent where wt=? and name!=? and ended is null", top, name)) do
      if not c:one("select 1 from event where kind='shared-tree' and agent=? and path=?", name, top) then
        db.log(c, name, "shared-tree", top, o.name)
        msgs.post(c, "swarm", o.name, ("%s also edits in %s (%s). Two agents' uncommitted edits in one tree mix and "
          .. "can't be told apart; make your own worktree."):format(name, top, locks.task_of(c, name)), false, "notice")
        return emit("PreToolUse", ("%s is also %s's worktree (%s). Two agents' uncommitted edits in one tree mix "
          .. "and can't be told apart. Make your own: `git worktree add …`."):format(top, o.name, locks.task_of(c, o.name)))
      end
    end
  end
end

local function log_push(c, name, cwd, cmd)
  local m = re.search([[\bgit\s+(?:-C\s+(\S+)\s+)?push\b]], cmd)
  if not m then return end
  -- agents push from their worktree (`cd <wt> && git push`), not the session cwd
  local cds = re.findall([[(?:^|[;&|(]\s*)cd\s+([^\s;&|)]+)]], cmd:sub(1, m.s - 1))
  local d = m[1] or cds[#cds]
  if d then
    d = d:gsub("^['\"]+", ""):gsub("['\"]+$", ""):gsub("^~(/?)", (os.getenv("HOME") or "~") .. "%1")
    d = util.join(cwd or "", d)
  else
    d = cwd
  end
  local function enc(v) return v and json.encode(v) or "null" end
  -- path carries {branch, subject} as JSON for the panel; state --json unpacks it
  db.log(c, name, "push", ('{"branch": %s, "subject": %s}'):format(
    enc(proc.git({ "rev-parse", "--abbrev-ref", "HEAD" }, d)), enc(proc.git({ "log", "-1", "--format=%s" }, d))),
    util.cut(cmd, 120))
end

function M.hook(ev)
  local name = agents.env("SWARM_NAME")
  local p = json.decode(io.read("*a") or "")
  if type(p) ~= "table" then p = {} end
  if not name then return end
  local c = db.connect()
  local cwd = p.cwd
  if not cwd or cwd == "" then cwd = require("posix.unistd").getcwd() end
  local tool, ti = p.tool_name, type(p.tool_input) == "table" and p.tool_input or {}
  local why = agents.fence(c, name)
  if why then  -- a predecessor's last turn or an ended agent: write nothing, say so once per terminal, never deny
    local here = agents.env("HC_TERMINAL_ID") or "-"
    local out = EVENTS[ev]
    if out and not c:one("select 1 from event where kind='fenced' and agent=? and path=? and data=?", name, here, why) then
      db.log(c, name, "fenced", here, why)
      emit(out, why)
    end
    return
  end
  agents.touch(c, name, cwd)

  if ev == "pre-tool" then
    pre_tool(c, name, cwd, tool, ti)
  elseif ev == "post-tool" then
    agents.set_status(c, name, "working")
    if tool == "Bash" then log_push(c, name, cwd, tostring(ti.command or "")) end
    local ctx, n = msgs.deliver(c, name), M.handoff_nudge(c, name, p)
    if ctx ~= "" or n then emit("PostToolUse", (ctx ~= "" and n) and (ctx .. "\n" .. n) or (ctx ~= "" and ctx or n)) end
  elseif ev == "prompt" then  -- a turn started without a tool call (human prompt or peer message)
    agents.set_status(c, name, "working")
    local m = msgs.deliver(c, name)
    if m ~= "" then emit("UserPromptSubmit", m) end
  elseif ev == "stop" then
    local k = M.ctx_from(p.transcript_path)
    agents.set_status(c, name, "idle", { ctx_tokens = k })
    if not k then set_null(c, name, "ctx_tokens") end
  elseif ev == "session" then
    agents.touch(c, name, nil, false, { claude_pid = machine.claude_pid() })
    if p.source == "compact" then
      local k = M.post_compact(p.transcript_path)
      agents.touch(c, name, nil, false, { compacted_at = util.now(), ctx_tokens = k })
      if not k then set_null(c, name, "ctx_tokens") end
      db.log(c, name, "compact")
    else
      agents.set_status(c, name, "idle")
    end
  else
    util.die("unknown hook event " .. tostring(ev))
  end
end

return M
