-- Hooks: stdin JSON in, stdout JSON out; the context-size notes (the communicator gets those from its commands).
local util, json, db = require "swarm.util", require "swarm.json", require "swarm.db"
local agents, msgs, proc = require "swarm.agents", require "swarm.msgs", require "swarm.proc"
local machine, locks, re = require "swarm.machine", require "swarm.locks", require "swarm.re"
local cost = require "swarm.cost"
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

function M.ctx_advice(k, stays)
  if stays then  -- a stayer (the communicator too) holds what others rely on, so a handoff carries it over
    if k >= 550000 then
      return "finish the current step, then hand off with the relaunch skill, same model, and pass on what you hold "
        .. "(what you stay for, open threads; the communicator: board, watchd PID)."
    end
    return "wrap up this step; at ~550k hand off with the relaunch skill, same model, and pass on what you hold "
      .. "(what you stay for, open threads; the communicator: board, watchd PID)."
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
local function ctx_mark(sid)
  return util.join(tmpdir(), "claude-ctx-" .. ((sid and sid ~= "") and sid or "x"))
end

function M.handoff_nudge(c, name, p, comms)
  local k = M.ctx_from(p.transcript_path)
  if not k or k == 0 then return nil end
  c:exec("update agent set ctx_tokens=? where name=?", k, name)
  local step = math.floor((k - (M.CTX_WARN - 100000)) / 100000)  -- 1 at 350k, 2 at 450k, ...
  if step < 1 then return nil end
  local mark = ctx_mark(p.session_id)
  local last = tonumber(util.slurp(mark) or "") or 0
  if step <= last then return nil end
  local f = io.open(mark, "w")
  if f then f:write(util.d(step)); f:close() end
  db.log(c, name, "ctx-note", nil, util.d(k))
  return ("Context is ~%dk tokens: %s"):format(math.floor(k / 1000), M.ctx_advice(k, comms or agents.stay_of(c, name)))
end

-- The communicator is a normal session with no swarm hooks: read/wait/board/who stand in for post-tool.
function M.comms_nudge(c, cmd)
  local name, sid = agents.env("SWARM_NAME"), agents.env("CLAUDE_CODE_SESSION_ID")
  if not name or not agents.is_comms(c, name) then return end
  local aw, n = agents.away(c), nil
  if sid then
    local home = os.getenv("HOME") or ""
    local tr = (glob.glob(home .. "/.claude/projects/*/" .. sid .. ".jsonl", 0) or {})[1]
    n = M.handoff_nudge(c, name, { transcript_path = tr, session_id = sid }, true)
  end
  local say = { aw and agents.away_line(aw) or nil }  -- away rule 2: reminded on every read/wait/board
  say[#say + 1] = n
  for _, s in ipairs(say) do
    if cmd == "wait" then io.stderr:write(s .. "\n") else print(s) end
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
    local base = require("swarm.workspaces").base_checkout(c, name, cmd, cwd)
    if base then
      db.log(c, name, "deny-base", base, util.cut(cmd, 120))
      return emit("PreToolUse", nil, ("Don't check out %s in your worktree: a base checked out here blocks `git push . HEAD:%s` "
        .. "for everyone. Land by a fast-forward of it from your branch (`git push . HEAD:%s`), or a PR for a remote base."):format(base, base, base))
    end
    local ok, pr = pcall(cost.predict, cmd, cwd)  -- information at decision time: context only, never a deny or a rewrite
    local avail, total, psi = machine.mem()
    if ok and pr and avail and (pr.peak_kb > avail / 2 or machine.pressure_high(avail, total, psi)) then
      emit("PreToolUse", ("`%s` took ~%.1fG and %d min the last %d time%s here; %.1fG is available now.\n%s"):format(pr.key,
        pr.peak_kb / 1048576, math.max(1, math.floor(pr.wall_s / 60 + 0.5)), pr.n, pr.n == 1 and "" or "s", avail / 1048576,
        machine.machine_note(c, name)))
    end
  elseif EDIT_TOOLS[tool] then
    local fp = ti.file_path
    if fp == nil or fp == "" then fp = ti.notebook_path end
    local top, path = locks.repo_rel(fp or "", cwd)
    if not top then return end
    local lk = locks.lock_holder(c, name, path, t)
    if lk then
      db.log(c, name, "deny-lock", path, lk.agent)
      return emit("PreToolUse", nil, ("%s is locked by %s since %s%s. Ask it with `swarm post %s ...`."):format(
        path, lk.agent, util.hhmm(lk.since), (lk.reason and lk.reason ~= "") and (" (" .. lk.reason .. ")") or "", lk.agent))
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

M.STOP_CAP = 2  -- blocks per reason in one chain of continuations: a safety net, then allow and tell comms

local function error_turn(path)  -- the turn ended on an API error (rate limit, auth, context overflow): nothing to ask
  local lines = tail_lines(path)
  for i = #(lines or {}), 1, -1 do
    local j = json.decode(lines[i])
    if type(j) == "table" and j.type == "assistant" then return j.isApiErrorMessage == true end
  end
  return false
end

-- The Stop hook's verdict (no model call): nil lets the stop through; else the reason to continue. Not endable (the
-- predicate watchd ends by) and no declared wait -> block with the ways out. Declared: a stay, a task blocked on a
-- question, a job of its own, a pushed branch. A stretch of the same reason blocks at most STOP_CAP times.
function M.stop_block(c, name, p, k)
  if agents.is_comms(c, name) or error_turn(p.transcript_path) then return nil end
  local watchd = require "swarm.watchd"
  local row = c:one("select * from agent where name=? and ended is null", name)
  if not row then return nil end
  local R = watchd.reads(c, watchd.main_wt(), require("swarm.conflict").wt_map(c), require("swarm.conflict").worktrees(), {})
  local rs = watchd.endable_reasons(c, row, R.f(name))
  local bg = {}
  for _, t in ipairs(type(p.background_tasks) == "table" and p.background_tasks or {}) do  -- its own waiter doesn't count
    if t.status == "running" and not tostring(t.command or ""):find("swarm%s+wait") then bg[#bg + 1] = t end
  end
  local lines, keys = {}, {}
  for _, r in ipairs(rs) do if r.key == "idle-job" then bg = {} end end  -- a sleep-only loop is no wait
  if #bg > 0 then return nil end
  for _, r in ipairs(rs) do
    if r.declared then return nil end
    lines[#lines + 1] = r.text
    keys[#keys + 1] = r.key
  end
  if #rs == 0 then return nil end
  local key = table.concat(keys, ",")
  if not p.stop_hook_active then db.log(c, name, "stop-chain") end
  local since = (c:one("select max(id) m from event where agent=? and kind='stop-chain'", name) or {}).m or 0
  local n = c:one("select count(*) n from event where agent=? and kind='stop-block' and data=? and id>?", name, key, since).n
  if n >= M.STOP_CAP then
    db.log(c, name, "stop-cap", nil, key)
    msgs.post(c, "swarm", agents.comms_name(c),
      ("%s stopped though not endable (%s); the stop hook let it go after %d blocks."):format(name, key, M.STOP_CAP), false, "notice")
    return nil
  end
  db.log(c, name, "stop-block", nil, key)
  local head = ("You are not endable: %s"):format(table.concat(lines, "\n"))
  if (k or 0) >= 550000 and row and c:one("select 1 from task where owner=? and state='claimed'", name) then
    return head .. "\n\nYour context is too large to continue: hand off. Commit WIP, `swarm task release <id>` (or the "
      .. "relaunch skill, same model), and leave a note for the successor."
  end
  return head .. "\n\nEnd this by changing state, not by arguing: (a) finish and land (`swarm task done`); (b) drop: "
    .. "`swarm task release <id>` and commit, ignore or delete what is listed (pushing the branch counts as handing "
    .. "off commits); (c) declare the wait: `swarm task block <id> \"<question>\"` or `swarm stay \"<what>\"`."
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
    local why = M.stop_block(c, name, p, k)
    if why then print('{"decision": "block", "reason": ' .. json.encode(why) .. "}") end
  elseif ev == "session" then
    agents.touch(c, name, nil, false, { claude_pid = machine.claude_pid() })
    if p.source == "compact" then
      local k = M.post_compact(p.transcript_path)
      agents.touch(c, name, nil, false, { compacted_at = util.now(), ctx_tokens = k })
      if not k then set_null(c, name, "ctx_tokens") end
      os.remove(ctx_mark(p.session_id))  -- the notes fire again as the smaller context regrows
      db.log(c, name, "compact")
    else
      agents.set_status(c, name, "idle")
    end
  else
    util.die("unknown hook event " .. tostring(ev))
  end
end

return M
