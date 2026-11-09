-- swarm: shared board, messages, conflict notices and locks for a swarm of Claude Code agents.
-- One sqlite db per repo (shared by its worktrees). Agents use it through Bash and hooks.
-- Run through the swarm/swarm launcher, which sets the module path.

-- Every rock, before any work: a missing one is told here, never by a stack trace (sw-lua §4).
local ROCKS = { "lsqlite3", "cjson", "posix.unistd", "rex_pcre2", "lfs", "argparse", "lua-utf8" }
local missing = {}
for _, m in ipairs(ROCKS) do
  if not pcall(require, m) then missing[#missing + 1] = m end
end
if #missing > 0 and os.getenv("SWARM_HERE") and io.open(os.getenv("SWARM_HERE") .. "/swarm.py") then
  -- cutover window only (sw-lua §4), deleted in P11: run the Python CLI instead, same argv and stdin
  local function q(s) return "'" .. s:gsub("'", "'\\''") .. "'" end
  local cmd = { "exec python3", q(os.getenv("SWARM_HERE") .. "/swarm.py") }
  for _, a in ipairs(arg) do cmd[#cmd + 1] = q(a) end
  local r, _, code = os.execute(table.concat(cmd, " "))
  if type(r) == "number" then code = r > 255 and math.floor(r / 256) or r end  -- Lua 5.1: the wait status
  os.exit(code)
end
if #missing > 0 then
  local hint = os.getenv("SWARM_INSTALL_HINT") or "LuaJIT's rocks (swarm/research/sw-lua.md section 4)"
  local msg = "swarm hooks are OFF: missing Lua modules " .. table.concat(missing, ", ") .. "; install with " .. hint
  if arg[1] == "hook" then
    local ev = ({ ["pre-tool"] = "PreToolUse", ["post-tool"] = "PostToolUse", prompt = "UserPromptSubmit",
      session = "SessionStart" })[arg[2]]
    if not os.getenv("SWARM_NAME") or os.getenv("SWARM_NAME") == "" then os.exit(0) end
    if not ev then  -- stop has no context field
      io.stderr:write("swarm: " .. msg .. "\n")
      os.exit(1)
    end
    local s = msg:gsub('[\\"]', "\\%0")  -- hand-made JSON: cjson may be the missing one
    io.write(('{"hookSpecificOutput": {"hookEventName": "%s", "additionalContext": "%s"}, "systemMessage": "%s"}\n')
      :format(ev, s, s))
    os.exit(0)
  end
  io.stderr:write("swarm: missing Lua modules " .. table.concat(missing, ", ") .. "; install " .. hint .. "\n")
  os.exit(127)
end

local argparse = require "argparse"
local util = require "swarm.util"
local stdlib = require "posix.stdlib"

-- Which module ports each command. A command whose module (or cmd_<name>) isn't there yet dies "not ported".
local MODULE = { spawn = "watchd", join = "agents", leave = "agents", post = "msgs", read = "msgs", wait = "msgs",
  ci = "ci", task = "tasks", rules = "tasks", board = "tasks", who = "agents", lock = "locks", unlock = "locks",
  machine = "machine", run = "run", state = "state", watch = "state", watchd = "watchd", hook = "hook" }
local VIEWS = { "activity", "agents", "board", "overview", "system" }  -- sorted(VIEWS) of the Python CLI; state.lua owns it once ported

local function int(s)  -- Python's type=int
  return s:match("^%s*[+-]?%d+%s*$") and tonumber(s) or nil
end

-- `3,5` (or `3`) for --after: distinct ids in the order given.
local function id_list(s)
  local r, seen = {}, {}
  for x in s:gsub(" ", ""):gmatch("[^,]+") do
    local n = int(x)
    if not n then return nil, ("not a list of task ids: '%s'"):format(s) end
    if not seen[n] then seen[n] = true; r[#r + 1] = n end
  end
  return r
end

local function parser()
  local ap = argparse("swarm"):command_target("cmd")
  local function opt(p, name, default, conv)
    local o = p:option(name)
    if default ~= nil then o:default(default) end
    if conv then o:convert(conv) end
    return o
  end

  local p = ap:command("spawn")
  p:argument("name")
  opt(p, "--model", "sonnet")
  opt(p, "--task", nil, int):target("task_id"):description("claim this board task for the new agent before launching")
  p:argument("task"):args("*")
  p = ap:command("join")
  p:argument("name"):args("?")
  opt(p, "--model")
  p:flag("--takeover"):description("move a live binding of this name to this terminal")
  p = ap:command("leave")
  p:argument("name"):args("?")
  p = ap:command("post")
  p:argument("to")
  p:flag("--urgent")
  p:argument("text"):args("+")
  ap:command("read")
  p = ap:command("wait")
  opt(p, "--me")
  opt(p, "--timeout", 21000, int)  -- under the hook timeout of 21600
  opt(p, "--poll", 1, tonumber)
  p = ap:command("ci")
  p:argument("sha"):args("?"):default("HEAD")
  p:flag("--wait"):description("block until a finished run includes it")
  opt(p, "--timeout", 3600, int)
  opt(p, "--poll", 10, tonumber)

  p = ap:command("task"):command_target("act")
  local q = p:command("add")
  q:argument("title")
  opt(q, "--body", "")
  opt(q, "--after", nil, id_list):description("ids it waits on: 3 or 3,5")
  opt(q, "--model")
  q = p:command("after")  -- change an open task's dependencies; an empty list clears them
  q:argument("id"):convert(int)
  q:argument("deps"):args("?"):convert(id_list)
  for _, act in ipairs({ "claim", "renew" }) do
    q = p:command(act)
    q:argument("id"):convert(int)
    opt(q, "--lease", "2h")
  end
  p:command("show"):argument("id"):convert(int)
  q = p:command("done")
  q:argument("id"):convert(int)
  q:option("--evidence"):count(1)
  q = p:command("block")
  q:argument("id"):convert(int)
  q:argument("question")
  q = p:command("unblock")
  q:argument("id"):convert(int)
  opt(q, "--answer", "")
  p:command("release"):argument("id"):convert(int)  -- give a claimed task back, still open; drop kills it
  p:command("drop"):argument("id"):convert(int)

  p = ap:command("rules"):command_target("act")
  p:command("show")
  p:command("set"):argument("text"):args("+")
  p = ap:command("board")
  p:flag("--all")
  ap:command("who")
  p = ap:command("lock")
  p:argument("path")
  opt(p, "--reason", "")
  opt(p, "--lease", "2h")
  ap:command("unlock"):argument("path")
  ap:command("machine")
  p = ap:command("run")  -- its command (a.argv) is split off before parsing: Python's REMAINDER
  opt(p, "--on"):description("an hc machine (`hc machine ls`); default: here")
  opt(p, "--env"):count("*"):argname("NAME[=VAL]"):description("also pass this variable (repeatable)")
  p = ap:command("state")
  p:flag("--json"):count(1)
  opt(p, "--view"):choices(VIEWS):description("only what that panel view shows (default: everything)")
  opt(p, "--agent"):description("also the detail pane's messages and events for this agent")
  p = ap:command("watch")
  opt(p, "--tail", 20, int)
  p:flag("--once")
  p = ap:command("watchd")
  opt(p, "--comms")
  opt(p, "--interval", 30, int)
  p:flag("--once")
  p:flag("--ci"):description("also watch main CI with gh")
  p:flag("--takeover"):description("replace a live watchd; it exits on its next tick")
  p:flag("--dry-run"):description("only list the worktrees the sweep would remove, then exit")
  opt(p, "--max-agents", nil, int):description("cap for auto-spawn (default: live agents now)")
  opt(p, "--min-free-mem", 4, tonumber):description("GiB of MemAvailable needed to auto-spawn")
  opt(p, "--model"):description("model for auto-spawned agents (default: the most common)")
  p = ap:command("hook")
  p:argument("event"):choices({ "pre-tool", "post-tool", "prompt", "stop", "session" })
  return ap
end

-- `swarm run [--on M] [--env X]... cmd…`: everything from the first positional (or `--`) on is the command.
local function split_run(argv)
  local i = 2
  while argv[i] do
    local x = argv[i]
    if x == "--on" or x == "--env" then i = i + 2
    elseif x:match("^%-%-on=") or x:match("^%-%-env=") or x == "-h" or x == "--help" then i = i + 1
    else break end
  end
  local head, rest = {}, {}
  for j = 1, #argv do
    if j < i then head[#head + 1] = argv[j] else rest[#rest + 1] = argv[j] end
  end
  if rest[1] == "--" then table.remove(rest, 1) end
  return head, rest
end

local function main(argv)
  local rest
  if argv[1] == "run" then argv, rest = split_run(argv) end
  local ap = parser()
  local ok, a = ap:pparse(argv)
  if not ok then
    io.stderr:write(ap:get_usage() .. "\nswarm: error: " .. a .. "\n")
    util.exit(2)
  end
  a.argv = rest
  if a.cmd == "task" and a.act == "after" then a.deps = a.deps or {} end
  if a.cmd == "spawn" and a.task[1] == "--" then table.remove(a.task, 1) end

  local mod, fn = MODULE[a.cmd], a.cmd == "hook" and "hook" or "cmd_" .. a.cmd
  local m = package.searchpath("swarm." .. mod, package.path) and require("swarm." .. mod)
  if not (m and m[fn]) then util.die(("`%s` is not ported to Lua yet"):format(a.cmd)) end
  if a.cmd == "hook" then return m.hook(a.event) end
  if a.cmd == "state" then return m.cmd_state(a) end
  if a.cmd == "wait" and a.me then stdlib.setenv("SWARM_NAME", a.me) end

  local agents = require "swarm.agents"
  local c = require("swarm.db").connect()
  local name = agents.env("SWARM_NAME")
  local fenced = { post = true, read = true, task = true, lock = true, unlock = true, leave = true }
  if name and fenced[a.cmd] and a.act ~= "show" then
    local why = agents.fence(c, name)
    if why then util.die(why) end
  end
  if a.cmd == "read" or a.cmd == "wait" or a.cmd == "board" or a.cmd == "who" then
    require("swarm.hook").comms_nudge(c, a.cmd)
  end
  return m[fn](c, a)
end

local ok, err = xpcall(main, function(e)
  if type(e) == "table" and e.exit then return e end
  return debug.traceback(e, 2)
end, arg)
io.stdout:flush()
if ok then os.exit(0) end
if type(err) == "table" then
  if err.lost then io.stderr:write(err.lost .. "\n") end  -- tasks.reserve's lost race, uncaught: Python prints SystemExit's text
  os.exit(err.exit)
end
io.stderr:write("swarm: " .. tostring(err) .. "\n")
os.exit(1)
