-- swarm: shared board, messages, conflict notices and locks for a swarm of Claude Code agents.
-- One sqlite db per repo (shared by its worktrees). Agents use it through Bash and hooks.
-- Run through the swarm/swarm launcher, which sets the module path.

-- Every rock, before any work: a missing one is told here, never by a stack trace (sw-lua §4).
local ROCKS = { "lsqlite3", "cjson", "posix.unistd", "rex_pcre2", "lfs", "argparse", "lua-utf8" }
local missing = {}
for _, m in ipairs(ROCKS) do
  if not pcall(require, m) then missing[#missing + 1] = m end
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
  ci = "ci", task = "tasks", rules = "tasks", board = "tasks", who = "agents", limits = "agents", away = "agents", stay = "agents", nudge = "agents", lock = "locks", unlock = "locks",
  machine = "machine", cost = "cost", role = "agents", run = "run", state = "state", watch = "state", watchd = "watchd", ["end"] = "watchd", hook = "hook" }
local EFFORTS = { "low", "medium", "high", "xhigh", "max" }  -- claude --effort
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
  opt(p, "--effort"):choices(EFFORTS):description("claude --effort for the new agent (default: its settings)")
  opt(p, "--stay"):description("what the new agent waits for: watchd won't end it while it stays")
  opt(p, "--task", nil, int):target("task_id"):description("claim this board task for the new agent before launching")
  opt(p, "--role"):description("the new agent's role label (`swarm role`)")
  opt(p, "--attach"):description("start it read-only in this swarm workspace instead of making it a worktree")
  p:argument("task"):args("*")
  p = ap:command("join")
  p:argument("name"):args("?")
  opt(p, "--model")
  p:flag("--takeover"):description("move a live binding of this name to this terminal")
  p = ap:command("end"):description("communicator: end an agent's terminal (not its worktree); checks it is idle with work landed")
  p:argument("agent")
  p:flag("--force"):description("skip the checks")
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
  opt(q, "--effort"):choices(EFFORTS)
  opt(q, "--base"):description("branch its work lands on (default: .claude/swarm.json base, else main)")
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
  q = p:command("release")  -- give a claimed task back, still open; drop kills it
  q:argument("id"):convert(int)
  opt(q, "--after", nil, id_list):description("ids it now waits on: 3 or 3,5")
  p:command("drop"):argument("id"):convert(int)

  p = ap:command("rules"):command_target("act")
  p:command("show")
  p:command("set"):argument("text"):args("+")
  p = ap:command("board")
  p:flag("--all")
  ap:command("who")
  ap:command("role"):argument("text"):args("*")
  p = ap:command("stay")  -- what I wait for; watchd doesn't end an agent that stays
  p:argument("text"):args("*")
  p:flag("--end"):description("clear it: judged as any agent again; `--end NAME` clears NAME's (human or the communicator)")
  p = ap:command("nudge"):description("type one fixed line into an agent's terminal: read your messages and continue")
  p:argument("agent")
  p = ap:command("limits")  -- the user's staffing numbers (sw-roles §6)
  opt(p, "--min", nil, int):description("auto-spawn number: watchd staffs tasks until this many agents are live")
  opt(p, "--max", nil, int):description("agent max: `swarm spawn` refuses at this many live agents")
  p = ap:command("away")  -- the user is away: questions wait, nobody is pinged for them
  p:argument("note"):args("*")
  p:flag("--back"):description("the user is back: print what waits for them")
  p = ap:command("lock")
  p:argument("path")
  opt(p, "--reason", "")
  opt(p, "--lease", "2h")
  ap:command("unlock"):argument("path")
  ap:command("machine")
  p = ap:command("cost")  -- what a command is expected to take here, or the most intensive ones
  p:argument("words"):args("*")
  p:flag("--top")
  opt(p, "--repo")
  p:flag("--all-repos")
  p = ap:command("run")  -- its command (a.argv) is split off before parsing: Python's REMAINDER
  opt(p, "--on"):description("an hc machine (`hc machine ls`); default: here")
  opt(p, "--env"):count("*"):argname("NAME[=VAL]"):description("also pass this variable (repeatable)")
  p = ap:command("state")
  p:flag("--json"):count(1)
  opt(p, "--view"):choices(VIEWS):description("only what that panel view shows (default: everything)")
  opt(p, "--agent"):description("also the detail pane's messages and events for this agent")
  opt(p, "--task", nil, int):description("also that task's body, events and the messages that name it")
  p = ap:command("watch")
  opt(p, "--tail", 20, int)
  p:flag("--once")
  p = ap:command("watchd")
  opt(p, "--comms")
  opt(p, "--interval", 30, int)
  p:flag("--once")
  p:flag("--ci"):description("also watch main CI with gh")
  p:flag("--takeover"):description("replace a live watchd; it exits on its next tick")
  p:flag("--restart"):description("start the same watchd (its recorded flags) in a hidden hc terminal, taking over")
  p:flag("--dry-run"):description("only list the worktrees the sweep would remove, then exit")
  opt(p, "--max-agents", nil, int):description("set the auto-spawn number (`swarm limits --min`; default: live agents when first started)")
  opt(p, "--min-free-mem", 4, tonumber):description("GiB of MemAvailable needed to auto-spawn")
  opt(p, "--model"):description("model for auto-spawned agents (default: sonnet; a task's own --model wins)")
  opt(p, "--effort"):choices(EFFORTS):description("effort for auto-spawned agents (default: their settings)")
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
  local fenced = { post = true, read = true, task = true, lock = true, unlock = true, leave = true, stay = true }
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
  if err.lost or err.refused then io.stderr:write((err.lost or err.refused) .. "\n") end  -- tasks.reserve's lost race, uncaught: Python prints SystemExit's text
  os.exit(err.exit)
end
io.stderr:write("swarm: " .. tostring(err) .. "\n")
os.exit(1)
