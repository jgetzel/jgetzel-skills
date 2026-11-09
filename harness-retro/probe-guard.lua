#!/usr/bin/env luajit
-- PreToolUse guard for harness-retro probe agents: keep a replay inside its checkout.
--
--   probe-guard.lua WORKTREE MAIN_REPO      (hook; event JSON on stdin)
--   probe-guard.lua --selftest
--
-- Allows a fixed set of local tools. Denies anything that reaches outside the
-- checkout: pushes, PRs, ssh, herdr, messages to other agents, shared git refs,
-- writes outside the worktree and /tmp, and any command naming the main repo.
local d = (arg[0]:match("^(.*)/[^/]*$") or ".")
package.path = d .. "/?.lua;" .. d .. "/../swarm/lua/?.lua;" .. package.path
local hr, re, json = require "hr", require "swarm.re", require "swarm.json"

local TOOLS = {}
for t in ([[Read Write Edit MultiEdit NotebookEdit Bash Glob Grep LS ToolSearch Skill TodoWrite Task Agent Monitor
  TaskStop TaskOutput BashOutput KillShell WebFetch WebSearch]]):gmatch("%S+") do TOOLS[t] = true end
-- shortcut: a denylist on command text, not a sandbox; Bash can still write outside via a script it wrote.
local DENY = [[\bgit\s+(push|worktree|tag|update-ref|stash|branch\s+(-[dDmMcC]\b|[^-\s])|checkout\s+-[bB]|switch\s+-[cC])]]
  .. [[|\bgh\s+(pr|issue|release|repo|api|workflow|run\s+(rerun|cancel))\b]]
  .. [[|\b(ssh|scp|rsync|herdr|pkill|killall)\b|\b(npm|cargo|uv)\s+publish\b|\bdocker\s+push\b]]
  .. [[|\bcurl\b[^|;&]*-X\s*(POST|PUT|PATCH|DELETE)]]

local function truthy(v) return v ~= nil and v ~= false and v ~= "" and v ~= 0 end

local function verdict(ev, wt, main)
  local tool, inp = ev.tool_name or "", ev.tool_input or {}
  if not TOOLS[tool] then return tool .. " reaches outside this sandboxed replay" end
  if truthy(inp.isolation) then return "worktree isolation creates shared git refs; work in this checkout" end
  local cmd = inp.command or ""
  if cmd ~= "" then
    local m = re.search(DENY, cmd)
    if m then return "`" .. m[0]:match("^%s*(.-)%s*$") .. "` leaves this sandboxed replay" end
    for _, p in ipairs { main, hr.plain_replace(main, hr.HOME, "~") } do
      if re.search(re.escape(p) .. [[(/|\s|$|['"])]], cmd) then
        return main .. " is the live repo; use this checkout (" .. wt .. ")"
      end
    end
  end
  local path = inp.file_path or inp.notebook_path
  if truthy(path) and not ({ Read = 1, Glob = 1, Grep = 1, LS = 1 })[tool] then
    local p = hr.realpath(hr.expanduser(path))
    local w = hr.realpath(wt)
    if not (p == w or p:sub(1, #w + 1) == w .. "/" or p == "/tmp" or p:sub(1, 5) == "/tmp/") then
      return "write to " .. path .. " is outside this checkout"
    end
  end
end

local function selftest()
  local wt, main = "/w/.r-worktrees/probe-1-a", hr.HOME .. "/r"
  local function ok(t, i) return verdict({ tool_name = t, tool_input = i }, wt, main) == nil end
  assert(not ok("Bash", { command = "git commit -m 'ssh fix'" }))  -- matches inside quotes too, deliberately
  assert(ok("Bash", { command = "just test && git commit -am wip" }))
  assert(not ok("Bash", { command = "git push origin HEAD" }))
  assert(not ok("Bash", { command = "bash -c 'gh pr create'" }))
  assert(not ok("Bash", { command = "git branch -D other" }))
  assert(ok("Bash", { command = "git branch --show-current" }))
  assert(not ok("Bash", { command = "cd " .. main .. " && ls" }))
  assert(not ok("Bash", { command = "git -C ~/r log" }))
  assert(ok("Bash", { command = "ls ~/rx" }))
  assert(not ok("Monitor", { command = "ssh desktop tail -F log" }))
  assert(not ok("SendMessage", { to = "wf-ml", message = "hi" }))
  assert(not ok("Agent", { prompt = "x", isolation = "worktree" }))
  assert(ok("Write", { file_path = wt .. "/a.py" }))
  assert(ok("Write", { file_path = "/tmp/x" }))
  assert(not ok("Write", { file_path = wt .. "/../../x" }))
  assert(not ok("Write", { file_path = hr.HOME .. "/.claude/projects/r/memory/m.md" }))
  assert(ok("Read", { file_path = "/etc/hosts" }))
  print("probe-guard selftest ok")
end

if arg[1] == "--selftest" and #arg == 1 then return selftest() end
local ev = assert(json.decode(io.read("*a")))
local why = verdict(ev, arg[1], arg[2])
if why then
  io.stderr:write("Blocked by harness-retro probe-guard: ", why, ". This is a sandboxed replay; ",
    "note what you would have done and continue locally.\n")
  os.exit(2)
end
