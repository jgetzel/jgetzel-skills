#!/usr/bin/env luajit
-- Check the harness mechanically and count what every session pays for.
--
--   harness-lint.lua [--repo DIR] [--max-bytes N]
--
-- Always-on bytes: user and project CLAUDE.md (+ @imports), .claude/rules, the auto-memory
-- MEMORY.md (first 200 lines). Errors (exit 1): a skill without SKILL.md or description, a
-- name that doesn't match its directory, a referenced skill script that is missing or not
-- executable, settings that don't parse, a hook command path that doesn't exist, a hook or
-- skill script that doesn't compile, always-on bytes over --max-bytes.
local d = (arg[0]:match("^(.*)/[^/]*$") or ".")
package.path = d .. "/?.lua;" .. d .. "/../swarm/lua/?.lua;" .. package.path
local hr, re, json, proc = require "hr", require "swarm.re", require "swarm.json", require "swarm.proc"
local util, utf8, unistd = require "swarm.util", require "lua-utf8", require "posix.unistd"

local HOME = hr.HOME
local EVENTS = {}
for e in ([[PreToolUse PostToolUse PostToolUseFailure PermissionRequest PermissionDenied Notification
  UserPromptSubmit Stop StopFailure SubagentStart SubagentStop PreCompact PostCompact SessionStart SessionEnd Setup
  TeammateIdle TaskCreated TaskCompleted ConfigChange CwdChanged FileChanged InstructionsLoaded WorktreeCreate
  WorktreeRemove Elicitation ElicitationResult]]):gmatch("%S+") do EVENTS[e] = true end
local errors, warnings = {}, {}

local function imports(path, seen)  -- a CLAUDE.md and the files it @imports, recursively (max depth 5, like Claude Code)
  for _, s in ipairs(seen) do if s == path then return end end
  if #seen > 50 or not hr.isfile(path) then return end
  seen[#seen + 1] = path
  local text = re.sub("```.*?```|`[^`\\n]*`", "", hr.read(path), re.S)
  for m in re.finditer([[(?:^|\s)@((?:~|\.{1,2})?/?[\w./-]+)]], text) do
    local p = hr.normpath(util.join(util.dirname(path), hr.expanduser(m[1])))
    if hr.isfile(p) then imports(p, seen)
    elseif m[1]:find("/", 1, true) then warnings[#warnings + 1] = path .. ": @" .. m[1] .. " not found" end
  end
end

local function always_on(repo)
  local files = {}
  local cands = { HOME .. "/.claude/CLAUDE.md" }
  if repo ~= "" then
    for _, f in ipairs { "/CLAUDE.md", "/CLAUDE.local.md", "/.claude/CLAUDE.md" } do cands[#cands + 1] = repo .. f end
  end
  for _, f in ipairs(cands) do imports(f, files) end
  if repo ~= "" then
    for _, f in ipairs(hr.walk(repo .. "/.claude/rules", ".md")) do files[#files + 1] = f end
    local common = proc.git({ "-C", repo, "rev-parse", "--path-format=absolute", "--git-common-dir" }) or ""
    local root = common:sub(-5) == "/.git" and util.dirname(common) or repo
    local mem = HOME .. "/.claude/projects/" .. re.sub("[^A-Za-z0-9]", "-", root) .. "/memory/MEMORY.md"
    if hr.isfile(mem) then files[#files + 1] = mem end
  end
  local rows = {}
  for _, f in ipairs(files) do
    local data = util.slurp(f)
    if f:sub(-17) == "/memory/MEMORY.md" then  -- the first 200 lines, without the newline after the last
      local pos = 0
      for _ = 1, 200 do
        pos = data:find("\n", pos + 1, true)
        if not pos then break end
      end
      if pos then data = data:sub(1, pos - 1) end
    end
    rows[#rows + 1] = { #data, f }
  end
  return rows
end

local function compiles(path)
  local err
  if path:sub(-3) == ".py" then
    local _, e, code = proc.exec({ "python3", "-c",
      "import sys; compile(open(sys.argv[1], encoding='utf-8').read(), sys.argv[1], 'exec')", path })
    if code ~= 0 and code ~= 127 then err = "does not compile: " .. (e:match("([^\n]*)\n*$") or e) end
  elseif path:sub(-3) == ".sh" then
    local _, e, code = proc.exec({ "bash", "-n", path })
    if code ~= 0 then err = "bash -n: " .. util.strip(e) end
  elseif path:sub(-4) == ".lua" then
    local _, e, code = proc.exec({ "luajit", "-b", path, "/dev/null" })
    if code ~= 0 and code ~= 127 then err = "does not compile: " .. util.strip(e) end
  end
  if err then errors[#errors + 1] = path .. ": " .. err end
end

local function skills(repo)
  local dirs = hr.subdirs(HOME .. "/.claude/skills")
  if repo ~= "" then for _, x in ipairs(hr.subdirs(repo .. "/.claude/skills")) do dirs[#dirs + 1] = x end end
  for _, dir in ipairs(dirs) do
    local name, md = util.basename(dir), dir .. "/SKILL.md"
    if not hr.isfile(md) then
      local found = false
      for _, f in ipairs(hr.walk(dir, "SKILL.md")) do if util.basename(f) == "SKILL.md" then found = true end end
      if not found then errors[#errors + 1] = dir .. ": no SKILL.md" end  -- else a container of skills, e.g. a synced bundle
    else
      local text = hr.read(md)
      local fm = re.match("---\\n(.*?)\\n---", text, re.S)
      local meta = {}
      if fm then for m in re.finditer([[^(\w[\w-]*):\s*(.*)$]], fm[1], re.M) do meta[m[1]] = m[2] end end
      local desc = util.strip(meta.description or ""):gsub("^[\"']+", ""):gsub("[\"']+$", "")
      if desc == "" then
        errors[#errors + 1] = md .. ": no description in frontmatter (the skill never triggers)"
      elseif utf8.len(desc) > 1024 then
        warnings[#warnings + 1] = md .. ": description is " .. utf8.len(desc) .. " chars (limit 1024)"
      end
      if meta.name and util.strip(meta.name) ~= name then
        errors[#errors + 1] = md .. ": name '" .. util.strip(meta.name) .. "' does not match directory '" .. name .. "'"
      end
      for m in re.finditer([[(\b(?:python3?|luajit|bash|sh)\s+)?(~/\.claude/skills/[\w./-]+\.(?:sh|py|lua))]], text) do
        local p = hr.expanduser(m[2])
        if not hr.isfile(p) then
          errors[#errors + 1] = md .. ": references " .. m[2] .. ", which does not exist"
        elseif not m[1] and not unistd.access(p, "x") then
          errors[#errors + 1] = md .. ": runs " .. m[2] .. " directly but it is not executable"
        end
      end
      for _, ext in ipairs { ".py", ".sh", ".lua" } do
        for _, f in ipairs(hr.walk(dir, ext)) do compiles(f) end
      end
    end
  end
end

local function settings(repo)
  local files = { HOME .. "/.claude/settings.json", HOME .. "/.claude/settings.local.json" }
  if repo ~= "" then
    files[#files + 1] = repo .. "/.claude/settings.json"
    files[#files + 1] = repo .. "/.claude/settings.local.json"
  end
  for _, f in ipairs(files) do
    if hr.isfile(f) then
      local cfg, e = json.decode(util.slurp(f))
      if type(cfg) ~= "table" then
        errors[#errors + 1] = f .. ": invalid JSON: " .. tostring(e)
      else
        local events = {}
        for ev in pairs(cfg.hooks or {}) do events[#events + 1] = ev end
        table.sort(events)  -- cjson loses the file's key order
        for _, event in ipairs(events) do
          if not EVENTS[event] then warnings[#warnings + 1] = f .. ": unknown hook event " .. event end
          for _, e2 in ipairs(cfg.hooks[event]) do
            for _, h in ipairs(e2.hooks or {}) do
              local cmd = h.command or ""
              for m in re.finditer([[(?:^|(?<=[\s"'=(]))((?:~|\$HOME|\$\{HOME\}|\$CLAUDE_PROJECT_DIR|/)[^\s"';|&]*)]], cmd) do
                local tok = m[1]
                if re.search([[\.(py|sh|lua)$|/bin/]], tok) then
                  local p = hr.expanduser(hr.plain_replace(hr.plain_replace(hr.plain_replace(tok,
                    "$CLAUDE_PROJECT_DIR", repo), "${HOME}", HOME), "$HOME", HOME))
                  if not hr.mode(p) then
                    errors[#errors + 1] = f .. ": " .. event .. " hook runs " .. tok .. ", which does not exist"
                  else
                    compiles(p)
                  end
                end
              end
            end
          end
        end
      end
    end
  end
end

local function main()
  local ap = require("argparse")("harness-lint.lua")
  ap:option("--repo", "default: the cwd's git root")
  ap:option("--max-bytes"):convert(tonumber)
  local ok, a = ap:pparse()
  if not ok then io.stderr:write(tostring(a), "\n"); os.exit(2) end
  local repo = a.repo or proc.git({ "rev-parse", "--show-toplevel" }) or ""
  local rows, total = always_on(repo), 0
  for _, r in ipairs(rows) do total = total + r[1] end
  print("## Always-on bytes")
  for _, r in ipairs(rows) do print(("%7d  %s"):format(r[1], hr.plain_replace(r[2], HOME, "~"))) end
  print(("%7d  total"):format(total))
  if a.max_bytes and a.max_bytes ~= 0 and total > a.max_bytes then
    errors[#errors + 1] = "always-on is " .. total .. " bytes, over --max-bytes " .. util.d(a.max_bytes)
  end
  skills(repo)
  settings(repo)
  for _, w in ipairs(warnings) do print("warn: " .. w) end
  for _, e in ipairs(errors) do print("ERROR: " .. e) end
  print(#errors == 0 and "ok" or (#errors .. " error(s)"))
  return #errors > 0 and 1 or 0
end

os.exit(main())
