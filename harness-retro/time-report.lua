#!/usr/bin/env luajit
-- Where the time went: tool wall time from Claude Code transcripts, plus CI job time.
--
--   time-report.lua [--since 2026-10-07T08:00] [--project-dir DIR]... [--top 15] [--no-ci]
--
-- Transcripts: every session in the project dir (the orchestrator and its herdr
-- agents share one; repeat --project-dir for agents that worked in another repo) whose records fall after --since
-- (default: 24 h ago). A foreground tool call runs from tool_use to tool_result; a background Bash call
-- runs to its task-notification. Commands are grouped by what they ran (`just
-- test`, `gh pr checks`, ...), so the top rows are the optimization targets.
-- CI: `gh run list` in the cwd's repo, job and step durations for runs created
-- after --since.
local d = (arg[0]:match("^(.*)/[^/]*$") or ".")
package.path = d .. "/?.lua;" .. d .. "/../swarm/lua/?.lua;" .. package.path
local hr, re, json, proc = require "hr", require "swarm.re", require "swarm.json", require "swarm.proc"
local lfs, unistd = require "lfs", require "posix.unistd"

local function ts(s) return (hr.parse_iso((s:gsub("Z$", "+00:00")))) or error("bad timestamp " .. s) end

local KEYS = {
  { "just", [[(?:^|[;&|(`]|\bflock\s+\S+|--command)\s*just\s+([\w-]+)]] }, { "gh", [[\bgh\s+(\w+\s+[\w-]+)]] },
  { "nix", [[\bnix\s+(\w+)]] }, { "cabal", [[\bcabal\s+(\w+)]] }, { "git", [[\bgit\s+([\w-]+)]] },
  { "herdr", [[\bherdr\s+(\w+\s+[\w-]+)]] }, { "script", [[([\w-]+\.(?:sh|py|lua))\b]] } }

local function key(name, inp)
  if name ~= "Bash" then return name end
  local cmd = type(inp.command) == "string" and inp.command or ""
  if re.match([[\s*(until|while|sleep)\b]], cmd) then return "bash: wait loop" end
  if re.search([[gh run watch|gh pr checks .*--watch]], cmd) then return "gh: wait for CI" end
  for _, k in ipairs(KEYS) do
    local m = re.search(k[2], cmd)
    if m then return k[1] .. " " .. m[1] end
  end
  return "bash: " .. (cmd:match("%S+") or "?")
end

local function text_of(c)  -- blocks joined with a space, as time-report always did
  if type(c) == "string" then return c end
  local t = {}
  for _, b in ipairs(c) do if type(b) == "table" then t[#t + 1] = b.text or "" end end
  return table.concat(t, " ")
end

local function label(first, sid)  -- agent briefs open "You are <name>", sometimes as pasted content
  local m = re.search([[agent \*\*([\w-]+)\*\*]], first) or re.search([[\A\W*(?:<pasted_content[^>]*>\s*)?You are \**([a-z][\w-]*)]], first)
  if m then return m[1] end
  if first:find("orchestrat", 1, true) then return "orchestrator" end
  return sid:sub(1, 8)
end

-- A table of [total, count, max] rows that remembers the order its keys arrived in.
local function rows() return { r = {}, order = {} } end
local function row(t, k)
  if not t.r[k] then t.r[k] = { 0, 0, 0 }; t.order[#t.order + 1] = k end
  return t.r[k]
end
local function add(r, dur) r[1] = r[1] + dur; r[2] = r[2] + 1; r[3] = math.max(r[3], dur) end

-- Waiting on CI, agents or the user, not doing work.
local WAITING = [[watch\.sh|wait loop|AskUserQuestion|wait for CI|gh pr checks|herdr agent wait]]

local function sessions(pdirs, since)
  local tools, model, per, morder = rows(), {}, {}, {}
  local files = {}
  for _, dir in ipairs(pdirs) do
    for _, f in ipairs(hr.walk(dir, ".jsonl")) do
      if f:match("^[^/]*$") == nil and f:sub(1, #dir + 1) == dir .. "/" and not f:find("/", #dir + 2, true) then
        files[#files + 1] = f
      end
    end
  end
  for _, f in ipairs(files) do
    if lfs.attributes(f, "modification") >= since then
      local recs = {}
      for line in io.lines(f) do
        local r = json.decode(line)
        if type(r) == "table" and r.timestamp then
          if (r.type == "user" or r.type == "assistant") and not r.isSidechain then
            recs[#recs + 1] = r
          end
        end
        if type(r) == "table" and r.type == "queue-operation" and r.operation == "enqueue" then  -- task-notifications
          recs[#recs + 1] = { type = "notify", timestamp = r.timestamp, message = { content = r.content or "" } }
        end
      end
      local kept = {}
      for _, r in ipairs(recs) do
        r.t = ts(r.timestamp)
        if r.t >= since then kept[#kept + 1] = r end
      end
      recs = kept
      if #recs > 0 then
        local first = ""
        for _, r in ipairs(recs) do
          if r.type == "user" then first = text_of(r.message.content or ""); break end
        end
        local who = label(first, f:match("[^/]*$"))
        local uses, bg, prevkind, prevt = {}, {}, nil, nil
        for _, r in ipairs(recs) do
          local t, c = r.t, r.message.content or ""
          local skip = false
          if r.type == "assistant" then
            if prevkind == "tool" then  -- model time after a tool result
              if model[who] == nil then morder[#morder + 1] = who end
              model[who] = (model[who] or 0) + (t - prevt)
            end
            if type(c) == "table" then
              for _, b in ipairs(c) do
                if b.type == "tool_use" then
                  local inp = type(b.input) == "table" and b.input or {}
                  uses[b.id] = { t, key(b.name, inp), inp.run_in_background }
                end
              end
            end
            prevkind, prevt = "asst", t
            skip = true
          end
          if not skip then
            for m in re.finditer([[<tool-use-id>(\w+)</tool-use-id>]], text_of(c)) do
              if bg[m[1]] then
                local b = bg[m[1]]; bg[m[1]] = nil
                add(row(tools, who .. "\0" .. b[2] .. " (bg)"), t - b[1])
              end
            end
            if r.type ~= "notify" then
              local is_tool = false
              if type(c) == "table" then
                for _, b in ipairs(c) do
                  if b.type == "tool_result" and uses[b.tool_use_id] then
                    is_tool = true
                    local u = uses[b.tool_use_id]; uses[b.tool_use_id] = nil
                    local background = u[3]
                    if background and background ~= 0 and background ~= "" then
                      bg[b.tool_use_id] = u
                    else
                      add(row(tools, who .. "\0" .. u[2]), t - u[1])
                      per[who] = (per[who] or 0) + (t - u[1])
                    end
                  end
                end
              end
              prevkind, prevt = is_tool and "tool" or "human", t
            end
          end
        end
      end
    end
  end
  return tools, model, per
end

local function jobsof(out)
  local j = json.decode(out ~= "" and out or '{"jobs":[]}')
  return type(j) == "table" and j.jobs or {}
end

local function ci(since)
  local q = '.[]|select(.createdAt >= "' .. os.date("!%Y-%m-%dT%H:%M:%SZ", math.floor(since)) .. '")|.databaseId'
  local out = proc.exec({ "gh", "run", "list", "--limit", "100", "--json", "databaseId,createdAt", "--jq", q })
  local ids = {}
  for i in out:gmatch("%S+") do ids[#ids + 1] = i end
  local jobs, steps, sorder = rows(), {}, {}
  for _, i in ipairs(ids) do
    local jo = proc.exec({ "gh", "run", "view", i, "--json", "jobs" })
    for _, j in ipairs(jobsof(jo)) do
      if j.completedAt and j.completedAt:sub(1, 4) ~= "0001" then
        local dur = ts(j.completedAt) - ts(j.startedAt)
        if j.conclusion ~= "skipped" and dur >= 0 then
          add(row(jobs, j.name), dur)
          for _, s in ipairs(j.steps or {}) do
            if s.completedAt and s.completedAt:sub(1, 4) ~= "0001" then
              local k = j.name .. " › " .. s.name
              if not steps[k] then sorder[#sorder + 1] = k end
              steps[k] = (steps[k] or 0) + (ts(s.completedAt) - ts(s.startedAt))
            end
          end
        end
      end
    end
  end
  return #ids, jobs, steps, sorder
end

local function fmt(s) return ("%6.1fm"):format(s / 60) end

local function main()
  local ap = require("argparse")("time-report.lua")
  ap:option("--since", "ISO time (local if no zone); default 24 h ago")
  ap:option("--project-dir", "repeatable; default: the cwd's project dir"):count("*")
  ap:option("--top"):default("15"):convert(tonumber)
  ap:flag("--no-ci")
  local ok, a = ap:pparse()
  if not ok then io.stderr:write(tostring(a), "\n"); os.exit(2) end
  local since = os.time() - 24 * 3600
  if a.since then
    since = hr.parse_iso(a.since)
    if not since then io.stderr:write("time-report.lua: error: bad --since ", a.since, "\n"); os.exit(2) end
  end
  local pdirs = #a.project_dir > 0 and a.project_dir
    or { hr.HOME .. "/.claude/projects/" .. re.sub("[^A-Za-z0-9]", "-", unistd.getcwd()) }
  local tools, model, per = sessions(pdirs, since)
  print(("# Time report since %s\n\n## Sessions (foreground tool time · model time)"):format(os.date("%Y-%m-%d %H:%M", math.floor(since))))
  local whos, seen = {}, {}
  for w in pairs(per) do whos[#whos + 1] = w; seen[w] = true end
  for w in pairs(model) do if not seen[w] then whos[#whos + 1] = w end end
  table.sort(whos)
  for _, who in ipairs(hr.sorted(whos, function(w) return -((per[w] or 0) + (model[w] or 0)) end)) do
    print(("%s tools · %s model   %s"):format(fmt(per[who] or 0), fmt(model[who] or 0), who))
  end
  local agg = rows()
  for _, wk in ipairs(tools.order) do
    local r = tools.r[wk]
    local x = row(agg, wk:match("%z(.*)$"))
    x[1] = x[1] + r[1]; x[2] = x[2] + r[2]; x[3] = math.max(x[3], r[3])
  end
  for _, sec in ipairs { { "Work", false }, { "Waiting (CI, agents, user)", true } } do
    print(("\n## %s: tool time, all sessions (total · calls · max)"):format(sec[1]))
    local list = {}
    for _, k in ipairs(agg.order) do if (re.search(WAITING, k) ~= nil) == sec[2] then list[#list + 1] = k end end
    list = hr.sorted(list, function(k) return -agg.r[k][1] end)
    for i = 1, math.min(a.top, #list) do
      local r = agg.r[list[i]]
      print(("%s %4d× max %s   %s"):format(fmt(r[1]), r[2], fmt(r[3]), list[i]))
    end
  end
  if not a.no_ci then
    local n, jobs, steps, sorder = ci(since)
    print(("\n## CI: %d runs (total · runs · max)"):format(n))
    for _, k in ipairs(hr.sorted(jobs.order, function(k) return -jobs.r[k][1] end)) do
      local r = jobs.r[k]
      print(("%s %4d× max %s   %s"):format(fmt(r[1]), r[2], fmt(r[3]), k))
    end
    print("\n## CI: top steps (total)")
    local list = hr.sorted(sorder, function(k) return -steps[k] end)
    for i = 1, math.min(a.top, #list) do print(("%s   %s"):format(fmt(steps[list[i]]), list[i])) end
  end
end

main()
