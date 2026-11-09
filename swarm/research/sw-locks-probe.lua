#!/usr/bin/env luajit
-- Measure what the proposed watchd conflict tick would report for a live repo, without writing to it.
-- usage: luajit sw-locks-probe.lua REPO SCRATCH   (SCRATCH gets a --shared bare clone; REPO's worktrees are only read)
-- Port of sw-locks-probe.py: same checks, same output. It runs swarm.conflict.real_hunk, the classifier the watchd ships.
local here = arg[0]:match("^(.*)/[^/]*$") or "."
local tree = (os.getenv("XDG_DATA_HOME") or ((os.getenv("HOME") or "") .. "/.local/share")) .. "/swarm/lua"
package.path = here .. "/../lua/?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. package.path  -- as the swarm launcher does
package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
local util, proc, conflict, re = require "swarm.util", require "swarm.proc", require "swarm.conflict", require "swarm.re"
local lfs = require "lfs"
local gettimeofday = require("posix.sys.time").gettimeofday

-- conflict.lua's HUNK, which is local there: the three sides of each diff3 hunk
local HUNK = [[^<<<<<<< .*?\n(.*?)^\|\|\|\|\|\|\| .*?\n(.*?)^=======\n(.*?)^>>>>>>> ]]

local function clock()
  local t = gettimeofday()
  return t.tv_sec + t.tv_usec / 1e6
end

-- Python's os.path.abspath (no symlink resolution)
local function abspath(p)
  if p:sub(1, 1) ~= "/" then p = lfs.currentdir() .. "/" .. p end
  local parts = {}
  for x in p:gmatch("[^/]+") do
    if x == ".." then parts[#parts] = nil elseif x ~= "." then parts[#parts + 1] = x end
  end
  return "/" .. table.concat(parts, "/")
end

-- os.path.relpath(p, base) for absolute paths
local function relpath(p, base)
  local a, b, r = {}, {}, {}
  for x in p:gmatch("[^/]+") do a[#a + 1] = x end
  for x in base:gmatch("[^/]+") do b[#b + 1] = x end
  local i = 1
  while a[i] and a[i] == b[i] do i = i + 1 end
  for _ = i, #b do r[#r + 1] = ".." end
  for j = i, #a do r[#r + 1] = a[j] end
  return #r == 0 and "." or table.concat(r, "/")
end

-- Python's repr of a list of strings, for the print of each clashing pair
local function pyrepr(list)
  local q = {}
  for _, s in ipairs(list) do
    if s:find("'") and not s:find('"') then
      q[#q + 1] = '"' .. s .. '"'  -- shortcut: repr escapes only quotes and backslashes; control characters print raw
    else
      q[#q + 1] = "'" .. s:gsub("\\", "\\\\"):gsub("'", "\\'") .. "'"
    end
  end
  return "[" .. table.concat(q, ", ") .. "]"
end
assert(pyrepr({ "a.hs", "b c" }) == "['a.hs', 'b c']")
assert(pyrepr({ "it's" }) == '["it\'s"]')
assert(pyrepr({ "x\\y" }) == "['x\\\\y']")

-- stdout of a command, raw
local function out(argv, o)
  return (proc.exec(argv, o))
end

local function G(gdir, ...)  -- git on the probe's own clone, with diff3 conflicts
  return { "git", "-c", "merge.conflictStyle=diff3", "--git-dir", gdir, ... }
end

-- Commit wt's working state (tracked + untracked, not ignored) into gd; return the commit.
local function snapshot(gdir, wt, env)
  local index = util.strip(out({ "git", "-C", wt, "rev-parse", "--path-format=absolute", "--git-path", "index" }))
  local tmp = os.tmpname()  -- a copy of the index, so add -A leaves the real one alone
  local f = assert(io.open(tmp, "wb"))
  f:write(util.slurp(index))
  f:close()
  local e = { GIT_DIR = env.GIT_DIR, GIT_OPTIONAL_LOCKS = env.GIT_OPTIONAL_LOCKS, GIT_WORK_TREE = wt, GIT_INDEX_FILE = tmp }
  local head = util.strip(out({ "git", "-C", wt, "rev-parse", "HEAD" }))
  proc.exec(G(gdir, "add", "-A"), { env = e })
  local tr = util.strip(out(G(gdir, "write-tree"), { env = e }))
  os.remove(tmp)
  return util.strip(out(G(gdir, "commit-tree", tr, "-p", head, "-m", "snap"), { env = env }))
end

local function main(repo, scratch)
  local gdir = scratch .. "/probe.git"
  if lfs.attributes(gdir, "mode") ~= "directory" then
    proc.exec({ "git", "clone", "-q", "--shared", "--bare", repo, gdir })
  end
  local common = util.strip(out({ "git", "-C", repo, "rev-parse", "--path-format=absolute", "--git-common-dir" }))
  lfs.mkdir(gdir)
  lfs.mkdir(gdir .. "/info")
  local exclude = util.slurp(common .. "/info/exclude")
  if exclude then  -- the clone must ignore what the repo ignores, or add -A hashes build output
    local f = assert(io.open(gdir .. "/info/exclude", "wb"))
    f:write(exclude)
    f:close()
  end
  proc.exec({ "git", "--git-dir", gdir, "fetch", "-q", repo, "+refs/heads/*:refs/heads/*" })
  local env = { GIT_DIR = gdir, GIT_OPTIONAL_LOCKS = "0" }
  local main_ = util.strip(out(G(gdir, "rev-parse", "main")))
  local wts = {}
  for _, l in ipairs(util.splitlines(out({ "git", "-C", repo, "worktree", "list", "--porcelain" }))) do
    if util.startswith(l, "worktree ") then wts[#wts + 1] = util.split(l)[2] end
  end

  local t0 = clock()
  local snap, files, names = {}, {}, {}
  for _, w in ipairs(wts) do
    local n = relpath(w, repo)
    snap[n] = snapshot(gdir, w, env)
    names[#names + 1] = n
    local mb = util.strip(out(G(gdir, "merge-base", main_, snap[n])))
    files[n] = {}
    for _, f in ipairs(util.split(out(G(gdir, "diff", "--name-only", mb, snap[n])))) do files[n][f] = true end
  end
  table.sort(names)
  local t1 = clock()

  local pairs_, shared = {}, 0
  for i = 1, #names do
    for j = i + 1, #names do
      local a, b, n = names[i], names[j], 0
      for f in pairs(files[a]) do if files[b][f] then n = n + 1 end end
      if n > 0 then
        pairs_[#pairs_ + 1] = { a, b }
        shared = shared + n
      end
    end
  end

  local line_files, line_pairs, hunks = 0, 0, 0
  local real, real_keys = {}, {}  -- real[a .. "\0" .. b] = set of files
  for _, p in ipairs(pairs_) do
    local a, b = p[1], p[2]
    local o, _, code = proc.exec(G(gdir, "merge-tree", "--write-tree", "--name-only", "--no-messages", snap[a], snap[b]))
    if code == 1 then
      line_pairs = line_pairs + 1
      local lines = util.splitlines(o)
      local tr = table.remove(lines, 1)
      local seen = {}
      for _, f in ipairs(lines) do
        if not seen[f] then
          seen[f] = true
          line_files = line_files + 1
          local key = a .. "\0" .. b
          for m in re.finditer(HUNK, out(G(gdir, "show", tr .. ":" .. f)), re.S + re.M) do
            hunks = hunks + 1
            if conflict.real_hunk(m[2], m[1], m[3]) then
              if not real[key] then
                real[key] = { a = a, b = b, files = {} }
                real_keys[#real_keys + 1] = key
              end
              real[key].files[f] = true
            end
          end
        end
      end
    end
  end
  local t2 = clock()

  local real_files = 0
  for _, k in ipairs(real_keys) do
    for _ in pairs(real[k].files) do real_files = real_files + 1 end
  end
  table.sort(real_keys, function(x, y)
    if real[x].a ~= real[y].a then return real[x].a < real[y].a end
    return real[x].b < real[y].b
  end)
  print(("worktrees %d: snapshots %.2fs"):format(#names, t1 - t0))
  print(("file overlap: %d pairs, %d (pair, file)"):format(#pairs_, shared))
  print(("line conflicts (git): %d pairs, %d (pair, file), %d hunks"):format(line_pairs, line_files, hunks))
  print(("token conflicts: %d pairs, %d (pair, file)"):format(#real_keys, real_files))
  print(("merges + classify %.2fs; tick %.2fs"):format(t2 - t1, t2 - t0))
  for _, k in ipairs(real_keys) do
    local fs = {}
    for f in pairs(real[k].files) do fs[#fs + 1] = f end
    table.sort(fs)
    print("   " .. real[k].a .. " " .. real[k].b .. " " .. pyrepr(fs))
  end
end

main(abspath(arg[1]), abspath(arg[2]))
