#!/usr/bin/env luajit
-- Time per-agent checkout options for a repo, in a scratch dir.
--
-- usage: luajit sw-worktrees-probe.lua <repo> <scratch> [runs]
-- Reads <repo> only (a --shared bare clone is the base). Prints the median
-- seconds and disk of each option; ext4 has no reflink, so that row says so.
-- Port of sw-worktrees-probe.py: same options, same output.
local here = arg[0]:match("^(.*)/[^/]*$") or "."
local tree = (os.getenv("XDG_DATA_HOME") or ((os.getenv("HOME") or "") .. "/.local/share")) .. "/swarm/lua"
package.path = here .. "/../lua/?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. package.path  -- as the swarm launcher does
package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
local util, proc = require "swarm.util", require "swarm.proc"
local lfs = require "lfs"
local gettimeofday = require("posix.sys.time").gettimeofday

-- Python's os.path.abspath (no symlink resolution)
local function abspath(p)
  if p:sub(1, 1) ~= "/" then p = lfs.currentdir() .. "/" .. p end
  local parts = {}
  for x in p:gmatch("[^/]+") do
    if x == ".." then parts[#parts] = nil elseif x ~= "." then parts[#parts + 1] = x end
  end
  return "/" .. table.concat(parts, "/")
end

local function clock()
  local t = gettimeofday()
  return t.tv_sec + t.tv_usec / 1e6
end

local function median(t)
  local s = {}
  for i, v in ipairs(t) do s[i] = v end
  table.sort(s)
  local n = #s
  if n % 2 == 1 then return s[(n + 1) / 2] end
  return (s[n / 2] + s[n / 2 + 1]) / 2
end

-- Returns stdout, stderr, exit code. make(dst) returns the same triple.
local function sh(argv, cwd)
  return proc.exec(argv, { cwd = cwd })
end

local function rmtree(p)
  sh({ "rm", "-rf", p })
end

local function du(p)
  return util.split((sh({ "du", "-sk", p })))[1] .. "K"
end

local repo, scratch = abspath(arg[1]), abspath(arg[2])
local runs = tonumber(arg[3]) or 5
local bare = scratch .. "/bare.git"

local function timed(name, make)
  local ts, dir = {}, nil
  for i = 0, runs - 1 do
    local dst = ("%s/%s-%d"):format(scratch, name, i)
    rmtree(dst)
    local t = clock()
    local _, err, code = make(dst)
    ts[#ts + 1] = clock() - t
    if code ~= 0 then
      print(("%-22s failed: %s"):format(name, util.strip(err):sub(1, 120)))
      return
    end
    dir = dst
  end
  print(("%-22s %7.0f ms  %8s"):format(name, median(ts) * 1000, du(dir)))
end

local function sparse(dst)
  sh({ "git", "worktree", "add", "-q", "--no-checkout", "--detach", dst, "HEAD" }, bare)
  sh({ "git", "sparse-checkout", "set", "--cone", "server" }, dst)
  return sh({ "git", "checkout", "-q" }, dst)
end

lfs.mkdir(scratch)
rmtree(bare)
local _, _, code = sh({ "git", "clone", "-q", "--bare", "--shared", repo, bare })
assert(code == 0)
local src = scratch .. "/src"
rmtree(src)
sh({ "git", "worktree", "add", "-q", "--detach", src, "HEAD" }, bare)

timed("worktree add", function(d) return sh({ "git", "worktree", "add", "-q", "--detach", d, "HEAD" }, bare) end)
timed("worktree add sparse", sparse)
timed("clone --shared", function(d) return sh({ "git", "clone", "-q", "--shared", repo, d }) end)
timed("clone --reference", function(d) return sh({ "git", "clone", "-q", "--reference", repo, repo, d }) end)
timed("clone --no-local", function(d) return sh({ "git", "clone", "-q", "--no-local", repo, d }) end)
timed("cp -r worktree", function(d) return sh({ "cp", "-r", src, d }) end)
local _, rerr, rcode = sh({ "cp", "--reflink=always", src .. "/README.md", scratch .. "/reflink-test" })
print(("%-22s %s"):format("cp --reflink=always",
  rcode == 0 and "ok" or "unsupported: " .. util.strip(rerr):sub(-40)))
sh({ "git", "worktree", "prune" }, bare)
