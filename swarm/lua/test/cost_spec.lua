-- cost.lua: the key, the tick's rows (shell seen on ticks then gone), the threshold, user sessions, pruning, summary.
local cost, db, machine = require "swarm.cost", require "swarm.db", require "swarm.machine"
local stdlib, unistd, proc = require "posix.stdlib", require "posix.unistd", require "posix.sys.stat"
local function eq(got, want, msg)
  local cli = require "test.cli"
  assert(cli.repr(got) == cli.repr(want), (msg or "") .. "\n  got  " .. cli.repr(got) .. "\n  want " .. cli.repr(want))
end

eq(cost.key("cd /x/y && FOO=1 cargo test --release -p a 2>&1 | tail -5"), "cargo test --release")
eq(cost.key("swarm run --on laptop -- make all"), "make all")
eq(cost.key("nix build .#x > /tmp/o"), "nix build .#x")
eq(cost.shell_cmd("zsh -c source s.sh && eval 'cd /a && it'\\''s' \\< /dev/null && pwd -P >| /tmp/x"), "cd /a && it's")

local src = require("swarm.util").slurp(package.searchpath("swarm.cost", package.path))  -- before the chdir
local dir = stdlib.realpath(stdlib.mkdtemp("/tmp/swarm-cost-XXXXXX"))  -- realpath: git reports /private/tmp
stdlib.setenv("SWARM_DB", dir .. "/swarm.db")
stdlib.setenv("XDG_STATE_HOME", dir .. "/state")
assert(require("swarm.proc").run({ "git", "init", "-q", "-b", "main", dir .. "/repo" }))
local wt = dir .. "/repo-wt"
assert(require("swarm.proc").run({ "git", "-C", dir .. "/repo", "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "--allow-empty", "-m", "i" }))
assert(require("swarm.proc").run({ "git", "-C", dir .. "/repo", "worktree", "add", "-q", wt, "-b", "w" }) or true)
unistd.chdir(dir .. "/repo")
local c = db.connect()
c:exec("insert into agent(name,cwd,status,last_active,started,claude_pid) values('sr-1',?, 'working',1,1,100)", dir .. "/repo")
local h = cost.open()
local function rows() return h:all("select * from cmd order by id") end

local function ps(age, rss, cpu, extra)  -- claude 100 (agent), shell 200 running `make`, its child 201
  local p = machine.parse_ps(([[
  100     1 5000 05:00:00 00:10:00 claude -n sr-1
  200   100 1000 %s 00:00:01 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-1.sh && eval 'cd /w && make test 2>&1 | tail' \< /dev/null && pwd -P >| /tmp/a
  201   200 %d %s %s cc -O2
]]):format(age, rss, age, cpu) .. (extra or ""))
  return p
end
cost.tick(c, h, ps("00:30", 100000, "00:00:20"), 1000)
cost.tick(c, h, ps("01:00", 300000, "00:00:50"), 1030)
cost.tick(c, h, ps("01:30", 200000, "00:01:20"), 1060)
eq(#rows(), 0, "still open")
cost.tick(c, h, machine.parse_ps("  100 1 5000 05:00:00 00:10:00 claude -n sr-1\n"), 1090)
local r = rows()
eq(#r, 1)
eq({ r[1].agent, r[1].source, r[1].cmd, r[1].key, r[1].wall_s, r[1].cpu_s, r[1].peak_kb, r[1].exact, r[1].repo },
  { "sr-1", "swarm", "cd /w && make test 2>&1 | tail", "make test", 90, 81, 301000, 0, "repo" })

-- a short, small command writes none
cost.tick(c, h, ps("00:05", 1000, "00:00:01"), 2000)
cost.tick(c, h, machine.parse_ps(""), 2030)
eq(#rows(), 1, "short and small: no row")

-- two concurrent shells of one agent write two rows
local two = ps("02:00", 10, "00:00:00", [[
  300   100 1000 02:00 00:00:01 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-2.sh && eval 'sleep 200' \< /dev/null
]])
cost.tick(c, h, two, 3000)
cost.tick(c, h, machine.parse_ps(""), 3030)
eq(#rows(), 3)

-- a user session in a worktree writes user:<name>; one elsewhere writes nothing
local mc = machine.cwds
machine.cwds = function() return { [400] = wt, [500] = "/elsewhere" } end
local function user(pid, shell, name)
  return machine.parse_ps(([[
  %d 1 5000 05:00:00 00:10:00 claude -n %s
  %d %d 1000 03:00 00:00:01 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-9.sh && eval 'cargo build' \< /dev/null
]]):format(pid, name, shell, pid))
end
cost.tick(c, h, user(400, 401, "me"), 4000)
cost.tick(c, h, user(500, 501, "other"), 4000)
cost.tick(c, h, machine.parse_ps(""), 4030)
machine.cwds = mc
r = rows()
eq(#r, 4)
eq(r[4].agent, "user:me")

-- pruning keeps 20 per (machine, repo, key)
for i = 1, 25 do cost.record(h, { repo = "repo", agent = "a", cmd = "make test", wall_s = 61 + i, peak_kb = 1 }) end
eq(h:one("select count(*) n from cmd where key='make test'").n, 20)
eq(h:one("select min(wall_s) m from cmd where key='make test'").m, 67)

-- summary: median and max
h:exec("delete from cmd")
for _, p in ipairs({ { 300, 2 }, { 360, 4 }, { 420, 9 } }) do
  cost.record(h, { repo = "repo", agent = "a", cmd = "cargo test --release", wall_s = p[1], cpu_s = 600, peak_kb = p[2] * 1048576 })
end
eq(cost.summary(h, "repo", "cargo test --release"),
  "`cargo test --release`, this repo, this machine: 3 runs, median 6 min, peak 4.0G (max 9.0G), 10 CPU-min.")
eq(cost.summary(h, "repo", "nope"), nil)

-- a cgroup per agent: a lone open command whose agent's memory.peak rose is exact; with two open it stays sampled
local sh = require("swarm.util")
local pr, cg0 = machine.PROC, machine.CGROUP
machine.PROC, machine.CGROUP = dir .. "/proc", dir .. "/cg"
local scope = "/user.slice/swarm-agent-sr-1-7.scope"
os.execute(("mkdir -p %s/proc/100 %s/cg%s"):format(dir, dir, scope))
local function cgset(kb)
  local f = io.open(dir .. "/proc/100/cgroup", "w"); f:write("0::" .. scope .. "\n"); f:close()
  f = io.open(dir .. "/cg" .. scope .. "/memory.peak", "w"); f:write(tostring(kb * 1024)); f:close()
  f = io.open(dir .. "/cg" .. scope .. "/cpu.stat", "w"); f:write("usage_usec 5000000\n"); f:close()
end
eq(machine.cgroup(100), nil)
cgset(1000)
eq({ machine.cgroup(100).peak_kb, machine.cgroup(100).cpu_s }, { 1000, 5 })
h:exec("delete from cmd")
cost.cg_peak = {}
cost.tick(c, h, ps("00:30", 100, "00:00:20"), 5000)  -- first sight of the cgroup: no rise yet
cgset(9000000)
cost.tick(c, h, ps("01:00", 100, "00:00:50"), 5030)
cost.tick(c, h, machine.parse_ps(""), 5060)
r = rows()
eq({ #r, r[1].exact, r[1].peak_kb }, { 1, 1, 9000000 })
h:exec("delete from cmd")
cost.tick(c, h, ps("00:30", 100, "00:00:20"), 6000)
cgset(9500000)
cost.tick(c, h, two, 6030)
cost.tick(c, h, machine.parse_ps(""), 6060)
r = rows()
eq({ #r, r[1].exact, r[2].exact }, { 2, 0, 0 })
machine.PROC, machine.CGROUP = pr, cg0

-- nothing here signals a process or writes oom_score_adj outside an agent's tree (the tick only reads)
assert(not src:find("oom_score_adj") and not src:find("SIGTERM") and not src:find("signal"), "cost.lua only measures")
