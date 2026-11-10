-- machine.lua's seam: both systems' `ps`, macOS sysctl/vm_stat/lsof, and the remote probe, from canned output.
local machine, run = require "swarm.machine", require "swarm.run"

local function eq(got, want, msg)
  local cli = require "test.cli"
  assert(cli.repr(got) == cli.repr(want), (msg or "") .. "\n  got  " .. cli.repr(got) .. "\n  want " .. cli.repr(want))
end

-- procps and BSD ps print the same columns, with different time formats
local linux = [[
      1       0 12345 9-02:03:04 00:12:34 /sbin/init
    501       1  2048      01:23 00:00:00 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-1.sh && eval 'make'
    502     501 900000  1:02:03 01:00:05 claude -n sr-1
]]
local darwin = [[
    1     0  12345 9-02:03:04   12:34.56 /sbin/init
  501     1   2048      01:23    0:00.03 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-1.sh && eval 'make'
  502   501 900000   01:02:03   60:05.99 claude -n sr-1
]]
local l, d = machine.parse_ps(linux), machine.parse_ps(darwin)
eq(l, d, "both systems' ps parse to the same rows")
eq(l[1].age, 9 * 86400 + 2 * 3600 + 3 * 60 + 4)
eq({ l[502].cpu_s, l[502].age, l[502].rss_kb, l[502].comm, l[502].ppid }, { 3605, 3723, 900000, "claude", 501 })
eq(l[501].comm, "zsh")
assert(l[501].args:find("/shell-snapshots/", 1, true))

local vm = [[
Mach Virtual Memory Statistics: (page size of 16384 bytes)
Pages free:                               12345.
Pages active:                            200000.
Pages inactive:                          100000.
Pages speculative:                         5000.
Pages throttled:                              0.
Pages wired down:                         80000.
Pages purgeable:                           2655.
]]
local avail, total, psi = machine.darwin_mem("34359738368", vm, "2", "{ 3.21 2.00 1.00 }", "10")
eq({ avail, total, psi }, { 120000 * 16, 32 * 2 ^ 20, { level = "warn", load = 3.21, cores = 10 } })
assert(machine.pressure_high(avail, total, psi), "warn is high")
assert(not machine.pressure_high(avail, total, { level = "normal" }))
eq(select(3, machine.darwin_mem("1", vm, "4")).level, "critical")
eq(machine.darwin_mem("", vm, "1"), nil, "no hw.memsize: unreadable")
eq(machine.machine_line(avail, total, psi), "machine: 1.8/32.0G mem available, pressure warn, load 3.21 on 10 cores")
eq(machine.machine_line(nil), "machine: unknown (memory unreadable)")

eq(machine.parse_lsof("p10\nfcwd\nn/Users/j/wt\np11\nfcwd\nn/\n"), { [10] = "/Users/j/wt", [11] = "/" })

-- the remote probe's head from each system
eq(run.parse_probe("@darwin\n10\n34359738368\n1\n{ 3.21 2.00 1.00 }\n" .. vm),
  { cores = 10, load = 3.21, avail_kb = 120000 * 16, total_kb = 32 * 2 ^ 20, level = "normal" })
eq(run.parse_probe("24\n3.50 2.0 1.0 1/900 77\nMemTotal: 1000 kB\nMemAvailable: 400 kB\nsome avg10=2.50 avg60=0\n"),
  { cores = 24, load = 3.5, avail_kb = 400, total_kb = 1000, psi = 2.5 })
eq(run.parse_probe("@darwin\n\n\n\n\n"), nil, "unreadable mac")
