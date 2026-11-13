import SwarmLean.Lib.Machine

/-! machine_spec.lua's asserts on machine.lua's pure parts (run.parse_probe's are board #101's), checked at build. -/


open SwarmLean SwarmLean.Machine

/-- procps's `ps` output. -/
def linux : String := "      1       0 12345 9-02:03:04 00:12:34 /sbin/init
    501       1  2048      01:23 00:00:00 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-1.sh && eval 'make'
    502     501 900000  1:02:03 01:00:05 claude -n sr-1
"

/-- BSD `ps` output of the same processes. -/
def darwin : String := "    1     0  12345 9-02:03:04   12:34.56 /sbin/init
  501     1   2048      01:23    0:00.03 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-1.sh && eval 'make'
  502   501 900000   01:02:03   60:05.99 claude -n sr-1
"

/-- A process of a parse by pid. -/
def at_ (ps : List Ps) (pid : Int) : Ps := (ps.find? (·.pid == pid)).getD default

-- both systems' ps parse to the same rows
#guard parsePs linux == parsePs darwin
#guard (at_ (parsePs linux) 1).age == 9 * 86400 + 2 * 3600 + 3 * 60 + 4
#guard let p := at_ (parsePs linux) 502; (p.cpu_s, p.age, p.rss_kb, p.comm, p.ppid) == (3605, 3723, 900000, "claude", 501)
#guard (at_ (parsePs linux) 501).comm == "zsh"
#guard hasSub (at_ (parsePs linux) 501).args "/shell-snapshots/"

/-- `vm_stat` output. -/
def vm : String := "Mach Virtual Memory Statistics: (page size of 16384 bytes)
Pages free:                               12345.
Pages active:                            200000.
Pages inactive:                          100000.
Pages speculative:                         5000.
Pages throttled:                              0.
Pages wired down:                         80000.
Pages purgeable:                           2655.
"

/-- The macOS reading of the spec. -/
def mac : Option (Int × Int × Psi) := darwinMem "34359738368" (some vm) "2" "{ 3.21 2.00 1.00 }" "10"

#guard match mac with
  | some (a, t, p) => a == 120000 * 16 && t == 32 * 2 ^ 20 && p.level == some "warn" && p.load == some 3.21 &&
    p.cores == some 10 && p.memory.isNone && p.cpu.isNone
  | none => false
-- warn is high, normal is not
#guard match mac with | some (a, t, p) => pressureHigh a t p && !pressureHigh a t { level := some "normal" } | none => false
#guard (darwinMem "1" (some vm) "4" "" "").map (·.2.2.level) == some (some "critical")
-- no hw.memsize: unreadable
#guard (darwinMem "" (some vm) "1" "" "").isNone
#guard lineOf mac == "machine: 1.8/32.0G mem available, pressure warn, load 3.21 on 10 cores"
#guard lineOf none == "machine: unknown (memory unreadable)"
#guard parseLsof "p10\nfcwd\nn/Users/j/wt\np11\nfcwd\nn/\n" == [(10, "/Users/j/wt"), (11, "/")]

-- beyond the spec: the cgroup scope, a job's command, an owner's command
#guard scopeOf "0::/user.slice/app.slice/swarm-agent-ll-1.scope\n" == some "/user.slice/app.slice/swarm-agent-ll-1.scope"
#guard scopeOf "0::/user.slice/x.scope\n" == none
#guard jobCmd "/bin/zsh -c source /h/snap.sh && eval 'make '\\''x'\\''' < /dev/null && pwd" == "make 'x'"
#guard procCmd (at_ (parsePs "1 0 1 00:01 00:00 /usr/bin/node /x/tsc --watch") 1) == "tsc --watch"


