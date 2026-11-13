import SwarmLean.Lib.Cost

/-! cost_spec.lua's asserts on cost.tick (a shell seen on ticks then gone, the threshold, two shells, user sessions,
cgroup exact peaks), on `tickStep`. -/

open SwarmLean Cost

/-- claude 100 (agent sr-1), shell 200 running `make`, its child 201 (cost_spec's ps). -/
def ps (age : String) (rss : Int) (cpu : String) (extra : String := "") : List Machine.Ps :=
  Machine.parsePs (s!"  100     1 5000 05:00:00 00:10:00 claude -n sr-1
  200   100 1000 {age} 00:00:01 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-1.sh && eval 'cd /w && make test 2>&1 | tail' \\< /dev/null && pwd -P >| /tmp/a
  201   200 {rss} {age} {cpu} cc -O2
" ++ extra)

/-- Only the agent's claude process. -/
def bare : List Machine.Ps := Machine.parsePs "  100 1 5000 05:00:00 00:10:00 claude -n sr-1\n"

/-- Ticks at the given times over the given ps readings (sr-1's claude is pid 100; `cgs` per tick), from `mem`; the
rows, as (agent, cmd, key, wall, cpu, peak, exact), and the memory after. -/
def run (ticks : List (List Machine.Ps × Int × List (String × Int))) (mem : TickMem := {})
    (cwds : List (Int × String) := []) (wts : Option (List String) := none) :
    List (String × String × String × Int × Int × Int × Int) × TickMem :=
  ticks.foldl (fun (out, mem) (p, t, cgs) =>
    let (mem, rs) := tickStep mem { owners := [(100, "sr-1")], cgs, procs := p, cwds, wts } t
    (out ++ rs.map fun r => (r.agent, r.cmd, key r.cmd, r.wall_s, r.cpu_s, r.peak_kb, r.exact), mem)) ([], mem)

#guard (run [(ps "00:30" 100000 "00:00:20", 1000, []), (ps "01:00" 300000 "00:00:50", 1030, []),
  (ps "01:30" 200000 "00:01:20", 1060, [])]).1 == []
#guard (run [(ps "00:30" 100000 "00:00:20", 1000, []), (ps "01:00" 300000 "00:00:50", 1030, []),
  (ps "01:30" 200000 "00:01:20", 1060, []), (bare, 1090, [])]).1 ==
  [("sr-1", "cd /w && make test 2>&1 | tail", "make test", 90, 81, 301000, 0)]

-- a short, small command gives a row the history drops (cost.record's threshold)
#guard (run [(ps "00:05" 1000 "00:00:01", 2000, []), ([], 2030, [])]).1.all fun (_, _, _, w, _, pk, _) =>
  (recordSql { ts := 0, machine := "", repo := "", agent := "", cmd := "", wall_s := w, peak_kb := pk }).isNone

/-- Two concurrent shells of sr-1. -/
def two : List Machine.Ps := ps "02:00" 10 "00:00:00"
  "  300   100 1000 02:00 00:00:01 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-2.sh && eval 'sleep 200' \\< /dev/null\n"

#guard (run [(two, 3000, []), ([], 3030, [])]).1.length == 2

/-- A user's own session: claude `pid` named `name`, its shell `shell` running cargo build. -/
def user (pid shell : Int) (name : String) : List Machine.Ps :=
  Machine.parsePs s!"  {pid} 1 5000 05:00:00 00:10:00 claude -n {name}
  {shell} {pid} 1000 03:00 00:00:01 /bin/zsh -c source /h/.claude/shell-snapshots/snapshot-zsh-9.sh && eval 'cargo build' \\< /dev/null
"

-- one in a worktree of the repo writes user:<name>; one elsewhere writes nothing
#guard (run [(user 400 401 "me", 4000, []), (user 500 501 "other", 4000, []), ([], 4030, [])] {}
  [(400, "/r/repo-wt"), (500, "/elsewhere")] (some ["/r/repo", "/r/repo-wt"])).1.map (·.1) == ["user:me"]
#guard (run [(user 400 401 "me", 4000, []), ([], 4030, [])] {} [(400, "/r/repo-wt")] none).1 == []
#guard needsUser [(100, "sr-1")] (user 400 401 "me") && !needsUser [(100, "sr-1")] two
#guard userWho "claude --name=x:" == "user:x" && userWho "claude" == "user" && userWho "claude -n  ab c" == "user:ab"

-- a lone open command whose agent's cgroup peak rose is exact; with two open it stays sampled
#guard (run [(ps "00:30" 100 "00:00:20", 5000, [("sr-1", 1000)]), (ps "01:00" 100 "00:00:50", 5030, [("sr-1", 9000000)]),
  ([], 5060, [])]).1.map (fun (_, _, _, _, _, pk, x) => (pk, x)) == [(9000000, 1)]
#guard (run [(ps "00:30" 100 "00:00:20", 6000, [("sr-1", 1000)]), (two, 6030, [("sr-1", 9500000)]),
  ([], 6060, [])]).1.map (·.2.2.2.2.2.2) == [0, 0]

-- a reused pid (younger than the open command) starts a new command; the old one is not recorded
#guard (run [(ps "05:00" 100 "00:00:20", 7000, []), (ps "00:10" 100 "00:00:01", 7030, []), (bare, 7060, [])]).1.map
  (·.2.2.2.1) == [10]
