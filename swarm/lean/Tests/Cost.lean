import SwarmLean.Lib.Cost

/-! cost_spec.lua's asserts on cost.lua's pure functions (the tick's are in Tests/CostTick.lean once Lib/Machine's ps
reader lands). -/

open SwarmLean Cost

#guard key "cd /x/y && FOO=1 cargo test --release -p a 2>&1 | tail -5" == "cargo test --release"
#guard key "swarm run --on laptop -- make all" == "make all"
#guard key "nix build .#x > /tmp/o" == "nix build .#x"
#guard shellCmd "zsh -c source s.sh && eval 'cd /a && it'\\''s' \\< /dev/null && pwd -P >| /tmp/x" == some "cd /a && it's"
#guard summaryOf "cargo test --release" [(300, 600, 2 * 1048576), (360, 600, 4 * 1048576), (420, 600, 9 * 1048576)] ==
  some "`cargo test --release`, this repo, this machine: 3 runs, median 6 min, peak 4.0G (max 9.0G), 10 CPU-min."
#guard summaryOf "nope" [] == none
#guard (recordSql { ts := 0, machine := "h", repo := "r", agent := "a", cmd := "x", wall_s := 10, peak_kb := 1 }).isNone
#guard (recordSql { ts := 0, machine := "h", repo := "r", agent := "a", cmd := "x", wall_s := 60, peak_kb := 1 }).isSome
