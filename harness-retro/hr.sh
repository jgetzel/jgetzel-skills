#!/bin/sh
# Runs one harness-retro tool: each <tool>.sh here links to this file and runs `harness-retro <tool>`, the Lean binary
# swarm/lean/build.sh builds (swarm/lean/HarnessRetro). A binary older than its sources still runs, with one stderr line.
tool=$(basename "$0" .sh)
here=$(cd -P "$(dirname "$(readlink -f "$0")")" && pwd)
lean=$here/../swarm/lean
for ref in "$lean/.lake/build/bin/harness-retro" "$lean/.lake/nix"; do
  bin=$ref; [ "$ref" = "$lean/.lake/nix" ] && bin=$ref/bin/harness-retro
  [ -x "$bin" ] || continue
  [ "$tool" = probe-guard ] || [ -z "$(cd "$lean" && find HarnessRetro HarnessRetroMain.lean SwarmLean -newer "$ref" 2>/dev/null | head -n 1)" ] ||
    echo "$tool: harness-retro is older than its sources; rebuild it with swarm/lean/build.sh" >&2
  exec "$bin" "$tool" "$@"
done
echo "$tool: harness-retro is not built; build it with $here/../swarm/lean/build.sh" >&2
exit 127
