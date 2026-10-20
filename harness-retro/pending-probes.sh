#!/bin/sh
# SessionStart hook: one line when a harness-retro probe verdict is waiting in a ledger; silent otherwise.
root=$(git rev-parse --show-toplevel 2>/dev/null) || root=/nonexistent
n=$(cat "$root/.claude/harness-ledger.md" "$HOME/.claude/harness-ledger.md" 2>/dev/null | grep -c 'probe: [^·]* pending ')
[ "${n:-0}" -gt 0 ] && echo "harness-retro: $n probe verdict(s) pending. Mention to the user once that /harness-retro resume reviews them."
exit 0
