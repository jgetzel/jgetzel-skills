#!/bin/sh
# harness-retro (../../harness-retro's tools) on the fixture in Tests/harness-retro: probe-guard's selftest, and
# transcript, time-report, harness-lint and probe-json against outputs the Lua tools gave for the same input.
cd "$(dirname "$0")" || exit 1
bin=$(realpath "${1:-.lake/build/bin/harness-retro}") F=Tests/harness-retro
T=$(mktemp -d) || exit 1
trap 'rm -r "$T"' EXIT
fail() { echo "harness-retro: $1" >&2; exit 1; }
"$bin" probe-guard --selftest || fail "probe-guard selftest"
touch "$F/s1.jsonl"  # time-report reads only sessions modified after --since
"$bin" transcript "$F/s1.jsonl" --redact "ll-9=agent" | diff "$F/s1.md" - || fail transcript
[ "$("$bin" transcript "$F/s1.jsonl" --last)" = "PROBE DONE" ] || fail "transcript --last"
TZ=UTC "$bin" time-report --since 2026-11-12T09:00Z --no-ci --project-dir "$F" | diff "$F/s1-time.txt" - || fail time-report
mkdir "$T/home"
[ "$(HOME=$T/home "$bin" harness-lint --repo "")" = "$(printf '## Always-on bytes\n      0  total\nok')" ] || fail harness-lint
[ "$(echo '{"a":{"b":[1]},"c":3}' | "$bin" probe-json get 'd.a.x or d.c')" = 3 ] || fail "probe-json get"
echo "harness-retro: ok"
