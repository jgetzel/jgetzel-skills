#!/usr/bin/env bash
# Differential test: run each tests/sql/*.sql through sqlite3 and our binary, diff stdout.
# usage: tests/diff.sh [--file] [BIN] [pattern]
#   default: both run against :memory:
#   --file : both run against a fresh temp file db; additionally runs
#            'pragma integrity_check' with sqlite3 on our file and compares .dump of both files.
# stdout is compared (and stderr whole, for a script named *-stderr.sql); for stderr only the count of lines starting with
# "Error", "Parse error" or "Runtime error" is compared.
here=$(cd "$(dirname "$0")" && pwd)
mode=mem
if [ "$1" = "--file" ]; then mode=file; shift; fi
BIN=${1:-$here/../.lake/build/bin/lsqlite3}
pat=${2:-}
tmp=$(mktemp -d "${TMPDIR:-/tmp}/lsqldiff.XXXXXX") || exit 2
trap 'rm -rf "$tmp"' EXIT
pass=0; fail=0
errcount() { grep -cE '^(Error|Parse error|Runtime error)' "$1"; }
for f in "$here"/sql/*.sql; do
  name=$(basename "$f" .sql)
  case "$name" in *"$pat"*) ;; *) continue ;; esac
  bad=""
  if [ $mode = mem ]; then
    ra=":memory:"; rb=":memory:"
  else
    rm -f "$tmp/ref.db" "$tmp/our.db"
    ra="$tmp/ref.db"; rb="$tmp/our.db"
  fi
  sqlite3 "$ra" < "$f" > "$tmp/ref.out" 2> "$tmp/ref.err"
  timeout 120 "$BIN" "$rb" < "$f" > "$tmp/our.out" 2> "$tmp/our.err"
  rc=$?
  if ! cmp -s "$tmp/ref.out" "$tmp/our.out"; then
    bad="$bad$(diff -u "$tmp/ref.out" "$tmp/our.out" | head -20)
"
  fi
  # a script named *-stderr: the whole of stderr is compared
  case "$name" in *-stderr) if ! cmp -s "$tmp/ref.err" "$tmp/our.err"; then
    bad="$bad$(diff -u "$tmp/ref.err" "$tmp/our.err" | head -20)
"
  fi;; esac
  e1=$(errcount "$tmp/ref.err"); e2=$(errcount "$tmp/our.err")
  if [ "$e1" != "$e2" ]; then
    bad="$bad--- error line count: sqlite3=$e1 ours=$e2 (exit $rc)
$(diff -u "$tmp/ref.err" "$tmp/our.err" | head -10)
"
  fi
  if [ $mode = file ]; then
    ic=$(sqlite3 "$tmp/our.db" 'pragma integrity_check' 2>&1)
    if [ "$ic" != "ok" ]; then
      bad="$bad--- integrity_check on our file:
$(printf '%s\n' "$ic" | head -10)
"
    fi
    sqlite3 "$tmp/ref.db" .dump > "$tmp/ref.dump" 2>&1
    sqlite3 "$tmp/our.db" .dump > "$tmp/our.dump" 2>&1
    if ! cmp -s "$tmp/ref.dump" "$tmp/our.dump"; then
      bad="$bad--- .dump differs:
$(diff -u "$tmp/ref.dump" "$tmp/our.dump" | head -20)
"
    fi
  fi
  if [ -z "$bad" ]; then
    echo "ok $name"; pass=$((pass+1))
  else
    echo "FAIL $name"; printf '%s' "$bad" | head -20 | sed 's/^/    /'; fail=$((fail+1))
  fi
done
echo "passed $pass, failed $fail"
[ $fail -eq 0 ]
