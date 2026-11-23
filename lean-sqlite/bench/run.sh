#!/usr/bin/env bash
# Benchmarks lean-sqlite against C sqlite3: each workload of bench/sql (bench/gen.sh) through each engine. An engine's
# output must equal sqlite3's byte for byte, or the run fails. Records user-space instructions (perf stat) and the
# minimum wall time of RUNS runs. Run it inside high-perf-lean's devshell (for perf): see README.md.
# usage: bench/run.sh [RUNS] [workload...]
set -uo pipefail
cd "$(dirname "$0")" || exit 1
RUNS=${1:-5}; shift || true
works=${*:-"insert insert-indexed scan lookup sort update join file-insert"}
[ -f sql/insert.sql ] || ./gen.sh >/dev/null
tmp=$(mktemp -d "${TMPDIR:-/tmp}/lsqlbench.XXXXXX") || exit 2
trap 'rm -rf "$tmp"' EXIT
declare -A bin=( [sqlite3]=$(command -v sqlite3) [stock]=../.lake/build/bin/lsqlite3 [stock-clang]=../clang/.lake/build/bin/lsqlite3
                 [hpl]=../hpl/.lake/build/bin/lsqlite3 [hpl-nounbox]=../hpl-nounbox/.lake/build/bin/lsqlite3 )
engines=${ENGINES:-"sqlite3 stock stock-clang hpl hpl-nounbox"}
for e in $engines; do [ -x "${bin[$e]}" ] || { echo "missing ${bin[$e]} (build it first)" >&2; exit 2; }; done
now() { date +%s%N; }
# runs engine $1 on workload $2 once; stdout to $3; the database is :memory: or, for file-*, a fresh file
run1() {
  local db=":memory:"
  case $2 in file-*) db=$tmp/$1.db; rm -f "$db";; esac
  "${bin[$1]}" "$db" < sql/$2.sql > "$3" 2>"$3.err"
}
out=results.tsv
{
  echo "# lean-sqlite benchmark $(date -Iseconds)"
  echo "# host $(uname -nrm), $(nproc) cpus, load at start: $(cut -d' ' -f1-3 /proc/loadavg)"
  echo "# sqlite3 $(sqlite3 --version | cut -d' ' -f1-2); hpl $(git -C "$HOME/workspace/high-perf-lean" rev-parse --short HEAD 2>/dev/null)"
  printf "workload\tengine\tms_min\tinstructions\n"
} > $out
fail=0
for w in $works; do
  run1 sqlite3 $w $tmp/ref.out
  for e in $engines; do
    run1 $e $w $tmp/$e.out
    if ! cmp -s $tmp/ref.out $tmp/$e.out; then echo "FAIL $w: $e's output differs from sqlite3's" >&2; fail=1; fi
    case $w in file-*) if [ $e != sqlite3 ]; then
      chk=$(sqlite3 $tmp/$e.db "pragma integrity_check")
      [ "$chk" = ok ] || { echo "FAIL $w: sqlite3 integrity_check of $e's file: $chk" >&2; fail=1; }
    fi;; esac
    best=
    for _ in $(seq $RUNS); do
      s=$(now); run1 $e $w $tmp/run.out; t=$(( ($(now) - s) / 1000000 ))
      if [ -z "$best" ] || [ $t -lt $best ]; then best=$t; fi
    done
    db=":memory:"; case $w in file-*) db=$tmp/perf.db; rm -f $db;; esac
    ins=$(perf stat -x, -e instructions:u "${bin[$e]}" "$db" < sql/$w.sql 2>&1 >/dev/null | grep instructions:u | cut -d, -f1)
    printf "%s\t%s\t%s\t%s\n" $w $e $best "${ins:-?}" >> $out
    printf "%-15s %-12s %8s ms %16s instructions\n" $w $e $best "${ins:-?}"
  done
done
exit $fail
