#!/usr/bin/env bash
# The file format both ways: sqlite3 writes a database (updates, deletes, overflow pages, a freelist, an index), BIN
# reads it and changes it, then sqlite3 checks it (integrity_check) and reads it back; and BIN reopens its own file.
# usage: tests/compat.sh [BIN]
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
BIN=${1:-$here/../.lake/build/bin/lsqlite3}
tmp=$(mktemp -d "${TMPDIR:-/tmp}/lsqlcompat.XXXXXX") || exit 2
trap 'rm -rf "$tmp"' EXIT
db=$tmp/a.db
fail=0
sqlite3 "$db" <<'EOF'
create table t(a integer primary key, b text, c real, d blob);
create index tb on t(b);
create table u(x unique, y);
with recursive r(n) as (select 1 union all select n+1 from r where n < 3000)
insert into t select n, 'v' || (n * 7 % 1000), n / 3.0, case when n % 100 = 0 then zeroblob(6000) else x'0102' end from r;
insert into u select a, b from t where a % 10 = 0;
update t set b = b || '-u' where a % 7 = 0;
delete from t where a % 5 = 0;
create view v as select b, count(*) n from t group by b;
EOF
q="select count(*), sum(a), sum(length(b)), sum(c), sum(length(d)) from t; select count(*), min(x), max(x) from u; select * from v order by n desc, b limit 3; select a, b from t where b = 'v7-u' order by a;"
ref=$(sqlite3 "$db" "$q")
got=$("$BIN" "$db" "$q")
[ "$ref" = "$got" ] || { echo "FAIL reading a sqlite3 database"; diff <(echo "$ref") <(echo "$got") | head; fail=1; }
# BIN changes it
"$BIN" "$db" "insert into t values(100000, 'new', 1.5, zeroblob(9000)); update t set c = c * 2 where a < 500; delete from t where a between 1000 and 1500; insert into u values('z', 1); create index tc on t(c); create index tp on t(b) where a % 2 = 0; update t set b = b || 'x' where a between 2000 and 2010; drop view v;" || fail=1
chk=$(sqlite3 "$db" "pragma integrity_check")
[ "$chk" = "ok" ] || { echo "FAIL integrity_check after BIN's changes: $chk" | head -5; fail=1; }
q2="select count(*), sum(a), sum(c), sum(length(d)) from t; select count(*) from u; select a, c from t indexed by tc where c > 300 order by c limit 3; select name from sqlite_schema order by name;"
ref=$(sqlite3 "$db" "$q2")
got=$("$BIN" "$db" "$q2")
[ "$ref" = "$got" ] || { echo "FAIL reading back BIN's changes"; diff <(echo "$ref") <(echo "$got") | head; fail=1; }
# a database BIN creates, reopened by BIN and by sqlite3
db2=$tmp/b.db
"$BIN" "$db2" "create table k(a integer primary key, b); with recursive r(n) as (select 1 union all select n+1 from r where n < 2000) insert into k select n, printf('%0500d', n) from r; delete from k where a % 3 = 0;" || fail=1
ref=$(sqlite3 "$db2" "pragma integrity_check; select count(*), sum(length(b)) from k;")
got=$("$BIN" "$db2" "select count(*), sum(length(b)) from k;")
[ "$ref" = "ok
$got" ] || { echo "FAIL BIN's own database: sqlite3 says '$ref', BIN says '$got'"; fail=1; }
[ $fail = 0 ] && echo "ok compat"
exit $fail
