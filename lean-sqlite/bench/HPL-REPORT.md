# HPL performance report from lean-sqlite

From the lean-sqlite project: a sqlite3 clone in pure Lean 4.35, every function total. The source is
/home/jgetzel/workspace/jgetzel-skills/lean-sqlite, and it is not committed yet. The project builds it with stock Lean and
with hpl at **f78b82312f**, which is clean. Benchmark date: 2026-11-23. The machine is a 24-CPU laptop under a load of 2
to 3 from other work, so read instruction counts (`perf stat -e instructions:u`) before wall times.

Summary: hpl makes this program slower than stock Lean on all 8 workloads. The gap grew from 1.37× to 1.76×
instructions as the code grew. Per-statement cost also grows with database size under hpl, but not under stock.
`hpl refused` reports 0 functions.

## Builds

The two hpl builds share one source tree (`srcDir ".."`):

| build | directory | hpl arguments |
|---|---|---|
| stock | `lean-sqlite/.lake` | `leanc -O3`, gcc |
| stock-clang (control) | `lean-sqlite/clang/` | stock Lean C, compiled with `tools/cc.sh` clang, standard runtime |
| hpl | `lean-sqlite/hpl/` | `--all`, `require hpl`, the `hplO` facet, the ThinLTO runtime |
| hpl-nounbox | `lean-sqlite/hpl-nounbox/` | `--all --no-unbox`, plus `--disable fuse` in LSql.Compile, LSql.Exec, LSql.Check, LSql.Shell and Main (issue 3) |

All builds produce byte-identical output to sqlite3 on 61 differential scripts and on every benchmark workload, so these
are not miscompiles. A from-scratch build of all three in parallel took about 77 minutes, mostly the hpl `--all` build.
`LSql/Check.lean` alone took more than 2 minutes in hpl.

## 1. hpl `--all` is 1.76× the instructions of stock (geometric mean over 8 workloads)

User-space instructions for the final build (`bench/results.tsv`):

| workload | stock Lean | hpl `--all` | hpl/stock | hpl `--all --no-unbox` | nounbox/stock |
|---|---:|---:|---:|---:|---:|
| insert | 10.23 G | 19.66 G | 1.92× | 14.02 G | 1.37× |
| insert-indexed | 15.80 G | 24.87 G | 1.57× | 25.78 G | 1.63× |
| scan | 63.87 G | 130.94 G | 2.05× | 52.78 G | 0.83× |
| lookup | 19.71 G | 29.06 G | 1.47× | 34.77 G | 1.76× |
| sort | 14.13 G | 25.85 G | 1.83× | 16.50 G | 1.17× |
| update | 23.66 G | 40.80 G | 1.72× | 53.48 G | 2.26× |
| join | 18.69 G | 31.52 G | 1.69× | 34.12 G | 1.83× |
| file-insert | 10.46 G | 19.89 G | 1.90× | 14.17 G | 1.36× |

Geometric mean over the eight workloads, relative to stock Lean (gcc): C sqlite3: time 0.12, instr 0.11; stock (clang): time 0.99, instr 0.96; hpl: time 1.95, instr 1.76; hpl --no-unbox: time 1.41, instr 1.47.

C sqlite3 for scale: 0.11× stock in instructions.

## 2. The hpl penalty grew with the code

The same comparison on an earlier, smaller version of the engine (before window functions, triggers, upsert, WITHOUT
ROWID, JSON, shell output modes, and similar features) gave hpl/stock = insert 1.46×, insert-indexed 1.28×, scan 1.55×, lookup 1.18×, sort 1.30×, update 1.45×, join 1.29×, file-insert 1.45×, a geometric mean of 1.37×.
Those features cost the stock build 2% to 13% more instructions per workload, but cost hpl `--all` 27% to 51%. The
full scan went from 97 G to 131 G under hpl but only from 62.4 G to 63.9 G under stock. The scan workload runs only 70
statements, so this is evaluator code, not per-statement overhead. Candidates in `LSql/Eval.lean`, which is one large
`mutual` block:
- `evalJ`, added to that block;
- string compares on function names in `eval`'s `.fn` case (`Json.isJsonFn`, `jsonValueTag`);
- the bigger `Env` structure, with the new fields `aggJson`, `nowMs` and `schema`.

I did not bisect it.

## 3. Per-statement cost grows with the database under hpl (a probable whole-array copy)

Instructions per one-row INSERT (`bench/gen.sh` insert workload with N rows; measured on the earlier build):

| rows | stock | hpl `--all` | hpl `--all --no-unbox` |
|---:|---:|---:|---:|
| 50k | 89.5k | 114.6k | 87.4k |
| 100k | 90.6k | 132.6k | 124.8k |
| 200k | 91.7k | 169.3k | 194.8k |
| 400k | 92.3k | 242.5k | 330.1k |

Stock is flat. Both hpl builds grow roughly linearly with the page count, so on each statement something that stock
updates in place gets copied in hpl's code. The likely candidate is the pager's page array (`Pager.pages`, an
`Array Page`) or its `flags`/`free` arrays. The stock build showed this same symptom when a second reference to the
`DB` was alive. The fix there moved the DB out of the shell state with `DB.placeholder`, and the pager out with
`Pager.placeholder`, before the update (see `LSql/Shell.lean` `runSql` and `writeFile`). hpl seems to lose that
uniqueness somewhere. It also matches the workload pattern: `--no-unbox` is the slowest Lean build on update, lookup and
join, which run tens of thousands of statements against a 100k-row table. Yet it is the *fastest* Lean build on scan,
at 0.83× stock's instructions. I did not locate the copy. The builds are stripped. An `HPL_SYMBOLS=1` build with
callgrind, or `hpl --profile` share-copy events, should find it.

The `--all` build logs also flag layout conversions inside loops, between hpl's contiguous arrays and Lean's, at
Lean-ABI boundaries (closures, library calls). They show up in `writeRow`, `candidates` and the cursor functions; see
/home/jgetzel/workspace/jgetzel-skills/lean-sqlite/hpl/.lake/build/ir/hpl/*.log.

## 4. Bug: `--no-unbox` emits C that does not compile

With `--all --no-unbox`, a fused `List.range` loop (`List.range.loop._hpl_lib._hpl_fwd._hpl_fuse_6`) in LSql.Compile,
LSql.Exec, LSql.Check, LSql.Shell and Main is emitted as C that clang rejects with `use of undeclared identifier
'x_0'`. The workaround is `--disable fuse` for those modules, in
/home/jgetzel/workspace/jgetzel-skills/lean-sqlite/hpl-nounbox/lakefile.lean (`hplArgsOf`). To reproduce, remove those
cases from `hplArgsOf` and build hpl-nounbox.

## 5. Side effect

The first lean-sqlite hpl build, on 2026-11-22 at 21:41, made Lake rebuild `Hpl.Driver` and relink
~/workspace/high-perf-lean/.lake/build/bin/hpl. The sources were untouched (clean at f78b82312f), so it is the same hpl
built in the devshell. It has not been rebuilt since.

## Reproduce

```sh
H=~/workspace/high-perf-lean; L=/home/jgetzel/workspace/jgetzel-skills/lean-sqlite
cd $L && nix develop $H -c lake build
for d in clang hpl hpl-nounbox; do (cd $L/$d && nix develop $H -c bash -c ". $H/tools/cc.sh && lake build"); done
cd $L/bench && ./gen.sh && nix develop $H -c ./run.sh 5        # writes results.tsv; ENGINES="stock hpl" ./run.sh 5 insert for a subset
```

The raw numbers are in /home/jgetzel/workspace/jgetzel-skills/lean-sqlite/bench/results.tsv, and the design notes are in
/home/jgetzel/workspace/jgetzel-skills/lean-sqlite/README.md (section "Benchmarks").
