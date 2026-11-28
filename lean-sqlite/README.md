# lean-sqlite

A clone of sqlite3 written in Lean 4 (v4.35.0): the shell, the SQL parser, a query engine, and b-trees in **sqlite's own file
format**. lean-sqlite opens databases sqlite3 wrote and writes databases sqlite3 accepts (`pragma integrity_check` ok).
Everything is Lean; there is no C. Every function is total. It is built two ways: by stock Lean, and by
[hpl](../../high-perf-lean) (high-perf-lean, an optimizing Lean → C backend). The benchmarks compare both against the C
sqlite3.

It covers sqlite's SQL language broadly: inner, LEFT, RIGHT, FULL, NATURAL and USING joins, subqueries, compound selects, recursive CTEs, window
functions, aggregates (with FILTER, and the percentile family), row values, upsert, RETURNING, triggers (BEFORE/AFTER/INSTEAD OF, with RAISE), views,
WITHOUT ROWID tables, TEMP objects, partial and expression indexes, savepoints, ALTER TABLE (rename, add/rename/drop
column), STRICT tables, WITH in front of INSERT/UPDATE/DELETE, the date/time and JSON functions, and table-valued
functions (json_each, json_tree, pragma_*). What is left out is listed in
[Not supported](#not-supported).

## Build and run

```sh
H=~/workspace/high-perf-lean                       # the Lean 4.35 toolchain, clang, perf
nix develop $H -c lake build                       # stock: .lake/build/bin/lsqlite3
(cd hpl && nix develop $H -c lake build)           # hpl: hpl/.lake/build/bin/lsqlite3 (about an hour; hpl's -K cc/lto/leanrt options pass through)
.lake/build/bin/lsqlite3 [FILE | :memory:] [SQL]   # SQL from the argument, else stdin
./check.sh                                         # the gate: totality, builds, proofs, all tests on both builds
```

The shell reads SQL like sqlite3's and prints rows in sqlite3 3.54's output modes (list, csv, column, box, table, markdown,
json, line, quote, insert, tabs, html, ascii and others, with their `.mode` options). Its dot commands are `.mode`,
`.headers`, `.nullvalue`, `.separator`, `.width`, `.tables`, `.indexes`, `.schema`, `.dump`, `.read`, `.print`,
`.bail`, `.echo` and `.quit`, with arguments quoted as sqlite3 parses them. Errors go to stderr as sqlite3 prints them
(`Parse error near line N: ...`, `Error near line N: ...`), and the exit status is 1 after an error.

## Design

The layers follow sqlite's (`src/` of the sqlite source, which served as the reference):

| module | role | sqlite |
|---|---|---|
| `LSql/Lex.lean`, `LSql/Parse.lean` | tokenizer; recursive-descent parser to `Ast` (keywords, fallback-to-identifier, `sqlText` as sqlite stores it) | tokenize.c, parse.y |
| `LSql/Ast.lean`, `LSql/Value.lean` | the SQL syntax tree; the five storage classes | sqliteInt.h |
| `LSql/Compile.lean`, `LSql/Plan.lean` | name resolution to frame slots, comparison affinity and collation, aggregates, access paths per table (rowid =, IN, ranges, index prefix + range) | resolve.c, where.c |
| `LSql/Eval.lean` | the interpreter: expressions, nested-loop joins (LEFT, RIGHT, FULL, USING, NATURAL), GROUP BY, aggregates, window functions and frames, DISTINCT, compound selects, ORDER BY/LIMIT, WITH (recursive too), table-valued functions; uncorrelated subqueries run once | vdbe.c, select.c, window.c |
| `LSql/Exec.lean` | statements: CREATE/DROP TABLE/INDEX/VIEW/TRIGGER, INSERT (OR REPLACE/IGNORE..., upsert), UPDATE, DELETE, RETURNING, triggers, constraints (NOT NULL, UNIQUE, CHECK, INTEGER PRIMARY KEY, AUTOINCREMENT, STRICT), WITHOUT ROWID and TEMP tables, partial and expression indexes, ALTER TABLE, PRAGMA, transactions and savepoints | build.c, insert.c, update.c, delete.c, trigger.c, alter.c, pragma.c |
| `LSql/Schema.lean`, `LSql/Pragma.lean` | tables, indexes, views and triggers read from `sqlite_schema`; the schema pragmas (table_info, index_list, ...) | build.c, pragma.c |
| `LSql/BTree.lean` | table and index b-trees: insert with page splits, delete with sibling merges, cursors | btree.c |
| `LSql/Pager.lean` | pages decoded into nodes, overflow chains, the freelist, statement and transaction journals, the file read and written | pager.c, btree.c page format |
| `LSql/Record.lean`, `LSql/Bytes.lean` | record format, varints | vdbeaux.c, util.c |
| `LSql/Num.lean` | REAL formatting (`%!.17g` via sqlite3FpDecode), text→number, casts, `round`, `printf` | util.c, printf.c |
| `LSql/Func.lean`, `LSql/Compare.lean` | affinity, arithmetic, LIKE/GLOB, scalar functions; value order and collations (BINARY, NOCASE, RTRIM) | func.c, vdbemem.c |
| `LSql/DateTime.lean`, `LSql/Json.lean` | the date/time functions and modifiers; the JSON functions, aggregates, json_each/json_tree, JSON5 input | date.c, json.c |
| `LSql/Check.lean` | `PRAGMA integrity_check`: tree order and depth, page ownership, overflow lengths, every index against its table | btree.c, pragma.c |
| `LSql/Output.lean`, `LSql/Shell.lean` | the shell's output modes; the shell and its dot commands | ext/qrf/qrf.c, shell.c |

**Functional state.** A database is a value (`DB`: pager, schema, counters). A statement is a function in
`EStateM Err DB`: a failed statement hands back the state it reached, and the pager's statement journal (the pages as they
were before their first change) puts it back. The state is never shared, so page arrays are updated in place. A savepoint
is the pager value itself. The interpreter (`runSel`, `eval`) is pure.

**Types.** A b-tree node's type records the kind of its tree (`Node : TreeKind → Type`): table nodes (rowid keys, rows)
and index nodes (entries) are different types with different operations, so an index entry cannot be put in a table node.
Pages are a sum of b-tree nodes, overflow and free pages (`Page`), and cursors check which they are on at run time.
Statements are compiled into a plan with column references resolved to slots before anything runs, and errors carry their
kind (`ErrKind.parse` / `.runtime`). `LSqlProofs.lean` holds checked theorems: comparison affinity is
symmetric, NOCASE folding is idempotent and leaves no upper-case letter, varints are 1 to 9 bytes, a cell takes at least
4 bytes, an integer's serial type and body length agree, and node array inserts add exactly their elements. There are
also 6,634 #guard tests taken from sqlite3 3.54 (`Tests/`, see [Tests](#tests)), and varint round trips
(`LSql/Bytes.lean`).

**Totality.** `Audit.lean` (run by `check.sh`) walks the compiled environment: all 6,538 constants lean-sqlite defines are
definitions the kernel checked, termination included; none is `partial` (opaque), `unsafe`, `extern` or
`implemented_by`, and `main` depends on no axiom (no `sorryAx`). A planted `partial def` makes it fail. In the source there is no `partial def`, no panicking access (`xs[i]!`, `.get!`, `set!`, `panic!`...), no
`while`/`repeat` (which desugar to a partial loop), no `sorry`/`unsafe`/`extern`/`implemented_by`; `check.sh` enforces
it (`../swarm/lean/nopanic.pl` plus a scan for the rest). Recursion is structural, by `termination_by`, or bounded by fuel
that cannot run out on valid input: the input's length, the page count, a b-tree depth of 64, the cell count. Stdin is read
by a fuel-bounded loop too. Only Lean's own runtime and library remain (`IO` primitives, `List.mergeSort`, ...).

## Tests

- `tests/diff.sh [BIN]`: 61 SQL scripts (`tests/sql/`) run through the real sqlite3 3.54 and BIN. Standard output must be
  byte-identical, and both must report the same number of errors. `--file` runs them against database files, then has
  sqlite3 run `integrity_check` on the file BIN wrote and compares the two files' `.dump`. All 61 pass in both modes on
  every build.
- `tests/compat.sh [BIN]`: the file format both ways. sqlite3 writes a database with updates, deletes, overflow pages, a
  freelist and an index. BIN reads it and changes it, sqlite3 checks it and reads it back, and BIN reopens its own file.
- `tests/sql-unsupported/`: the two scripts that need text that is not valid UTF-8 (below).
- `Tests/`: 6,634 `#guard`s checked at compile time, their expected values taken from sqlite3: number formatting and
  casts (2,857), date/time (2,148), JSON (696), shell output modes (590) and the parser (343). `LSqlProofs.lean` holds 9
  theorems about the comparison, case-folding, varint and record code.

## Not supported

- At most one RIGHT or FULL JOIN per SELECT; `UPDATE ... SET (a, b) = (SELECT ...)` (a row value of expressions works);
  upsert on a WITHOUT ROWID table; generated columns; ATTACH; EXPLAIN; virtual tables (FTS, R-tree) and ANALYZE;
  parameters (`?`), which only an API binds; the `jsonb_*` functions.
- When a statement fails at run time partway through its rows, sqlite3 has already printed the rows before the error;
  lean-sqlite builds a statement's whole result first and prints none of them. sqlite3 3.54 also prints the statement
  with a `^--- error here` marker under some error messages; lean-sqlite prints the message line only.
- `localtime`/`utc` modifiers treat local time as UTC. `random()` is a deterministic splitmix sequence, not sqlite's
  generator, so its values differ.
- In the shell: only the dot commands listed in [Build and run](#build-and-run) exist (`.mode` lacks tty, psql, split
  and www). A window function's result does not carry the JSON subtype, so
  `json_array(json_group_array(x) OVER ())` quotes the inner array where sqlite3 embeds it.
- **Text is a Lean `String`**, which must be valid UTF-8. A text value holding other bytes (a blob concatenated into text,
  a database written with such text) has those bytes read one by one as Latin-1 characters, so writing it back changes it.
- **No journal file, no locking.** A file database is read whole when opened. At each commit (each statement outside a
  transaction), lean-sqlite re-encodes the pages that changed and rewrites the whole file. A crash during that write can
  corrupt the file, and a large database written one autocommit statement at a time is slow (do it in a transaction).
  Concurrent writers are not detected.
- Interiors of the format it reads: auto-vacuum and UTF-16 databases are refused. The query planner is much simpler than
  sqlite's: no join reordering, no covering indexes, no ORDER BY through an index.

## Benchmarks

`bench/gen.sh` writes eight speedtest1-style workloads (sqlite's `test/speedtest1.c` is the model), generated by sqlite3
itself from an LCG so every engine reads the same bytes:
- **insert:** 100k one-row INSERTs in a transaction.
- **insert-indexed:** the same, into a table with an INTEGER PRIMARY KEY in random order and a secondary index.
- **scan:** 70 full-table scans with BETWEEN, aggregates and LIKE, over 100k rows.
- **lookup:** 20k index lookups and 20k rowid lookups.
- **sort:** ORDER BY, GROUP BY, DISTINCT and HAVING over 100k rows.
- **update:** 20k UPDATEs and 2k DELETEs by rowid, then range UPDATE and DELETE.
- **join:** an indexed join, plus 200 small joins.
- **file-insert:** `insert` into a database file.

All but file-insert run in `:memory:`.

`bench/run.sh [RUNS]` runs each workload through each engine. The output must equal sqlite3's byte for byte, or the run
fails. Every engine's output was identical on every workload. For file-insert, sqlite3 also checks each file the Lean builds
wrote. It reports the minimum wall time of 5 runs and the user-space instructions of one run (`perf stat -e
instructions:u`). The raw numbers are in `bench/results.tsv`.

The machine was a laptop with 24 CPUs and a load of about 2.2 to 3.1 from other work during the run. Wall time on a shared laptop
is noisy, so read the instruction counts first.

The engines:
- **C sqlite3:** sqlite3 3.54.0 from nixpkgs.
- **stock Lean (gcc):** Lean's own C backend, with the C compiled by the devshell's gcc (`leanc -O3`).
- **stock Lean (clang):** a control build (`clang/`). The same Lean C, compiled by hpl's clang wrapper
  (`lake query hplcc`), but linked against the toolchain's standard runtime, not hpl's ThinLTO one. It separates the C
  compiler from hpl's own passes.
- **hpl `--all`:** hpl (high-perf-lean at f78b82312f) compiles every function of every module. It refused none.
- **hpl `--all --no-unbox`:** the same, keeping Lean's data layout (`hpl-nounbox/`). Loop fusion is disabled in five
  modules, because of an hpl bug (below).

Wall time (minimum of 5), with the ratio to C sqlite3:

| workload | C sqlite3 | stock Lean (gcc) | stock Lean (clang) | hpl `--all` | hpl `--all --no-unbox` |
|---|---:|---:|---:|---:|---:|
| insert | 137 ms | 751 ms (5.5×) | 765 ms (5.6×) | 1619 ms (11.8×) | 1016 ms (7.4×) |
| insert-indexed | 231 ms | 1211 ms (5.2×) | 1182 ms (5.1×) | 2085 ms (9.0×) | 1821 ms (7.9×) |
| scan | 276 ms | 4404 ms (16.0×) | 5313 ms (19.3×) | 11085 ms (40.2×) | 3632 ms (13.2×) |
| lookup | 192 ms | 1315 ms (6.8×) | 1264 ms (6.6×) | 2144 ms (11.2×) | 2173 ms (11.3×) |
| sort | 136 ms | 1141 ms (8.4×) | 1094 ms (8.0×) | 2012 ms (14.8×) | 1299 ms (9.6×) |
| update | 147 ms | 1634 ms (11.1×) | 1528 ms (10.4×) | 3010 ms (20.5×) | 3263 ms (22.2×) |
| join | 113 ms | 1264 ms (11.2×) | 1154 ms (10.2×) | 2600 ms (23.0×) | 2502 ms (22.1×) |
| file-insert | 144 ms | 867 ms (6.0×) | 816 ms (5.7×) | 1755 ms (12.2×) | 1108 ms (7.7×) |

User-space instructions:

| workload | C sqlite3 | stock Lean (gcc) | stock Lean (clang) | hpl `--all` | hpl `--all --no-unbox` |
|---|---:|---:|---:|---:|---:|
| insert | 1.58 G | 10.23 G (6.5×) | 10.13 G (6.4×) | 19.66 G (12.4×) | 14.02 G (8.9×) |
| insert-indexed | 2.59 G | 15.80 G (6.1×) | 15.30 G (5.9×) | 24.87 G (9.6×) | 25.78 G (9.9×) |
| scan | 4.10 G | 63.87 G (15.6×) | 59.66 G (14.6×) | 130.94 G (31.9×) | 52.78 G (12.9×) |
| lookup | 2.13 G | 19.71 G (9.2×) | 18.66 G (8.7×) | 29.06 G (13.6×) | 34.77 G (16.3×) |
| sort | 1.77 G | 14.13 G (8.0×) | 13.53 G (7.6×) | 25.85 G (14.6×) | 16.50 G (9.3×) |
| update | 1.72 G | 23.66 G (13.7×) | 22.38 G (13.0×) | 40.80 G (23.7×) | 53.48 G (31.0×) |
| join | 1.46 G | 18.69 G (12.8×) | 17.62 G (12.1×) | 31.52 G (21.6×) | 34.12 G (23.4×) |
| file-insert | 1.58 G | 10.46 G (6.6×) | 10.35 G (6.5×) | 19.89 G (12.6×) | 14.17 G (9.0×) |

Geometric mean over the eight workloads, relative to stock Lean (gcc): C sqlite3: time 0.12, instr 0.11; stock (clang): time 0.99, instr 0.96; hpl: time 1.95, instr 1.76; hpl --no-unbox: time 1.41, instr 1.47.

What the numbers say:

- **C sqlite3 is 5.2× to 16× faster than the stock Lean build**, and 6.1× to 16× in instructions. The largest gaps are full
  scans, UPDATE and joins. lean-sqlite is a tree-walking interpreter over decoded pages, where each cell is a heap object and
  each row a boxed `Array Value`. sqlite runs bytecode over raw page buffers. Each statement also has a fixed cost of about
  43k instructions in lean-sqlite (`SELECT 1;`, parse, compile and run), most of it allocation and freeing.
- **The C compiler barely matters.** Stock Lean through clang runs 4% fewer instructions than through gcc. Its wall time is
  1% lower in the geometric mean, which is within this laptop's noise (clang's scan time is an outlier of that noise).
- **hpl made lean-sqlite slower, and more so as the engine grew.** `--all` runs 1.76× the instructions of stock Lean
  (geometric mean) and takes 1.95× the time, and it is slower on every workload. Before the last round of features (window
  functions, triggers, upsert, WITHOUT ROWID, JSON, output modes and the rest), the same comparison was 1.37× instructions.
  That round cost the stock build 2% to 13% more instructions per workload, but cost the hpl `--all` build 27% to 51%.
  So hpl's result depends on the shape of the code in ways this project did not track down.
- **Per-statement cost grows with the table under hpl.** These counts come from the earlier build. Instructions per
  one-row INSERT as the table grows (`bench/gen.sh` with N = 50k to 400k, the insert workload):

  | rows | stock Lean | hpl `--all` | hpl `--all --no-unbox` |
  |---:|---:|---:|---:|
  | 50k | 89.5k | 114.6k | 87.4k |
  | 100k | 90.6k | 132.6k | 124.8k |
  | 200k | 91.7k | 169.3k | 194.8k |
  | 400k | 92.3k | 242.5k | 330.1k |

  Stock Lean's cost per statement is flat. Under both hpl builds it grows with the database, so some array that stock Lean
  updates in place is copied whole on each statement in hpl's code (the "second live reference" pattern). The stock build
  had the same symptom while the shell held the old database during a statement, until `LSql/Shell.lean` moved it out.
  At 50k rows `--no-unbox` runs 2% fewer instructions per INSERT than stock, so its constant factor is not the problem.
  I did not locate the copy. The hpl builds are stripped, so finding it needs an `HPL_SYMBOLS=1` rebuild with callgrind,
  or `hpl --profile` (its `share-copy` events).

  `--all` also converts arrays between hpl's contiguous layout and Lean's at Lean-ABI boundaries (closures, library
  calls). Its build logs flag such conversions inside loops in `writeRow`, `candidates` and the cursor functions
  (`hpl/.lake/build/ir/hpl/*.log`).
- **`--no-unbox` is mixed.** It keeps Lean's layout, so there are no conversions, but loop fusion is off in five modules
  (the bug below). That means it differs from `--all` in two ways. It is the fastest Lean build on **scan** (3.6 s
  against 4.4 s for stock, 17% fewer instructions). It is the slowest Lean build on update, lookup and join. That fits the
  per-statement copy: those three run tens of thousands of statements against a 100k-row table, while scan runs about 70.
- **Load:** the laptop ran other work during the run, at a load of 2.2 to 3.1.
- **Not measured:** times on an idle machine or on the desktop (the hpl project's rule for timings), sqlite3 built from
  source with clang, and database sizes past 400k rows.

Side effect: the first hpl build here also rebuilt the `hpl` binary in `~/workspace/high-perf-lean` (Lake rebuilt
`Hpl.Driver` and relinked `hpl` at 2026-11-22 21:41). That tree's sources are untouched (clean at f78b82312f), so it is
the same hpl, built in this devshell.

hpl bug found on the way: with `--no-unbox`, a fused `List.range` loop (`List.range.loop._hpl_lib._hpl_fwd._hpl_fuse_6`) in
`LSql.Compile`, `LSql.Exec`, `LSql.Check`, `LSql.Shell` and `Main` is emitted as C that does not compile (`use of undeclared identifier
'x_0'`). `hpl-nounbox/lakefile.lean` works around it with `--disable fuse` in those five modules.

## Reproducing the benchmark

```sh
H=~/workspace/high-perf-lean
nix develop $H -c lake build                                                    # stock (gcc)
clang/build.sh; for d in hpl hpl-nounbox; do (cd $d && nix develop $H -c lake build); done
cd bench && ./gen.sh && nix develop $H -c ./run.sh 5                             # perf comes from the devshell
```

`run.sh` writes `bench/results.tsv`; `ENGINES="sqlite3 stock" ./run.sh 5 insert` runs a subset. From scratch, the three
builds run in parallel took about 77 minutes on this laptop, most of it the hpl `--all` build.

## Layout

```
LSql/*.lean      the engine          Main.lean   the executable     LSqlProofs.lean   theorems
Tests/*.lean     #guard tests        tests/      differential tests (diff.sh, compat.sh, sql/, sql-unsupported/)
bench/           gen.sh, run.sh, results.tsv
hpl/             the hpl build (--all)           hpl-nounbox/  the hpl build keeping Lean's layout
clang/           the stock build with hpl's C toolchain (a control)
check.sh         the gate
```
