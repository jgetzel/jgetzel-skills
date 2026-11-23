# Theorems to prove about lean-sqlite

This file lists the properties we want to prove about lean-sqlite in Lean, from small lemmas up to the large results. It
gives each a precise statement, what it depends on and how far along it is. Proved results go in `LSqlProofs.lean`,
which `lake build LSqlProofs` checks. The executable doesn't import it.

These are theorems about this Lean implementation, not about the C sqlite3. The link to real sqlite is still
differential testing (`tests/sql`, `check.sh`). A proof shows the clone keeps its own guarantees on every input. The
tests show that the clone's behaviour matches sqlite's.

Status: **proved**, **partial**, **open**, or **blocked** (it needs code that doesn't exist yet).

## Already proved

In `LSqlProofs.lean`:
- `cmpAff_comm`: comparison affinity doesn't depend on operand order.
- `cmpAff_numeric`: in a comparison, a numeric side wins.
- `foldCase_idem`: NOCASE case folding is idempotent.
- `foldCase_not_upper`: case folding leaves no upper-case ASCII letter.
- `swap_swap`: reversing a sort order twice gives the original order.
- `varintLen_bounds`: a varint is 1 to 9 bytes long.
- `leafCellBytes_ge`: a cell takes at least 4 bytes on a page.
- `serialLen_int`: an integer's serial type agrees with its body length.
- `insertMany_size`: inserting into a page's arrays adds exactly the inserted elements.

Also checked, but not a proof of behaviour: `Audit.lean` confirms every constant is total (no `partial`, `unsafe` or
`extern`) and that `main` uses no `sorry`.

## Cross-cutting issue: fuel

Much of the recursion is bounded by a fuel counter, for example `maxDepth = 64` in `LSql/BTree.lean`. When fuel runs
out, the function returns a default or an error. A behavioural theorem is therefore true only when there was enough
fuel, and every theorem below needs one of these:
- a hypothesis about fuel (for example, tree depth ≤ `maxDepth`); or
- a lemma that the invariants imply the fuel always suffices. This is better: for example, a well-formed tree over
  fewer than 2^64 pages has depth < 64.

Stating "enough fuel" as a predicate once, and proving it is preserved, is part of the foundation work.

## Layer 0: foundations (small, local)

**F1. Varint round-trip.** `getVarint (putVarint b v) b.size = (v, varintLen v)`, and `putVarint` writes exactly
`varintLen v` bytes. Modules: `LSql/Bytes.lean`. Status: open. (A varint encoding bug was fixed earlier.)

**F2. Record round-trip.** `decodeRecord (encodeRecord vs) = vs` for every array of values, up to the canonical form
sqlite writes. For example, a REAL with an integral value may be stored as an integer: state what is preserved. Modules:
`LSql/Record.lean`. Depends on F1. Status: open.

**F3. Values are totally ordered.** For every collation `c`, `cmpValues c` is a total preorder:
- reflexive;
- antisymmetric up to "equal under `c`";
- transitive;
- `cmpValues c a b = (cmpValues c b a).swap`.

It agrees with sqlite's ordering: NULL < numbers < text < blob, with integers and reals compared exactly. REAL values
are assumed not to be NaN, since sqlite stores NaN as NULL; the proof must establish this or assume it. Modules:
`LSql/Compare.lean`. Status: open.

**F4. Collations.** BINARY, NOCASE and RTRIM each give an equivalence relation that is consistent with F3's order.
Modules: `LSql/Compare.lean`. Depends on F3. Status: open.

**F5. Encoded index keys compare like values.** Comparing two encoded index keys under a `KeyInfo` (sort orders and
collations per column) agrees with comparing the decoded value arrays lexicographically under F3. Modules:
`LSql/Compare.lean`, `LSql/Record.lean`. Depends on F2 and F3. Status: open.

**F6. Page structure in the types.** Make interior-node invariants part of the types (`Vector` or subtypes):
- kids = keys + 1;
- keys are sorted;
- cells fit in the page.

With these in the types, malformed pages can't be built and the B-layer proofs get shorter. Modules:
`LSql/Pager.lean`, `LSql/BTree.lean`. This is refactoring that proves things, not a theorem. Status: open.

## Layer 1: storage

**S1. Page encoding round-trip.** Decoding the page bytes the pager writes gives back the same `Node`, including
overflow chains. Modules: `LSql/Pager.lean`. Depends on F1 and F2. Status: open.

**S2. Table b-trees refine finite maps.** An abstraction `toMap : Pager → Pgno → (Int64 → Option ByteArray)`. For a
well-formed tree:
- `tableFind` is lookup in that map;
- `tableInsert` is map insert;
- `tableDelete` is map erase;
- `tableMaxKey` is the maximum key.

A cursor scan (`first`, `next`) enumerates the map in key order. Each operation also preserves well-formedness:
sorted, balanced, page fill within bounds, and fuel sufficient. Modules: `LSql/BTree.lean`. Depends on F6 and S1.
Status: open. **This unlocks most of what follows.**

**S3. Index b-trees refine sorted multisets.** `indexInsert` and `indexDelete` act on the multiset of keys. `seekKey`
followed by `next` enumerates the keys ≥ the probe in F5's order. Modules: `LSql/BTree.lean`. Depends on F5 and S2's
proof technique. Status: open.

**S4. The free list is sound.** No page is both in use and free. `drop` and `clear` return exactly the tree's pages to
the free list. No page is reachable from two roots. Modules: `LSql/Pager.lean`, `LSql/BTree.lean`. Status: open.

**S5. Every reachable file is well-formed.** Every database reachable from an empty one by any sequence of statements
satisfies sqlite's file-format invariants: the properties `PRAGMA integrity_check` checks, plus header consistency.
**In words: lean-sqlite never corrupts a database.** Depends on S1–S4 and E-layer preservation. Status: open.

## Layer 2: execution and data integrity

**E1. Statement atomicity.** If a statement fails, `rollbackStmt` gives back a pager equal (as an abstract database)
to the one before the statement. The journal (`Pager.journal`) saves every page before its first change in the
statement. Modules: `LSql/Pager.lean`, `LSql/Exec.lean`. Status: open.

**E2. Transaction atomicity and savepoints.** ROLLBACK restores the state at BEGIN (`rollbackTxn`). ROLLBACK TO a
savepoint restores the state at that savepoint, and savepoints nest. Depends on E1. Status: open.

**E3. Index consistency.** After any sequence of statements, each index's multiset (S3) equals the keys computed from
its table's rows. This covers partial-index predicates, expression indexes, WITHOUT ROWID tables, and REPLACE or upsert
conflict handling. Modules: `LSql/Exec.lean`. Depends on S2, S3 and E1. Status: open.

**E4. Constraint preservation.** Every reachable database satisfies its declared constraints: NOT NULL, UNIQUE and
PRIMARY KEY (through E3), CHECK, STRICT column types, and the INTEGER PRIMARY KEY rowid rules. Triggers fire as
declared, and their effects are inside the statement's atomic unit. Foreign keys hold when `foreign_keys` is on.
Depends on E1 and E3. Status: open.

## Layer 3: query semantics

**Q1. A reference semantics.** Write a separate evaluator meant to be obviously correct, and keep it small:
- FROM as a cross product of bags, then WHERE, then GROUP BY/HAVING, then the window functions, then SELECT, then
  DISTINCT, then ORDER BY/LIMIT;
- SQL three-valued NULL logic, sqlite's type affinity and collations;
- no indexes and no optimization.

It is a specification, not a theorem. It should cite Guagliardo & Libkin, *A Formal Semantics of SQL Queries, Its
Validation, and Applications* (VLDB 2017), and Benzaken & Contejean, *A Coq mechanised formal semantics for realistic
SQL queries* (CPP 2019). Differential tests against sqlite3 check that it matches sqlite. Status: open.

**Q2. Access paths are sound.** Using an index (equality, range, or covering) instead of a full scan returns the same
bag of rows. Depends on S3, E3 and Q1. Status: open.

**Q3. Planner and executor correctness.** For each fragment, the real engine's result equals Q1's result as a bag, and
as a list when there is an ORDER BY. Do the fragments in this order:
1. single-table SELECT/WHERE;
2. inner joins;
3. LEFT, RIGHT and FULL joins;
4. aggregates and GROUP BY;
5. subqueries, including correlated and hoisted ones;
6. compound selects;
7. window functions;
8. CTEs, including recursive ones.

Modules: `LSql/Plan.lean`, `LSql/Compile.lean`, `LSql/Eval.lean`. Depends on Q1 and Q2. Status: open. **This is the
crown jewel.** Most of the wrong-answer bugs SQLancer has found in sqlite are unsound optimizations of this kind.

**Q4. DML semantics.** INSERT, UPDATE, DELETE, upsert and RETURNING are equivalent to the reference semantics on the
abstract database (S2 and S3 maps). Depends on Q1, E1 and E3. Status: open.

## Layer 4: durability (blocked)

**D1. Crash safety.** After a crash at any point during a commit, recovery gives either the old database or the new
one. Status: blocked. lean-sqlite rewrites the whole file and has no rollback journal, WAL or locking. It needs those,
plus a model of crashes and of the file system: what a partial write and fsync ordering can leave behind, as in FSCQ.

## Suggested order

F1 → F2 → F3/F4 → F5 → F6 → S1 → S2 → S3/S4 → E1/E2 → E3 → S5/E4 → Q1 → Q2 → Q3 (by fragment) → Q4.

When S2, S3 and E3 are done, we can say that no statement corrupts a table or index and that indexes never change
query answers. When Q3 is done, we can say that the engine computes the specified answer.
