# sw-architecture-review: types, purity and coupling in swarm-lean, swarm/model, claim and harness-retro

Review, 2026-11-21. Read-only: nothing was built or run. Every `path:line` is at commit 43d7bd1 and, unless it says
otherwise, relative to `swarm/lean/`. `origin/main` moved to 8d81653 (#75) while this was written; where that changes
a finding it says so. "Proofs doc" is `sw-global-proofs.md`; "spec" is `sw-global.md`.

Five passes read the code (dependent types, pure core vs effects, coupling, `claim/`, `swarm/model`). Each claim kept
here was then checked against the file it cites. Claims that rest on reading alone and need a test or the owning
task's check are marked **to confirm**.

Proposals are ranked by value per cost. The top twelve are board tasks, held for the user (§7).

## 1. What is right, and should stay

The base is sound, and most proposals below add a type on top of it instead of replacing it.

- **Effects are one class per part** (`World.lean:9-69`, `Sys.lean:22-57`, `Store.lean:9-12`). Commands are generic in
  `m`, `App` and `RecM` run the same code, and `RecM` records calls as data. No file in `Cmd/` or `Lib/` imports
  `Real`, `RealSys` or `Sqlite`'s FFI, or calls `IO.Process`/`IO.FS`. A free monad of effects would be these classes
  again.
- **`Txn`** (`Db/Txn.lean:105-137`) is reads, pure continuations, statements and a guarded update. `Txn.step` is the
  spec's `decide : Slice → Plan × α`.
- **`Db/*` is pure**, with no `let mut`. Decisions take `now` in a `Ctx`, so the clock cannot be read inside a
  transaction. `Cmd/Tasks.lean:65-69` is the right command shape: read the world once, one transaction, die at the edge.
- **Gather, decide, apply already exists in three places**: `Lib/Ci.lean` (`ciPollGate`/`ciPollApply`,
  `ciCheckFirst`/`ciCheckApply`), `Lib/Conflict.lean:186-239` (`tickApply`), `Lib/Cost.lean:334-382` (`tickStep`).
  Finding B1 asks the other watchd passes to follow them.
- **Results and refusals are inductives**: `Status`, `Notes.Dest`, `Fence`, `Refusal`, `DoneOut`, `Queue.Place`.
- **`claim/`**: `Admit.decide` is pure with IO only behind `Host`; swarm imports the `Claims` library instead of
  running a process; `Assumptions.lean` is narrow.
- **The Herdr mods never open the db**, and read state only through `swarm state --json`.

## 2. The ranking

Value: what it rules out or deletes. Cost: S (hours), M (a day or two), L (a week). "When" is against the in-flight
tasks.

| # | Proposal | Value | Cost | When |
|---|---|---|---|---|
| A1 | `swarm limits` validates every flag before its first commit | real bug | S | in #72 |
| A2 | `AgentName`/`SwarmName`: one parser at the four entry points | real collisions; a hypothesis §3.7 needs | S | with or right after #72, before #71's `@<swarm>` |
| A3 | The claim's holder is changed by the ledger script, not by swarm's `sed` | race outside the ledger's lock | S | any time |
| A4 | `Exit` carries its message; `Guard` returns a typed `Stop` | watchd tells the communicator why a pass failed | S-M | before or after #77 |
| A5 | The model in CI; `Decide/Rows.lean` split; `lives`/`prAct` call the model; the fate verdict an enum | drift caught; ~280 proof lines; a silent fall-through | S-M | any time (verdict: with #77) |
| A6 | `layering.sh` checks the implementation layers; `Sqlite.Val` split; harness-retro off `RealSys` | 19 edges fixed and kept fixed | S | any time |
| A7 | The raw-git check matches what it says; one `Git` path | 26 argv outside the rule | M | before #79 |
| A8 | Regex literals are checked values | a typo can't turn off a deny hook | S-M | any time |
| B1 | watchd passes: gather, one `Txn` with a pure decision, a list of `Act` | stale-snapshot writes; #82's lemma count | L | **with #77** |
| B2 | Statements and conditions typed by the schema, lowered to today's `Stmt` | ~70 `X.plain` lemmas; typo divergence | M-L | **in #99**, before #79 |
| B3 | `Scope` an inductive; `Txn` indexed by its machine-wide tables | an undefinable function in §3.5; read isolation | M | **in #99**, before #79 |
| B4 | `Task` as a phase with per-state payloads, flat columns kept | `WF.board` a lemma; 20 hand-written transitions | M-L | after #77, before #80, with B2 |
| B5 | `Dest` and `Who` as sums | a message to `""`; `ToIt` without string arguments | M | with #71 |
| B6 | Swarm resolution as a pure `pickSwarm` | the spec's §2 rule gets a test and a statement | M | with #99 |
| B7 | `swarm state --json`: wire types, one encoder, a version; no CLI text parsed by the mods | the one cross-language interface gets a definition | M | with or after #77; agree with #91/#101 |
| B8 | The slice typed by the tables read | "not read" and "empty" stop being one value | M | after #77, before #80 |
| C1 | `StayCond` inductive | a stay that never wakes on a parse default | S | with #72 |
| C2 | `GitRef` kept, not thrown away | five re-checks; a new git call can't forget one | S-M | after #74 |
| C3 | One `Agents.endRow` | four writers of "ended" disagree | S | with #72 |
| C4 | Lock paths carry their repo (`InRepo`) | a file of repo B checked against repo A's locks (**to confirm**) | S-M | with #73 |
| C5 | claim: one `Size`, one `Answer`, `WF` as two structures | flags parsed three times; positional `WF` | M | any time |
| C6 | Say what "the model" is; freeze or upgrade `swarm/model` | a stale model nobody decided to keep | S (freeze) / L | #78 |
| C7 | Duplicates: `dbPath` ×3, git wrapper ×3, hung ×3, worktree-list parse ×5, BFS ×5 | drift between copies | S each | when touched |
| C8 | `TaskId`, typed events, durations parsed at the edge | proof noise only | M | after #70 |

## 3. Tier A: cheap, and each fixes something that is wrong today

### A1. `swarm limits` commits before it validates

- **Where**: `Cmd/Agents.lean:191-203`.
  ```lean
  if mn.isSome || mx.isSome then
    …
    orDie (← Store.txn [.agent, .«meta»] (setLimits · envComms me mn mx now))
  if let some q := a.str "queue_only" then
    …
  if cn.any (· < 0) || cc.any (· < 0) || rb.any (· < 0) then die "a context threshold is tokens, 0 for off"
  ```
- **Now**: `swarm limits --min 3 --ctx-nudge -1` sets the minimum and the queue knob, then exits 1. The command is
  four write transactions, with `me` and `now` read four times.
- **Proposed**: parse and validate every flag to a `LimitsReq` (pure, `Except String`), then one transaction. `Txn` is
  a monad, so the four steps compose.
- **Buys**: all or nothing. **Cost**: S (27 lines). **Conflicts**: #72 converts this command; do it there.

The same composition applies to the post-tool hook (`Cmd/Hook.lean:234-246`): up to six `Store.run` calls, each
taking the write lock, with `touch` and `setStatus` rewriting the same agent row. One `postToolTxn` takes the lock
once. That is the hot path the spec's §1 names; measure before and after.

### A2. Agent and swarm names: one parser each, at the places a name enters

- **Where**: `Db/Agents.lean:84` is the only check on an agent name:
  ```lean
  def notHuman (name : String) : Except String Unit :=
    if name == HUMAN then .error "'human' is the user's name …" else .ok ()
  ```
  Swarm names are checked in `swarm new` (`Cmd/Agents.lean:342`) and not on the other creator, `join` as `<x>-comms`
  (`Cmd/Agents.lean:91-99`).
- **Now**: an agent may join as `swarm`, `@all`, `#5`, `nil`, or a name with a space or slash. Each collides with a
  meaning the same columns already have:
  - `swarm` is the system sender (`Lib/Watchd.lean:82`), and `unread` drops rows with `frm = name`
    (`Db/Msgs.lean:24`), so an agent named `swarm` never reads a system message;
  - `#5` is task 5's note box (`Db/Notes.lean:12`), so that agent reads the task's held notes as its mail;
  - `nil` is what `leaseLate` addresses when a claimed task has no owner (`Lib/Watchd.lean:95`);
  - once #71 rewrites `@all` to `@<swarm>` (proofs doc §1.4), a message to an agent named `@x` is a broadcast to
    swarm `x`. Swarm names exclude `@`; agent names do not.
  `sw-security-review.md` L4 lists the unvalidated characters; the collisions are new.
- **Proposed**: the pattern `GitRef` already uses (`Util.lean:122`).
  ```lean
  /-- An agent's name: 1-32 of a-z 0-9 - _, and none of the names the tables use for something else. -/
  structure AgentName where private mk ::
    val : String
    deriving DecidableEq, Repr
  def AgentName.parse? (s : String) : Option AgentName :=
    if 0 < s.length && s.length ≤ 32 && s.all (fun c => c.isLower || c.isDigit || c == '-' || c == '_')
        && !["human", "swarm", "nil"].contains s then some ⟨s⟩ else none
  structure SwarmName where private mk ::
    val : String
  /-- Who acts or sends: `Ctx.me`, `msg.frm`, `event.agent`. -/
  inductive Who | user | system | agent (n : AgentName)
  ```
  Step A: `parse?` at the four entry points (`World.me`, `join`'s name, `spawn`'s name, `Swarms.create` taking a
  `SwarmName`); values unwrap to `String` after. Step B, optional and later: rows and `Ctx.me` carry the types.
- **Buys**: the collisions cannot be stored, and the second swarm creator cannot skip the check. The proofs doc's
  `ToIt` with `r.dest = some ("@" ++ s)` (§3.7) is only right if no agent name starts with `@`; with `AgentName` that
  is `parse?`'s definition, not a WF clause.
- **Cost**: A is S (4 entry points; the names the CLI tests use all pass the rule). B is L (about 200 signatures) for
  no bug found: no argument swap among the ~70 `post`/`say`/`touch`/`bind` call sites.
- **Conflicts**: #72 touches the entry points. #71 should not land `@<swarm>` before step A.

### A3. swarm rewrites the ledger's claim files itself

- **Where**: `Cmd/Run.lean:328-329` (remote job) and `:483-484` (detached job):
  ```lean
  s!"f=\"$\{SWARM_COMPUTE_DIR:-…/swarm-compute}/claims/{claimId}\"; trap 'rm -f \"$f\"' EXIT",
  s!"if [ -f \"$f\" ]; then sed \"s/^\\([^ ]* [^ ]* \\)[^ ]* /\\1p$$ /\" \"$f\" > … && mv … \"$f\"; fi",
  ```
- **Now**: the ledger is a directory of text files kept by one `sh`+awk script in `claim/Claims/Ledger.lean`, under a
  lock. Here swarm repeats the ledger's path and field layout and rewrites a claim's holder with its own `sed`,
  outside that lock. **To confirm**: a remote claim's 15-minute holder can lapse during `rsync`, after which the
  `[ -f "$f" ]` is false and the job runs holding nothing, silently.
- **Proposed**: a `hold <id> <pid>` op in the ledger script, called at both sites; it fails loudly when the claim is
  gone.
- **Buys**: the ledger's format is known to one side. **Cost**: S (one script op, ~10 lines in `Ledger.lean`, two
  call sites, a `claim-tests` case). **Conflicts**: none; #90 edits `detachStart` 270 lines above.

### A4. `die` throws a bare code, and `Guard` reports "exit 1"

- **Where**: `World.lean:75-77`, `Real.lean:349-355`:
  ```lean
  def die … (msg : String) : m α := do
    Env.err s!"swarm: {msg}"
    throw (Exit.mk 1)
  -- Guard App
  | .error e => pure (.ok (.error s!"exit {e.code}"))
  ```
- **Now**: under watchd's per-pass guard, a pass that dies is told to the communicator as `lifecycle: exit 1`; the
  reason went to the stderr of a hidden terminal. `autoSpawn` reports a died spawn as "launch error"
  (`Lib/Watchd.lean:629,645`). `retryBusy` recognises a busy db by the substring "database is locked"
  (`Cmd/Msgs.lean:112`). Exit codes are literals where they are thrown (`Exit.mk 255` seven times in `Cmd/Run.lean`).
- **Proposed**:
  ```lean
  structure Exit where
    code : UInt32
    msg : Option String := none        -- none: already said
  def die [Monad m] [MonadExceptOf Exit m] (msg : String) : m α := throw { code := 1, msg := some msg }
  inductive Stop
    | exit (e : Exit)
    | busy                              -- SQLITE_BUSY after the busy timeout
    | world (msg : String)
  class Guard (m : Type → Type) where
    guard {α : Type} : m α → m (Except Stop α)
  ```
  `Main.lean` prints `swarm: {msg}` when it turns the `Exit` into the process's code. Named codes in one place.
- **Buys**: the communicator reads why a pass failed; `die` loses `[Env m]`, so `Env` leaves every signature that only
  dies; in `RecM` "this decision dies" needs no fact about the stderr trace.
- **Cost**: S-M. `die`'s 96 call sites don't change. 13 `Exit.mk` sites, 3 `Guard` instances, 26 `Guard.guard` uses,
  the C shim to surface `SQLITE_BUSY`. **Conflicts**: touches `Cmd/Watchd.lean`; not during #77.

### A5. The model and the code share almost nothing, and nothing checks that

- **Where**: only four imports of `SwarmModel` reach swarm-lean: `Glob` (`Spec/Data.lean:3`, `Db/Locks.lean:2`) and
  `Decide` (`Lib/Watchd.lean:5`, `Challenge.lean:4`). `swarm/model/SwarmModel/Decide.lean:1-2` imports `Model` and
  `PrWatch`.
- **Now**:
  - No model theorem reaches the code by a refinement proof; there is no `abs : Db → Swarm.State`. The running code
    calls `Glob.covers`/`overlaps` and `Decide.keepsL`/`ARow`. `lives`, `fate`, `endWhy` and `prAct` are restated in
    swarm-lean with equality theorems in `Proofs/Watchd.lean`, which is out of the build since #84. `wakes` is restated
    with no link.
  - The model is executable, but its replay against the CLI was deleted with the Lua (#110) and not rebuilt. CI builds
    the 4 model files the binary needs; `swarm/model/check.sh` (38 files) is run by nobody.
  - Because `Decide.lean` imports `Model`, the binary builds about 1,700 lines of model for about 150 lines of
    row-level functions, and `layering.sh` whitelists `SwarmModel.*`.
  - `Lifecycle.fateHeard` returns its verdict as `Option String`, matched at `Lib/Watchd.lean:703-709` with a last
    `| _, _ => pure ()`. A new verdict text falls through silently.
- **Proposed**, in order:
  1. Run `swarm/model/check.sh` in CI (S).
  2. Split an import-free `SwarmModel/Decide/Rows.lean` out of `Decide.lean` (S). The binary then depends on that
     file and `Glob` only.
  3. `lives` and `prAct` call `Decide.livesL`/`prActL` instead of restating them; the verdict becomes
     `inductive Verdict | keep | unclean | reuse | «end»` shared with the model (S-M).
  4. Later: a differential test of the model's step against `XCmd.step` over the pure `Db` steps (M).
- **Buys**: single source for the decisions, so there is nothing to prove equal (about 280 lines of
  `Proofs/Watchd.lean`); the fall-through becomes a missing match arm; model drift fails CI.
- **Cost**: S for 1-2, S-M for 3. **Conflicts**: no in-flight branch touches `swarm/model`. Item 3's `fateHeard`
  sits in files #72 and #77 edit: with or after them.

### A6. `layering.sh` checks the spec and proof rules; the implementation has no checked layers

- **Where**: `layering.sh:6-10` (the spec list), `:24-31` (three rules).
- **Now**: 143 modules, 397 import edges. Nothing checks that commands don't import commands or that pure modules
  stay below the effects. 19 edges break the layer table in Appendix A (listed in Appendix B). The ones that matter:
  - `Cmd.Watchd → Cmd.{Agents,Hook,Msgs}` (`Cmd/Watchd.lean:1-3`). watchd calls `hcSwarm`, `bindAgent`, `stopBlock`,
    `deliverTo`, `typeLine`, `compactLine`, and passes an empty object as a fake Stop-hook payload
    (`Cmd/Watchd.lean:178,204`).
  - `Db.Rows → Sqlite` (`Db/Rows.lean:1`): `Sqlite.lean` holds the pure `Val` and 22 externs, so 124 of 143 modules,
    the spec layer included, import the FFI.
  - `HarnessRetro.Hr → RealSys` (`HarnessRetro/Hr.lean:1`) for one function, `execIO'`. Its closure is 21 modules
    including the store, and `hr.sh` marks it stale on any `SwarmLean/` edit.
  - `Spec.Data → Lib.Re` for one function, which puts the regex engine under 58 implementation modules;
    `Db.Msgs`/`Lib.Machine → Spec.Data` (implementation importing from `Spec/`).
  - Six unused imports: `World → Store`, `Cmd → World`, `Db.Locks → Db.Tasks`, `Lib.Lifecycle → Lib.Agents`,
    `Lib.Merge → Lib.Ci`, `Report → Lib.Hook`.
- **Proposed**: add the rank table to `layering.sh` (about 25 lines; it already has the edge list). Then: split
  `Sqlite/Val.lean` out of `Sqlite.lean`; move `execIO'` to a small `Proc` module; drop the unused imports; move the
  six shared functions watchd needs from `Cmd/` to `Lib/`.
- **Buys**: the spec layer's trusted base no longer includes the FFI; harness-retro stops rebuilding on store edits;
  the other coupling fixes stay fixed.
- **Cost**: S for the script and each fix, bar the watchd moves (S-M, about 110 lines). **Conflicts**: #84 changes
  one line of rule 2. The watchd moves collide with #70's branch (380 lines of `Cmd/Watchd.lean`) and #77: do them
  inside #71/#72/#77 or after. The rest any time.

### A7. The "no raw git" check matches none of the raw git calls

- **Where**: `check.sh:14-15`:
  ```sh
  # git runs only through Git.git / Git.out (World.lean: they put `--end-of-options` before ref operands), never a raw argv
  if grep -rn 'Proc\.output (\?\["git"' SwarmLean Main.lean | …
  ```
- **Now**: 26 `["git", …]` argv go through `Lifecycle.run`/`code`, `Sys.exec` or a local `run`, which the grep does
  not see: `Cmd/Run.lean:103,104,113`; `Lib/Conflict.lean:106,117`; `Lib/Lifecycle.lean:30-40,58,64,79,111,112,260`;
  `Lib/Watchd.lean:214-319` (nine). Several pass a ref with no `--end-of-options` (for example
  `Lib/Lifecycle.lean:30`, `merge-base --is-ancestor ref b`). Whether an unchecked base can reach one was not traced.
  The same holds for the kill rule: it misses the two `cgroup.kill` writes (`Lib/Lifecycle.lean:300,304`).
- **Proposed**: widen the grep to `\["git"` anywhere outside `World.lean`; route the 26 through `Git.git`/`Git.out`
  (a variant returning the exit code covers `code`); delete the three duplicate wrappers. With C2 the operands are
  `GitRef`s.
- **Buys**: the check says what its comment says. `Assumptions.lean` pins these argv, so the proofs' git assumptions
  then cover every call.
- **Cost**: M (26 sites in 4 files). **Conflicts**: before #79-#82, since it changes argv the assumptions name. #77
  edits `Lib/Watchd.lean`.

### A8. Regex literals compile at each call and the error is swallowed

- **Where**: `Lib/Re.lean:456-457`; `Cmd/Hook.lean:113`:
  ```lean
  let co := (Re.search Workspaces.CHECKOUT cmd).toOption.join.isSome
  ```
- **Now**: 27 call sites pass a literal pattern and get `Except String` back, the error being "the pattern does not
  parse". The hooks turn that into "no match": a typo in `CHECKOUT` would silently turn off the base-checkout deny.
  HarnessRetro turns it into an `IO` exception, which is the only reason `key`, `label` and `clip` are in `IO`, and
  why `sessions` (`HarnessRetro/TimeReport.lean:87-147`) is a 60-line `IO` loop with 10 `let mut`.
- **Proposed**:
  ```lean
  /-- A pattern known to parse. -/
  structure Pat where
    re : Regex
  def Pat.lit (p : String) (fl : Flags := {}) : Pat := ⟨(compile p fl).toOption.getD Regex.never⟩
  def Pat.search (p : Pat) (s : String) : Option Match := exec p.re s.toList.toArray
  ```
  with a table of every literal that `Tests/Re.lean` compiles. A subtype of patterns that compile is not possible
  here: `compile` is `partial`, so the proof would need `native_decide`, an axiom the gates forbid.
- **Buys**: a bad pattern fails the suite, not a hook in the field; HarnessRetro's text handling becomes pure and
  `sessions` a fold that can be tested on a literal transcript.
- **Cost**: S-M (27 sites). **Conflicts**: none.

## 4. Tier B: shape decisions, each with a window

These cost more. Each has a point after which it is no longer worth doing, because the proofs phase will have fixed
its statements on the current shape.

### B1. watchd's passes read, decide and act row by row

- **Where**: `Cmd/Watchd.lean:122-151` (`hcBlocked`), `:158-226` (`compactPass`), `:238-277` (`apiErrorPass`),
  `:290-315` (`commsInbox`); `Lib/Watchd.lean:325-351`, `:355-386`, `:452-513`, `:526-554`, `:670-731`, `:748-808`.
  ```lean
  let db0 ← Store.txn [.agent, .event] fun db => (db, db)
  for a in Agents.live db0 do
    …
    let now ← Clock.now
      Store.txn [.task, .agent, .event] fun db =>
        let db := { db with tasks := db.tasks.map back }
        (if a.status == some "blocked" then (db.setAgent a.name …).log now … else db, ())
  ```
- **Now**: a pass snapshots whole tables with an identity transaction, loops over the live agents, and inside the
  loop reads the clock, asks `pidAlive`, reads transcripts, types into terminals and commits one to three small
  transactions per agent. The lambdas decide on the snapshot row `a`, not on the row in the transaction's `db`, so a
  hook's write between the two is overwritten or ignored. The two files hold 92 `Store.txn` calls.
  `Tests/Spec/Watchd.lean:4-10` exists to test exactly "a peer writes between a read and the write that depends on
  it", and needs a hooked monad to do it. Two related problems sit in the same code:
  - **The order of record and send is chosen per site.** `compactPass` logs the event, then sends
    (`Cmd/Watchd.lean:202-205`: a failed send is never retried), and 15 lines later sends, then logs
    (`:219-221`: a crash between resends). Nothing says which a site wants.
  - **A tick's `t` goes stale** while each write stamps a fresh `Clock.now` (52 reads in the two files). A lease
    handed back at `Cmd/Watchd.lean:133` is short by however long the tick has run. No wrong reap was found: reap
    re-checks in its own transaction.
- **Proposed**: the shape `Cost.tickStep`, `Conflict.tickApply` and `Ci.ciCheckApply` already have.
  ```lean
  /-- What a tick read of the machine before deciding: no db rows. -/
  structure TickIn where
    now : Int
    terms : Option (List Term)
    procs : List Machine.Ps
    waiterAlive : List (String × Bool)
    apiError : List (String × String)
    away : Bool
  inductive Once | atMost | atLeast
  /-- A non-db effect a pass asks for; the edge runs it. -/
  inductive Act
    | send (agent hc text : String) (mark : List Stmt) (once : Once)   -- atMost: mark, then send; atLeast: send, mark if sent
    | endAgent (name : String)
    | err (line : String)
  def compactTxn (i : TickIn) (comms a : String) : Txn (List Act) := do
    let d ← Txn.slice [Sels.agent a, Sels.owned a, Sels.metas ["ctx:" ++ a], Sels.lastEv a "compact"] [.msg]
    let (d', acts) := Compact.pass i comms a d        -- pure
    Txn.exec (slicePlan d d'); pure acts
  ```
  `runActs : List Act → m Unit` is the only place a pass sends. Effects become data only for watchd's outputs, a
  small closed set (about 20 call sites). Reads (git, `ps`, `hc ls`) are inputs and belong in the gather step. Long
  sequential flows (`Spawn.spawnE`, `runRemote`) stay as they are: each step needs the last one's result.
- **Buys**: the stale-closure shape cannot be written, since the decision reads the row inside the transaction. Pass
  logic is testable as a table with no fake hc and no sleeps. For #82: the proofs doc's §3.7 lists only the *named*
  watchd steps; the inline lambdas of seven passes each still need a `Preserves` lemma (the legacy `Proofs/Crash.lean`
  had 87 `X.*`/`K.*` lemmas, one per lambda). One named pure step per pass is about ten. The clock hypothesis
  `∀ w, M.now w ≤ t` becomes a hypothesis on one value.
- **Cost**: L alone (10 passes, about 600 lines). The CLI suites should stay green unchanged.
- **Conflicts**: #77 must touch every one of the 92 sites. Do this **with #77**: converting each lambda to a `Txn`
  one for one and restructuring later is the same edit twice. #75's `plan` (a gather step for swarms and repos) fits.

### B2. Statements and conditions typed by the schema

- **Where**: `Db/Plan.lean:38-44` and `Db/Txn.lean:11-17`:
  ```lean
  inductive Stmt
    | del (t : String) (ks : List String) (k : List Val)
    | upd (t : String) (ks : List String) (k : List Val) (cs : List String) (vs : List Val)
    | ins (t : String) (cs : List String) (vs : List Val)
  inductive Cond | eq (c : String) (v : Val) | …
  ```
  and the scoping by string match, `Real.lean:205-222`:
  ```lean
  | .ins "meta" cs vs => match vs with
    | [.text "comms", v] => .upd "swarm" ["name"] [.text sc.swarm] ["comms"] [v]
  | .upd t ks k cs vs => if ["lock", "ci", "workspace"].contains t then .upd t (ks ++ ["repo"]) … else .upd t ks k cs vs
  ```
- **Now**: tables are named twice (`Table`, an enum; `Row.table : String`) with no function between them. Columns are
  strings in four places that must agree (the `create table` text, `Row.cols`, the `col v i` indexes of `dec`,
  `columns`), and the proofs doc adds a fifth (`freshDb`). A misspelt column in a `Cond` is an SQL error in `Real` and
  a silent "no row matches" in the model (`Row.cell` gives NULL for a column the row lacks, `Db/Txn.lean:61-62`), so
  model and SQLite part exactly where a typo is. Which tables are scoped is said three times in `Real.lean`. Today 1
  site outside `Real.lean` builds a `Stmt` by hand and 20 build a `Cond`; #70-#73 and #77 add more.
- **Proposed**: a typed layer above; today's `Stmt` stays as the lowered form that `Stmt.run` gives meaning to.
  ```lean
  /-- A column of row type `α` holding `τ`. -/
  structure Col (α : Type) (τ : Type) where
    name : String
    get : α → τ
    set : τ → α → α
  inductive Cond (α : Type)
    | all
    | eq [ToVal τ] (c : Col α τ) (v : τ)
    | gt [ToVal τ] (c : Col α τ) (v : τ)
    | null (c : Col α (Option τ))
    | and (a b : Cond α) | or (a b : Cond α)
  inductive Write
    | ins [Row α] (r : α)
    | put [Row α] (r : α)                                  -- by key, every other column
    | del [Row α] (k : Key α)
    | setIf [Row α] (k : Key α) (f : α → α) (c : Cond α)   -- the guarded update
    | log (e : Event)
  def Write.lower (sc : Scope) : Write → List Stmt         -- today's scopeStmts, by cases on the row type
  ```
  A `Col` is needed only for the ~15 columns conditions name; `put` covers the rest.
- **Buys**: in the proofs doc's §3.3, `Stmt.Plain` is the image of `lower`, so the `X.plain` lemmas (one per command,
  about 70 in §3.7's list), `update_plain` and the `hp : st.Plain` hypotheses of `abs_run`, `onSql_refines`,
  `isolation` and `preserves_of` go. `CondClass` holds of every `Cond α` by `ToVal`. `execIf_upd`'s
  `(Row.setCells cs vs x).getD x` becomes `f x`, total. The typo divergence cannot be written.
  **To confirm in #79**: `scopeStmts_inScope` (§3.8) is stated for any plain statement, but `scopeStmt` leaves
  `.upd "agent"` and `.del "agent"` unscoped (`Real.lean:220-222`), so a keyed update of another swarm's agent row by
  name is not in scope and the lemma as written looks unprovable. `lower` by cases on the row type has to say what an
  agent update in scope means.
- **Cost**: M-L (`Db/Rows.lean`, `Db/Txn.lean`, `Db/Sels.lean`, the scoping, the 21 sites plus what #70-#77 add).
- **Conflicts**: every converting task writes statements; do not start under them. It fits **#99**, which already
  moves the scoping into a pure `Db/Scope.lean`. After #79 the lemmas are proved against strings and the value is low.

### B3. `Scope` is a sum written as two strings and a flag

- **Where**: origin/main `Store.lean:17-23`:
  ```lean
  structure Scope where
    swarm : String
    repo : String
    every : Bool := false
  def Scope.metaName (sc : Scope) : String := if sc.swarm == "" then "repo:" ++ sc.repo else sc.swarm
  ```
  and `Db/Txn.lean:67-71` (`Sel.inScope : Bool := true`).
- **Now**: four scopes are in use (a swarm in a repo; a repo's own; a repo with every swarm's agents; the machine),
  told apart by empty strings. Whether a read is machine-wide is a defaulted `Bool` on each `Sel`. The proofs doc
  carries the consequences as hypotheses: `hev : sc.every = false ∨ ¬ t.InsertsAgent` on four theorems, and
  `Txn.WideTables : Txn α → List Table` (§3.5), which is not computable as declared: `Txn.read` holds a continuation
  `Db → Txn α`, so the tables a transaction may read wide depend on every `Db`.
  **To confirm in #73**: `sharedTxn` (`Cmd/Hook.lean:85`) looks for another live agent in the same worktree with the
  default scope, so only in the caller's swarm. A worktree belongs to a repo. The lock read six lines above was made
  wide for that reason (proofs doc §1.2 is the same shape).
- **Proposed**:
  ```lean
  inductive Scope
    | swarm (s : SwarmName) (repo : String)     -- a command's
    | repo (repo : String) (agents : Bool)      -- watchd's per-repo loop
    | machine
  /-- A transaction that may read the tables `wide` machine-wide. -/
  inductive Txn (wide : List Table) (α : Type) where
    | done (a : α)
    | read (ss : List Sel) (ws : List { s : Sel // s.table ∈ wide }) (next : List Table) (k : Db → Txn wide α)
    | write (p : List Stmt) (k : Txn wide α)
    | guard (s : Stmt) (c : Cond) (k : Bool → Txn wide α)
  ```
  A command's type then reads `Txn [] α` (sees only its scope) or `Txn [.agent] α` (the lock hook).
- **Buys**: `Txn.WideTables` is the index, so `onSql_refines` needs no recursion through continuations. For
  `Txn [] α` the read half of isolation, which §3.8 does not state, is a corollary: equal views give equal answers. An
  unscoped read in a scoped command shows in the command's signature, in review.
- **Cost**: S-M for the `Scope` inductive (about 15 uses of `sc.every`/`sc.swarm == ""`/`metaName`). M for the index
  (`Db/Txn.lean`, `Real.runTxnOn`, `RecM`'s store, 32 `Store.run`/`view` sites, more after #77). Indexing `Store`
  itself by scope kind would remove `hev`, but is L: not proposed unless `hev` proves painful.
- **Conflicts**: #75 just landed this `Scope`; #77 and #99 rewrite its users. Do the inductive in **#99**, and decide
  the `Txn` index before #79 states `onSql_refines`.

### B4. `Task`: a phase with per-state payloads, flat columns kept

- **Where**: `Db/Rows.lean:76-85` (`state : Status`, `owner`, `lease_until`, `evidence`, … all `Option`), and the
  agreement as a separate proposition, `Spec/Board.lean:29-30`:
  ```lean
  def Task.Owned (t : Task) : Prop :=
    (t.state = .claimed → t.owner.isSome) ∧ (t.state = .open → t.owner = none)
  ```
- **Now**: six states and eight columns that belong to some of them. 20 record updates write them, each choosing by
  hand what to set and clear, and they disagree: to *open*, `reopenF` keeps `question` (`Db/Tasks.lean:184`) while
  `reopenFromF` (`:187`) and `Agents.release` clear it; to *dropped* (`Db/Tasks.lean:530`), `owner` is cleared but
  `question`, `land_sha`, `lander` stay. Consequences:
  - a dead branch: `Db/Notes.lean:51` sends a note on a dropped task to "whoever did it" by matching `t.owner`, but
    the only writer of `dropped` nulls the owner, so the note always goes to the communicator;
  - runtime re-checks of what the state should guarantee: `Db/Tasks.lean:431`, `Lib/Watchd.lean:95` and `:121`
    (`r.owner.getD "nil"`, then a message to `nil`);
  - 96 tests of the form `r.state = .claimed || r.state = .blocked` are not exhaustive matches, so adding `landing`
    did not ask each to decide. **To confirm**: `Lib/Ci.lean:299-300` (`openRed`: open, claimed or blocked) skips a
    red task in `landing` when main goes green.
- **Proposed**:
  ```lean
  def Evidence := { s : String // strip s ≠ "" }
  inductive Phase
    | «open»
    | claimed (owner : String) (lease : Int)
    | blocked (owner : String) (question : String)
    | landing (owner : String) (sha : String) (lander : Option String) (since : Int)
    | done (evidence : Evidence) (doer : Option String)
    | dropped (doer : Option String)
  structure Task where
    id : Nat
    phase : Phase := .open
    title : Option String := none
    …                                       -- the columns no state owns
  def Task.state (t : Task) : Status := …   -- derived, so the 96 state tests still compile
  def Task.owner (t : Task) : Option String := …
  ```
  `enc` writes the same 34 columns; `dec` refuses `claimed` with no owner. Transitions become one function per edge.
- **Buys**: `Board.Inv`'s `Task.Owned` clause and `DoneEv` hold of every decoded row. With `Good` (proofs doc §3.2)
  that gives `Good d → Board.BInv (abs sc d)` once, so `WF.board` (§3.6) is a lemma, not a field, and the `BInv` third
  of `ViewPres` drops out of all 22 `P.Tasks.*`/`P.Queue.*` obligations. `done_has_evidence` becomes a projection. The
  three re-checks and the messages to `nil` go.
- **Cost**: M-L: the codec, the 20 write sites in 9 files, `Spec/Board.lean` and the `Challenge.lean` copies (they
  compile through the projections, but the challenged text changes meaning and must be re-read). **Honest limit**: a
  statement that updates only some columns can produce a row that does not decode; `Row.setCells` then returns `none`
  and the model leaves the row alone while SQLite would write it (`Db/Txn.lean:173-175`). So guarded transitions need
  B2's typed `setIf`. Without B2 this moves work and removes none.
- **Conflicts**: #70 rewrites the same write sites and #74 adds `task_repo`. After #77, before #80, with B2.

### B5. Message addressee and sender are sums stored as text

- **Where**: `Db/Rows.lean:186-187` (`frm`, `dest : Option String`); matched by literal at `Db/Msgs.lean:14,25,43`,
  `Lib/Msgs.lean:20`, `Cmd/Msgs.lean:66,69`, `Db/Notes.lean:85,93,98`. And `Cmd/Hook.lean:181`:
  ```lean
  let (db, _) := Msgs.post db t "swarm" ((commsName db envComms).getD "") s!"{name} stopped though not endable …"
  ```
- **Now**: `dest` is an agent, `@all`, or `#N`; `frm` is an agent, `human` or `swarm`. `Msgs.post db now frm dest body`
  takes three strings in a row. With no communicator the stop hook stores a message to `""` that nobody can read.
- **Proposed**:
  ```lean
  inductive Dest
    | agent (n : AgentName)
    | all (swarm : SwarmName)     -- #71's `@<swarm>`
    | task (id : Nat)             -- held for the task's next owner
  def Msgs.post (db : Db) (now : Int) (frm : Who) (dest : Dest) (body : String) … : Db × Nat
  ```
  with `Dest.text`/`ofText` as the codec. A caller with an `Option String` communicator must match before it posts.
- **Buys**: the `""` addressee cannot be built. `ToIt` (proofs doc §1.4, §3.7) is a match on `Dest` with no string
  injectivity argument.
- **Cost**: M (about 70 `post`/`say` sites, 45 of them behind `say`'s one signature; `Spec/Msgs.lean`).
- **Conflicts**: **#71** has to touch every `"@all"` site anyway; do it there or directly after, before #81. Needs A2.

### B6. Which swarm a command acts on is decided by hidden IO in the store

- **Where**: `Real.lean:89-145` (`repoHere`, `hcSwarmLabel`, `resolveSwarm`, `useSwarm`); `Cmd/Agents.lean:101,107`:
  ```lean
  Store.txn [] fun db => (db, ())  -- resolves the swarm (or refuses), which the store exports as $SWARM
  let sw ← env "SWARM"  -- exported by the store once its first transaction resolved it
  ```
- **Now**: the first `Store.*` call of a process runs the spec's §2 resolution order with raw `IO.getEnv`,
  `IO.Process.output` and SQL, outside `Env`/`Proc`/`Git`; it may print and exit, and sets an environment variable
  that six call sites read back. `join` runs an empty transaction to trigger it and repeats part of the rule. `RecM`'s
  store has no scope, so no theorem and no fake-world test covers the rule. Since #75 the scope is ambient in two
  places, a `Ref` and the working directory.
- **Proposed**: split the rule from its reads, and resolve at dispatch.
  ```lean
  structure Who where              -- what the rule reads
    flag : Option String           -- $SWARM (`--swarm` sets it)
    ofAgent : Option String        -- the swarm of $SWARM_NAME's row
    label : Option String          -- hc's `swarm=` label on $HC_TERMINAL_ID
    known : List String
    live : List String
  def pickSwarm (w : Who) : Except String String
  ```
  (Name it other than A2's `Who`.) `Dispatch` resolves once and runs the command under `Scoped.within sc`.
- **Buys**: the five-rule order is a pure function with a table test. "Lands in the wrong swarm" is the bug class the
  spec's §1 was written to end, and this rule is the one piece of the new design no test reaches without a real
  machine. Isolation (§3.8) is about the scope a command runs in; that the binary picks the scope §2 names becomes
  `pickSwarm`'s spec.
- **Cost**: M. **Conflicts**: the read side of proofs doc §1.1's move; **with #99**.

### B7. `swarm state --json` has no single definition

- **Where**: `Cmd/State.lean:383-571` (one 189-line function; 37 object literals in the file), `Lib/SwarmsView.lean`
  (12 more), and the decoder specs in `swarm/herdr/mods/rw-rail/tree.js:53-103`.
- **Now**: the keys are string literals on both sides, with no version field. The shape is defined only by the control
  flow of `state`, which reads ten tables and then calls hc and git per agent while appending JSON fields.
  `--view swarms` re-implements `Queue.staffing` and the hung test over eight raw selects through `Sys.sqlAt`
  (`Lib/SwarmsView.lean:78`, a fourth raw reader of the swarm db beside the three of proofs doc §1.1). And the mods
  parse human CLI text in five places, for example the new task's id from `task add`'s stdout:
  ```js
  const id = /task #(\d+)/.exec(r.stdout)?.[1];        // swarm/herdr/mods/rw-swarm/main.js:1362
  ```
  and the sentence "auto-spawn holding:". **To confirm**: `keyOf` in the JS has drifted from `Cost.key`, so a command
  under `timeout` gets no memory forecast.
- **Proposed**: wire structures in one module, each with its encoder, and a `"v"` field. `StateIn` (the slice plus
  what hc and git said) gathered first; `stateJson : StateIn → View → Json` pure. `task add --json` and JSON fields
  for the five parsed texts.
- **Buys**: golden tests of the JSON on literal inputs; a reworded CLI sentence cannot break a panel; one definition
  for the interface with a consumer in another language.
- **Cost**: M. **Conflicts**: #77 rewrites `state`'s read and #99 moves the machine tables: with or after them.
  #91/#101 edit the same JS files and should agree the schema first.

### B8. The slice a decision reads is typed `Db`

- **Where**: `Db/Txn.lean:88-102` (`Db.slice`: `taskNext := if next.contains .task then db.taskNext else 0`), `:109`;
  hand stitching at `Cmd/Hook.lean:80,92` (`{ d with agents := a.agents }`).
- **Now**: the spec says `decide : Slice → Plan × α`; the code passes a `Db` whose unread tables are `[]` and whose
  unread next ids are 0. A decision that reads a table its selects did not load gets the empty answer, which fails
  open: `Locks.others` on a slice without agents says no lock is held. The table lists of the 60 `Store.txn`/`step`
  sites in four command files were compared with what their steps read and none is missing. This is a hazard for the
  conversions, not a present bug.
- **Proposed**:
  ```lean
  structure Slice (ts next : List Table) where
    private db : Db
  def Slice.agents (s : Slice ts n) (h : Table.agent ∈ ts := by decide) : List Agent := s.db.agents
  /-- An old-shape step with the tables it reads, declared once next to it. -/
  def Slice.run (s : Slice ts n) (f : Step need α) (h : need ⊆ ts := by decide) : Db × α := f.fn s.db
  ```
- **Buys**: the table half of the frame lemma `OnSlice` (proofs doc §3.4) is checked by the elaborator for every
  command. A step's `need` is stated once, so `X.refines` cannot be proved for one table list while the CLI passes
  another.
- **Cost**: M (a `need` for each of the ~70 steps, which the proofs must list anyway). **Conflicts**: after #77, when
  `Store.txn` and its table lists are gone; before #80.

## 5. Tier C: smaller

- **C1. Stay conditions** (`Db/Agents.lean:163-216`). The condition is validated, stored as text, then re-parsed by
  prefix with `getD 0` defaults and a last `else none`, which for a stay means "never wakes".
  `inductive StayCond | job (id : String) | task (id : Nat) | msg (frm : String) | ci | time (h : Fin 24) (m : Fin 60)`
  with `parse?`/`text`; `stayMet` becomes a total match. S, two files, with #72.
- **C2. `GitRef`** (`Util.lean:122`). All 8 uses are `(GitRef.parse? b).isSome`/`.isNone`: the value is thrown away,
  bases are stored as text and re-checked at some uses only (`Bases.remoteRef`, `ref`, `baseFor` take them unchecked).
  Make `AddArgs.base : Option GitRef` and `Bases.*` take `GitRef`. S-M, 19 call sites. After #74.
- **C3. One `Agents.endRow`**. Four writers of "the agent ended" disagree: `Db/Spawn.lean:57` sets `ended` but leaves
  `status`, `stay`, conflicts and pair keys, though its doc says "as every end does"; `Db/Agents.lean:123`,
  `Lib/Lifecycle.lean:275` and `Lib/Watchd.lean:141` set both and release. One function, four callers. S, with #72.
  An `Agent` inductive of live/ended is not proposed: no WF clause is about an agent's own fields, readers of an
  ended row still want `hc`, `cwd` and `wt`, and `bind` revives rows in place. A status enum
  (`idle | working | blocked | ended`) is worth it only when #72 touches those 35 sites anyway.
- **C4. Lock paths** (`Cmd/Hook.lean:124-125`, `Cmd/Locks.lean:55-58`). `repoRel` returns the toplevel a path is in
  and both `swarm lock` and the edit hook drop it; the store fills `repo` from the process's folder. **To confirm in
  #73**: a file of repo B edited from a session in repo A is checked against A's locks by its B-relative path.
  `structure InRepo where repo : String; rel : String`, and `lockTxn` takes it. S-M.
- **C5. claim**. (a) A request's size has three encodings (`Ask.cores : String` with "all" or a count; `Option Int`
  plus an ignored `mem`; flags parsed in `claim/Main.lean`, `Cmd/Run.lean` and `Claims/Cli.lean`, with GiB→KiB written
  three times): one `Size` inductive. (b) `Try` duplicates `Admit.Answer`, `Claim`/`Ticket` exist twice, and
  `parseTry` and `Answer.line` are unrelated: one type and a round-trip `#guard`. (c) `WF` is a 15-way conjunction
  taken apart by position at about 15 sites in `claim/Claims/Proofs.lean`: two `structure … : Prop`. (d)
  `Claims/Util.lean`'s eight functions are textually identical to `SwarmLean/Util.lean`'s and both are in swarm's
  environment: `export` them from one. Toolchains are equal (v4.35.0). (e) **To confirm with a test**: a claim has no
  id in `ls` or the model, so a second `try` under a held id is outside the model. (f) `cap` is a read-modify-write
  outside the lock.
- **C6. Say what "the model" is.** Both sw-global docs say "the model" for swarm-lean's `Db` and never name
  `swarm/model`. That is the right target: `abs : SDb → Db`, one hop. `Swarm.State` is not a function of the db (ghost
  fields, clock, processes, git). But `swarm/model` has one swarm, one repo and one communicator, and already lacks
  `landing`, hold/queue, reuse offers and compaction. Decide: freeze it with a README paragraph saying which parts
  still describe the code (S), or give it swarms and repos (about 150 lines in `Model.lean`, a guessed 2-3k lines of
  proof churn). The freeze is recommended until A5's differential test exists. The model's `Sql.lean` and `Iso.lean`
  (1,583 lines) describe the deleted Lua's SQL and connect to nothing: retire them. Put the wording in #78.
- **C7. Duplicates.** `dbPath` ×3; the hc swarm label ×2; a `git` wrapper ×3; `num` ×3 (they differ); `join`/`dirname`
  ×2 (they differ on `//a`); the hung test ×3; JSON escapers ×2; `git worktree list --porcelain` parsed five times
  next to the pure `wtLines` (`Lib/Watchd.lean:218-223`); five hand-rolled fuel-bounded breadth-first walks
  (`Lib/Watchd.lean:63-74`, `Lib/Run.lean:103-117`, `Lib/Cost.lean:354-361`, `Lib/Lifecycle.lean:120-135`) that one
  `reach (next : α → List α) (fuel : Nat)` replaces. S each; fix when the file is next touched.
- **C8. Proof noise.** Task ids are `Nat` in rows and `Int` in about 35 step signatures, with 78 casts and two
  `.toNat` truncations (a negative id reads as task 0). `--lease` travels as text into the decisions and the `Spec`
  commands, so each step has a "bad duration" branch: parse it in `Args`. Events are free text with per-kind
  conventions; `spawn` has two shapes in which `agent` means different things (`Lib/Spawn.lean:181` vs
  `Lib/Watchd.lean:635`): an inductive for the ~12 kinds decisions read back. M each, no bug found, after #70/#77.

## 6. Considered and not proposed

- **Agent names typed through every signature** (A2's step B): about 200 signatures, and no swapped argument found.
- **`Agent` as an inductive of live/ended**, and **`Store` indexed by scope kind**: see C3 and B3.
- **A typed `Parsed`** (`Args.lean:77`): 171 reads by key; all 96 distinct keys match declared targets. No typo today.
- **Re-typing the model's `State`** as indexed families: it would save four length invariants against 1,267 accessor
  uses, the Frame simp set and three of `STYLE.md`'s rules.
- **A `Ledger cap` type in claim** carrying "sum of claims ≤ capacity": that is not an invariant, since `cap` and
  `reserve` can be set below what is already claimed. `Nat` for sizes would delete only the non-negativity lemmas
  (60-90 of 795 lines).
- **Narrowing the `variable` blocks** that give every definition every class: both monads implement every class, and
  Lean has no parametricity, so a narrower signature gives no theorem. The gain is in removing `m` (B1, A8), not in
  narrowing it.
- **A `RepoPath` wrapper**: `Scope.repo` and `Workspaces.main` both realpath git's first worktree, so the two sources
  of a repo key agree.
- **A third shared Lean package** for `Util`, and **merging the three `Audit.lean` copies**: low value.

## 7. Sequencing, and the held tasks

Nothing here should start under #70-#73 or #77: they are rewriting the same call sites.

- **Fold into the in-flight task** (noted on each): A1, C1, C3 → #72; B5 → #71; C4 and B3's `sharedTxn` check → #73;
  B1 → #77; B2, B3, B6 → #99; C6's wording → #78.
- **Any time, independent**: A3, A5 (items 1-2), A6 (bar the watchd moves), A8, C5.
- **Before #79 fixes the statements**: A7, B2, B3.
- **Between #77 and #80**: B4, B8.

The twelve proposals added to the board, each held as "architecture proposal: awaits the user": A1-A8 and B1-B4 as
one task each, with B5-B8 and tier C left in this document until the first twelve are decided.

## Appendix A: proposed layers for `layering.sh`

An import may go to a lower rank.

| Rank | Layer | Modules today | May use |
|---|---|---|---|
| 0 | Util | `Util`, `Lib.Re`, `Lib.Json`, `Lib.Difflib`, `Args`, new `Sqlite.Val`, new `Proc` | Lean, Std |
| 1 | Rows and pure db functions | `Db`, `Db.*`, `Spec.Data` (to become `Types`), `SwarmModel.Glob`, `SwarmModel.Decide.Rows` | no effect class, no `IO` |
| 2 | Interfaces | `Store`, `World`, `Sys` | classes only |
| 3 | Lib, pure | `Lib.Merge` and any `Lib` file with no effect class | ranks 0-1 |
| 4 | Lib, effectful | the other 16 `Lib.*` | the classes of rank 2 |
| 5 | Command base | `Cmd`, `Cmd.*Help` | |
| 6 | Commands | `Cmd.{Agents,Ci,Compute,Cost,Hook,Locks,Msgs,Pr,Run,State,Tasks,Watchd}`; none imports another | ranks 0-5 |
| 7 | Dispatch | `Dispatch` | |
| 8 | Effects | `Sqlite` (FFI), `Real`, `RealSys` | imported only by rank 9 and tests |
| 9 | Entry points | `Main`, `Report`, `TestMain`, `HarnessRetroMain`, `SwarmLean` | |
| side | Herdr tools, HarnessRetro | `SwarmLean.Herdr.*`, `HarnessRetro.*` | rank 0 only |
| spec, top, tests | as `layering.sh` has them | | |

## Appendix B: edges that break the table today

| Edge | Import at | Rule broken | Fix |
|---|---|---|---|
| `Cmd.Watchd → Cmd.Agents`, `Cmd.Hook`, `Cmd.Msgs` | `SwarmLean/Cmd/Watchd.lean:1-3` | command imports command | A6 |
| `Cmd.Hook → Cmd.Locks` | `SwarmLean/Cmd/Hook.lean:1` | command imports command (`repoRel`) | A6, C4 |
| `Lib.Merge → Lib.Ci` | `SwarmLean/Lib/Merge.lean:1` | pure Lib imports effectful Lib, and uses nothing of it | import `Lib.Json` |
| `HarnessRetro.Hr → RealSys` | `HarnessRetro/Hr.lean:1` | side binary imports effects, and through it the store | A6 |
| `Db.Rows → Sqlite` | `SwarmLean/Db/Rows.lean:1` | pure rows import the FFI module | A6 |
| `Db.Msgs → Spec.Data`, `Lib.Machine → Spec.Data` | `SwarmLean/Db/Msgs.lean:2`, `SwarmLean/Lib/Machine.lean:4` | implementation imports from `Spec/` | `Types` |
| `Spec.Data → Lib.Re` | `SwarmLean/Spec/Data.lean:2` | regex engine in the spec layer, for one function | `runDirOk` without it |
| `Lib.Swarms → Db.Schema`, `Lib.SwarmsView → Db.Plan` | `SwarmLean/Lib/Swarms.lean:2`, `SwarmLean/Lib/SwarmsView.lean:4` | Lib runs its own SQL on the swarm db | #99, B7 |
| `World → Store`, `Cmd → World`, `Db.Locks → Db.Tasks`, `Lib.Lifecycle → Lib.Agents` | line 1 or 2 of each | unused | drop |
| `Report → Lib.Hook` | `Report.lean:3` | entry point pulls a hook module for one string escaper | C7 |

Through an interface, not an import: the 26 raw `git` argv of A7, and four `Sys.sqlAt` calls on the swarm db
(`Lib/Swarms.lean:41,52,60`; `Lib/SwarmsView.lean:78`).
