import SwarmLean.Spec.Cross
import SwarmLean.Spec.Machine
import SwarmLean.Db.Locks
import SwarmLean.Lib.Watchd

/-! The spec layer's definitions that run the code (board #216): each area's transactions as the CLI's own step
functions, and what the sweep checked of a worktree before removing it. They name the implementation, so the challenge
(`Challenge.lean`) cannot import this module: it holds a copy of everything below, word for word, after its holes, and
Comparator checks that the copy is this module's definitions, constant for constant. Each is an `abbrev`: a `def`'s
reducibility hint is its height, one more than the highest constant it names, so it would differ between the challenge,
where the code is holes of height 1, and here. -/

-- BEGIN CHALLENGE COPY
namespace SwarmLean
open Tasks

/-- A command's whole effect on the db, and its answer: the CLI's own step functions. -/
abbrev Cmd.step : Cmd → Db → Db × Result
  | .add c a, db => ((Tasks.add c a db).1, .added (Tasks.add c a db).2)
  | .claim c i l, db => ((Tasks.claim c i l db).1, .claimed (Tasks.claim c i l db).2)
  | .release c i af, db => ((Tasks.release c i af db).1, .released (Tasks.release c i af db).2)
  | .land c i s l, db => ((Tasks.land c i s l db).1, .landed (Tasks.land c i s l db).2)
  | .unland c i w, db => ((Tasks.unland c i w db).1, .unlanded (Tasks.unland c i w db).2)
  | .board, db => (db, .board db.tasks)

end SwarmLean

namespace SwarmLean.Board
open Tasks

/-- A command's effect on the db and whether it succeeded: the CLI's own step functions. -/
abbrev TCmd.step : TCmd → Db → Db × Bool
  | .add c a, db => ((Tasks.add c a db).1, (Tasks.add c a db).2.toBool)
  | .claim c i l, db => ((Tasks.claim c i l db).1, (Tasks.claim c i l db).2.toBool)
  | .after c i l, db => ((Tasks.after c i l db).1, (Tasks.after c i l db).2.toBool)
  | .priority c i p, db => ((Tasks.priority c i p db).1, (Tasks.priority c i p db).2.toBool)
  | .renew c i l, db => ((Tasks.renew c i l db).1, (Tasks.renew c i l db).2.toBool)
  | .done c i e, db => ((Tasks.done c i e db).1, (Tasks.done c i e db).2.toBool)
  | .block c i q, db => ((Tasks.block c i q db).1, (Tasks.block c i q db).2.toBool)
  | .unblock c i a, db => ((Tasks.unblock c i a db).1, (Tasks.unblock c i a db).2.toBool)
  | .release c i af, db => ((Tasks.release c i af db).1, (Tasks.release c i af db).2.toBool)
  | .edit c i a, db => ((Tasks.edit c i a db).1, (Tasks.edit c i a db).2.toBool)
  | .drop c i, db => ((Tasks.drop c i db).1, (Tasks.drop c i db).2.toBool)
  | .land c i s l, db => ((Tasks.land c i s l db).1, (Tasks.land c i s l db).2.toBool)
  | .unland c i w, db => ((Tasks.unland c i w db).1, (Tasks.unland c i w db).2.toBool)
  | .board, db => (db, true)

/-- The db after `cs` from `db`. -/
abbrev run (db : Db) (cs : List TCmd) : Db := (replay TCmd.step db cs).1

/-- Each command of `cs`, from `db`, with whether it succeeded. -/
abbrev trace (db : Db) (cs : List TCmd) : List (TCmd × Bool) := (replay TCmd.step db cs).2

end SwarmLean.Board

namespace SwarmLean.Locks
open Agents

/-- A command's whole effect on the db, and its answer: the CLI's own step functions. -/
abbrev LCmd.step : LCmd → Db → Db × LResult
  | .lock c p r l, db => ((Locks.lock c p r l db).1, .locked (Locks.lock c p r l db).2)
  | .unlock me p now, db => (Locks.unlock me p now db, .unlocked)
  | .leave n now, db => (Agents.leave db n now, .left)
  | .join n cwd hc model r now, db => match notHuman n with
    | .error e => (db, .joined (.error e))
    | .ok () => ((Agents.bind db n cwd hc model r now).1, .joined (Agents.bind db n cwd hc model r now).2)
  | .task c, db => ((c.step db).1, .task (c.step db).2)

end SwarmLean.Locks

namespace SwarmLean.Inbox
open Msgs

/-- A transaction's effect and the messages it showed: the CLI's own step functions. -/
abbrev MCmd.step : MCmd → Db → Db × List Msg
  | .post now f d b u k, db => ((Msgs.post db now f d b u k).1, [])
  | .read n, db => ((take n id db).1, (take n id db).2.2)
  | .deliver n b, db => ((deliverStep n b db).1, (deliverStep n b db).2.1)
  | .typed n i, db => ((typedStep n i db).1, (typedStep n i db).2.2)
  | .other f _, db => (f db, [])

/-- The db after `cs` from `db`. -/
abbrev run (db : Db) (cs : List MCmd) : Db := (replay MCmd.step db cs).1

/-- Each transaction of `cs`, from `db`, with what it showed. -/
abbrev trace (db : Db) (cs : List MCmd) : List (MCmd × List Msg) := (replay MCmd.step db cs).2

end SwarmLean.Inbox

namespace SwarmLean.Cross
open Board Agents

/-- Each transaction's effect on the db: the CLI's own steps, as each area's theorems run them. -/
abbrev XCmd.step : XCmd → Db → Db
  | .task c, db => (c.step db).1
  | .post now f d b u k, db => (Inbox.MCmd.step (.post now f d b u k) db).1
  | .read n, db => (Inbox.MCmd.step (.read n) db).1
  | .deliver n b, db => (Inbox.MCmd.step (.deliver n b) db).1
  | .typed n i, db => (Inbox.MCmd.step (.typed n i) db).1
  | .lock c, db => (c.step db).1
  | .end_ n hc force by_ now, db => (Lifecycle.endStep n hc force by_ now db).1
  | .reapTask r t now, db => (Watchd.reapTask r t now db).1
  | .reapLock l t now, db => (Watchd.reapLock l t now db).1
  | .reapGone n h t, db => (Watchd.reapGone n h t db).1

/-- The db after `cs` from `db`. -/
abbrev run (db : Db) (cs : List XCmd) : Db := cs.foldl (fun d x => x.step d) db

/-- The db after the first `k` transactions of the run `r` from `db`. -/
abbrev at_ (db : Db) (r : Nat → XCmd) : Nat → Db
  | 0 => db
  | k + 1 => (r k).step (at_ db r k)

end SwarmLean.Cross

namespace SwarmLean.SweepProofs

variable {M : Tools}

/-- What the sweep, run from state `s0`, checked of worktree `x` of the main checkout `m` before removing it, `L` the
calls it made before: `x` is listed (the realpath of a `worktree` line of the `git worktree list` it ran first, `m`
the first such line's), not the main checkout, used by no live agent of the db (realpaths read on one machine `w`), no process sat in it when
`Machine.cwds` read, untouched for `SWEEP_IDLE` and `status` clean (both read on one machine `wk`), and `landed` found
it landed on the refs of the protected bases. -/
structure Gate (s0 : Rec M) (m x : String) (L : List (M.World × Call)) : Prop where
  main : ∃ first, (lsLines s0.w).head? = some first ∧ m = realW (M.after s0.w lsArgv none) (first.drop 9).toString
  notMain : x ≠ m
  listed : ∃ e ∈ Watchd.wtLines (lsLines s0.w).tail, ∃ w : M.World, x = realW w e.1
  unused : ∃ w : M.World, ∀ p ∈ ((Agents.live s0.db).flatMap fun a => [a.wt.getD "", a.cwd.getD ""]).filter (· != ""),
    Watchd.inside (realW w p) x = false
  noProc : ∃ (s : Rec M) (cs : List (Int × String)), s.log <+: L ∧ (Rec.go (Machine.cwds : RecM M _) s).1 = .ok (some cs) ∧
    ∀ c ∈ cs, Watchd.inside (realW (Rec.go (Machine.cwds : RecM M _) s).2.w c.2) x = false
  idle : ∃ wk t, (wk, .git ["-C", x, "rev-parse", "--absolute-git-dir"] none) ∈ L ∧
    (wk, .cmd ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none) ∈ L ∧
    (∃ st, (M.out wk ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none).bind
      (fun o => if o.code == 0 then some o.stdout else none) = some st ∧ strip st = "") ∧
    (∃ st : Rec M, st.log <+: L ∧ t = M.now st.w) ∧
    Watchd.SWEEP_IDLE ≤ t - lastAt wk x (M.git wk ["-C", x, "rev-parse", "--absolute-git-dir"] none)
  landed : ∃ s sp sb : Rec M,
    (Rec.go (Lifecycle.landed x (Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf s0.db (some m) : RecM M _) sp)
      (some m) : RecM M _) sb) (some m) : RecM M Bool) s).2.log <+: L ∧
    (Rec.go (Lifecycle.landed x (Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf s0.db (some m) : RecM M _) sp)
      (some m) : RecM M _) sb) (some m) : RecM M Bool) s).1 = .ok true

/-- The worktree `x` of main checkout `m` passed `Gate` on the calls `L` before its removal, in the sweep that started
from some state. -/
abbrev GateAny (m x : String) (L : List (M.World × Call)) : Prop := ∃ sk : Rec M, Gate sk m x L

/-- What a step runs. -/
abbrev Step.run : Step → RecM M Unit
  | .sweep comms dry nl dir => discard (Watchd.sweep comms dry nl dir)
  | .branches main ended prot => Watchd.sweepBranches main ended prot
  | .stop a force by_ => discard (Lifecycle.endAgent a force by_)

end SwarmLean.SweepProofs
-- END CHALLENGE COPY
