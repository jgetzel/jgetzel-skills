import SwarmLean.Assumptions

/-! The spec layer of the code on a machine (board #216): what a recorded run answers, the sweep's command lines and
reads, the steps of a run of sweeps and ends as data, and `Sat`, a postcondition of a monadic run whatever its reads
return. Moved from `Proofs/Sweep.lean`, `Proofs/Keep.lean` and `Proofs/Watchd.lean`. -/

namespace SwarmLean.SweepProofs

variable {M : Tools}

/-- What `x` answers from state `s` when it does not throw (`default` when it does). -/
@[irreducible] def Rec.val [Inhabited α] (x : RecM M α) (s : Rec M) : α := match (Rec.go x s).1 with | .ok a => a | .error _ => default

/-- `git -C main worktree remove wt`. -/
def rmArgv (main wt : String) : List String := ["git", "-C", main, "worktree", "remove", wt]

/-- `p` as `Watchd.real` reads it on machine `w`. -/
def realW (w : M.World) (p : String) : String := (M.realpath w p).getD p

/-- `git worktree list --porcelain`, the sweep's first command. -/
def lsArgv : List String := ["git", "worktree", "list", "--porcelain"]

/-- The lines of what the sweep's `git worktree list` printed, run on machine `w`. -/
def lsLines (w : M.World) : List String :=
  splitlines (((M.out w lsArgv none).bind fun o => if o.code == 0 then some o.stdout else none).getD "")

/-- The later mtime of `wt` and of its git dir's logs/HEAD, `gd` what `rev-parse --absolute-git-dir` printed: the
sweep's "last touched", read on machine `w`. -/
def lastAt (w : M.World) (wt : String) (gd : Option String) : Int :=
  max (max 0 ((M.mtime w wt).getD 0)) ((M.mtime w (joinPath (joinPath ((py (gd.map strip)).getD wt) "logs") "HEAD")).getD 0)

/-- Every worktree removal at or after index `n` of log `l` passed `G` on the calls before it. -/
def GoodFrom (n : Nat) (G : String → String → List (M.World × Call) → Prop) (l : List (M.World × Call)) : Prop :=
  ∀ i w m x, n ≤ i → l[i]? = some (w, .cmd (rmArgv m x) none) → G m x (l.take i)

/-- `gh pr list --head br --state merged …`, landedRef1's last check. -/
def ghArgv (br : String) : List String :=
  ["gh", "pr", "list", "--head", br, "--state", "merged", "--json", "number,headRefOid"]

/-- landedRef1 answering true: a machine it ran a command on has `b` holding `ref`'s changes, or it asked `gh`. -/
def Reached (cwd ref b : String) (l : List (M.World × Call)) : Prop :=
  (∃ e ∈ l, M.Holds e.1 cwd ref b) ∨ ∃ w br, (w, .cmd (ghArgv br) (some cwd)) ∈ l

/-- One step of watchd or the CLI that touches worktrees or branches: a sweep (watchd's, or `--dry-run`), the branch
sweep after it, or ending an agent (`swarm end`, lifecycle's end, hung's). -/
inductive Step
  | sweep (comms : Option String) (dry : Bool) (notLanded : List String) (dir : Option String)
  | branches (main : String) (ended prot : List String)
  | stop (a : Agent) (force : Bool) (by_ : Option String)

end SwarmLean.SweepProofs

namespace SwarmLean.WatchdProofs

/-- Every result `x` can give satisfies `p` (Batteries' `SatisfiesM`): `x` factors through results carrying a proof. -/
def Sat {m : Type → Type} [Functor m] {α : Type} (p : α → Prop) (x : m α) : Prop :=
  ∃ x' : m {a // p a}, Subtype.val <$> x' = x

end SwarmLean.WatchdProofs
