import Claims.Admit

/-! What the proofs assume about the world (sw-compute-backfill.md §7): each assumption is a definition that a theorem
takes as a hypothesis, tagged `(claims_spec: …)` with the `claim-tests` cases that test it; check.sh refuses a tag that
names no case of `claim-tests --list`. -/

namespace Claims

/-- What the `mkdir` lock, with its guarded break of a stale one, gives, assumed and tested, not proved: when processes ran the
tries `ran` (each with the answer it got) at once on a ledger reading `m0` and left `final`, the tries one after another in
some order give those answers and `final` (the shape of swarm's `Atomic`). Not tied: a breaker and a holder both
crashing (the comment on `lock`) (claims_spec: lock_exclusive). -/
def LockExclusive (m0 : Admit.Machine) (ran : List (Admit.Req × Admit.Answer)) (final : Admit.Machine) : Prop :=
  ∃ order : List (Admit.Req × Admit.Answer), order.Perm ran ∧ Admit.tries m0 (order.map (·.1)) = (final, order)

/-- The shipped script's admission, assumed and tested, not proved: on a machine and ledger that read as `m` (after
`clean`, under the lock), `try` prints `(Admit.decide m r).line` and leaves `Admit.after m r`. Not tied: `clean`'s liveness reading, and the measurement (`/proc/stat`,
`vm_stat`, `/proc/meminfo`) (claims_spec: admit_awk, script_try). -/
def ScriptAdmits (run : Admit.Machine → Admit.Req → Admit.Answer) : Prop :=
  ∀ m r, Admit.WF m r → run m r = Admit.decide m r

end Claims
