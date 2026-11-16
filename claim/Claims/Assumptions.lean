import Claims.Admit

/-! What the proofs assume about the world (sw-compute-backfill.md §7): each assumption is a definition that a theorem
takes as a hypothesis, tagged `(claims_spec: …)` with the `claim-tests` cases that test it; check.sh refuses a tag that
names no case of `claim-tests --list`. -/

namespace Claims

/-- The shipped script's admission, assumed and tested, not proved: on a machine and ledger that read as `m` (after
`clean`, under the lock), `try` prints `(Admit.decide m r).line` and leaves `Admit.after m r`. Not tied: the `mkdir` lock
serialising tries (the 50-parallel script test covers it), `clean`'s liveness reading, and the measurement (`/proc/stat`,
`vm_stat`, `/proc/meminfo`) (claims_spec: admit_awk, script_try). -/
def ScriptAdmits (run : Admit.Machine → Admit.Req → Admit.Answer) : Prop :=
  ∀ m r, Admit.WF m r → run m r = Admit.decide m r

end Claims
