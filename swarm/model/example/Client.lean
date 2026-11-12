import SwarmModel.Contract

/-! A proof downstream of the swarm (board #25), from `SwarmModel.Contract` alone: a toy client, and one assumption of
the environment discharged for another machine. `check.sh` checks it: `lake env lean example/Client.lean`. -/

namespace Client
open Swarm Swarm.Contract

/-- the toy client: agent a, while at work, works on the first task it believes it holds, and on none until it has
claimed one (`believes` is the model's ghost record of what the agent thinks it holds, which a claim adds to) -/
def worksOn (s : State) (a : Nat) : Option Nat := if active (s.agt a) then (s.agt a).believes.head? else none

/-- a client that claims a task before working on it never works on a task another agent holds on the board, while no
one releases a task from it (`humanRelease` off: finding #32) -/
theorem never_works_on_others {c : Cfg} (hfix : c.release = .idle) (hhr : c.humanRelease = false) {s : State}
    (h : Reachable c s) {a b t : Nat} (hw : worksOn s a = some t) (hab : b ≠ a) : held (s.tk t) b = false := by
  unfold worksOn at hw
  split at hw
  · rename_i ha
    rcases s1_believes_held hfix hhr h ha (List.mem_of_mem_head? hw) with hh | hd
    · cases e : held (s.tk t) b
      · rfl
      · simp only [held, Bool.and_eq_true, beq_iff_eq] at hh e
        exact absurd (Option.some.inj (e.1.symm.trans hh.1)) hab
    · rcases hd with hd | hd <;> simp [held, hd]
  · cases hw

/-- the readable S1 gives back the checker's form that the replay runs: restating it (board #86) lost nothing -/
example {c : Cfg} (fixes : S1Fixes c) {s : State} (reachable : Reachable c s) : oneWorker s = true :=
  (oneWorker_iff s).mpr (one_worker_per_task fixes reachable)

/-- `env_landedRef` on `Env.ideal`, a machine whose tools tell the truth: its two assumptions are proved here, not
assumed (`Env.consistent` proves all of them at once) -/
theorem ideal_landed {w : Env.ideal.World} {k b : Nat} (h : Env.landedRef Env.ideal w k b false = true) :
    (Env.ideal.git w).reachFrom k b = true :=
  (env_landedRef (t := Env.ideal) (fun _ _ _ h => h) (fun _ _ _ h => h) h).resolve_right (by simp)

end Client
