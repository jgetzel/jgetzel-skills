import SwarmModel.Basic
import SwarmModel.Real

/-! N1' (board #50): `swarm nudge a` (agents.cmd_nudge) is Model.lean's `hnudge`, an action of `step`. The CLI refuses an
unknown, ended or unbound agent; else it runs `hc send <a's terminal> <line>` and logs one nudge event, and writes
nothing else. The model keeps neither the event log's nudge rows nor terminal text, so the step is the state unchanged:
no task, claim, lock, lease, message or cursor moves (`N1'_frame`). The line's effect on a, a turn, is a's own `prompt`,
already a step. What `hc send` does to the world is Env.lean's `HcSendTargets`: the line goes into that terminal only,
no terminal starts or ends, and the repo's durable state stays (`Tools.N1'`, which takes it as a hypothesis). The step
is not in `Run.Fair`: a run may nudge or not, so S1-S5, N1, W1-W4 and L1-L4 hold with it in `step` and need nothing of it. -/

namespace Swarm

/-- `swarm nudge a` is enabled exactly for a live agent with a terminal -/
theorem hnudge_enabled {c : Cfg} {s : State} {a : Nat} :
    (step c s (.hnudge a)).isSome = ((s.agt a).live && !c.unbound.contains a) := by
  simp only [step, hnudge, when]; split <;> simp_all

/-- N1' in the model: a nudge changes nothing -/
theorem N1'_frame {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.hnudge a) = some s') : s' = s :=
  ((when_eq_some.mp h).2).symm

/-- a reachable state's nudge reaches only itself: every invariant of reachable states holds after it -/
theorem hnudge_reachable {c : Cfg} {s s' : State} {a : Nat} (hr : Reachable c s) (h : step c s (.hnudge a) = some s') :
    Reachable c s' := (N1'_frame h) ▸ hr

namespace Env

/-- N1' with the tool: the model's state unchanged, and `hc send` to a's live terminal h types the line into h, into no
other terminal, ends or starts no terminal, and leaves every worktree, branch and commit -/
theorem Tools.N1' {t : Tools} (hs : HcSendTargets t) {c : Cfg} {s s' : State} {a : Nat}
    (h : step c s (.hnudge a) = some s') {w : t.World} {hT : Nat} (hl : t.termLive w hT = true) (l : String) :
    s' = s ∧ t.typed (t.hcSend w hT l) hT = t.typed w hT ++ [l] ∧
      (∀ h', h' ≠ hT → t.typed (t.hcSend w hT l) h' = t.typed w h') ∧
      (∀ h', t.termLive (t.hcSend w hT l) h' = t.termLive w h') ∧
      Git.durable (t.git (t.hcSend w hT l)) = Git.durable (t.git w) :=
  ⟨N1'_frame h, hs w hT l hl⟩

end Env
end Swarm
