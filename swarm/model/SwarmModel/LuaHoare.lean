import SwarmModel.Lua.Interp

/-! A program logic for the interpreter (board #39): `RunP m h P` says the computation `m` (a function of the fuel),
started in heap `h`, returns a result and heap satisfying `P` at every fuel from some bound on. Running out of
fuel is never the answer for a large enough fuel: so a `RunP` is total correctness, and says what the run is
(for every fuel that suffices), which is what the Lua suite sees from LuaJIT. One rule per interpreter clause. -/

namespace Swarm.Lua

def RunP {α : Type} (m : Nat → M α) (h : Heap) (P : α → Heap → Prop) : Prop :=
  ∃ N a h', (∀ n ≥ N, m n h = .ok a h') ∧ P a h'

section rules
variable {α β : Type} {m : Nat → M α} {h : Heap} {P Q : α → Heap → Prop}

theorem RunP.mono (r : RunP m h P) (hq : ∀ a h', P a h' → Q a h') : RunP m h Q := by
  obtain ⟨N, a, h', e, p⟩ := r; exact ⟨N, a, h', e, hq _ _ p⟩

/-- a computation that does not use the fuel -/
theorem RunP.const {m : M α} {a : α} {h' : Heap} (e : m h = .ok a h') (p : P a h') : RunP (fun _ => m) h P :=
  ⟨0, a, h', fun _ _ => e, p⟩

theorem RunP.pure' {a : α} (p : P a h) : RunP (fun _ => (pure a : M α)) h P := RunP.const rfl p

theorem RunP.bind {f : Nat → α → M β} {R : β → Heap → Prop}
    (r : RunP m h (fun a h1 => RunP (fun n => f n a) h1 R)) : RunP (fun n => m n >>= f n) h R := by
  obtain ⟨N, a, h1, e, N2, b, h2, e2, p⟩ := r
  refine ⟨max N N2, b, h2, fun n hn => ?_, p⟩
  have e1 := e n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have e2 := e2 n (Nat.le_trans (Nat.le_max_right _ _) hn)
  show EStateM.bind (m n) (f n) h = _
  rw [EStateM.bind, e1]; exact e2

/-- a step of one more fuel: the clauses of the interpreter match on `n + 1` -/
theorem RunP.succ {m : Nat → M α} (r : RunP (fun n => m (n + 1)) h P) : RunP m h P := by
  obtain ⟨N, a, h', e, p⟩ := r
  exact ⟨N + 1, a, h', fun n hn => by obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩; exact e k (by omega), p⟩

theorem RunP.cong {m m' : Nat → M α} (e : ∀ n, m n = m' n) (r : RunP m h P) : RunP m' h P := by
  have : m = m' := funext e
  subst this; exact r

end rules
end Swarm.Lua
