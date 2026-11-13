import SwarmLean.Store

namespace SwarmLean

/-- A task's owner fits its status: a claimed task has an owner, an open one has none. -/
def Task.Owned (t : Task) : Prop :=
  (t.status = .claimed → t.owner.isSome) ∧ (t.status = .open → t.owner = none)

/-- The store's invariant: ids are unique and below `next`, and every task's owner fits its status. -/
def Inv (db : Db) : Prop :=
  (db.tasks.map (·.id)).Nodup ∧ (∀ t ∈ db.tasks, t.id < db.next) ∧ ∀ t ∈ db.tasks, t.Owned

/-- The db after `cs` from the empty db. -/
def run (cs : List Cmd) : Db := (replay Cmd.step {} cs).1

/-- Each command of `cs`, from `db`, with its answer. -/
def trace (db : Db) (cs : List Cmd) : List (Cmd × Result) := (replay Cmd.step db cs).2

/-- Agent `a` owns task `i` in `db`. -/
def Owns (db : Db) (i : Nat) (a : String) : Prop := ∃ t ∈ db.tasks, t.id = i ∧ t.owner = some a

/-- An answer `claimed` to a claim of task `i`. -/
def ClaimedOf (i : Nat) : Cmd × Result → Bool
  | (.claim j _, .claimed) => j == i
  | _ => false

/-- An answer `released` to a release of task `i`. -/
def ReleasedOf (i : Nat) : Cmd × Result → Bool
  | (.release j _, .released) => j == i
  | _ => false

theorem inv_empty : Inv {} := by simp [Inv]

theorem set_tasks_ids (db : Db) (i : Nat) (f : Task → Task) (hf : ∀ t, (f t).id = t.id) :
    (db.set i f).tasks.map (·.id) = db.tasks.map (·.id) := by
  simp only [Db.set, List.map_map]
  exact List.map_congr_left fun t _ => by by_cases h : t.id = i <;> simp [h, hf]

theorem set_inv (db : Db) (i : Nat) (f : Task → Task) (hf : ∀ t, (f t).id = t.id) (ho : ∀ t, (f t).Owned)
    (h : Inv db) : Inv (db.set i f) := by
  obtain ⟨hn, hb, hw⟩ := h
  refine ⟨set_tasks_ids db i f hf ▸ hn, ?_, ?_⟩ <;> intro t' ht' <;>
    simp only [Db.set, List.mem_map] at ht' <;> obtain ⟨t, ht, rfl⟩ := ht' <;>
    by_cases e : t.id = i <;> simp [e, hf, ho, hw t ht] <;> simpa [Db.set, e] using hb t ht

theorem step_inv (c : Cmd) (db : Db) (h : Inv db) : Inv (c.step db).1 := by
  cases c with
  | add title =>
    obtain ⟨hn, hb, hw⟩ := h
    dsimp only [Cmd.step, Inv]
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      exact List.nodup_append.2 ⟨hn, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩,
        fun a ha b hb' => by simp at hb'; subst hb'; obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha; exact Nat.ne_of_lt (hb t ht)⟩
    · intro t ht; simp at ht; rcases ht with ht | rfl
      · exact Nat.lt_succ_of_lt (hb t ht)
      · exact Nat.lt_succ_self _
    · intro t ht; simp at ht; rcases ht with ht | rfl
      · exact hw t ht
      · simp [Task.Owned]
  | claim i a =>
    simp only [Cmd.step]; split
    · exact h
    · split
      · exact set_inv _ _ _ (fun _ => rfl) (fun _ => by simp [Task.Owned]) h
      · exact h
      · exact h
  | release i a =>
    simp only [Cmd.step]; split
    · exact h
    · split
      · exact set_inv _ _ _ (fun _ => rfl) (fun _ => by simp [Task.Owned]) h
      · exact h
  | board => exact h

theorem replay_inv (db : Db) (cs : List Cmd) (h : Inv db) : Inv (replay Cmd.step db cs).1 := by
  induction cs generalizing db with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_inv c db h)

/-- The invariant holds after any commands by any agents from the empty db. -/
theorem run_inv (cs : List Cmd) : Inv (run cs) := replay_inv _ cs inv_empty

theorem nodup_inj {l : List Task} (h : (l.map (·.id)).Nodup) {x y : Task} (hx : x ∈ l) (hy : y ∈ l)
    (e : x.id = y.id) : x = y := by
  induction l with
  | nil => cases hx
  | cons t l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd ⟨y, hy', e.symm⟩ h.1
    · exact absurd ⟨x, hx', e⟩ h.1
    · exact ih h.2 hx' hy'

/-- No task has two owners, after any commands by any agents in any order from the empty db. -/
theorem one_owner (cs : List Cmd) (i : Nat) (a b : String) (ha : Owns (run cs) i a) (hb : Owns (run cs) i b) :
    a = b := by
  obtain ⟨t, ht, rfl, hta⟩ := ha
  obtain ⟨t', ht', e, htb⟩ := hb
  have := nodup_inj (run_inv cs).1 ht ht' e.symm
  subst this; simpa [hta] using htb

/-- Task `i` is claimed in `db`. -/
def Held (db : Db) (i : Nat) : Prop := ∃ t, db.find i = some t ∧ t.status = .claimed

theorem find_set (db : Db) (i j : Nat) (f : Task → Task) (hf : ∀ t, (f t).id = t.id) :
    (db.set j f).find i = (db.find i).map fun t => if t.id = j then f t else t := by
  simp only [Db.find, Db.set, List.find?_map]
  congr 2; funext t; by_cases h : t.id = j <;> simp [h, hf]

theorem find_id {db : Db} {i : Nat} {t : Task} (h : db.find i = some t) : t.id = i := by
  simpa using List.find?_some h

/-- A claim answered `claimed` leaves its task claimed. -/
theorem claimed_held (db : Db) (i : Nat) (a : String) (h : ((Cmd.claim i a).step db).2 = .claimed) :
    Held ((Cmd.claim i a).step db).1 i := by
  revert h; simp only [Cmd.step]; split
  · simp
  · rename_i t ht; split
    · intro _; refine ⟨_, by dsimp only; rw [find_set, ht] <;> first | rfl | (intro; rfl), ?_⟩; simp [find_id ht]
    all_goals simp

/-- From a db where task `i` is claimed, a command other than its successful release keeps it claimed and is not
answered `claimed` for it. -/
theorem held_step (db : Db) (i : Nat) (c : Cmd) (h : Held db i) (hr : ReleasedOf i (c, (c.step db).2) = false) :
    Held (c.step db).1 i ∧ ClaimedOf i (c, (c.step db).2) = false := by
  obtain ⟨t, ht, hs⟩ := h
  cases c with
  | add title =>
    refine ⟨⟨t, ?_, hs⟩, rfl⟩
    simp only [Cmd.step, Db.find] at ht ⊢; rw [List.find?_append, ht]; rfl
  | claim j a =>
    simp only [Cmd.step] at hr ⊢; split
    · exact ⟨⟨t, ht, hs⟩, rfl⟩
    · rename_i t' ht'; split
      · rename_i hso
        have : j ≠ i := fun e => by subst e; rw [ht] at ht'; cases ht'; rw [hs] at hso; cases hso
        refine ⟨⟨t, by dsimp only; rw [find_set, ht] <;> first | (intro; rfl) | simp [find_id ht, Ne.symm this], hs⟩, ?_⟩
        simp [ClaimedOf, this]
      all_goals exact ⟨⟨t, ht, hs⟩, rfl⟩
  | release j a =>
    simp only [Cmd.step] at hr ⊢; split
    · exact ⟨⟨t, ht, hs⟩, rfl⟩
    · rename_i t' ht'; split
      · have : j ≠ i := fun e => by subst e; split at hr <;> simp_all [ReleasedOf]
        refine ⟨⟨t, by dsimp only; rw [find_set, ht] <;> first | (intro; rfl) | simp [find_id ht, Ne.symm this], hs⟩, rfl⟩
      · exact ⟨⟨t, ht, hs⟩, rfl⟩
  | board => exact ⟨⟨t, ht, hs⟩, rfl⟩

theorem trace_cons (db : Db) (c : Cmd) (cs : List Cmd) :
    trace db (c :: cs) = (c, (c.step db).2) :: trace (c.step db).1 cs := rfl

theorem claimedOf_true {i : Nat} {c : Cmd} {r : Result} (h : ClaimedOf i (c, r) = true) :
    ∃ a, c = .claim i a ∧ r = .claimed := by
  cases c <;> cases r <;> simp_all [ClaimedOf]

/-- From a db where task `i` is claimed, a later `claimed` answer for it comes after a successful release of it. -/
theorem held_claimed (db : Db) (i : Nat) (cs : List Cmd) (h : Held db i) (t2 t3 : List (Cmd × Result)) (b : String)
    (e : trace db cs = t2 ++ (.claim i b, .claimed) :: t3) : ∃ x ∈ t2, ReleasedOf i x := by
  induction cs generalizing db t2 with
  | nil => cases t2 <;> simp [trace, replay] at e
  | cons c cs ih =>
    rw [trace_cons] at e
    cases t2 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, hc⟩, -⟩ := e
      have := (held_step db i (.claim i b) h (by simp [ReleasedOf])).2
      simp [ClaimedOf, hc] at this
    | cons x t2 =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      by_cases hr : ReleasedOf i (c, (c.step db).2)
      · exact ⟨_, List.mem_cons_self .., hr⟩
      · obtain ⟨y, hy, hy'⟩ := ih _ (held_step db i c h (by simpa using hr)).1 t2 e
        exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-- Of any commands by any agents from any db, two `claimed` answers for one task have a successful release of it
between them: a claim answers `claimed` to at most one agent until the task is released. -/
theorem claimed_once (db : Db) (cs : List Cmd) (i : Nat) (a b : String) (t1 t2 t3 : List (Cmd × Result))
    (e : trace db cs = t1 ++ (.claim i a, .claimed) :: t2 ++ (.claim i b, .claimed) :: t3) :
    ∃ x ∈ t2, ReleasedOf i x := by
  induction cs generalizing db t1 with
  | nil => cases t1 <;> simp [trace, replay] at e
  | cons c cs ih =>
    rw [trace_cons] at e
    cases t1 with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨rfl, hc⟩, e⟩ := e
      exact held_claimed _ i cs (claimed_held db i a hc) t2 t3 b e
    | cons x t1 =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at e
      exact ih _ t1 (by simpa using e.2)

/-- From a db where task `i` is claimed, with no successful release of it, no command is answered `claimed` for it. -/
theorem claims_held (db : Db) (i : Nat) (cs : List Cmd) (h : Held db i)
    (hr : ∀ x ∈ trace db cs, ReleasedOf i x = false) : (trace db cs).filter (ClaimedOf i) = [] := by
  induction cs generalizing db with
  | nil => rfl
  | cons c cs ih =>
    rw [trace_cons] at hr ⊢
    have ⟨h', hc⟩ := held_step db i c h (hr _ (List.mem_cons_self ..))
    simp only [List.filter_cons, hc, Bool.false_eq_true, ↓reduceIte]
    exact ih _ h' fun x hx => hr x (List.mem_cons_of_mem _ hx)

/-- With no successful release of task `i` among them, at most one of the commands from `db` is answered `claimed`
for it. -/
theorem claims_le (db : Db) (i : Nat) (cs : List Cmd) (hr : ∀ x ∈ trace db cs, ReleasedOf i x = false) :
    ((trace db cs).filter (ClaimedOf i)).length ≤ 1 := by
  induction cs generalizing db with
  | nil => simp [trace, replay]
  | cons c cs ih =>
    rw [trace_cons] at hr ⊢
    have hr' := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    cases hcl : ClaimedOf i (c, (c.step db).2)
    · simp only [List.filter_cons, hcl, Bool.false_eq_true, ↓reduceIte]; exact ih _ hr'
    · obtain ⟨a, rfl, hc⟩ := claimedOf_true hcl
      simp [hcl, claims_held _ i cs (claimed_held db i a hc) hr']

theorem replay_fst (db : Db) (cs : List Cmd) : (trace db cs).map (·.1) = cs := by
  induction cs generalizing db with
  | nil => rfl
  | cons c cs ih => rw [trace_cons]; simp [ih]

/-- Under the store's assumption (`Atomic`), when processes ran commands at once with no successful release of task
`i` among them, at most one of them was answered `claimed` for it. -/
theorem one_winner (before after : Db) (ran : List (Cmd × Result)) (i : Nat) (h : Atomic Cmd.step before after ran)
    (hr : ∀ x ∈ ran, ReleasedOf i x = false) : (ran.filter (ClaimedOf i)).length ≤ 1 := by
  obtain ⟨order, hp, e⟩ := h
  have ht : trace before (order.map (·.1)) = order := congrArg Prod.snd e
  rw [← (hp.filter _).length_eq, ← ht]
  exact claims_le before i _ (by rw [ht]; exact fun x hx => hr x (hp.mem_iff.1 hx))

/-- Under the store's assumption, when every process ran `task claim i` (as any agents) on a store where task `i`
is open, exactly one was answered `claimed`: what `test-claim.sh` checks of the real store. -/
theorem exactly_one_winner (before after : Db) (ran : List (Cmd × Result)) (i : Nat) (t : Task)
    (h : Atomic Cmd.step before after ran) (ho : before.find i = some t) (hs : t.status = .open)
    (hc : ∀ x ∈ ran, ∃ a, x.1 = .claim i a) (hn : ran ≠ []) : (ran.filter (ClaimedOf i)).length = 1 := by
  refine Nat.le_antisymm (one_winner before after ran i h fun x hx => ?_) ?_
  · obtain ⟨a, ha⟩ := hc x hx; obtain ⟨c, r⟩ := x; cases ha; rfl
  · obtain ⟨order, hp, e⟩ := h
    have ht : trace before (order.map (·.1)) = order := congrArg Prod.snd e
    obtain ⟨x, xs, rfl⟩ : ∃ x xs, order = x :: xs := by
      cases order with
      | nil => exact absurd (List.Perm.nil_eq hp).symm hn
      | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨a, ha⟩ := hc x (hp.mem_iff.1 (List.mem_cons_self ..))
    rw [← (hp.filter _).length_eq, ← ht, List.map_cons, ha, trace_cons]
    have : ((Cmd.claim i a).step before).2 = .claimed := by simp [Cmd.step, ho, hs]
    simp [this, ClaimedOf]

end SwarmLean
