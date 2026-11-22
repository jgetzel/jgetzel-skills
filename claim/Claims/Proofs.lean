import Claims.Admit
import Claims.Assumptions

/-! sw-compute-backfill.md §6.2: the theorems of the admission model `Claims.Admit`, and at the end (§6.2 11) the same
for the shipped script through the assumption `ScriptAdmits` (Claims/Assumptions.lean). -/

namespace Claims.Proofs
open Claims.Admit

/-! ### Lemmas: the head, the shadow, sums -/

theorem foldl_opt {α : Type} {f : Option α → α → Option α} (hf : ∀ a t, f a t = some t ∨ (f a t = a ∧ a.isSome)) :
    ∀ (l : List α) (a : Option α) (x : α), l.foldl f a = some x → a = some x ∨ x ∈ l := by
  intro l
  induction l with
  | nil => intro a x h; exact .inl h
  | cons t l ih =>
    intro a x h
    rcases ih _ _ h with e | e
    · rcases hf a t with e' | ⟨e', _⟩
      · rw [e'] at e; cases e; exact .inr (List.mem_cons_self ..)
      · rw [e'] at e; exact .inl e
    · exact .inr (List.mem_cons_of_mem _ e)

theorem foldl_opt_some {α : Type} {f : Option α → α → Option α} (hf : ∀ a t, f a t = some t ∨ (f a t = a ∧ a.isSome)) :
    ∀ (l : List α) (a : Option α), a.isSome ∨ l ≠ [] → (l.foldl f a).isSome := by
  intro l
  induction l with
  | nil => intro a h; simpa using h
  | cons t l ih =>
    intro a _
    apply ih
    left
    rcases hf a t with e | ⟨e, h⟩ <;> simp [*]

/-- The step `head` folds with. -/
theorem head_step (a : Option Ticket) (t : Ticket) :
    (match a with
      | none => some t
      | some h => if before (t.first, t.id) (h.first, h.id) then some t else some h) = some t ∨
    ((match a with
      | none => some t
      | some h => if before (t.first, t.id) (h.first, h.id) then some t else some h) = a ∧ a.isSome) := by
  cases a with
  | none => simp
  | some h => by_cases e : before (t.first, t.id) (h.first, h.id) <;> simp [e]

theorem head_mem {m : Machine} {r : Req} {h : Ticket} (e : head m r = some h) : h ∈ aheadOf m r := by
  rcases foldl_opt head_step _ none h e with e | e
  · cases e
  · exact e

theorem head_isSome {m : Machine} {r : Req} : (head m r).isSome ↔ aheadOf m r ≠ [] := by
  constructor
  · intro e h0
    simp [head, h0] at e
  · intro e
    exact foldl_opt_some head_step _ none (.inr e)

theorem head_none {m : Machine} {r : Req} : head m r = none ↔ aheadOf m r = [] := by
  have := (head_isSome (m := m) (r := r))
  cases e : head m r <;> simp_all

theorem events_ge {m : Machine} {x : Int} (e : x ∈ events m) : m.now ≤ x := by
  simp only [events, List.mem_cons, List.mem_filterMap, endOf, Option.map_eq_some_iff] at e
  rcases e with e | ⟨c, _, e, _, rfl⟩
  · omega
  · omega

theorem shadow_spec {m : Machine} {h : Ticket} {s : Int} (e : shadow m h = some s) :
    s ∈ events m ∧ fitsAt m h s = true ∧ ∀ τ ∈ events m, fitsAt m h τ = true → s ≤ τ := by
  have := List.min?_eq_some_iff.mp e
  simp only [List.mem_filter] at this
  exact ⟨this.1.1, this.1.2, fun τ h1 h2 => this.2 τ ⟨h1, h2⟩⟩

theorem shadow_le {m : Machine} {h : Ticket} {τ : Int} (e : τ ∈ events m) (f : fitsAt m h τ = true) :
    ∃ s, shadow m h = some s ∧ s ≤ τ := by
  cases hs : shadow m h with
  | none =>
    have := List.min?_eq_none_iff.mp hs
    have : τ ∈ (events m).filter (fitsAt m h) := List.mem_filter.mpr ⟨e, f⟩
    simp_all
  | some s => exact ⟨s, rfl, (shadow_spec hs).2.2 τ e f⟩

theorem shadow_none {m : Machine} {h : Ticket} : shadow m h = none ↔ ∀ τ ∈ events m, fitsAt m h τ = false := by
  constructor
  · intro e τ hτ
    cases f : fitsAt m h τ
    · rfl
    · obtain ⟨s, hs, _⟩ := shadow_le hτ f; simp_all
  · intro e
    apply List.min?_eq_none_iff.mpr
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro τ hτ
    have := List.mem_filter.mp hτ
    simp_all

theorem sum_nonneg {α : Type} (l : List α) (f : α → Int) (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons]; have := h a (by simp); have := ih (fun x hx => h x (by simp [hx])); omega

theorem sum_split {α : Type} (l : List α) (p : α → Bool) (f : α → Int) :
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter (fun x => !p x)).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => cases e : p a <;> simp [e, ih] <;> omega

theorem sum_filter_le {α : Type} (l : List α) (p : α → Bool) (f : α → Int) (h : ∀ x ∈ l, 0 ≤ f x) :
    ((l.filter p).map f).sum ≤ (l.map f).sum := by
  have := sum_split l p f
  have := sum_nonneg (l.filter fun x => !p x) f (fun x hx => h x (List.mem_filter.mp hx).1)
  omega

theorem sum_sublist {α : Type} {l₁ l₂ : List α} (s : l₁.Sublist l₂) (f : α → Int) (h : ∀ x ∈ l₂, 0 ≤ f x) :
    (l₁.map f).sum ≤ (l₂.map f).sum := by
  induction s with
  | slnil => simp
  | cons a _ ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (by simp); have := ih (fun x hx => h x (by simp [hx])); omega
  | cons_cons a _ ih =>
    simp only [List.map_cons, List.sum_cons]
    have := ih (fun x hx => h x (by simp [hx])); omega

theorem sum_filter_all {α : Type} (l : List α) (p : α → Bool) (f : α → Int) (h : ∀ x ∈ l, p x = true) :
    ((l.filter p).map f).sum = (l.map f).sum := by
  rw [List.filter_eq_self.mpr h]

/-- Every claim's expected end, when it has one, is at most some event. -/
theorem events_top (m : Machine) : ∃ τ ∈ events m, ∀ c ∈ m.claims, ∀ x, endOf m c = some x → x ≤ τ := by
  cases e : (events m).max? with
  | none => simp [events] at e
  | some τ =>
    have := List.max?_eq_some_iff.mp e
    refine ⟨τ, this.1, fun c hc x hx => this.2 x ?_⟩
    simp only [events, List.mem_cons, List.mem_filterMap]
    exact .inr ⟨c, hc, hx⟩

/-! ### The room -/

theorem outside_nonneg (m : Machine) : 0 ≤ outside m := by simp only [outside]; omega

theorem limC_le_capC (m : Machine) : limC m ≤ capC m := by simp only [limC, lim]; omega
theorem limM_le_capM (m : Machine) : limM m ≤ capM m := by simp only [limM, lim]; omega

/-- A sized ticket is not held exactly when it has not yielded, its cores are within the cap less the reservation, and its
memory would fit with every claim ended. -/
theorem held_sized {m : Machine} {t : Ticket} {c : Int} (e : t.cores = some c) :
    held m t = false ↔ yielded m t = false ∧ c ≤ limC m ∧ t.mem ≤ freeM m + cm m := by
  simp [held, e]

/-- An exclusive ticket is not held exactly when it has not yielded, the cap is the whole machine and nothing is reserved. -/
theorem held_excl {m : Machine} {t : Ticket} (e : t.cores = none) :
    held m t = false ↔ yielded m t = false ∧ whole m = true ∧ m.res = (0, 0) := by
  simp [held, e]

/-! ### 1-2. The rule, stated whole -/

/-- The backfill condition inside `decide`. -/
abbrev bf (m : Machine) (r : Req) : Bool := match head m r, r.est with
  | some h, some e => (shadow m h).any (m.now + e ≤ ·)
  | _, _ => false

theorem bf_iff {m : Machine} {r : Req} :
    bf m r = true ↔ ∃ h e s, head m r = some h ∧ r.est = some e ∧ shadow m h = some s ∧ m.now + e ≤ s := by
  rcases hh : head m r with _ | h <;> rcases he : r.est with _ | e <;> simp [bf, hh, he]
  rcases hs : shadow m h with _ | s <;> simp

theorem decide_eq (m : Machine) (r : Req) : Admit.decide m r =
    if m.off then .off else if tooBig m r then .never (capC m) (capM m) else
    if fitsNow m r && ((aheadOf m r).isEmpty || bf m r) then .ok (take m r).1 (take m r).2
    else .wait (max 0 (freeC m)) (max 0 (freeM m)) (aheadOf m r).length := rfl

theorem decide_ok_iff {m : Machine} {r : Req} {c g : Int} :
    Admit.decide m r = .ok c g ↔ m.off = false ∧ tooBig m r = false ∧ fitsNow m r = true ∧ (c, g) = take m r ∧
      (aheadOf m r = [] ∨ ∃ h e s, head m r = some h ∧ r.est = some e ∧ shadow m h = some s ∧ m.now + e ≤ s) := by
  rw [decide_eq, ← bf_iff, ← List.isEmpty_iff]
  generalize take m r = tk
  cases m.off <;> cases tooBig m r <;> cases fitsNow m r <;> cases bf m r <;> cases (aheadOf m r).isEmpty <;>
    simp only [Bool.false_eq_true, ite_true, ite_false, Bool.and_true, Bool.and_false, Bool.or_true, Bool.or_false,
      reduceCtorEq, Answer.ok.injEq, true_and, and_true, false_and, and_false, or_false, or_true, Prod.ext_iff] <;> constructor <;> intro h <;> simp_all

theorem off_iff {m : Machine} {r : Req} : Admit.decide m r = .off ↔ m.off = true := by
  rw [decide_eq]
  cases m.off <;> cases tooBig m r <;> simp <;> split <;> simp

theorem never_iff {m : Machine} {r : Req} {a b : Int} :
    Admit.decide m r = .never a b ↔ m.off = false ∧ tooBig m r = true ∧ a = capC m ∧ b = capM m := by
  rw [decide_eq]
  cases m.off <;> cases tooBig m r <;> simp
  · split <;> simp
  · constructor <;> rintro ⟨rfl, rfl⟩ <;> simp

/-! ### 10. Reserve and cap arithmetic -/

theorem lim_bounds {cap size res : Int} (hc : 0 ≤ cap) (hs : 0 ≤ size) :
    0 ≤ lim cap size res ∧ lim cap size res ≤ size ∧ lim cap size res ≤ cap := by
  simp only [lim]; omega

/-- The reservation of nothing leaves the cap, clamped to the machine. (Needs `0 ≤ size`, which §6.2 left out: for a
negative size `lim` clamps the reservation to it and returns `min cap 0`.) -/
theorem lim_zero {cap size : Int} (hs : 0 ≤ size) : lim cap size 0 = min cap size := by
  simp only [lim]; omega

theorem lim_antitone {cap size res res' : Int} (h : res ≤ res') : lim cap size res' ≤ lim cap size res := by
  simp only [lim]; omega

theorem reserve_restores {f : Files} {c g : Int} (h : f.res = (0, 0)) : setReserve (setReserve f c g) 0 0 = f := by
  cases f; simp_all [setReserve]

theorem reserve_keeps_cap (f : Files) (c g : Int) : (setReserve f c g).cap = f.cap := rfl
theorem cap_keeps_reserve (f : Files) (c g : Option Int) : (setCap f c g).res = f.res := rfl

theorem capC_nonneg {m : Machine} {r : Req} (w : WF m r) : 0 ≤ capC m := by
  obtain ⟨hn, -, -, -, -, hc, -⟩ := w
  simp only [capC]; cases e : m.cap.1 <;> simp_all; omega

theorem capM_nonneg {m : Machine} {r : Req} (w : WF m r) : 0 ≤ capM m := by
  obtain ⟨-, ht, -, -, -, -, hc, -⟩ := w
  simp only [capM]; cases e : m.cap.2 <;> simp_all

theorem limC_bounds {m : Machine} {r : Req} (w : WF m r) : 0 ≤ limC m ∧ limC m ≤ m.ncpu ∧ limC m ≤ capC m :=
  lim_bounds (capC_nonneg w) (by obtain ⟨_, -⟩ := w; omega)

theorem limM_bounds {m : Machine} {r : Req} (w : WF m r) : 0 ≤ limM m ∧ limM m ≤ m.total ∧ limM m ≤ capM m :=
  lim_bounds (capM_nonneg w) (by obtain ⟨-, _, -⟩ := w; omega)

/-! ### 9. Exclusive claims -/

theorem excl_grant {m : Machine} {r : Req} {c g : Int} (hx : r.cores = none) (e : Admit.decide m r = .ok c g) :
    m.claims = [] ∧ m.res = (0, 0) ∧ outside m = 0 ∧ c = m.ncpu ∧ g = m.avail ∧ whole m = true := by
  obtain ⟨-, hb, hf, ht, -⟩ := decide_ok_iff.mp e
  simp only [tooBig, fitsNow, take, hx, Bool.not_eq_false', Bool.and_eq_true, List.isEmpty_iff, quiet,
    beq_iff_eq, Prod.ext_iff] at hb hf ht
  exact ⟨hf.1, Prod.ext hf.2.1.1 hf.2.1.2, hf.2.2, ht.1, ht.2, hb⟩

theorem cc_nil {m : Machine} (h : m.claims = []) : cc m = 0 ∧ cm m = 0 := by simp [cc, cm, h]

theorem claims_nonneg {m : Machine} {r : Req} (w : WF m r) : 0 ≤ cc m ∧ 0 ≤ cm m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hc, -⟩ := w
  exact ⟨sum_nonneg _ _ fun c h => (hc c h).1, sum_nonneg _ _ fun c h => (hc c h).2.1⟩

/-! ### 3. Grants stay within the limits -/

theorem grant_within {m : Machine} {r : Req} {c g : Int} (w : WF m r) (e : Admit.decide m r = .ok c g) :
    cc m + c ≤ limC m ∧ cc m + c + outside m ≤ m.ncpu ∧ cm m + g ≤ limM m ∧ g ≤ m.avail := by
  rcases hx : r.cores with _ | k
  · obtain ⟨h0, hr, ho, rfl, rfl, hw⟩ := excl_grant hx e
    obtain ⟨hn, ht, -, ha, hat, -⟩ := w
    have := cc_nil h0
    simp only [whole, decide_eq_true_eq, Bool.and_eq_true] at hw
    simp only [limC, limM, lim, hr]
    omega
  · obtain ⟨-, -, hf, ht, -⟩ := decide_ok_iff.mp e
    simp only [fitsNow, take, hx, Bool.and_eq_true, decide_eq_true_eq, Prod.ext_iff] at hf ht
    obtain ⟨rfl, rfl⟩ := ht
    simp only [freeC, freeM] at hf
    omega

theorem grant_within_cap {m : Machine} {r : Req} {c g : Int} (w : WF m r) (e : Admit.decide m r = .ok c g) :
    cc (grant m r) ≤ capC m := by
  have h := grant_within w e
  have := (limC_bounds w).2.2
  have ht := (decide_ok_iff.mp e).2.2.2.1
  simp only [cc, grant, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h ⊢
  rw [← ht]; omega

/-! ### 4-5. No history, no backfill; no shadow, no backfill -/

theorem no_history_no_backfill {m : Machine} {r : Req} {c g : Int} (he : r.est = none)
    (e : Admit.decide m r = .ok c g) : aheadOf m r = [] := by
  rcases (decide_ok_iff.mp e).2.2.2.2 with h | ⟨_, _, _, _, h, _⟩
  · exact h
  · simp_all

theorem held_false_of_head {m : Machine} {r : Req} {h : Ticket} (e : head m r = some h) : held m h = false := by
  have := List.mem_filter.mp (head_mem e)
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at this
  exact this.2.1.2

/-- A ticket that is not held has a known start once every claim has an estimate: the last expected end at the latest. -/
theorem unheld_shadow_some {m : Machine} {h : Ticket} (hh : held m h = false) (hc : ∀ c ∈ m.claims, c.est.isSome) :
    shadow m h ≠ none := by
  obtain ⟨τ, hτ, top⟩ := events_top m
  have ends : ∀ c ∈ m.claims, (endOf m c).any (· ≤ τ) = true := by
    intro c hm
    have := hc c hm
    cases e : endOf m c with
    | none => simp [endOf] at e; simp_all
    | some x => simpa using top c hm x e
  have fit : fitsAt m h τ = true := by
    rcases hx : h.cores with _ | k
    · simp only [fitsAt, hx, List.all_eq_true]; exact ends
    · obtain ⟨-, h1, h2⟩ := (held_sized hx).mp hh
      have r1 := sum_filter_all m.claims (fun c => (endOf m c).any (· ≤ τ)) (·.cores) ends
      have r2 := sum_filter_all m.claims (fun c => (endOf m c).any (· ≤ τ)) (·.mem) ends
      simp only [fitsAt, hx, released, Bool.and_eq_true, decide_eq_true_eq, r1, r2]
      simp only [cc, cm] at h1 h2 ⊢
      omega
  obtain ⟨s, hs, -⟩ := shadow_le hτ fit
  simp [hs]

/-- §6.2 5, restated for the generalised `held`: a head with no known start blocks every backfill, and that happens
only through a live claim without an estimate (a head that would not fit with every claim ended is held, not head). -/
theorem unknown_shadow_no_backfill {m : Machine} {r : Req} {h : Ticket} (e : head m r = some h)
    (hs : shadow m h = none) : (∃ c ∈ m.claims, c.est = none) ∧ ∀ c g, Admit.decide m r ≠ .ok c g := by
  constructor
  · apply Classical.byContradiction
    intro hn
    apply unheld_shadow_some (held_false_of_head e) _ hs
    intro c hc
    cases he : c.est <;> simp_all
  · intro c g d
    rcases (decide_ok_iff.mp d).2.2.2.2 with h0 | ⟨h', _, _, e', -, hs', -⟩
    · have := head_mem e; simp_all
    · rw [e] at e'; cases e'; simp_all

/-! ### 12. When the head's start is known -/

theorem shadow_some {m : Machine} {h : Ticket} {k : Int} (hx : h.cores = some k) (hc : ∀ c ∈ m.claims, c.est.isSome)
    (hf : k ≤ limC m ∧ h.mem ≤ freeM m + cm m) : shadow m h ≠ none := by
  have e : shadow m h = shadow m { h with since := none } := rfl
  rw [e]
  exact unheld_shadow_some ((held_sized (t := { h with since := none }) hx).mpr ⟨by simp [yielded], hf⟩) hc

theorem excl_shadow_some {m : Machine} {t : Ticket} (hx : t.cores = none) (hc : ∀ c ∈ m.claims, c.est.isSome) :
    shadow m t ≠ none := by
  obtain ⟨τ, hτ, top⟩ := events_top m
  have fit : fitsAt m t τ = true := by
    simp only [fitsAt, hx, List.all_eq_true]
    intro c hm
    have := hc c hm
    cases e : endOf m c with
    | none => simp [endOf] at e; simp_all
    | some x => simpa using top c hm x e
  obtain ⟨s, hs, -⟩ := shadow_le hτ fit
  simp [hs]

theorem excl_alone {m : Machine} {r : Req} (w : WF m r) (hc : m.ncpu ≤ cc m) : ∀ c g, Admit.decide m r ≠ .ok c g := by
  intro c g e
  have ho := outside_nonneg m
  have hn := w.1
  rcases hx : r.cores with _ | k
  · have := cc_nil (excl_grant hx e).1; omega
  · have := grant_within w e
    have := (decide_ok_iff.mp e).2.2.2.1
    simp only [take, hx, Prod.ext_iff] at this
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := w
    have := hk k (by simp [hx])
    omega

/-! ### 8. Held tickets block no one -/

theorem held_not_ahead {m : Machine} {r : Req} {t : Ticket} (h : held m t = true) : t ∉ aheadOf m r := by
  intro e
  have := (List.mem_filter.mp e).2
  simp_all

theorem held_not_head {m : Machine} {r : Req} {t : Ticket} (h : held m t = true) : head m r ≠ some t :=
  fun e => held_not_ahead h (head_mem e)

/-- An exclusive ticket blocks no one while the reservation or a cap below the machine keeps it off, or once it has
yielded (the user's rule of 2026-11-21: unclaimed use alone does not hold it). -/
theorem excl_waiting_blocks_none {m : Machine} {r : Req} {t : Ticket} (hx : t.cores = none)
    (h : m.res ≠ (0, 0) ∨ whole m = false ∨ yielded m t = true) : t ∉ aheadOf m r := by
  apply held_not_ahead
  cases e : held m t
  · obtain ⟨hy, hw, hr⟩ := (held_excl hx).mp e
    rcases h with h | h | h <;> simp_all
  · rfl

/-- A sized ticket blocks no one when it needs more cores than the cap less the reservation, more memory than it could
have with every claim ended, or once it has yielded. -/
theorem sized_waiting_blocks_none {m : Machine} {r : Req} {t : Ticket} {k : Int} (hx : t.cores = some k)
    (h : limC m < k ∨ freeM m + cm m < t.mem ∨ yielded m t = true) : t ∉ aheadOf m r := by
  apply held_not_ahead
  cases e : held m t
  · obtain ⟨hy, h1, h2⟩ := (held_sized hx).mp e
    rcases h with h | h | h
    · omega
    · omega
    · simp_all
  · rfl

/-! ### 8b. Unclaimed use holds no one; the yield -/

/-- The fix of 2026-11-21: what is held, who is ahead, the head and its shadow do not depend on the busy cores; unclaimed
use can keep a request from starting (`fitsNow`), never a waiting ticket from its place. -/
theorem unclaimed_use_moves_no_one (m : Machine) (r : Req) (b : Int) (t : Ticket) :
    held { m with busy := b } t = held m t ∧ aheadOf { m with busy := b } r = aheadOf m r ∧
      head { m with busy := b } r = head m r ∧ shadow { m with busy := b } t = shadow m t :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- An older exclusive ticket under a cap at the machine, with nothing reserved and no yield, is ahead of a request
whatever the machine's unclaimed use. -/
theorem excl_unheld_ahead {m : Machine} {r : Req} {t : Ticket} (hx : t.cores = none) (hm : t ∈ m.tickets)
    (hid : t.id ≠ r.id) (hw : whole m = true) (hr : m.res = (0, 0)) (hy : yielded m t = false)
    (hb : before (t.first, t.id) (first m r, r.id) = true) : t ∈ aheadOf m r := by
  have : held m t = false := (held_excl hx).mpr ⟨hy, hw, hr⟩
  simp only [aheadOf, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  exact ⟨hm, ⟨hid, this⟩, hb⟩

/-- A ticket that has been blocked only by unclaimed use for `YIELD` seconds is held. -/
theorem yield_holds {m : Machine} {t : Ticket} {s : Int} (hs : t.since = some s) (hy : s + YIELD ≤ m.now) :
    held m t = true := by
  simp [held, yielded, hs, hy]

/-- The clock runs only while the request would start on the claims alone and does not: no live claim, and it does not
fit now. It keeps the time it started. -/
theorem since_only_blocked_out {m : Machine} {r : Req} {s : Int} (e : sinceOf m r = some s) :
    m.claims = [] ∧ fitsNow m r = false ∧ (s = m.now ∨ ownSince m r = some s) := by
  simp only [sinceOf] at e
  split at e
  · rename_i hb
    simp only [blockedOut, Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true'] at hb
    refine ⟨hb.1.1, hb.1.2, ?_⟩
    cases ho : ownSince m r <;> simp_all
  · simp at e

/-! ### 4b. No estimate, no start past a ticket that is not held -/

/-- A request without an estimate is never granted past an older live ticket that is not held (the head, or any other). -/
theorem no_estimate_never_past_unheld {m : Machine} {r : Req} {t : Ticket} (he : r.est = none) (hm : t ∈ m.tickets)
    (hid : t.id ≠ r.id) (hh : held m t = false) (hb : before (t.first, t.id) (first m r, r.id) = true) :
    ∀ c g, Admit.decide m r ≠ .ok c g := by
  intro c g e
  have h0 := no_history_no_backfill he e
  have : t ∈ aheadOf m r := by
    simp only [aheadOf, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
    exact ⟨hm, ⟨hid, hh⟩, hb⟩
  simp_all

/-! ### 6. A backfill does not move the head's start later -/

theorem outside_le {m m' : Machine} (hb : m'.busy = m.busy) (hn : m'.ncpu = m.ncpu) (hc : cc m ≤ cc m') :
    outside m' ≤ outside m := by
  simp only [outside, hb, hn]
  have : (m.busy - 100 * cc m' + 50).tdiv 100 ≤ (m.busy - 100 * cc m + 50).tdiv 100 :=
    Int.tdiv_le_tdiv (by decide) (by omega)
  omega

theorem take_nonneg {m : Machine} {r : Req} (w : WF m r) : 0 ≤ (take m r).1 ∧ 0 ≤ (take m r).2 := by
  obtain ⟨hn, -, -, ha, -, -, -, -, -, -, -, -, hk, hm, -⟩ := w
  rcases hx : r.cores with _ | k
  · simp only [take, hx]; omega
  · have := hk k (by simp [hx]); simp only [take, hx]; omega

theorem grant_sums (m : Machine) (r : Req) :
    cc (grant m r) = cc m + (take m r).1 ∧ cm (grant m r) = cm m + (take m r).2 := by
  simp [cc, cm, grant]

theorem released_grant (m : Machine) (r : Req) (τ : Int) (he : (endOf m ⟨(take m r).1, (take m r).2, m.now, r.est⟩).any (· ≤ τ)) :
    released (grant m r) τ = ((released m τ).1 + (take m r).1, (released m τ).2 + (take m r).2) := by
  simp only [released, grant, List.filter_append, List.map_append, List.sum_append]
  simp only [endOf] at he ⊢
  simp [he]

theorem backfill_no_delay {m : Machine} {r : Req} {h : Ticket} {c g : Int} (w : WF m r) (hh : head m r = some h)
    (e : Admit.decide m r = .ok c g) :
    ∃ s s', shadow m h = some s ∧ shadow (grant m r) h = some s' ∧ s' ≤ s := by
  obtain ⟨-, -, -, -, hor⟩ := decide_ok_iff.mp e
  rcases hor with h0 | ⟨h', est, s, hh', he, hs, hle⟩
  · have := head_mem hh; simp_all
  rw [hh] at hh'; cases hh'
  obtain ⟨hev, hfit, -⟩ := shadow_spec hs
  have hnow := events_ge hev
  have hend : (endOf m ⟨(take m r).1, (take m r).2, m.now, r.est⟩).any (· ≤ s) = true := by
    simp [endOf, he]; omega
  have hev' : s ∈ events (grant m r) := by
    simp only [events, List.mem_cons, List.mem_filterMap] at hev ⊢
    rcases hev with hev | ⟨c, hc, hc'⟩
    · exact .inl hev
    · exact .inr ⟨c, by simp [grant, hc], hc'⟩
  have fit' : fitsAt (grant m r) h s = true := by
    rcases hx : h.cores with _ | k
    · simp only [fitsAt, hx, List.all_eq_true] at hfit ⊢
      intro c hc
      simp only [grant, List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact hfit c hc
      · exact hend
    · simp only [fitsAt, hx, Bool.and_eq_true, decide_eq_true_eq] at hfit ⊢
      rw [released_grant m r s hend]
      have ⟨g1, g2⟩ := grant_sums m r
      have := take_nonneg w
      have ho := outside_le (m := m) (m' := grant m r) rfl rfl (by omega)
      have l1 : limC (grant m r) = limC m := rfl
      have l2 : limM (grant m r) = limM m := rfl
      simp only [freeM, l1, l2, g1, g2] at hfit ⊢
      have : (grant m r).ncpu = m.ncpu := rfl
      have : (grant m r).avail = m.avail := rfl
      simp only [*] at ⊢
      omega
  obtain ⟨s', hs', hle'⟩ := shadow_le hev' fit'
  exact ⟨s, s', hs, hs', hle'⟩

/-! ### 13. The ledger `try` leaves -/

theorem after_ledger (m : Machine) (r : Req) :
    ((after m r).claims.length = m.claims.length + 1 ↔ ∃ c g, Admit.decide m r = .ok c g) ∧
    ((∀ c g, Admit.decide m r ≠ .ok c g) → (after m r).claims = m.claims) ∧
    ((∃ t ∈ (after m r).tickets, t.id = r.id) ↔ ∃ a b n, Admit.decide m r = .wait a b n) := by
  unfold after
  cases d : Admit.decide m r <;> simp [grant, List.mem_filter]

/-! ### 13b. Concurrent tries, through `LockExclusive` -/

/-- A request the script would take: a sized one of at least a core, no negative size or estimate. -/
def ReqOK (r : Req) : Prop := (∀ x ∈ r.cores, 1 ≤ x) ∧ 0 ≤ r.mem ∧ ∀ e ∈ r.est, 0 ≤ e

/-- A ledger any `ReqOK` request is well formed on. -/
def Inv (m : Machine) : Prop := WF m ⟨"", none, 0, none⟩

theorem wf_of {m : Machine} {r : Req} (hi : Inv m) (hr : ReqOK r) : WF m r := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, -, -, -⟩ := hi
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, hr.1, hr.2.1, hr.2.2⟩

theorem inv_after {m : Machine} {r : Req} (w : WF m r) : Inv (after m r) := by
  have tn := take_nonneg w
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, hk, hm, he⟩ := w
  have key : ∀ (cl : List Claim) (ts : List Ticket), (∀ c ∈ cl, 0 ≤ c.cores ∧ 0 ≤ c.mem ∧ ∀ e ∈ c.est, 0 ≤ e) →
      (∀ t ∈ ts, (∀ x ∈ t.cores, 0 ≤ x) ∧ 0 ≤ t.mem) → (ts.map (·.id)).Nodup →
      Inv { m with claims := cl, tickets := ts } := fun cl ts hc ht hn =>
    ⟨a, b, c, d, e, f, g, h, i, hc, ht, hn, by simp, by simp, by simp⟩
  have filt : (∀ t ∈ m.tickets.filter (·.id != r.id), (∀ x ∈ t.cores, 0 ≤ x) ∧ 0 ≤ t.mem) :=
    fun t ht => k t (List.mem_filter.mp ht).1
  have filtn : ((m.tickets.filter (·.id != r.id)).map (·.id)).Nodup := by
    exact l.sublist (List.filter_sublist.map _)
  unfold after
  cases hd : Admit.decide m r with
  | ok c' g' =>
    simp only [grant]
    refine key _ _ ?_ ?_ ?_
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact j x hx
      · have : x = ⟨(take m r).1, (take m r).2, m.now, r.est⟩ := by simpa using hx
        subst this; exact ⟨tn.1, tn.2, he⟩
    · exact filt
    · exact filtn
  | wait x y z =>
    simp only
    refine key _ _ j ?_ ?_
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact filt t ht
      · have : t = ⟨r.id, first m r, r.cores, if r.cores.isSome then r.mem else 0, sinceOf m r⟩ := by simpa using ht
        subst this
        refine ⟨fun x hx => by have := hk x hx; omega, ?_⟩
        show 0 ≤ (if r.cores.isSome then r.mem else 0)
        split <;> omega
    · rw [List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨filtn, by simp, ?_⟩
      intro u hu v hv; simp at hv; subst hv
      simp only [List.mem_map, List.mem_filter] at hu
      obtain ⟨t, ⟨-, ht⟩, rfl⟩ := hu
      simpa using ht
  | never x y => simp only; exact key _ _ j filt filtn
  | off => simp only; exact key _ _ j filt filtn

theorem cc_after_ge {m : Machine} {r : Req} (w : WF m r) : cc m ≤ cc (after m r) := by
  have tn := take_nonneg w
  unfold after
  cases hd : Admit.decide m r <;> simp [grant, cc, List.sum_append] at * <;> omega

/-- Over a batch of tries, at most one is granted an exclusive claim, and none is granted anything once a claim holds the
whole machine. -/
theorem tries_excl {rs : List Req} (hr : ∀ r ∈ rs, ReqOK r) :
    ∀ {m : Machine}, Inv m → ∀ {fin ran}, tries m rs = (fin, ran) →
      (ran.filter fun p => p.1.cores.isNone && (match p.2 with | .ok .. => true | _ => false)).length ≤ 1 ∧
      (m.ncpu ≤ cc m → (ran.filter fun p => match p.2 with | .ok .. => true | _ => false).length = 0) := by
  induction rs with
  | nil => intro m _ fin ran h; simp only [tries, Prod.mk.injEq] at h; obtain ⟨-, h2⟩ := h; subst h2; simp
  | cons r rs ih =>
    intro m hi fin ran h
    have w := wf_of hi (hr r (by simp))
    have hi' := inv_after w
    have ncpu_eq : (after m r).ncpu = m.ncpu := by
      unfold after; cases Admit.decide m r <;> rfl
    obtain ⟨l, hl⟩ : ∃ l, tries (after m r) rs = (fin, l) := ⟨(tries (after m r) rs).2, by
      have := h; simp only [tries] at this; rw [Prod.ext_iff] at this ⊢; exact ⟨this.1, rfl⟩⟩
    have hran : ran = (r, decide m r) :: l := by
      simp only [tries, hl, Prod.mk.injEq] at h; exact h.2.symm
    subst hran
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) hi' hl
    have ge := cc_after_ge w
    constructor
    · cases hd : Admit.decide m r with
      | ok c g =>
        rcases hx : r.cores with _ | k
        · have e := excl_grant hx hd
          have hcc : (after m r).ncpu ≤ cc (after m r) := by
            have : cc (after m r) = cc m + c := by
              unfold after; rw [hd]; simp only; rw [(grant_sums m r).1]; simp only [take, hx]; omega
            have := (cc_nil e.1).1; omega
          have := ih2 hcc
          have h0 := List.filter_eq_nil_iff.mp (List.length_eq_zero_iff.mp this)
          have key : ∀ a ∈ l, (a.1.cores.isNone && match a.2 with | .ok .. => true | _ => false) = false := fun a ha => by
            have := h0 a ha
            cases hb : (match a.2 with | .ok .. => true | _ => false) <;> simp_all
          rw [List.filter_cons, List.filter_eq_nil_iff.mpr (fun a ha => by simp [key a ha])]
          simp [hx]
        · simpa [List.filter_cons, hd, hx] using ih1
      | _ => simpa [List.filter_cons, hd] using ih1
    · intro hc
      have hne := excl_alone w hc
      have := ih2 (by omega)
      simp only [List.filter_cons]
      cases hd : Admit.decide m r with
      | ok c g => exact absurd hd (hne c g)
      | _ => simpa [hd] using this

/-- The bug the break guard fixes: under `LockExclusive`, of any batch of concurrent tries at most one is granted an
exclusive claim (`--cores all`). -/
theorem lock_one_exclusive {m0 fin : Machine} {ran : List (Req × Answer)} (lk : LockExclusive m0 ran fin) (hi : Inv m0)
    (hr : ∀ p ∈ ran, ReqOK p.1) :
    (ran.filter fun p => p.1.cores.isNone && (match p.2 with | .ok .. => true | _ => false)).length ≤ 1 := by
  obtain ⟨order, hp, ht⟩ := lk
  rw [← (hp.filter _).length_eq]
  exact (tries_excl (fun r hrr => by
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hrr
    exact hr p (hp.subset hp')) hi ht).1

/-! ### 7. The head runs by its shadow -/

theorem before_asymm {a b : Int × String} (h : before a b = true) : before b a = false := by
  simp only [before, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  simp only [before, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not]
  rcases h with h | ⟨h1, h2⟩
  · omega
  · exact ⟨by omega, .inr (String.lt_asymm h2)⟩

theorem find_id {l : List Ticket} {h : Ticket} (nd : (l.map (·.id)).Nodup) (hm : h ∈ l) :
    l.find? (·.id == h.id) = some h := by
  induction l with
  | nil => simp at hm
  | cons t l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nd
    simp only [List.mem_cons] at hm
    by_cases e : t.id = h.id
    · rcases hm with rfl | hm
      · simp
      · exact absurd ⟨h, hm, e.symm⟩ nd.1
    · rcases hm with rfl | hm
      · simp at e
      · simp [e, ih nd.2 hm]

/-- §6.2 7, no starvation under stated assumptions. `h` was the head of `m` with estimated start `s`; in the later state
`m'` the machine and its files are the same, every claim that was to end by `s` did and nothing granted in between is
left (`m'.claims` is a sublist of the claims expected past `s`), unclaimed use did not grow and the memory the ended
claims held came back. Then `h`'s next try is granted, whatever its estimate.

Restated against §6.2 for the generalised `held`: `head0 m' h` is replaced by "`h` is still queued, before every other
ticket of `m'` that is not held". That `h` itself is not held in `m'` now follows (the hypotheses leave it the room it had
at `s`), so it is no longer assumed. The statement also takes the queue's file names being distinct in `m'`
(`(m'.tickets.map (·.id)).Nodup`, part of `WF`), which §6.2 left out and without which it is false: another ticket under
`h`'s id would set the request's `first`. `s ≤ m'.now` is not needed. -/
theorem head_runs_by_shadow {m m' : Machine} {r : Req} {h : Ticket} {s : Int} (w : WF m r) (hh : head0 m h)
    (hs : shadow m h = some s) (e : Option Int)
    (hn : m'.ncpu = m.ncpu) (ht : m'.total = m.total) (hc : m'.cap = m.cap) (hr : m'.res = m.res)
    (hoff : m'.off = false)
    (hcl : m'.claims.Sublist (m.claims.filter fun c => !(endOf m c).any (· ≤ s)))
    (hout : outside m' ≤ m.ncpu - limC m) (hav : m.avail + (released m s).2 ≤ m'.avail)
    (hm' : h ∈ m'.tickets)
    (hfirst : ∀ t ∈ m'.tickets, t.id ≠ h.id → held m' t = false → before (h.first, h.id) (t.first, t.id) = true)
    (hnd : (m'.tickets.map (·.id)).Nodup) :
    Admit.decide m' ⟨h.id, h.cores, h.mem, e⟩ =
      .ok (take m' ⟨h.id, h.cores, h.mem, e⟩).1 (take m' ⟨h.id, h.cores, h.mem, e⟩).2 := by
  let q : Req := ⟨h.id, h.cores, h.mem, e⟩
  have hfit := (shadow_spec hs).2.1
  have hheld := hh.2.1
  have hcap1 : capC m' = capC m := by simp [capC, hn, hc]
  have hcap2 : capM m' = capM m := by simp [capM, ht, hc]
  have hlim1 : limC m' = limC m := by simp [limC, hcap1, hn, hr]
  have hlim2 : limM m' = limM m := by simp [limM, hcap2, ht, hr]
  -- nothing is ahead of `h` in `m'`
  have hfst : first m' q = h.first := by simp [first, q, find_id hnd hm']
  have hahead : aheadOf m' q = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht'
    simp only [aheadOf, List.mem_filter, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', hfst, q] at ht'
    obtain ⟨ht', ⟨hne, hnh⟩, hb⟩ := ht'
    have := before_asymm (hfirst t ht' hne hnh)
    simp_all
  -- the claims left are a part of those expected past `s`
  have hnn := (w.2.2.2.2.2.2.2.2.2.1)
  have hsub : ∀ f : Claim → Int, (∀ c ∈ m.claims, 0 ≤ f c) →
      (m'.claims.map f).sum + ((m.claims.filter fun c => (endOf m c).any (· ≤ s)).map f).sum ≤ (m.claims.map f).sum := by
    intro f hf
    have h1 := sum_sublist hcl f (fun c hc => hf c (List.mem_filter.mp hc).1)
    have h2 := sum_split m.claims (fun c => (endOf m c).any (· ≤ s)) f
    omega
  have hcc := hsub (·.cores) (fun c hc => (hnn c hc).1)
  have hcm := hsub (·.mem) (fun c hc => (hnn c hc).2.1)
  have hr1 := sum_filter_le m.claims (fun c => (endOf m c).any (· ≤ s)) (·.cores) (fun c hc => (hnn c hc).1)
  have hr2 := sum_filter_le m.claims (fun c => (endOf m c).any (· ≤ s)) (·.mem) (fun c hc => (hnn c hc).2.1)
  have ho := outside_nonneg m'
  simp only [released] at hav
  apply decide_ok_iff.mpr
  refine ⟨hoff, ?_, ?_, rfl, .inl hahead⟩
  all_goals rcases hx : h.cores with _ | k
  · obtain ⟨-, hw, -⟩ := (held_excl hx).mp hheld
    simp only [tooBig, Bool.not_eq_false', whole, hcap1, hcap2, hn, ht]
    simpa [whole] using hw
  · simp only [fitsAt, hx, Bool.and_eq_true, decide_eq_true_eq] at hfit
    simp only [released] at hfit
    have := limC_le_capC m
    have := limM_le_capM m
    simp only [tooBig, hcap1, hcap2, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    simp only [freeM, cc, cm] at hfit
    omega
  · obtain ⟨-, hw, hr0⟩ := (held_excl hx).mp hheld
    have hl : limC m = m.ncpu := by
      have hw' : m.ncpu ≤ capC m := by simp [whole] at hw; exact hw.1
      have h1 : m.res.1 = 0 := by rw [hr0]
      have := w.1
      simp only [limC, lim, h1]; omega
    simp only [fitsAt, hx, List.all_eq_true] at hfit
    have h0 : m.claims.filter (fun c => !(endOf m c).any (· ≤ s)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro c hc; simp [hfit c hc]
    rw [h0] at hcl
    have ho0 : outside m' = 0 := by have := outside_nonneg m'; rw [hl] at hout; omega
    simp only [fitsNow, Bool.and_eq_true, List.isEmpty_iff, quiet, beq_iff_eq, List.sublist_nil.mp hcl,
      hr, hr0, ho0, true_and]
  · simp only [fitsAt, hx, Bool.and_eq_true, decide_eq_true_eq] at hfit
    simp only [released] at hfit
    have := (limC_bounds w).2.1
    simp only [fitsNow, Bool.and_eq_true, decide_eq_true_eq, freeC, freeM, hlim1, hlim2, hn]
    simp only [freeM, cc, cm] at hfit ⊢
    omega

/-! ### 11. The same of the shipped script, through `ScriptAdmits` -/

section Script
variable {run : Machine → Req → Answer} (sa : ScriptAdmits run) {m : Machine} {r : Req} (w : WF m r)
include sa w

theorem script_ok_iff {c g : Int} :
    run m r = .ok c g ↔ m.off = false ∧ tooBig m r = false ∧ fitsNow m r = true ∧ (c, g) = take m r ∧
      (aheadOf m r = [] ∨ ∃ h e s, head m r = some h ∧ r.est = some e ∧ shadow m h = some s ∧ m.now + e ≤ s) := by
  rw [sa m r w]; exact decide_ok_iff

theorem script_off_iff : run m r = .off ↔ m.off = true := by rw [sa m r w]; exact off_iff

theorem script_never_iff {a b : Int} :
    run m r = .never a b ↔ m.off = false ∧ tooBig m r = true ∧ a = capC m ∧ b = capM m := by
  rw [sa m r w]; exact never_iff

theorem script_grant_within {c g : Int} (e : run m r = .ok c g) :
    cc m + c ≤ limC m ∧ cc m + c + outside m ≤ m.ncpu ∧ cm m + g ≤ limM m ∧ g ≤ m.avail :=
  grant_within w (sa m r w ▸ e)

theorem script_no_history_no_backfill {c g : Int} (he : r.est = none) (e : run m r = .ok c g) : aheadOf m r = [] :=
  no_history_no_backfill he (sa m r w ▸ e)

theorem script_unknown_shadow_no_backfill {h : Ticket} (e : head m r = some h) (hs : shadow m h = none) :
    (∃ c ∈ m.claims, c.est = none) ∧ ∀ c g, run m r ≠ .ok c g := by
  rw [sa m r w]; exact unknown_shadow_no_backfill e hs

theorem script_backfill_no_delay {h : Ticket} {c g : Int} (hh : head m r = some h) (e : run m r = .ok c g) :
    ∃ s s', shadow m h = some s ∧ shadow (grant m r) h = some s' ∧ s' ≤ s :=
  backfill_no_delay w hh (sa m r w ▸ e)

theorem script_excl_grant {c g : Int} (hx : r.cores = none) (e : run m r = .ok c g) :
    m.claims = [] ∧ m.res = (0, 0) ∧ outside m = 0 ∧ c = m.ncpu ∧ g = m.avail ∧ whole m = true :=
  excl_grant hx (sa m r w ▸ e)

theorem script_excl_alone (hc : m.ncpu ≤ cc m) : ∀ c g, run m r ≠ .ok c g := by
  rw [sa m r w]; exact excl_alone w hc

theorem script_no_estimate_never_past_unheld {t : Ticket} (he : r.est = none) (hm : t ∈ m.tickets) (hid : t.id ≠ r.id)
    (hh : held m t = false) (hb : before (t.first, t.id) (first m r, r.id) = true) : ∀ c g, run m r ≠ .ok c g := by
  rw [sa m r w]; exact no_estimate_never_past_unheld he hm hid hh hb

end Script

theorem script_head_runs_by_shadow {run : Machine → Req → Answer} (sa : ScriptAdmits run) {m m' : Machine} {r : Req}
    {h : Ticket} {s : Int} (w : WF m r) (hh : head0 m h) (hs : shadow m h = some s) (e : Option Int)
    (w' : WF m' ⟨h.id, h.cores, h.mem, e⟩)
    (hn : m'.ncpu = m.ncpu) (ht : m'.total = m.total) (hc : m'.cap = m.cap) (hr : m'.res = m.res)
    (hoff : m'.off = false)
    (hcl : m'.claims.Sublist (m.claims.filter fun c => !(endOf m c).any (· ≤ s)))
    (hout : outside m' ≤ m.ncpu - limC m) (hav : m.avail + (released m s).2 ≤ m'.avail)
    (hm' : h ∈ m'.tickets)
    (hfirst : ∀ t ∈ m'.tickets, t.id ≠ h.id → held m' t = false → before (h.first, h.id) (t.first, t.id) = true) :
    run m' ⟨h.id, h.cores, h.mem, e⟩ =
      .ok (take m' ⟨h.id, h.cores, h.mem, e⟩).1 (take m' ⟨h.id, h.cores, h.mem, e⟩).2 := by
  rw [sa _ _ w']
  exact head_runs_by_shadow w hh hs e hn ht hc hr hoff hcl hout hav hm' hfirst w'.2.2.2.2.2.2.2.2.2.2.2.1

end Claims.Proofs
