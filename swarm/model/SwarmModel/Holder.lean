import SwarmModel.Taken

/-! L3, the holder half. `Pa s a t`: agent `a` (not booting) holds the claimed task `t`, whose unblock answer it has not
read, and the answer message is unread in its inbox. `pa_step`: any step keeps that, or the holder stops holding (the
task reopened or ended), or the answer is read, or the slot is a fresh agent. -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

def Pa (s : State) (a t : Nat) : Prop :=
  ownsClaimed s a t = true ∧ t ∈ s.pend ∧ (s.agt a).boot = false ∧ (s.agt a).live = true ∧
    ∃ i, i ∈ unread s a ∧ (s.msg i).kind = .answer ∧ (s.msg i).task = t

theorem unread_ext_mem {s x : State} {a i : Nat} (h : Ext s x a) (hi : i ∈ unread s a) :
    i ∈ unread x a ∧ x.msg i = s.msg i := by
  obtain ⟨⟨e, p⟩, q⟩ := h
  rw [mem_unread] at hi
  obtain ⟨h1, h2, h3⟩ := hi
  have hm := msg_ext p h2
  refine ⟨?_, hm⟩
  rw [mem_unread]
  refine ⟨by rw [q]; exact h1, by rw [p, List.length_append]; omega, ?_⟩
  simp only [addressed] at h3 ⊢
  rw [hm]; exact h3

theorem showMsg_pend_sub (s : State) (a j t : Nat) (h : t ∉ s.pend) : t ∉ (showMsg s a j).pend := by
  unfold showMsg; simp only []; split
  · simp [h]
  · split <;> simp [h]

theorem showAll_pend_sub (a t : Nat) : ∀ (ids : List Nat) (s : State), t ∉ s.pend → t ∉ (showAll s a ids).pend
  | [], _, h => h
  | j :: js, s, h => by rw [showAll_cons]; exact showAll_pend_sub a t js _ (showMsg_pend_sub s a j t h)

theorem showAll_clears (a t i : Nat) : ∀ (ids : List Nat) (s : State), i ∈ ids → (s.msg i).kind = .answer →
    (s.msg i).task = t → (s.tk t).owner = some a → t ∉ (showAll s a ids).pend
  | [], _, hm, _, _, _ => by cases hm
  | j :: js, s, hm, hk, ht, ho => by
    rw [showAll_cons]
    by_cases hj : i = j
    · subst hj
      refine showAll_pend_sub a t js _ ?_
      unfold showMsg
      simp only [State.tk, List.getD_eq_getElem?_getD] at ho
      simp [hk, ht, ho]
    · have hm' : i ∈ js := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e hj
        · exact e
      exact showAll_clears a t i js _ hm' (by simpa [State.msg] using hk) (by simpa [State.msg] using ht)
        (by simpa [State.tk] using ho)


/-- the log only grew, `a`'s cursor stayed, and `a` is live: relative to the state `s` before -/
def Gk (s x : State) (a : Nat) : Prop := Ext s x a ∧ (x.agt a).live = true

theorem gk_frame {s x x' : State} {a : Nat} (hag : x'.ag = x.ag) (hl : x'.log = x.log) (hc : x'.cursor = x.cursor)
    (h : Gk s x a) : Gk s x' a := by
  obtain ⟨⟨⟨e, pe⟩, q⟩, h2⟩ := h
  refine ⟨⟨⟨e, by rw [hl]; exact pe⟩, by simpa [State.cur, hc] using q⟩, by rw [agt_of_ag hag]; exact h2⟩

theorem gk_setTask {s x : State} {a t : Nat} {f : Task → Task} (h : Gk s x a) : Gk s (setTask x t f) a :=
  gk_frame (by simp) (by simp) (by simp) h
theorem gk_post {s x : State} {a : Nat} {m : Msg} (h : Gk s x a) : Gk s (post x m) a := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨ext_trans h1 (ext_post _ _ _), by simpa using h2⟩
theorem gk_takes {c : Cfg} {s x : State} {a b t : Nat} (h : Gk s x a) : Gk s (takes c x b t) a := by
  obtain ⟨⟨⟨e, pe⟩, q⟩, h2⟩ := h
  refine ⟨⟨⟨e, by simpa using pe⟩, by simpa [State.cur] using q⟩, ?_⟩
  unfold Agent.live at h2 ⊢; simp only [takes_st]; exact h2
theorem gk_setAg {s x : State} {a b : Nat} {f : Agent → Agent} (hf : ∀ g, g.live = true → (f g).live = true) (h : Gk s x a) :
    Gk s (setAg x b f) a := by
  obtain ⟨⟨⟨e, pe⟩, q⟩, h2⟩ := h
  refine ⟨⟨⟨e, by simpa using pe⟩, by simpa [State.cur] using q⟩, ?_⟩
  rw [agt_setAg]; split
  · exact hf _ h2
  · exact h2
theorem gk_deliver_ne {s x : State} {a b : Nat} (hb : b ≠ a) (h : Gk s x a) : Gk s (deliver x b) a := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨ext_trans h1 (ext_deliver_ne x hb), by simpa [Agent.live] using h2⟩

macro "gk_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible assumption
    | (with_reducible apply gk_takes)
    | (with_reducible apply gk_setTask)
    | (with_reducible apply gk_post)
    | (refine gk_setAg ?_ ?_ <;> first | (intro g hg; simp_all [Agent.live]; done) | skip)
    | (refine gk_frame ?_ ?_ ?_ ‹Gk _ _ _› <;> rfl)))

theorem step_gen {c : Cfg} {s s' : State} {a : Nat} {act : Action}
    (hq : act ≠ .tick ∧ ∀ b, act ≠ .leave b ∧ act ≠ .reapGone b ∧ act ≠ .readAll b ∧ act ≠ .wake b ∧ act ≠ .prompt b ∧
      act ≠ .boot b ∧ act ≠ .hcClear b ∧ act ≠ .wakeWrite b ∧ ∀ f, act ≠ .endOther b f)
    (hl : (s.agt a).live = true) (hs : step c s act = some s') : Gk s s' a := by
  have h0 : Gk s s a := ⟨ext_refl s a, hl⟩
  open_step hs
  case tick => exact absurd rfl hq.1
  case leave b => exact absurd rfl (hq.2 b).1
  case reapGone b => exact absurd rfl (hq.2 b).2.1
  case readAll b => exact absurd rfl (hq.2 b).2.2.1
  case wake b => exact absurd rfl (hq.2 b).2.2.2.1
  case prompt b => exact absurd rfl (hq.2 b).2.2.2.2.1
  case boot b => exact absurd rfl (hq.2 b).2.2.2.2.2.1
  case hcClear b => exact absurd rfl (hq.2 b).2.2.2.2.2.2.1
  case wakeWrite b => exact absurd rfl (hq.2 b).2.2.2.2.2.2.2.1
  case endOther b f => exact absurd rfl ((hq.2 b).2.2.2.2.2.2.2.2 f)
  case unblock t₀ =>
    split at hs
    · rw [when_eq_some] at hs; obtain ⟨hg, rfl⟩ := hs
      exact gk_frame (s := s) (x := post (setTask s t₀ _) _) rfl rfl rfl (gk_post (gk_setTask h0))
    · cases hs
  case claimWrite b =>
    obtain ⟨hg, rfl⟩ := hs
    split
    · have hI' : Gk s { takes c (claimed s b (s.agt b).reading) b (s.agt b).reading with early := s.early || !depsDone s (s.agt b).reading } a :=
        gk_frame (x := takes c (claimed s b (s.agt b).reading) b (s.agt b).reading) rfl rfl rfl (gk_takes (gk_setTask h0))
      exact gk_setAg (fun g hg => by simp_all [Agent.live]) hI'
    · gk_tac
  all_goals (obtain ⟨hg, rfl⟩ := hs)
  all_goals (try split)
  all_goals (try simp only [unbelieve, awake, claimed])
  all_goals gk_tac


-- ---------- ending an agent, and the tick ----------

theorem endAgent_own {y : State} {b a t : Nat} (h : ownsClaimed (endAgent y b) a t = true) :
    ownsClaimed y a t = true ∧ (endAgent y b).agt a = y.agt a := by
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h
  rw [endAgent_tk] at h
  by_cases hh : held (y.tk t) b = true
  · rw [if_pos hh] at h; simp at h
  · rw [if_neg hh] at h
    have hb : ¬ (b = a ∧ a < y.ag.length) := by
      rintro ⟨rfl, _⟩
      apply hh
      simp [held, h.1, h.2]
    refine ⟨by simp [ownsClaimed, h.1, h.2], ?_⟩
    rw [endAgent_agt, if_neg hb]

theorem Tp_end {s y : State} {a t b : Nat}
    (h : ownsClaimed y a t = true → (y.agt a).boot = false → Gk s y a) :
    ownsClaimed (endAgent y b) a t = true → ((endAgent y b).agt a).boot = false → Gk s (endAgent y b) a := by
  intro h1 h2
  obtain ⟨o, e⟩ := endAgent_own h1
  rw [e] at h2
  obtain ⟨⟨⟨e1, p1⟩, q1⟩, g2⟩ := h o h2
  exact ⟨⟨⟨e1, by simpa using p1⟩, by simpa [State.cur] using q1⟩, by rw [e]; exact g2⟩


theorem gk_trans {s x x' : State} {a : Nat} (h : Gk s x a) (e : Ext x x' a) (hl : (x.agt a).live = true → (x'.agt a).live = true) :
    Gk s x' a := ⟨ext_trans h.1 e, hl h.2⟩

theorem reapTask_own {c : Cfg} {x : State} {v a t : Nat} (h : ownsClaimed (reapTask c x v) a t = true) :
    ownsClaimed x a t = true := by
  by_cases hv : v = t
  · subst hv
    unfold reapTask at h; simp only [] at h
    split at h
    · split at h
      · have : (x.tk v).st ≠ .absent := by
          rename_i hc; simp [Bool.and_eq_true] at hc; simp [hc.1.1]
        simp [ownsClaimed, tk_setTask_self this] at h
      · exact h
    · exact h
  · rwa [ownsClaimed, reapTask_tk_ne (Ne.symm hv), ← ownsClaimed] at h

theorem Tp_reap {c : Cfg} {s y : State} {a t v : Nat}
    (h : ownsClaimed y a t = true → (y.agt a).boot = false → Gk s y a) :
    ownsClaimed (reapTask c y v) a t = true → ((reapTask c y v).agt a).boot = false → Gk s (reapTask c y v) a := by
  intro h1 h2
  have e : (reapTask c y v).agt a = y.agt a := by simp [State.agt]
  rw [e] at h2
  obtain ⟨e1, p1⟩ := reapTask_ext c y v
  exact gk_trans (h (reapTask_own h1) h2) ⟨⟨e1, p1⟩, by simp [State.cur]⟩ (by rw [e]; exact id)

theorem Tp_dig {s y : State} {a t b : Nat} {pl : List Nat}
    (h : ownsClaimed y a t = true → (y.agt a).boot = false → Gk s y a) :
    ownsClaimed (post (setAg y b fun g => { g with told := pl ++ g.told }) ⟨none, b, false, .digest, 0⟩) a t = true →
    ((post (setAg y b fun g => { g with told := pl ++ g.told }) ⟨none, b, false, .digest, 0⟩).agt a).boot = false →
    Gk s (post (setAg y b fun g => { g with told := pl ++ g.told }) ⟨none, b, false, .digest, 0⟩) a := by
  intro h1 h2
  have e : (post (setAg y b fun g => { g with told := pl ++ g.told }) ⟨none, b, false, .digest, 0⟩).agt a =
      if b = a ∧ a < y.ag.length then { y.agt a with told := pl ++ (y.agt a).told } else y.agt a := by
    simp only [post_agt, agt_setAg]
  have h1' : ownsClaimed y a t = true := by simpa [ownsClaimed] using h1
  have h2' : (y.agt a).boot = false := by rw [e] at h2; split at h2 <;> simpa using h2
  refine gk_trans (h h1' h2') (ext_trans (x := setAg y b _) (ext_frame (by simp) (by simp) a) (ext_post _ _ a)) ?_
  rw [e]; split <;> simp [Agent.live]


theorem spawnFor_own {c : Cfg} {pl : List Nat} {y : State} {u a t : Nat} (hlt : a < y.ag.length)
    (h : ownsClaimed (spawnFor c pl y u) a t = true) :
    ownsClaimed y a t = true ∨ ((spawnFor c pl y u).agt a).boot = true := by
  unfold spawnFor at h ⊢
  split at h
  · rename_i a' hna
    split at h
    · rename_i hc
      simp only [hna]
      rw [if_pos hc]
      rcases claimed_tk (State.mk _ _ _ _ _ _ _ _ _ _) a' u t with e | e
      · refine Or.inl ?_
        simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h ⊢
        rw [e] at h; simpa only [tk_mk, setAg_task, tk_def] using h
      · refine Or.inr ?_
        simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h
        rw [e] at h
        have : a' = a := by simpa using h.2
        subst this
        simp only [claimed_agt, agt_mk, agt_def, agt_setAg, setAg_ag_length]
        simp [hlt]
    · exact Or.inl h
  · exact Or.inl h

theorem Tp_spawn {c : Cfg} {pl : List Nat} {s y : State} {a t u : Nat} (hlt : a < y.ag.length)
    (h : ownsClaimed y a t = true → (y.agt a).boot = false → Gk s y a) :
    ownsClaimed (spawnFor c pl y u) a t = true → ((spawnFor c pl y u).agt a).boot = false → Gk s (spawnFor c pl y u) a := by
  intro h1 h2
  rcases spawnFor_own hlt h1 with o | o
  · rcases spawnFor_agt c pl y u a with e | ⟨_, _, hb, _⟩
    · rw [e] at h2
      have g := h o h2
      exact ⟨⟨⟨(g.1.1).choose, by rw [spawnFor_log]; exact (g.1.1).choose_spec⟩, by
        have e2 := spawnFor_cur_ne (c := c) (pl := pl) (u := u) g.2
        show (spawnFor c pl y u).cur a = s.cur a
        rw [e2]; exact g.1.2⟩, by rw [e]; exact g.2⟩
    · rw [hb] at h2; cases h2
  · rw [o] at h2; cases h2


theorem lt_of_live {s : State} {a : Nat} (h : (s.agt a).live = true) : a < s.ag.length := by
  refine Classical.byContradiction fun hl => ?_
  rw [agt_of_ge (Nat.le_of_not_lt hl)] at h; exact absurd h (by decide)

theorem pa_tick {c : Cfg} {s s' : State} {a t : Nat} (hP : Pa s a t) (hs : step c s .tick = some s')
    (hy1 : ownsClaimed s' a t = true) (hy3 : (s'.agt a).boot = false) : Gk s s' a := by
  obtain ⟨_, e⟩ := (step_tick hs).2
  subst e
  have hlt := lt_of_live hP.2.2.2.1
  have h0 : Gk s s a := ⟨ext_refl s a, hP.2.2.2.1⟩
  have := tick_inv (c := c) (fun y => y.ag.length = s.ag.length ∧ (ownsClaimed y a t = true → (y.agt a).boot = false → Gk s y a))
    (fun x v ⟨hl, h⟩ => ⟨by simp [hl], Tp_reap h⟩)
    (fun x ⟨hl, h⟩ => ⟨by simp [hl], fun h1 h2 => by
      have := h (by simpa [ownsClaimed, State.tk] using h1) (by simpa [State.agt] using h2)
      exact gk_frame (x := x) (by simp) (by simp) (by simp) this⟩)
    (fun x b ⟨hl, h⟩ => ⟨by simp [endAgent, hl], Tp_end h⟩)
    (fun x b pl ⟨hl, h⟩ => ⟨by simp [hl], Tp_dig h⟩)
    (fun pl x u ⟨hl, h⟩ _ => ⟨by rw [spawnFor_len, hl], Tp_spawn (by rw [hl]; exact hlt) h⟩)
    (s := s) ⟨rfl, fun _ _ => h0⟩
  exact this.2 hy1 hy3


theorem pa_owner {s : State} {a t : Nat} (h : ownsClaimed s a t = true) : (s.tk t).owner = some a := by
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h; exact h.2

theorem deliver_clears {s : State} {a t : Nat} (hP : Pa s a t) : t ∉ (deliver s a).pend := by
  obtain ⟨hown, _, _, _, i, hi, hk, ht⟩ := hP
  exact showAll_clears a t i (unread s a) s hi hk ht (pa_owner hown)

theorem deliver_clears_of {x s : State} {a t : Nat} (hl : x.log = s.log) (hc : x.cursor = s.cursor)
    (ho : (x.tk t).owner = some a) (hP : Pa s a t) : t ∉ (deliver x a).pend := by
  obtain ⟨_, _, _, _, i, hi, hk, ht⟩ := hP
  have hu : unread x a = unread s a := unread_congr hl hc a
  have hm : x.msg i = s.msg i := by simp [State.msg, hl]
  exact showAll_clears a t i (unread x a) x (hu ▸ hi) (hm ▸ hk) (hm ▸ ht) ho

theorem gk_leave {s : State} {b a t : Nat} {f : Agent → Agent} (hf : ∀ g, g.live = true → (f g).live = true)
    (h0 : Gk s s a) (hy1 : ownsClaimed (endAgent (setAg s b f) b) a t = true) : Gk s (endAgent (setAg s b f) b) a := by
  obtain ⟨_, e⟩ := endAgent_own hy1
  have gy : Gk s (setAg s b f) a := gk_setAg hf h0
  obtain ⟨⟨⟨e1, p1⟩, q1⟩, g2⟩ := gy
  exact ⟨⟨⟨e1, by simpa using p1⟩, by simpa [State.cur] using q1⟩, by rw [e]; exact g2⟩

theorem gk_of_step {c : Cfg} {s s' : State} {a t : Nat} {act : Action} (hr : c.racy = false) (hP : Pa s a t)
    (hs : step c s act = some s') (hy1 : ownsClaimed s' a t = true) (hy2 : t ∈ s'.pend) (hy3 : (s'.agt a).boot = false) :
    Gk s s' a := by
  have hl := hP.2.2.2.1
  have h0 : Gk s s a := ⟨ext_refl s a, hl⟩
  have hfl : ∀ (g : Agent) (f : Agent → Agent), (∀ g, g.live = true → (f g).live = true) → g.live = true → (f g).live = true :=
    fun g f hf => hf g
  match act, hs with
  | .tick, hs => exact pa_tick hP hs hy1 hy3
  | .leave b, hs =>
    simp only [step, leave, leaveIf, when_eq_some] at hs
    obtain ⟨_, rfl⟩ := hs
    exact gk_leave (fun g hg => by simpa [Agent.live] using hg) h0 hy1
  | .reapGone b, hs =>
    simp only [step, reapGone, leaveIf, when_eq_some] at hs
    obtain ⟨_, rfl⟩ := hs
    exact gk_leave (fun g hg => by simpa [Agent.live] using hg) h0 hy1
  | .endOther b f, hs =>
    simp only [step, endOther, leaveIf, when_eq_some] at hs
    obtain ⟨_, rfl⟩ := hs
    exact gk_leave (fun g hg => by simpa [Agent.live] using hg) h0 hy1
  | .readAll b, hs =>
    simp only [step, readAll, when_eq_some] at hs
    obtain ⟨_, rfl⟩ := hs
    by_cases hb : b = a
    · subst hb; exact absurd hy2 (deliver_clears hP)
    · exact gk_deliver_ne hb h0
  | .wake b, hs =>
    simp only [step, wake, when_eq_some] at hs
    obtain ⟨_, rfl⟩ := hs
    by_cases hb : b = a
    · subst hb; exact absurd (by simpa [awake] using hy2) (deliver_clears hP)
    · exact gk_setAg (fun g hg => by simp [awake, Agent.live]) (gk_deliver_ne hb h0)
  | .prompt b, hs =>
    simp only [step, prompt, when_eq_some] at hs
    obtain ⟨_, rfl⟩ := hs
    by_cases hb : b = a
    · subst hb; exact absurd (by simpa using hy2) (deliver_clears hP)
    · exact gk_setAg (fun g hg => by simp [Agent.live]) (gk_deliver_ne hb h0)
  | .boot b, hs =>
    simp only [step, boot, when_eq_some] at hs
    obtain ⟨hg, rfl⟩ := hs
    have hb : b ≠ a := by rintro rfl; simp [hP.2.2.1] at hg
    split
    · exact gk_takes (gk_setAg (fun g hg => by simp [Agent.live]) (gk_deliver_ne hb h0))
    · exact gk_setAg (fun g hg => by simp [Agent.live]) (gk_deliver_ne hb h0)
  | .hcClear b, hs =>
    simp only [step, hcClear, when_eq_some] at hs
    obtain ⟨_, rfl⟩ := hs
    by_cases hb : b = a
    · subst hb
      refine absurd (by simpa using hy2) ?_
      refine deliver_clears_of (s := s) rfl rfl ?_ hP
      rw [tk_map (s := s) (g := fun k => if (k.owner = some b ∧ k.st = TSt.blocked) ∧ k.hcq = true then
          { k with st := .claimed, lease := true, hcq := false } else k) (by simp) rfl t]
      split <;> simp [pa_owner hP.1]
    · exact gk_setAg (fun g hg => by simp [Agent.live]) (gk_deliver_ne hb (gk_frame (x := s) (by simp) (by simp) (by simp) h0))
  | .wakeWrite b, hs =>
    simp only [step, wakeWrite, when_eq_some] at hs
    simp [hr] at hs
  | .bgStart b, hs => exact step_gen (by simp) hl hs
  | .bgEnd b, hs => exact step_gen (by simp) hl hs
  | .claim b u, hs => exact step_gen (by simp) hl hs
  | .claimRead b u, hs => exact step_gen (by simp) hl hs
  | .claimWrite b, hs => exact step_gen (by simp) hl hs
  | .renew b u, hs => exact step_gen (by simp) hl hs
  | .release b u, hs => exact step_gen (by simp) hl hs
  | .block b u, hs => exact step_gen (by simp) hl hs
  | .done b u e, hs => exact step_gen (by simp) hl hs
  | .dropOwn b u, hs => exact step_gen (by simp) hl hs
  | .lock b u, hs => exact step_gen (by simp) hl hs
  | .unlock b u, hs => exact step_gen (by simp) hl hs
  | .postTo b u v, hs => exact step_gen (by simp) hl hs
  | .stop b u, hs => exact step_gen (by simp) hl hs
  | .wakeRead b, hs => exact step_gen (by simp) hl hs
  | .git b op, hs => exact step_gen (by simp) hl hs
  | .world w op, hs => exact step_gen (by simp) hl hs
  | .stale b, hs => exact step_gen (by simp) hl hs
  | .nudge b, hs => exact step_gen (by simp) hl hs
  | .waiterGone b, hs => exact step_gen (by simp) hl hs
  | .age b, hs => exact step_gen (by simp) hl hs
  | .cool b, hs => exact step_gen (by simp) hl hs
  | .expire b, hs => exact step_gen (by simp) hl hs
  | .expireLock b, hs => exact step_gen (by simp) hl hs
  | .hcPrompt b, hs => exact step_gen (by simp) hl hs
  | .die b, hs => exact step_gen (by simp) hl hs
  | .add b, hs => exact step_gen (by simp) hl hs
  | .after b u, hs => exact step_gen (by simp) hl hs
  | .unblock b, hs => exact step_gen (by simp) hl hs
  | .drop b, hs => exact step_gen (by simp) hl hs
  | .releaseOther b, hs => exact step_gen (by simp) hl hs


-- ---------- no agent starts a background job ----------

def Bf (s : State) : Prop := ∀ b, (s.agt b).bg = false

theorem bf_frame {s s' : State} (hag : s'.ag = s.ag) (h : Bf s) : Bf s' := fun b => by rw [agt_of_ag hag]; exact h b

theorem bf_setAg' {s : State} {a : Nat} {f : Agent → Agent} (hf : (f (s.agt a)).bg = false) (h : Bf s) : Bf (setAg s a f) := by
  intro b
  rw [agt_setAg]
  split
  · rename_i hab; obtain ⟨rfl, _⟩ := hab; exact hf
  · exact h b

theorem bf_setAg {s : State} {a : Nat} {f : Agent → Agent} (hf : (s.agt a).bg = false → (f (s.agt a)).bg = false) (h : Bf s) :
    Bf (setAg s a f) := bf_setAg' (hf (h a)) h

theorem bf_deliver {s : State} {a : Nat} (h : Bf s) : Bf (deliver s a) := fun b => by simp only [deliver_bg]; exact h b
theorem bf_takes {c : Cfg} {s : State} {a t : Nat} (h : Bf s) : Bf (takes c s a t) := fun b => by simp only [takes_bg]; exact h b
theorem bf_showAll {s : State} {a : Nat} {ids : List Nat} (h : Bf s) : Bf (showAll s a ids) := fun b => by
  obtain ⟨bl, e⟩ := showAll_agt a ids b s
  rw [e]; exact h b
theorem bf_setTask {s : State} {t : Nat} {f : Task → Task} (h : Bf s) : Bf (setTask s t f) := bf_frame (by simp) h
theorem bf_post {s : State} {m : Msg} (h : Bf s) : Bf (post s m) := bf_frame (by simp) h

theorem bf_endAgent {s : State} {a : Nat} (h : Bf s) : Bf (endAgent s a) := fun b => by
  rw [endAgent_agt]; split
  · simp; exact h b
  · exact h b

theorem bf_spawnFor {c : Cfg} {pl : List Nat} {x : State} {t : Nat} (h : Bf x) : Bf (spawnFor c pl x t) := by
  unfold spawnFor; split
  · split
    · intro b
      simp only [claimed_agt, agt_mk, agt_def, agt_setAg]
      split
      · rfl
      · exact h b
    · exact h
  · exact h

theorem bf_tickOf {c : Cfg} {s : State} (h : Bf s) : Bf (tickOf c s) :=
  tick_inv (Bf) (fun x t hx => bf_frame (by simp) hx) (fun x hx => bf_frame (by simp) hx)
    (fun _ _ => bf_endAgent) (fun x a pl hx => bf_post (bf_setAg (fun hh => by simpa using hh) hx))
    (fun _ _ _ hx _ => bf_spawnFor hx) h

macro "bf_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible assumption
    | (with_reducible apply bf_deliver)
    | (with_reducible apply bf_takes)
    | (with_reducible apply bf_setTask)
    | (with_reducible apply bf_post)
    | (with_reducible apply bf_showAll)
    | (refine bf_setAg ?_ ?_ <;> first | (intro hh; simp_all; done) | skip)
    | (refine bf_frame ?_ ‹Bf _› <;> rfl)))

theorem bf_step {c : Cfg} {s s' : State} {act : Action} (hq : ∀ b, act ≠ .bgStart b) (hI : Bf s) (hs : step c s act = some s') : Bf s' := by
  open_step hs
  case tick => obtain ⟨_, rfl⟩ := hs; exact bf_tickOf hI
  case bgStart a => exact absurd rfl (hq a)
  case unblock t₀ =>
    split at hs
    · rw [when_eq_some] at hs; obtain ⟨_, rfl⟩ := hs; exact bf_frame (s := s) (by simp) hI
    · cases hs
  case leave a => obtain ⟨_, rfl⟩ := hs; exact bf_endAgent (bf_setAg (fun hh => by simpa using hh) hI)
  case reapGone a => obtain ⟨_, rfl⟩ := hs; exact bf_endAgent (bf_setAg (fun hh => by simpa using hh) hI)
  case endOther a f => obtain ⟨_, rfl⟩ := hs; exact bf_endAgent (bf_setAg (fun hh => by simpa using hh) hI)
  case claimWrite a =>
    obtain ⟨hg, rfl⟩ := hs
    split
    · have hI' : Bf { takes c (claimed s a (s.agt a).reading) a (s.agt a).reading with early := s.early || !depsDone s (s.agt a).reading } :=
        bf_frame (s := takes c (claimed s a (s.agt a).reading) a (s.agt a).reading) rfl (bf_takes (bf_setTask hI))
      exact bf_setAg' (by simpa using hI' a) hI'
    · bf_tac
  all_goals (obtain ⟨hg, rfl⟩ := hs)
  all_goals (try split)
  all_goals (try simp only [unbelieve, awake, claimed])
  all_goals bf_tac



/-- The per-action step lemma. A step leaves `a` holding `t` with the answer unread (and the answer message unread in its inbox),
or `a` no longer holds `t` (reopened, done, dropped, blocked), or the answer is read, or the slot is a fresh agent that boots. -/
theorem pa_step {c : Cfg} {s s' : State} {a t : Nat} {act : Action} (hr : c.racy = false) (hP : Pa s a t)
    (hs : step c s act = some s') (hy1 : ownsClaimed s' a t = true) (hy2 : t ∈ s'.pend) (hy3 : (s'.agt a).boot = false) :
    Pa s' a t := by
  have g := gk_of_step hr hP hs hy1 hy2 hy3
  obtain ⟨_, _, _, _, i, hi, hk, ht⟩ := hP
  obtain ⟨h1, h2⟩ := unread_ext_mem g.1 hi
  exact ⟨hy1, hy2, hy3, g.2, i, h1, by rw [h2]; exact hk, by rw [h2]; exact ht⟩

theorem readAll_clears {c : Cfg} {s s' : State} {a t : Nat} (hP : Pa s a t) (hs : step c s (.readAll a) = some s') :
    t ∉ s'.pend := by
  simp only [step, readAll, when_eq_some] at hs
  obtain ⟨_, rfl⟩ := hs
  exact deliver_clears hP

theorem hcClear_clears {c : Cfg} {s s' : State} {a t : Nat} (hP : Pa s a t) (hs : step c s (.hcClear a) = some s') :
    t ∉ s'.pend := by
  simp only [step, hcClear, when_eq_some] at hs
  obtain ⟨_, rfl⟩ := hs
  show t ∉ (deliver _ a).pend
  refine deliver_clears_of (s := s) rfl rfl ?_ hP
  rw [tk_map (s := s) (g := fun k => if (k.owner == some a && k.st == TSt.blocked && k.hcq) = true then
      { k with st := .claimed, lease := true, hcq := false } else k) (by simp) rfl t]
  split <;> simp [pa_owner hP.1]

/-- L3, the holder half. In a fair run of an instance with PR #110 or #111, an agent that holds a claimed task whose unblock
answer sits unread in its inbox either reads it, or stops holding the task (it is reopened, or ended), or the slot is taken by a spawned agent
(the other half: it reads the answer at its first turn, which `boot` does but a reap may beat, finding #17). The agent must not die or
start a background job after the start. -/
theorem holder_leads_to {c : Cfg} (hr : c.racy = false) (hfix : c.release ≠ .ended) (hw : c.watchd = true) {a t : Nat}
    (ha : a ∈ c.agents) (ht : t ∈ c.tasks) (r : Run c) (hf : r.Fair) {n : Nat}
    (hdd : ∀ b, ((r.st n).agt b).dead = false) (hbg : ∀ b, ((r.st n).agt b).bg = false)
    (hq : ∀ k, n ≤ k → ∀ b, r.act k ≠ .bgStart b ∧ r.act k ≠ .die b)
    (hP : Pa (r.st n) a t) :
    ∃ m, n ≤ m ∧ (ownsClaimed (r.st m) a t = false ∨ t ∉ (r.st m).pend ∨ ((r.st m).agt a).boot = true) := by
  refine Classical.byContradiction fun hne => ?_
  have hne' : ∀ m, n ≤ m → ownsClaimed (r.st m) a t = true ∧ t ∈ (r.st m).pend ∧ ((r.st m).agt a).boot = false := by
    intro m hm
    refine Classical.byContradiction fun hc => hne ⟨m, hm, ?_⟩
    by_cases h1 : ownsClaimed (r.st m) a t = true
    · by_cases h2 : t ∈ (r.st m).pend
      · right; right; cases hb : ((r.st m).agt a).boot
        · exact absurd ⟨h1, h2, hb⟩ hc
        · rfl
      · right; left; exact h2
    · left; simpa using h1
  have hPa : ∀ m, n ≤ m → Pa (r.st m) a t :=
    forever (fun m => Pa (r.st m) a t) n hP (fun k hk ih =>
      pa_step hr ih (r.ok k) (hne' (k+1) (by omega)).1 (hne' (k+1) (by omega)).2.1 (hne' (k+1) (by omega)).2.2)
  have hD : ∀ m, n ≤ m → Dd (r.st m) :=
    forever (fun m => Dd (r.st m)) n hdd (fun k hk ih => d_step (fun b => (hq k hk b).2) ih (r.ok k))
  have hB : ∀ m, n ≤ m → Bf (r.st m) :=
    forever (fun m => Bf (r.st m)) n hbg (fun k hk ih => bf_step (fun b => (hq k hk b).1) ih (r.ok k))
  by_cases hinf : ∀ N, ∃ k ≥ N, ((r.st k).agt a).st ≠ .idle
  · by_cases hwk : ∀ N, ∃ k ≥ N, ((r.st k).agt a).st = .working
    · obtain ⟨k, hk, hact⟩ := hf (.readAll a) (fun N => by
        obtain ⟨k, hk, hk2⟩ := hwk (max N n)
        refine ⟨k, by omega, by simp [fair, ha, hD k (by omega) a], ?_⟩
        have hu := (hPa k (by omega)).2.2.2.2
        obtain ⟨i, hi, _⟩ := hu
        have : unread (r.st k) a ≠ [] := List.ne_nil_of_mem hi
        simp [step, readAll, when, busy, hk2, this]) n
      have hok := r.ok k
      rw [hact] at hok
      exact readAll_clears (hPa k hk) hok (hne' (k+1) (by omega)).2.1
    · have : ∃ N0, ∀ k, N0 ≤ k → ((r.st k).agt a).st ≠ .working := by
        refine Classical.byContradiction fun hh => hwk fun N => ?_
        refine Classical.byContradiction fun h2 => hh ⟨N, fun k hk hk2 => h2 ⟨k, hk, hk2⟩⟩
      obtain ⟨N0, hN0⟩ := this
      obtain ⟨k, hk, hact⟩ := hf (.hcClear a) (fun N => by
        obtain ⟨k, hk, hk2⟩ := hinf (max N (max n N0))
        refine ⟨k, by omega, by simp [fair, ha, hD k (by omega) a], ?_⟩
        have hl := (hPa k (by omega)).2.2.2.1
        have hw0 := hN0 k (by omega)
        have hbl : ((r.st k).agt a).st = .blocked := by
          simp only [Agent.live, Bool.and_eq_true, bne_iff_ne, ne_eq] at hl
          generalize ((r.st k).agt a).st = x at *
          cases x <;> simp_all
        simp [step, hcClear, when, hbl]) n
      have hok := r.ok k
      rw [hact] at hok
      exact hcClear_clears (hPa k hk) hok (hne' (k+1) (by omega)).2.1
  · have : ∃ N, ∀ k, N ≤ k → ((r.st k).agt a).st = .idle := by
      refine Classical.byContradiction fun hh => hinf fun N => ?_
      refine Classical.byContradiction fun h2 => hh ⟨N, fun k hk => ?_⟩
      exact Classical.byContradiction fun h3 => h2 ⟨k, hk, h3⟩
    obtain ⟨N, hN⟩ := this
    have hN' : n ≤ max N n := by omega
    have hic : idleClaim (r.st (max N n)) a t = true := by
      simp [idleClaim, (hne' _ hN').1, hN (max N n) (Nat.le_max_left ..)]
    obtain ⟨m, hm, hm2⟩ := idleClaim_leads_to hr hfix hw ha ht r hf (n := max N n)
      (fun k hk b => hq k (by omega) b) (hB _ hN' a) (hD _ hN' a) hic
    simp [idleClaim, (hne' m (by omega)).1, hN m (by omega)] at hm2


/-- What `unblock` establishes: the owner of the blocked task holds it claimed with the answer unread in its inbox, provided it
is a live agent that is not booting (not proved of every reachable state: no spawned agent blocks a task before its first turn). -/
theorem unblock_pa {c : Cfg} {s s' : State} {t o : Nat} (hR : Reachable c s) (hs : step c s (.unblock t) = some s')
    (ho : (s.tk t).owner = some o) (hl : (s.agt o).live = true) (hb : (s.agt o).boot = false) : Pa s' o t := by
  simp only [step, unblock, ho, when_eq_some] at hs
  obtain ⟨hg, rfl⟩ := hs
  have hst : (s.tk t).st = .blocked := by simpa using hg
  have hne : (s.tk t).st ≠ .absent := by rw [hst]; decide
  have hcur := ((inbInv_of_reachable hR).2.2 o).1
  refine ⟨?_, by simp, ?_, ?_, s.log.length + 1, ?_, ?_, ?_⟩
  · change ownsClaimed (setTask s t (fun k => { k with st := .claimed, lease := true, hcq := false, answer := k.answer || c.answerOnTask })) o t = true
    simp [ownsClaimed, tk_setTask_self hne, ho]
  · simpa [State.agt] using hb
  · simpa [State.agt] using hl
  · rw [mem_unread]
    simp [State.cur, State.msg, addressed, post] at hcur ⊢
    omega
  · simp [State.msg, post]
  · simp [State.msg, post]

end Swarm
