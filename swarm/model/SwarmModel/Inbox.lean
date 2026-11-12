import SwarmModel.Locks

/-! S4, for every reachable state of every instance with the fix on; and what S1 needs of inboxes: a cursor
never passes a message it didn't show, with or without the fix. Also `tick_inv`, the shape of every proof
about watchd's tick. -/

namespace Swarm
set_option linter.unusedSimpArgs false

-- ---------- reading the state after a change ----------
@[simp] theorem default_believes : (default : Agent).believes = [] := rfl
@[simp] theorem default_snap : (default : Agent).snap = [] := rfl
@[simp] theorem default_st : (default : Task).st = .absent := rfl
@[simp] theorem default_owner : (default : Task).owner = none := rfl

theorem getD_set {α : Type} (l : List α) (i j : Nat) (v d : α) :
    (l.set i v).getD j d = if i = j ∧ j < l.length then v else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hij : i = j
  · subst hij
    by_cases hl : i < l.length
    · simp [hl]
    · simp [hl, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · simp [hij]

theorem agt_setAg (s : State) (a b : Nat) (f : Agent → Agent) :
    (setAg s a f).agt b = if a = b ∧ b < s.ag.length then f (s.agt b) else s.agt b := by
  simp only [State.agt, setAg_ag]; exact getD_modify ..

theorem agt_of_ge {s : State} {a : Nat} (h : s.ag.length ≤ a) : s.agt a = default := by
  simp [State.agt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem tk_setTask_or (s : State) (t u : Nat) (f : Task → Task) :
    (setTask s t f).tk u = s.tk u ∨ (u = t ∧ (setTask s t f).tk u = f (s.tk u)) := by
  unfold setTask; split
  · left; rfl
  · by_cases hu : u = 0
    · left; simp [State.tk, hu]
    · simp only [State.tk, hu, ite_false]
      rw [getD_modify]; split
      · right; exact ⟨by omega, rfl⟩
      · left; rfl
theorem tk_setTask_ne {s : State} {t u : Nat} {f : Task → Task} (h : u ≠ t) : (setTask s t f).tk u = s.tk u := by
  rcases tk_setTask_or s t u f with e | ⟨e, _⟩
  · exact e
  · exact absurd e h
theorem tk_in_range {s : State} {t : Nat} (h : (s.tk t).st ≠ .absent) : t ≠ 0 ∧ t - 1 < s.task.length := by
  unfold State.tk at h; split at h
  · exact absurd rfl h
  · refine ⟨‹_›, ?_⟩
    by_cases hl : t - 1 < s.task.length
    · exact hl
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)] at h
theorem tk_setTask_self {s : State} {t : Nat} {f : Task → Task} (h : (s.tk t).st ≠ .absent) :
    (setTask s t f).tk t = f (s.tk t) := by
  obtain ⟨h0, hl⟩ := tk_in_range h
  simp only [setTask, State.tk, h0, ite_false]; rw [getD_modify]; simp [hl]
/-- a change of every task that leaves the empty task alone -/
theorem tk_map {s s' : State} {g : Task → Task} (hg : g default = default) (h : s'.task = s.task.map g) (u : Nat) :
    s'.tk u = g (s.tk u) := by
  simp only [State.tk, h]; split
  · exact hg.symm
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]; cases s.task[u - 1]? <;> simp [hg]
theorem endAgent_tk (x : State) (a u : Nat) : (endAgent x a).tk u =
    if held (x.tk u) a then { x.tk u with st := .opn, owner := none, lease := false, hcq := false } else x.tk u :=
  tk_map (g := fun k => if held k a then { k with st := .opn, owner := none, lease := false, hcq := false } else k)
    (by simp [held]) rfl u

-- ---------- watchd's tick ----------
theorem spawnFor_not {c : Cfg} {pl : List Nat} {x : State} {t : Nat} (h : pl.contains t = false) : spawnFor c pl x t = x := by
  unfold spawnFor; split
  · rw [h]; simp
  · rfl
theorem spawnFor_tk_ne {c : Cfg} {pl : List Nat} {x : State} {t u : Nat} (h : u ≠ t) : (spawnFor c pl x t).tk u = x.tk u := by
  unfold spawnFor; split
  · split
    · unfold claimed; rw [tk_setTask_ne h]; rfl
    · rfl
  · rfl
/-- board #53: a change that keeps every task's stop and puts no agent to work, nor moves an active one's cursor -/
def SP (x x' : State) : Prop :=
  (∀ u, (x'.tk u).stopTo = (x.tk u).stopTo ∧ (x'.tk u).stopMsg = (x.tk u).stopMsg) ∧
  ∀ o, active (x'.agt o) = true → active (x.agt o) = true ∧ x'.cur o = x.cur o
theorem sp_refl (x : State) : SP x x := ⟨fun _ => ⟨rfl, rfl⟩, fun _ h => ⟨h, rfl⟩⟩
theorem sp_trans {x y z : State} (h1 : SP x y) (h2 : SP y z) : SP x z :=
  ⟨fun u => ⟨(h2.1 u).1.trans (h1.1 u).1, (h2.1 u).2.trans (h1.1 u).2⟩, fun o h => by
    obtain ⟨a2, c2⟩ := h2.2 o h; obtain ⟨a1, c1⟩ := h1.2 o a2; exact ⟨a1, c2.trans c1⟩⟩
theorem sp_stopped {x x' : State} {u : Nat} (h : SP x x') (hs : stopped x u = false) : stopped x' u = false := by
  unfold stopped at hs ⊢
  rw [(h.1 u).1, (h.1 u).2]
  cases e : (x.tk u).stopTo with
  | none => rfl
  | some o =>
    rw [e] at hs; simp only [] at hs ⊢
    cases ha : active (x'.agt o)
    · rfl
    · obtain ⟨h1, h2⟩ := h.2 o ha; rw [h2]; rw [h1] at hs; simpa using hs
theorem sp_tasks {x x' : State} (ht : ∀ u, (x'.tk u).stopTo = (x.tk u).stopTo ∧ (x'.tk u).stopMsg = (x.tk u).stopMsg)
    (hag : ∀ o, active (x'.agt o) = true → active (x.agt o) = true) (hc : x'.cursor = x.cursor) : SP x x' :=
  ⟨ht, fun o h => ⟨hag o h, by simp [State.cur, hc]⟩⟩
theorem sp_endAgent (x : State) (a : Nat) : SP x (endAgent x a) := by
  refine sp_tasks (fun u => ?_) (fun o h => ?_) (by simp)
  · rw [endAgent_tk]; split <;> exact ⟨rfl, rfl⟩
  · have e : (endAgent x a).agt o = (setAg x a fun g => { g with st := .ended, boot := false, believes := [] }).agt o := by
      simp [endAgent, releaseAll, State.agt]
    rw [e, agt_setAg] at h; split at h
    · simp [active] at h
    · exact h
theorem sp_digest (x : State) (a : Nat) (pl : List Nat) :
    SP x (post (setAg x a fun g => { g with told := pl ++ g.told }) ⟨none, a, false, .digest, 0⟩) := by
  refine sp_tasks (fun u => ⟨rfl, rfl⟩) (fun o h => ?_) (by simp)
  have e : (post (setAg x a fun g => { g with told := pl ++ g.told }) ⟨none, a, false, .digest, 0⟩).agt o =
    (setAg x a fun g => { g with told := pl ++ g.told }).agt o := by simp [State.agt]
  rw [e, agt_setAg] at h; split at h
  · simpa [active] using h
  · exact h
theorem claimed_stop (s : State) (a t u : Nat) :
    ((claimed s a t).tk u).stopTo = (s.tk u).stopTo ∧ ((claimed s a t).tk u).stopMsg = (s.tk u).stopMsg := by
  unfold claimed
  rcases tk_setTask_or s t u (fun k => { k with st := .claimed, owner := some a, lease := true, reaped := if k.reaped == some a then k.reaped else none })
    with e | ⟨_, e⟩ <;> rw [e] <;> exact ⟨rfl, rfl⟩
theorem sp_spawnFor (c : Cfg) (pl : List Nat) (x : State) (t : Nat) : SP x (spawnFor c pl x t) := by
  unfold spawnFor; split
  · rename_i a _
    split
    · refine ⟨fun u => by rw [(claimed_stop ..).1, (claimed_stop ..).2]; exact ⟨rfl, rfl⟩, fun o h => ?_⟩
      simp only [State.agt, State.cur, claimed_ag, claimed_cursor, setAg_ag, getD_modify, getD_set, setAg_log] at h ⊢
      split at h
      · simp [active] at h
      · rename_i hh
        refine ⟨h, ?_⟩
        by_cases hao : a = o
        · subst hao
          have hl : x.ag.length ≤ a := Nat.le_of_not_lt fun hl => hh ⟨rfl, hl⟩
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hl, active] at h
          cases h <;> contradiction
        · rw [if_neg fun hc => hao hc.1]; rfl
    · exact sp_refl x
  · exact sp_refl x

theorem spawn_fold {c : Cfg} (P : State → Prop) (pl : List Nat)
    (hspawn : ∀ x t, P x → (x.tk t).st = .opn → stopped x t = false → P (spawnFor c pl x t))
    (l : List Nat) (hl : l.Nodup) (x : State) (hx : P x)
    (hopn : ∀ t ∈ l, pl.contains t = true → (x.tk t).st = .opn ∧ stopped x t = false) :
    P (l.foldl (spawnFor c pl) x) := by
  induction l generalizing x with
  | nil => exact hx
  | cons t ts ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldl_cons]
    refine ih hl.2 _ ?_ ?_
    · cases hc : pl.contains t
      · rw [spawnFor_not hc]; exact hx
      · exact hspawn x t hx (hopn t (List.mem_cons_self ..) hc).1 (hopn t (List.mem_cons_self ..) hc).2
    · intro u hu hcu
      rw [spawnFor_tk_ne (by rintro rfl; exact hl.1 hu)]
      exact ⟨(hopn u (List.mem_cons_of_mem _ hu) hcu).1, sp_stopped (sp_spawnFor c pl x t) (hopn u (List.mem_cons_of_mem _ hu) hcu).2⟩

/-- A property every part of watchd's tick keeps is kept by the tick. A spawn claims a task that is still open and not
stopped: lifecycle picked it from the pool, and nothing in the tick before that spawn takes an open task or puts an agent
to work. -/
theorem tick_inv2 {c : Cfg} (P : State → Prop)
    (hreap : ∀ x t, P x → P (reapTask c x t)) (hlocks : ∀ x, P x → P (reapLocks x)) (hend : ∀ x a, P x → P (endAgent x a))
    (hdig : ∀ x a pl, P x → P (post (setAg x a fun g => { g with told := pl ++ g.told }) ⟨none, a, false, .digest, 0⟩))
    (hspawn : ∀ pl x t, P x → (x.tk t).st = .opn → stopped x t = false → P (spawnFor c pl x t)) {s : State} (h : P s)
    (hgit : ∀ x g, P x → P { x with git := g } := by intro _ _ h; exact h)
    (hnote : ∀ x e n, P x → P { x with evs := e, cbox := n } := by intro _ _ _ h; exact h) : P (tickOf c s) := by
  have h1 : P (reapLocks (reapTasks c s)) := hlocks _ (foldl_inv _ P _ _ h (fun b t hb => hreap b t hb))
  obtain ⟨e, n, he⟩ := tickOf_ex c s
  rw [he]; refine hnote _ _ _ ?_
  unfold tickS
  refine hgit _ _ ?_
  unfold lifecycle
  generalize reapLocks (reapTasks c s) = s1 at h1 ⊢
  have h2 := foldl_inv (fun x a => if finished c s1 a && !reusable c s1 a then endAgent x a else x)
    (fun x : State => P x ∧ (∀ t, (s1.tk t).st = .opn → (x.tk t).st = .opn) ∧ SP s1 x) c.agents s1
    ⟨h1, fun _ h => h, sp_refl _⟩ (fun b a hb => by
      split
      · refine ⟨hend _ _ hb.1, fun t ht => ?_, sp_trans hb.2.2 (sp_endAgent _ _)⟩
        have := hb.2.1 t ht
        rw [endAgent_tk]; split
        · rfl
        · exact this
      · exact hb)
  have h3 := foldl_inv (fun x a =>
    if reusable c s1 a && !(pool c s1).all (x.agt a).told.contains then
      post (setAg x a fun g => { g with told := pool c s1 ++ g.told }) ⟨none, a, false, .digest, 0⟩
    else x) (fun x : State => P x ∧ (∀ t, (s1.tk t).st = .opn → (x.tk t).st = .opn) ∧ SP s1 x) c.agents _ h2 (fun b a hb => by
      split
      · exact ⟨hdig _ _ _ hb.1, fun t ht => hb.2.1 t ht, sp_trans hb.2.2 (sp_digest _ _ _)⟩
      · exact hb)
  simp only []
  split
  · exact h3.1
  · refine spawn_fold P _ (hspawn _) _ (List.nodup_range' (s := 1) (n := c.ntasks)) _ h3.1 (fun t _ hc => ?_)
    have := (List.mem_filter.mp (List.contains_iff_mem.mp hc)).2
    simp only [claimable, startable, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    exact ⟨h3.2.1 t this.1.1, sp_stopped h3.2.2 this.2⟩

theorem sp_reapTask (c : Cfg) (x : State) (t : Nat) : SP x (reapTask c x t) := by
  unfold reapTask; simp only []; split
  · split
    · rename_i o _ _
      refine sp_tasks (fun u => ?_) (fun b h => by simpa [State.agt] using h) (by simp)
      rcases tk_setTask_or x t u (fun r => { r with st := .opn, owner := none, lease := false, reaped := some o }) with e | ⟨_, e⟩ <;>
        simp only [State.tk, post_task] at e ⊢ <;> rw [e] <;> exact ⟨rfl, rfl⟩
    · exact sp_refl x
  · exact sp_refl x
/-- watchd's tick keeps every task's stop and puts no agent to work -/
theorem sp_tick (c : Cfg) (s : State) : SP s (tickOf c s) :=
  tick_inv2 (SP s) (fun x t h => sp_trans h (sp_reapTask c x t))
    (fun x h => sp_trans h (sp_tasks (fun u => by simp [State.tk, reapLocks]) (fun b h => by simpa [State.agt, reapLocks] using h) rfl))
    (fun x a h => sp_trans h (sp_endAgent x a)) (fun x a pl h => sp_trans h (sp_digest x a pl))
    (fun pl x t h _ _ => sp_trans h (sp_spawnFor c pl x t)) (sp_refl s)
    (fun x g h => sp_trans h (sp_tasks (fun u => ⟨rfl, rfl⟩) (fun b h => h) rfl))

/-- `tick_inv2` for a property whose spawn step needs only that the task is open -/
theorem tick_inv {c : Cfg} (P : State → Prop)
    (hreap : ∀ x t, P x → P (reapTask c x t)) (hlocks : ∀ x, P x → P (reapLocks x)) (hend : ∀ x a, P x → P (endAgent x a))
    (hdig : ∀ x a pl, P x → P (post (setAg x a fun g => { g with told := pl ++ g.told }) ⟨none, a, false, .digest, 0⟩))
    (hspawn : ∀ pl x t, P x → (x.tk t).st = .opn → P (spawnFor c pl x t)) {s : State} (h : P s)
    (hgit : ∀ x g, P x → P { x with git := g } := by intro _ _ h; exact h)
    (hnote : ∀ x e n, P x → P { x with evs := e, cbox := n } := by intro _ _ _ h; exact h) : P (tickOf c s) :=
  tick_inv2 P hreap hlocks hend hdig (fun pl x t hx ho _ => hspawn pl x t hx ho) h hgit hnote

-- ---------- messages ----------
theorem msg_congr {s s' : State} (h : s'.log = s.log) (i : Nat) : s'.msg i = s.msg i := by simp [State.msg, h]
theorem addressed_congr {s s' : State} (h : s'.log = s.log) (a i : Nat) : addressed s' a i = addressed s a i := by
  simp [addressed, msg_congr h]
theorem msg_post {s : State} {m : Msg} {i : Nat} (h : i ≤ s.log.length) : (post s m).msg i = s.msg i := by
  by_cases h0 : i = 0
  · simp [State.msg, h0]
  · have : i - 1 < s.log.length := by omega
    simp [State.msg, post, h0, List.getD_eq_getElem?_getD, List.getElem?_append_left this]
theorem msg_post_new (s : State) (m : Msg) : (post s m).msg (s.log.length + 1) = m := by
  simp [State.msg, post, List.getD_eq_getElem?_getD]
theorem addressed_post {s : State} {m : Msg} {a i : Nat} (h : i ≤ s.log.length) : addressed (post s m) a i = addressed s a i := by
  simp [addressed, msg_post h]
@[simp] theorem post_log_length (s : State) (m : Msg) : (post s m).log.length = s.log.length + 1 := by simp [post]

theorem mem_unread {s : State} {a i : Nat} : i ∈ unread s a ↔ s.cur a < i ∧ i ≤ s.log.length ∧ addressed s a i = true := by
  simp only [unread, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
theorem unread_pairwise (s : State) (a : Nat) : (unread s a).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range'

theorem foldl_max (ids : List Nat) (c : Nat) :
    c ≤ ids.foldl max c ∧ (∀ i ∈ ids, i ≤ ids.foldl max c) ∧ (ids.foldl max c = c ∨ ids.foldl max c ∈ ids) := by
  induction ids generalizing c with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨h1, h2, h3⟩ := ih (max c x)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨by omega, ?_, ?_⟩
    · intro i hi
      rcases hi with rfl | hi
      · omega
      · exact h2 i hi
    · rcases h3 with h3 | h3
      · rcases Nat.le_total c x with h | h
        · right; left; rw [h3]; omega
        · left; rw [h3]; omega
      · right; right; exact h3

-- ---------- a delivery ----------
theorem showMsg_cursor (s : State) (a i : Nat) : (showMsg s a i).cursor = s.cursor.modify a (max · i) := by frame showMsg
theorem showMsg_seen (s : State) (a i : Nat) : (showMsg s a i).seen = s.seen.modify a (· ++ [i]) := by frame showMsg
theorem showMsg_ag (s : State) (a i : Nat) : (showMsg s a i).ag =
    if (s.msg i).kind = .released then
      s.ag.modify a (fun g => { g with believes := g.believes.filter (· != (s.msg i).task) })
    else s.ag := by
  unfold showMsg; simp only []
  split
  · rename_i h; simp at h; simp [h.1]
  · split <;> simp_all [setAg]

theorem showMsg_bel (s : State) (a i b u : Nat) : u ∈ ((showMsg s a i).agt b).believes ↔
    u ∈ (s.agt b).believes ∧ ¬(b = a ∧ (s.msg i).kind = .released ∧ (s.msg i).task = u) := by
  simp only [State.agt, showMsg_ag]
  split
  · rename_i hk
    rw [getD_modify]
    split
    · rename_i h; obtain ⟨rfl, _⟩ := h
      simp only [List.mem_filter, hk, true_and]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun e => by simp [e] at h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by simp; exact fun e => h2 e.symm⟩
    · rename_i h
      by_cases hb : b = a
      · subst hb
        have : s.ag.length ≤ b := by
          apply Nat.le_of_not_lt; intro hl; exact h ⟨rfl, hl⟩
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none this]
      · simp [hb]
  · rename_i hk; simp [hk]

/-- a delivery changes nothing of an agent but what it believes -/
theorem showMsg_proj {β : Type} (p : Agent → β) (hp : ∀ g l, p { g with believes := l } = p g) (s : State) (a i b : Nat) :
    p ((showMsg s a i).agt b) = p (s.agt b) := by
  simp only [State.agt, showMsg_ag]
  split
  · rw [getD_modify]; split
    · exact hp _ _
    · rfl
  · rfl

theorem showAll_cons (s : State) (a i : Nat) (is : List Nat) : showAll s a (i :: is) = showAll (showMsg s a i) a is := rfl
theorem showAll_proj {β : Type} (p : Agent → β) (hp : ∀ g l, p { g with believes := l } = p g) (s : State) (a : Nat)
    (ids : List Nat) (b : Nat) : p ((showAll s a ids).agt b) = p (s.agt b) := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => rw [showAll_cons, ih, showMsg_proj p hp]
theorem showAll_bel (ids : List Nat) (s : State) (a b u : Nat) : u ∈ ((showAll s a ids).agt b).believes ↔
    u ∈ (s.agt b).believes ∧ ¬(b = a ∧ ∃ i ∈ ids, (s.msg i).kind = .released ∧ (s.msg i).task = u) := by
  induction ids generalizing s with
  | nil => simp [showAll]
  | cons i is ih =>
    rw [showAll_cons, ih, showMsg_bel]
    simp only [msg_congr (showMsg_log s a i), List.mem_cons]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      rintro ⟨hb, j, hj | hj, hk⟩
      · subst hj; exact h2 ⟨hb, hk⟩
      · exact h3 ⟨hb, j, hj, hk⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun ⟨hb, hk⟩ => h2 ⟨hb, i, Or.inl rfl, hk⟩⟩, fun ⟨hb, j, hj, hk⟩ => h2 ⟨hb, j, Or.inr hj, hk⟩⟩

theorem showMsg_cur (s : State) (a i b : Nat) :
    (showMsg s a i).cur b = if a = b ∧ b < s.cursor.length then max (s.cur b) i else s.cur b := by
  simp only [State.cur, showMsg_cursor]; exact getD_modify ..
theorem showAll_lens (ids : List Nat) (s : State) (a : Nat) :
    (showAll s a ids).cursor.length = s.cursor.length ∧ (showAll s a ids).seen.length = s.seen.length := by
  induction ids generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons i is ih =>
    rw [showAll_cons]; obtain ⟨h1, h2⟩ := ih (showMsg s a i)
    rw [h1, h2, showMsg_cursor, showMsg_seen]; simp
theorem showAll_cur (ids : List Nat) (s : State) (a b : Nat) :
    (showAll s a ids).cur b = if b = a ∧ a < s.cursor.length then ids.foldl max (s.cur a) else s.cur b := by
  induction ids generalizing s with
  | nil => simp only [showAll, List.foldl_nil]; split <;> simp_all
  | cons i is ih =>
    rw [showAll_cons, ih]
    simp only [showMsg_cur, showMsg_cursor, List.length_modify, List.foldl_cons]
    by_cases hb : b = a
    · subst hb; by_cases hl : b < s.cursor.length <;> simp [hl]
    · have : ¬ a = b := fun e => hb e.symm
      simp [hb, this]
theorem showAll_seen (ids : List Nat) (s : State) (a b : Nat) :
    (showAll s a ids).seen.getD b [] = if b = a ∧ a < s.seen.length then s.seen.getD a [] ++ ids else s.seen.getD b [] := by
  induction ids generalizing s with
  | nil => simp only [showAll, List.foldl_nil, List.append_nil]; split <;> simp_all
  | cons i is ih =>
    rw [showAll_cons, ih]
    simp only [showMsg_seen, List.length_modify, getD_modify]
    by_cases hb : b = a
    · subst hb; by_cases hl : b < s.seen.length <;> simp [hl]
    · have : ¬ a = b := fun e => hb e.symm
      simp [hb, this]

-- ---------- the inbox invariant ----------
/-- Agent a's inbox. Whatever the switches: the cursor is inside the log, and the waiter's snapshot skips no
message between the cursor and its last id. With PR #115: what was shown is in order and behind the cursor, and
everything behind the cursor since the agent's spawn was shown. -/
def Inb (c : Cfg) (s : State) (a : Nat) : Prop :=
  s.cur a ≤ s.log.length ∧
  (∀ j ∈ (s.agt a).snap, j ≤ s.log.length ∧ ∀ i, s.cur a < i → i ≤ j → addressed s a i = true → i ∈ (s.agt a).snap) ∧
  (c.deliverCas = true →
    (s.seen.getD a []).Pairwise (· < ·) ∧ (s.agt a).snap.Pairwise (· < ·) ∧ (∀ i ∈ s.seen.getD a [], i ≤ s.cur a) ∧
    ∀ i, s.start.getD a 0 < i → i ≤ s.cur a → addressed s a i = true → i ∈ s.seen.getD a [])

def InbInv (c : Cfg) (s : State) : Prop :=
  s.start.length = s.cursor.length ∧ s.seen.length = s.cursor.length ∧ ∀ a, Inb c s a

/-- the log grew, a's cursor and what it was shown are the same, its snapshot the same or dropped -/
theorem inb_mono {c : Cfg} {s s' : State} {a : Nat}
    (hlog : s.log.length ≤ s'.log.length) (hmsg : ∀ i, i ≤ s.log.length → addressed s' a i = addressed s a i)
    (hcur : s'.cur a = s.cur a) (hstart : s'.start.getD a 0 = s.start.getD a 0) (hseen : s'.seen.getD a [] = s.seen.getD a [])
    (hsnap : (s'.agt a).snap = (s.agt a).snap ∨ (s'.agt a).snap = []) (h : Inb c s a) : Inb c s' a := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, ?_, ?_⟩
  · rcases hsnap with e | e <;> rw [e]
    · intro j hj
      have hjl := (h2 j hj).1
      refine ⟨by omega, fun i hi hij had => ?_⟩
      rw [hcur] at hi; rw [hmsg i (by omega)] at had
      exact (h2 j hj).2 i hi hij had
    · intro j hj; cases hj
  · intro hc
    obtain ⟨p1, p2, p3, p4⟩ := h3 hc
    rw [hseen, hcur, hstart]
    refine ⟨p1, ?_, p3, fun i hi hic had => ?_⟩
    · rcases hsnap with e | e <;> rw [e]
      · exact p2
      · exact List.Pairwise.nil
    · rw [hmsg i (by omega)] at had; exact p4 i hi hic had

theorem ii_same {c : Cfg} {s s' : State} (hlog : s'.log = s.log) (hcur : s'.cursor = s.cursor) (hstart : s'.start = s.start)
    (hseen : s'.seen = s.seen) (hsnap : ∀ a, (s'.agt a).snap = (s.agt a).snap ∨ (s'.agt a).snap = [])
    (h : InbInv c s) : InbInv c s' :=
  ⟨by rw [hstart, hcur]; exact h.1, by rw [hseen, hcur]; exact h.2.1, fun a =>
    inb_mono (by rw [hlog]; exact Nat.le_refl _) (fun i _ => addressed_congr hlog a i) (by simp [State.cur, hcur])
      (by rw [hstart]) (by rw [hseen]) (hsnap a) (h.2.2 a)⟩
/-- the agents and the inboxes are untouched -/
theorem ii_frame {c : Cfg} {s s' : State} (hag : s'.ag = s.ag) (hlog : s'.log = s.log) (hcur : s'.cursor = s.cursor)
    (hstart : s'.start = s.start) (hseen : s'.seen = s.seen) (h : InbInv c s) : InbInv c s' :=
  ii_same hlog hcur hstart hseen (fun a => Or.inl (by simp [State.agt, hag])) h
theorem ii_setAg {c : Cfg} {s : State} {a : Nat} {f : Agent → Agent} (hf : ∀ g, (f g).snap = g.snap ∨ (f g).snap = [])
    (h : InbInv c s) : InbInv c (setAg s a f) :=
  ii_same (setAg_log ..) (setAg_cursor ..) (setAg_start ..) (setAg_seen ..) (fun b => by
    rw [agt_setAg]; split
    · exact hf _
    · exact Or.inl rfl) h
theorem ii_setTask {c : Cfg} {s : State} {t : Nat} {f : Task → Task} (h : InbInv c s) : InbInv c (setTask s t f) :=
  ii_frame (setTask_ag ..) (setTask_log ..) (setTask_cursor ..) (setTask_start ..) (setTask_seen ..) h
theorem ii_post {c : Cfg} {s : State} {m : Msg} (h : InbInv c s) : InbInv c (post s m) :=
  ⟨h.1, h.2.1, fun a => inb_mono (by simp) (fun _ hi => addressed_post hi) rfl rfl rfl (Or.inl rfl) (h.2.2 a)⟩

/-- Showing ids to a. With PR #115 they are in order, past the cursor, and skip nothing addressed to a. -/
theorem ii_showAll {c : Cfg} {s : State} {a : Nat} {ids : List Nat} (h1 : ∀ j ∈ ids, j ≤ s.log.length)
    (h2 : c.deliverCas = true → ids.Pairwise (· < ·) ∧
      ∀ j ∈ ids, s.cur a < j ∧ ∀ i, s.cur a < i → i < j → addressed s a i = true → i ∈ ids)
    (h : InbInv c s) : InbInv c (showAll s a ids) := by
  obtain ⟨l1, l2, hI⟩ := h
  have hlen := showAll_lens ids s a
  refine ⟨by rw [showAll_start, hlen.1]; exact l1, by rw [hlen.2, hlen.1]; exact l2, fun b => ?_⟩
  have hadd : ∀ i, addressed (showAll s a ids) b i = addressed s b i := fun i => addressed_congr (showAll_log ..) b i
  have hsnap : ((showAll s a ids).agt b).snap = (s.agt b).snap := showAll_proj (·.snap) (fun _ _ => rfl) ..
  by_cases hb : b = a ∧ a < s.cursor.length
  · obtain ⟨rfl, hl⟩ := hb
    obtain ⟨q1, q2, q3⟩ := hI b
    obtain ⟨m1, m2, m3⟩ := foldl_max ids (s.cur b)
    have hcur : (showAll s b ids).cur b = ids.foldl max (s.cur b) := by rw [showAll_cur]; simp [hl]
    have hseen : (showAll s b ids).seen.getD b [] = s.seen.getD b [] ++ ids := by rw [showAll_seen]; simp [l2, hl]
    have hm : ids.foldl max (s.cur b) ≤ s.log.length := by
      rcases m3 with e | e
      · omega
      · exact h1 _ e
    refine ⟨by rw [hcur, showAll_log]; exact hm, ?_, ?_⟩
    · rw [hsnap, hcur, showAll_log]; intro j hj
      exact ⟨(q2 j hj).1, fun i hi hij had => (q2 j hj).2 i (by omega) hij (hadd i ▸ had)⟩
    · intro hc
      obtain ⟨p1, p2, p3, p4⟩ := q3 hc
      obtain ⟨g1, g2⟩ := h2 hc
      rw [hseen, hsnap, hcur, showAll_start]
      refine ⟨?_, p2, ?_, ?_⟩
      · rw [List.pairwise_append]
        exact ⟨p1, g1, fun x hx y hy => by have := p3 x hx; have := (g2 y hy).1; omega⟩
      · intro i hi; rw [List.mem_append] at hi
        rcases hi with hi | hi
        · have := p3 i hi; omega
        · exact m2 i hi
      · intro i hi hic had
        rw [hadd] at had; rw [List.mem_append]
        by_cases hle : i ≤ s.cur b
        · exact Or.inl (p4 i hi hle had)
        · right
          rcases m3 with e | e
          · omega
          · by_cases heq : i = ids.foldl max (s.cur b)
            · rw [heq]; exact e
            · exact (g2 _ e).2 i (by omega) (by omega) had
  · exact inb_mono (by simp) (fun i _ => hadd i) (by rw [showAll_cur]; simp [hb]) (by simp)
      (by rw [showAll_seen]; simp [l2, hb]) (Or.inl hsnap) (hI b)

theorem ii_deliver {c : Cfg} {s : State} {a : Nat} (h : InbInv c s) : InbInv c (deliver s a) :=
  ii_showAll (fun j hj => (mem_unread.mp hj).2.1) (fun _ => ⟨unread_pairwise s a, fun j hj =>
    ⟨(mem_unread.mp hj).1, fun i hi hij had => mem_unread.mpr ⟨hi, by have := (mem_unread.mp hj).2.1; omega, had⟩⟩⟩) h

theorem ii_wakeRead {c : Cfg} {s : State} {a : Nat} (h : InbInv c s) :
    InbInv c (setAg s a fun g => { g with snap := unread s a }) := by
  refine ⟨h.1, h.2.1, fun b => ?_⟩
  by_cases hb : a = b ∧ b < s.ag.length
  · obtain ⟨rfl, hl⟩ := hb
    have hsn : ((setAg s a fun g => { g with snap := unread s a }).agt a).snap = unread s a := by rw [agt_setAg]; simp [hl]
    obtain ⟨q1, q2, q3⟩ := h.2.2 a
    refine ⟨q1, ?_, fun hc => ?_⟩
    · rw [hsn]; intro j hj
      have hj' := mem_unread.mp hj
      exact ⟨hj'.2.1, fun i hi hij had => mem_unread.mpr ⟨hi, Nat.le_trans hij hj'.2.1, had⟩⟩
    · obtain ⟨p1, _, p3, p4⟩ := q3 hc
      rw [hsn]; exact ⟨p1, unread_pairwise s a, p3, p4⟩
  · exact inb_mono (s := s) (Nat.le_refl _) (fun _ _ => rfl) rfl rfl rfl (Or.inl (by rw [agt_setAg]; simp [hb])) (h.2.2 b)

/-- a spawn into slot a: a new agent, its inbox starting at the end of the log -/
theorem ii_reset {c : Cfg} {x : State} {a : Nat} (f : Agent → Agent) (hf : ∀ g, (f g).snap = []) (h : InbInv c x) :
    InbInv c { setAg x a f with
      cursor := x.cursor.set a x.log.length, start := x.start.set a x.log.length, seen := x.seen.set a [] } := by
  obtain ⟨l1, l2, hI⟩ := h
  refine ⟨by simp [l1], by simp [l2], fun b => ?_⟩
  have hsn : ((setAg x a f).agt b).snap = (x.agt b).snap ∨ ((setAg x a f).agt b).snap = [] := by
    rw [agt_setAg]; split
    · right; exact hf _
    · left; rfl
  by_cases hb : a = b ∧ b < x.cursor.length
  · obtain ⟨rfl, hl⟩ := hb
    refine ⟨?_, ?_, fun hc => ?_⟩
    · simp [State.cur, getD_set, hl]
    · show ∀ j ∈ ((setAg x a f).agt a).snap, _
      rcases hsn with e | e <;> rw [e]
      · intro j hj
        have := ((hI a).2.1 j hj).1
        refine ⟨this, fun i hi hij _ => ?_⟩
        simp [State.cur, getD_set, hl] at hi; omega
      · intro j hj; cases hj
    · refine ⟨by simp [getD_set, l2, hl], ?_, by simp [getD_set, l2, hl], ?_⟩
      · show ((setAg x a f).agt a).snap.Pairwise _
        rcases hsn with e | e <;> rw [e]
        · exact ((hI a).2.2 hc).2.1
        · exact List.Pairwise.nil
      · intro i h1 h2
        simp [State.cur, getD_set, l1, hl] at h1 h2; omega
  · have hb1 : ¬(a = b ∧ b < x.start.length) := by rw [l1]; exact hb
    have hb2 : ¬(a = b ∧ b < x.seen.length) := by rw [l2]; exact hb
    exact inb_mono (s := x) (Nat.le_refl _) (fun _ _ => rfl)
      (show (x.cursor.set a x.log.length).getD b 0 = x.cursor.getD b 0 by rw [getD_set, ite_eq_right hb])
      (show (x.start.set a x.log.length).getD b 0 = x.start.getD b 0 by rw [getD_set, ite_eq_right hb1])
      (show (x.seen.set a []).getD b [] = x.seen.getD b [] by rw [getD_set, ite_eq_right hb2]) hsn (hI b)

theorem ii_takes {c : Cfg} {s : State} {a t : Nat} (h : InbInv c s) : InbInv c (takes c s a t) := by
  unfold takes; simp only []; split
  · exact ii_frame (s := setAg s a fun g => { g with believes := t :: g.believes }) rfl rfl rfl rfl rfl
      (ii_setAg (fun _ => Or.inl rfl) h)
  · exact ii_setAg (fun _ => Or.inl rfl) h
theorem ii_endAgent {c : Cfg} {s : State} {a : Nat} (h : InbInv c s) : InbInv c (endAgent s a) :=
  ii_frame rfl rfl rfl rfl rfl (ii_setAg (f := fun g => { g with st := .ended, boot := false, believes := [] })
    (fun _ => Or.inl rfl) h)
theorem ii_reapTask {c : Cfg} {s : State} {t : Nat} (h : InbInv c s) : InbInv c (reapTask c s t) := by
  unfold reapTask; simp only []; split
  · split
    · exact ii_post (ii_setTask h)
    · exact h
  · exact h
theorem ii_spawnFor {c : Cfg} {pl : List Nat} {s : State} {t : Nat} (h : InbInv c s) : InbInv c (spawnFor c pl s t) := by
  unfold spawnFor; split
  · split
    · exact ii_setTask (ii_reset _ (fun _ => rfl) h)
    · exact h
  · exact h
theorem ii_tickOf {c : Cfg} {s : State} (h : InbInv c s) : InbInv c (tickOf c s) :=
  tick_inv (InbInv c) (fun _ _ => ii_reapTask) (fun _ => ii_frame rfl rfl rfl rfl rfl) (fun _ _ => ii_endAgent)
    (fun _ _ _ hx => ii_post (ii_setAg (fun _ => Or.inl rfl) hx)) (fun _ _ _ hx _ => ii_spawnFor hx) h

/-- one step of "the inbox invariant is kept" over the changes an action is made of -/
macro "ii_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible assumption
    | ((with_reducible refine ii_setAg ?_ ?_); (intro g; first | exact Or.inl rfl | exact Or.inr rfl))
    | with_reducible apply ii_setTask
    | with_reducible apply ii_post
    | with_reducible apply ii_deliver
    | with_reducible apply ii_takes
    | with_reducible apply ii_endAgent
    | assumption))

theorem inbInv_of_reachable {c : Cfg} {s : State} (h : Reachable c s) : InbInv c s := by
  refine reachable_induct ?_ ?_ h
  · refine ⟨by simp [init], by simp [init], fun a => ?_⟩
    have hcur : (init c).cur a = 0 := by
      simp only [State.cur, init, List.getD_eq_getElem?_getD, List.getElem?_map]; cases c.agents[a]? <;> rfl
    have hseen : (init c).seen.getD a [] = [] := by
      simp only [init, List.getD_eq_getElem?_getD, List.getElem?_map]; cases c.agents[a]? <;> rfl
    have hsnap : ((init c).agt a).snap = [] := by
      simp only [State.agt, init, List.getD_eq_getElem?_getD, List.getElem?_map]; cases c.agents[a]? <;> rfl
    refine ⟨(by rw [hcur]; exact Nat.zero_le _), (by rw [hsnap]; intro j hj; cases hj), fun _ => ?_⟩
    rw [hseen, hsnap, hcur]
    exact ⟨.nil, .nil, (by intro i hi; cases hi), (by intro i h1 h2; omega)⟩
  intro s s' act _ hs hstep
  open_step hstep
  case unblock t =>
    split at hstep
    · rw [when_eq_some] at hstep; obtain ⟨_, rfl⟩ := hstep; exact ii_frame rfl rfl rfl rfl rfl (ii_post (ii_setTask hs))
    · cases hstep
  case tick => obtain ⟨_, rfl⟩ := hstep; exact ii_tickOf hs
  case wakeRead a => obtain ⟨_, rfl⟩ := hstep; exact ii_wakeRead hs
  case wakeWrite a =>
    obtain ⟨hg, rfl⟩ := hstep
    refine ii_setAg (fun _ => Or.inr rfl) (ii_setAg (f := fun g => { g with st := .working, waiter := false, aged := false, cold := false, stale := false, nudged := false })
      (fun _ => Or.inl rfl) (ii_deliver ?_))
    split
    · exact hs
    · rename_i hcond
      have hI := hs.2.2 a
      refine ii_showAll (fun j hj => (hI.2.1 j hj).1) (fun hc => ?_) hs
      obtain ⟨_, p2, _, _⟩ := hI.2.2 hc
      refine ⟨p2, fun j hj => ?_⟩
      cases hsn : (s.agt a).snap with
      | nil => rw [hsn] at hj; cases hj
      | cons x xs =>
        rw [hsn] at hj p2 hcond
        simp [hc] at hcond
        have hxj : x ≤ j := by
          rcases List.mem_cons.mp hj with e | e
          · omega
          · exact Nat.le_of_lt ((List.pairwise_cons.mp p2).1 j e)
        exact ⟨by omega, fun i hi hij had => by
          rw [← hsn]; exact (hI.2.1 j (by rw [hsn]; exact hj)).2 i hi (by omega) had⟩
  case lock a p => obtain ⟨_, rfl⟩ := hstep; exact ii_frame (s := s) rfl rfl rfl rfl rfl hs
  case world w op => obtain ⟨_, rfl⟩ := hstep; exact hs
  case git a op => obtain ⟨_, rfl⟩ := hstep; exact ii_setAg (fun _ => Or.inl rfl) hs
  case unlock a p => obtain ⟨_, rfl⟩ := hstep; exact ii_frame (s := s) rfl rfl rfl rfl rfl hs
  case expireLock p => obtain ⟨_, rfl⟩ := hstep; exact ii_frame (s := s) rfl rfl rfl rfl rfl hs
  case claimWrite a =>
    obtain ⟨_, rfl⟩ := hstep
    split
    · exact ii_setAg (fun _ => Or.inl rfl) (ii_frame (s := takes c (claimed s a (s.agt a).reading) a (s.agt a).reading)
        rfl rfl rfl rfl rfl (ii_takes (ii_setTask hs)))
    · exact ii_setAg (fun _ => Or.inl rfl) hs
  case hcClear a => obtain ⟨_, rfl⟩ := hstep; exact ii_setAg (fun _ => Or.inl rfl) (ii_deliver (ii_frame (s := s) rfl rfl rfl rfl rfl hs))
  all_goals
    obtain ⟨hg, rfl⟩ := hstep
    (try split) <;> (try simp only [unbelieve, awake, claimed]) <;> ii_tac

/-- S4. With PR #115 (a delivery moves the cursor only from where it read), no message is shown twice and no
cursor passes a message it didn't show. -/
theorem inboxExact_of_reachable {c : Cfg} (hfix : c.deliverCas = true) {s : State} (h : Reachable c s) :
    inboxExact s = true := by
  obtain ⟨_, _, hI⟩ := inbInv_of_reachable h
  simp only [inboxExact, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_range]
  intro a _
  obtain ⟨p1, _, _, p4⟩ := (hI a).2.2 hfix
  refine ⟨p1, fun i hi => ?_⟩
  rw [List.mem_range'_1] at hi
  cases had : addressed s a i
  · simp
  · simpa using p4 i (by omega) (by omega) had

end Swarm
