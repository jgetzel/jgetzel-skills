import SwarmModel.Basic

/-! S3, for every reachable state of every instance with the fix on. -/

namespace Swarm

theorem getD_modify {α : Type} (l : List α) (i j : Nat) (f : α → α) (d : α) :
    (l.modify i f).getD j d = if i = j ∧ j < l.length then f (l.getD j d) else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases hij : i = j
  · subst hij
    by_cases hl : i < l.length
    · simp [hl]
    · simp [hl, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · simp [hij]

@[simp] theorem setAg_ag (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).ag = s.ag.modify a f := rfl

/-- every agent live before is live after -/
def LiveL (l l' : List Agent) : Prop := ∀ b, (l.getD b default).live = true → (l'.getD b default).live = true

theorem liveL_refl (l : List Agent) : LiveL l l := fun _ h => h
theorem liveL_modify {l l' : List Agent} {f : Agent → Agent} (a : Nat) (h : LiveL l l')
    (hf : ∀ g, g.live = true → (f g).live = true) : LiveL l (l'.modify a f) := by
  intro b hb; rw [getD_modify]; split
  · exact hf _ (h b hb)
  · exact h b hb
theorem liveL_showMsg {l : List Agent} {s : State} (a i : Nat) (h : LiveL l s.ag) : LiveL l (showMsg s a i).ag := by
  unfold showMsg; simp only []; split
  · exact h
  · split
    · exact liveL_modify _ h (by intro g hg; simpa [Agent.live] using hg)
    · exact h
theorem liveL_showAll {l : List Agent} {s : State} (a : Nat) (ids : List Nat) (h : LiveL l s.ag) :
    LiveL l (showAll s a ids).ag := by
  induction ids generalizing s with
  | nil => exact h
  | cons i is ih => exact ih (liveL_showMsg a i h)
theorem liveL_deliver {l : List Agent} {s : State} (a : Nat) (h : LiveL l s.ag) : LiveL l (deliver s a).ag :=
  liveL_showAll _ _ h
theorem liveL_takes {l : List Agent} {c : Cfg} {s : State} (a t : Nat) (h : LiveL l s.ag) : LiveL l (takes c s a t).ag := by
  unfold takes; simp only []; split <;> exact liveL_modify _ h (by intro g hg; simpa [Agent.live] using hg)

/-- the lock invariant: a holder is live, and two unexpired locks of different agents have no file in common -/
def LkInv (c : Cfg) (lk : List Lock) (ag : List Agent) : Prop :=
  (∀ (p : Nat) (l : Lock) (a : Nat), lk[p]? = some l → l.holder = some a → (ag.getD a default).live = true) ∧
  (∀ (p q : Nat) (l m : Lock) (a b : Nat), lk[p]? = some l → lk[q]? = some m → p ≠ q → l.holder = some a → m.holder = some b → a ≠ b →
    l.exp = false → m.exp = false → overlap (c.pat p) (c.pat q) = false)

/-- each lock after is the lock before, or freed, or expired -/
def Shrinks (lk lk' : List Lock) : Prop := ∀ (p : Nat) (l' : Lock), lk'[p]? = some l' →
  ∃ l : Lock, lk[p]? = some l ∧ (l'.holder = none ∨ (l'.holder = l.holder ∧ (l'.exp = false → l.exp = false)))

theorem lk_live {c : Cfg} {lk : List Lock} {ag ag' : List Agent} (h : LkInv c lk ag) (hl : LiveL ag ag') : LkInv c lk ag' :=
  ⟨fun p l a hp ha => hl a (h.1 p l a hp ha), h.2⟩
theorem lk_shrink {c : Cfg} {lk lk' : List Lock} {ag : List Agent} (h : LkInv c lk ag) (hs : Shrinks lk lk') : LkInv c lk' ag := by
  refine ⟨fun p l' a hp ha => ?_, fun p q l' m' a b hp hq hpq ha hb hab he1 he2 => ?_⟩
  · obtain ⟨l, hl, h1 | ⟨h1, _⟩⟩ := hs p l' hp
    · simp [h1] at ha
    · exact h.1 p l a hl (h1 ▸ ha)
  · obtain ⟨l, hl, h1 | ⟨h1, h1e⟩⟩ := hs p l' hp
    · simp [h1] at ha
    · obtain ⟨m, hm, h2 | ⟨h2, h2e⟩⟩ := hs q m' hq
      · simp [h2] at hb
      · exact h.2 p q l m a b hl hm hpq (h1 ▸ ha) (h2 ▸ hb) hab (h1e he1) (h2e he2)
theorem shrinks_map (lk : List Lock) (f : Lock → Lock)
    (hf : ∀ l, (f l).holder = none ∨ ((f l).holder = l.holder ∧ ((f l).exp = false → l.exp = false))) :
    Shrinks lk (lk.map f) := by
  intro p l' hp
  rw [List.getElem?_map] at hp
  cases hl : lk[p]? with
  | none => simp [hl] at hp
  | some l => simp [hl] at hp; subst hp; exact ⟨l, rfl, hf l⟩
theorem shrinks_set (lk : List Lock) (p : Nat) (x : Lock)
    (hx : ∀ l, lk[p]? = some l → x.holder = none ∨ (x.holder = l.holder ∧ (x.exp = false → l.exp = false))) :
    Shrinks lk (lk.set p x) := by
  intro q l' hq
  rw [List.getElem?_set] at hq
  split at hq
  · subst ‹p = q›
    split at hq
    · cases hq
      have hlt : p < lk.length := ‹_›
      exact ⟨lk[p], by simp [hlt], hx _ (by simp [hlt])⟩
    · cases hq
  · exact ⟨l', hq, Or.inr ⟨rfl, id⟩⟩

theorem refuses_eq {c : Cfg} {p q : String} (h1 : c.lockOverlap = true) (h2 : c.lockForms = true) :
    refuses c p q = overlap p q := by simp [refuses, overlap, h1, h2]

theorem overlap_comm (p q : String) : overlap p q = overlap q p := Glob.overlaps_comm _ _

theorem lk_endAgent {c : Cfg} {s : State} (a : Nat) (h : LkInv c s.lock s.ag) :
    LkInv c (endAgent s a).lock (endAgent s a).ag := by
  have hsh : Shrinks s.lock (endAgent s a).lock := by
    simp only [endAgent, releaseAll, setAg]
    exact shrinks_map _ _ (by intro l; split <;> simp)
  refine ⟨fun p l' b hp hb => ?_, (lk_shrink (ag := s.ag) h hsh).2⟩
  simp only [endAgent, releaseAll, setAg] at hp ⊢
  rw [List.getElem?_map] at hp
  cases hl : s.lock[p]? with
  | none => simp [hl] at hp
  | some l =>
    simp [hl] at hp
    by_cases hla : l.holder = some a
    · simp [hla] at hp; subst hp; simp at hb
    · simp [hla] at hp; subst hp
      rw [getD_modify]
      have hba : ¬ a = b := fun e => hla (e ▸ hb)
      simp [hba]; exact h.1 p _ b hl hb

theorem lk_tickOf {c : Cfg} {s : State} (h : LkInv c s.lock s.ag) : LkInv c (tickOf c s).lock (tickOf c s).ag := by
  have hspawn : ∀ pl (x : State) t, LkInv c x.lock x.ag → LkInv c (spawnFor c pl x t).lock (spawnFor c pl x t).ag :=
    fun pl x t hx => by
      rw [spawnFor_lock]
      refine lk_live hx ?_
      unfold spawnFor; split
      · split
        · simp only [claimed_ag]; exact liveL_modify _ (liveL_refl _) (by intro g _; rfl)
        · exact liveL_refl _
      · exact liveL_refl _
  have h1 : LkInv c (reapLocks (reapTasks c s)).lock (reapLocks (reapTasks c s)).ag := by
    simp only [reapLocks_ag, reapTasks_ag]
    refine lk_shrink h ?_
    simp only [reapLocks, reapTasks_lock]
    exact shrinks_map _ _ (by intro l; split <;> simp)
  unfold tickOf lifecycle
  generalize reapLocks (reapTasks c s) = s1 at h1 ⊢
  have h2 := foldl_inv (fun x a => if finished c s1 a && !reusable c s1 a then endAgent x a else x)
    (fun x : State => LkInv c x.lock x.ag) c.agents s1 h1 (fun b a hb => by split; exact lk_endAgent _ hb; exact hb)
  have h3 := foldl_inv (fun x a =>
    if reusable c s1 a && !(pool c s1).all (x.agt a).told.contains then
      post (setAg x a fun g => { g with told := pool c s1 ++ g.told }) ⟨none, a, false, .digest, 0⟩
    else x) (fun x : State => LkInv c x.lock x.ag) c.agents _ h2 (fun b a hb => by
      split
      · simp only [post_lock, post_ag, setAg_lock, setAg_ag]
        exact lk_live hb (liveL_modify _ (liveL_refl _) (by intro g hg; simpa [Agent.live] using hg))
      · exact hb)
  simp only []
  split
  · exact h3
  · exact foldl_inv _ (fun x : State => LkInv c x.lock x.ag) _ _ h3 (fun b t hb => hspawn _ _ _ hb)

/-- a tactic for "every agent live before is live after" over the agent changes of one action -/
macro "live_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible exact liveL_refl _
    | rw [setTask_ag]
    | rw [setAg_ag]
    | with_reducible apply liveL_deliver
    | with_reducible apply liveL_showAll
    | with_reducible apply liveL_takes
    | ((with_reducible refine liveL_modify _ ?_ ?hf); case hf => (intro g hg; first | rfl | simp_all [Agent.live]))))

theorem lkInv_of_reachable {c : Cfg} (hfix : c.lockOverlap = true) (hforms : c.lockForms = true) {s : State} (h : Reachable c s) :
    LkInv c s.lock s.ag := by
  refine reachable_induct (P := fun s => LkInv c s.lock s.ag) ?_ ?_ h
  · refine ⟨fun p l a hp ha => ?_, fun p q l m a b hp hq _ ha => ?_⟩ <;>
      (simp [init, List.getElem?_map] at hp; obtain ⟨_, _, rfl⟩ := hp; cases ha)
  intro s s' act _ hs hstep
  open_step hstep
  case unblock t =>
    split at hstep
    · rw [when_eq_some] at hstep; obtain ⟨_, rfl⟩ := hstep; simpa using hs
    · cases hstep
  case tick => obtain ⟨_, rfl⟩ := hstep; exact lk_tickOf hs
  case leave a =>
    obtain ⟨_, rfl⟩ := hstep
    exact lk_endAgent _ (by simp only [setAg_lock, setAg_ag]; exact lk_live hs (by live_tac))
  case reapGone a =>
    obtain ⟨_, rfl⟩ := hstep
    exact lk_endAgent _ (by simp only [setAg_lock, setAg_ag]; exact lk_live hs (by live_tac))
  case endOther a f =>
    obtain ⟨_, rfl⟩ := hstep
    exact lk_endAgent _ (by simp only [setAg_lock, setAg_ag]; exact lk_live hs (by live_tac))
  case lock a p =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range] at hg
    obtain ⟨⟨hw, hp⟩, hall⟩ := hg
    have halive : (s.ag.getD a default).live = true := by
      simp [working, busy, State.agt] at hw; simp [Agent.live, hw.1]
    have key : ∀ (q : Nat) (m : Lock) (b : Nat), s.lock[q]? = some m → m.holder = some b → b ≠ a → m.exp = false →
        overlap (c.pat p) (c.pat q) = false := by
      intro q m b hq hb hba he
      have hql : q < s.lock.length := (List.getElem?_eq_some_iff.mp hq).1
      have := hall q hql
      have hm : s.lock.getD q default = m := by simp [List.getD_eq_getElem?_getD, hq]
      have hlive := hs.1 q m b hq hb
      rw [hm] at this
      simp [hb, hba, he, State.owned, State.agt, refuses_eq hfix hforms] at this
      rw [List.getD_eq_getElem?_getD] at hlive
      rcases this with h0 | h0
      · rw [hlive] at h0; cases h0
      · exact h0
    show LkInv c (s.lock.set p ⟨some a, false⟩) s.ag
    refine ⟨fun p' l' b hp' hb => ?_, fun p1 q1 l m a1 b1 h1 h2 hne ha hb hab he1 he2 => ?_⟩
    · by_cases e : p = p'
      · subst e; simp [List.getElem?_set, hp] at hp'; subst hp'; cases hb; exact halive
      · simp [List.getElem?_set, e] at hp'; exact hs.1 p' l' b hp' hb
    · by_cases e1 : p = p1
      · subst e1
        have e2 : ¬ p = q1 := hne
        simp [List.getElem?_set, hp] at h1
        simp [List.getElem?_set, e2] at h2
        subst h1; cases ha
        exact key q1 m b1 h2 hb (fun e => hab e.symm) he2
      · simp [List.getElem?_set, e1] at h1
        by_cases e2 : p = q1
        · subst e2
          simp [List.getElem?_set, hp] at h2
          subst h2; cases hb
          rw [overlap_comm]; exact key p1 l a1 h1 ha hab he1
        · simp [List.getElem?_set, e2] at h2
          exact hs.2 p1 q1 l m a1 b1 h1 h2 hne ha hb hab he1 he2
  case unlock a p =>
    obtain ⟨_, rfl⟩ := hstep
    exact lk_shrink hs (shrinks_set _ _ _ (fun l _ => Or.inl rfl))
  case world w op => obtain ⟨_, rfl⟩ := hstep; exact hs
  case expireLock p =>
    obtain ⟨_, rfl⟩ := hstep
    refine lk_shrink hs (shrinks_set _ _ _ (fun l hl => Or.inr ⟨?_, by simp⟩))
    simp [List.getD_eq_getElem?_getD, hl]
  all_goals
    obtain ⟨hg, rfl⟩ := hstep
    (try split) <;> (try simp only [unbelieve, awake, claimed]) <;> simp <;>
      ((with_reducible refine lk_live hs ?_); live_tac)

/-- S3. With PR #114 (swarm lock refuses any common file) and board #26 (exactly the patterns that share a file),
no two live locks of different agents cover a common file. -/
theorem locksDisjoint_of_reachable {c : Cfg} (hfix : c.lockOverlap = true) (hforms : c.lockForms = true) {s : State}
    (h : Reachable c s) : locksDisjoint c s = true := by
  have hinv := lkInv_of_reachable hfix hforms h
  simp only [locksDisjoint, List.all_eq_true, List.mem_range]
  intro p hp q hq
  have h1 : s.lock[p]? = some (s.lock.getD p default) := by simp [List.getD_eq_getElem?_getD, hp]
  have h2 : s.lock[q]? = some (s.lock.getD q default) := by simp [List.getD_eq_getElem?_getD, hq]
  generalize s.lock.getD p default = l at h1 ⊢
  generalize s.lock.getD q default = m at h2 ⊢
  cases hl : l.holder with
  | none => simp
  | some a =>
    cases hm : m.holder with
    | none => simp
    | some b =>
      by_cases hpq : p = q
      · simp [hpq]
      by_cases hab : a = b
      · simp [hab]
      cases he1 : l.exp <;> cases he2 : m.exp <;> simp [hpq, hab]
      exact Or.inr (hinv.2 p q l m a b h1 h2 hpq hl hm hab he1 he2)

/-- S3 as files: with both fixes on, no path is covered by two unexpired locks of different agents, for any
patterns (a path is a Lua string: bytes; `Glob.overlaps_complete`). -/
theorem noSharedFile_of_reachable {c : Cfg} (hfix : c.lockOverlap = true) (hforms : c.lockForms = true) {s : State}
    (h : Reachable c s) {p q : Nat} {l m : Lock} {a b : Nat} (hp : s.lock[p]? = some l) (hq : s.lock[q]? = some m)
    (hpq : p ≠ q) (ha : l.holder = some a) (hb : m.holder = some b) (hab : a ≠ b) (he1 : l.exp = false)
    (he2 : m.exp = false) (x : String) (hx : Glob.Bytes x.toList) :
    ¬ (covers c x (c.pat p) = true ∧ covers c x (c.pat q) = true) := by
  rintro ⟨h1, h2⟩
  have hd := (lkInv_of_reachable hfix hforms h).2 p q l m a b hp hq hpq ha hb hab he1 he2
  simp only [covers, hforms] at h1 h2
  rw [overlap, Glob.overlaps_complete hx h1 h2] at hd; cases hd

end Swarm
