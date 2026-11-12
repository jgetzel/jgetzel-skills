import SwarmModel.Inbox

/-! S1, for every reachable state of every instance with the fix on (reap reopens a lapsed claim only when its
owner is idle or gone). -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

-- ---------- the board's ids: the tasks that exist are 1..n, so `add` makes a new one ----------
def Pfx (s : State) : Prop := ∃ n, n ≤ s.task.length ∧ ∀ u, (s.tk u).st ≠ .absent ↔ (0 < u ∧ u ≤ n)

theorem filter_prefix {α : Type} (p : α → Bool) : ∀ (l : List α) (n : Nat), n ≤ l.length →
    (∀ i (h : i < l.length), p l[i] = true ↔ i < n) → (l.filter p).length = n
  | [], n, hn, _ => by simp at hn; simp [hn]
  | x :: xs, n, hn, h => by
    have h0 := h 0 (by simp)
    cases n with
    | zero =>
      have hx : p x = false := by simpa using h0
      have ih := filter_prefix p xs 0 (Nat.zero_le _) (fun i hi => by
        have := h (i + 1) (by simp; omega); simpa using this)
      simp [List.filter_cons, hx, ih]
    | succ n =>
      have hx : p x = true := by simpa using h0
      have ih := filter_prefix p xs n (by simp at hn; omega) (fun i hi => by
        have := h (i + 1) (by simp; omega); simpa using this)
      simp [List.filter_cons, hx, ih]

theorem pfx_same {s s' : State} (hl : s'.task.length = s.task.length)
    (h : ∀ u, (s'.tk u).st = .absent ↔ (s.tk u).st = .absent) (hp : Pfx s) : Pfx s' := by
  obtain ⟨n, h2, h3⟩ := hp
  exact ⟨n, by rw [hl]; exact h2, fun u => by rw [← h3 u]; exact not_congr (h u)⟩
theorem pfx_task {s s' : State} (h : s'.task = s.task) (hp : Pfx s) : Pfx s' :=
  pfx_same (by rw [h]) (fun u => by simp [State.tk, h]) hp
/-- a change of a task that exists, to a state other than absent -/
theorem pfx_setTask {s : State} {t : Nat} {f : Task → Task}
    (h : t ≠ 0 → (s.tk t).st ≠ .absent ∧ (f (s.tk t)).st ≠ .absent) (hp : Pfx s) : Pfx (setTask s t f) := by
  by_cases h0 : t = 0
  · subst h0; exact hp
  · refine pfx_same (by unfold setTask; split <;> simp) (fun u => ?_) hp
    rcases tk_setTask_or s t u f with e | ⟨rfl, e⟩
    · rw [e]
    · rw [e]; exact ⟨fun ha => absurd ha (h h0).2, fun ha => absurd ha (h h0).1⟩
theorem pfx_map {s s' : State} {g : Task → Task} (hg : g default = default) (h : ∀ k, (g k).st = .absent ↔ k.st = .absent)
    (ht : s'.task = s.task.map g) (hp : Pfx s) : Pfx s' :=
  pfx_same (by rw [ht]; simp) (fun u => by rw [tk_map hg ht]; exact h _) hp
theorem pfx_endAgent {s : State} {a : Nat} (hp : Pfx s) : Pfx (endAgent s a) :=
  pfx_map (g := fun k => if held k a then { k with st := .opn, owner := none, lease := false, hcq := false } else k)
    (by simp [held]) (fun k => by
      split
      · rename_i h; simp [held] at h; rcases h.2 with e | e <;> simp [e]
      · exact Iff.rfl) rfl hp
theorem pfx_reapTask {c : Cfg} {s : State} {t : Nat} (hp : Pfx s) : Pfx (reapTask c s t) := by
  unfold reapTask; simp only []; split
  · split
    · rename_i h
      exact pfx_task (post_task ..) (pfx_setTask (fun _ => by simp_all) hp)
    · exact hp
  · exact hp
theorem pfx_spawnFor {c : Cfg} {pl : List Nat} {s : State} {t : Nat} (hopn : (s.tk t).st = .opn) (hp : Pfx s) :
    Pfx (spawnFor c pl s t) := by
  unfold spawnFor; split
  · split
    · refine pfx_setTask (fun _ => ⟨?_, by simp⟩) (pfx_task (s := s) rfl hp)
      show (s.tk t).st ≠ .absent
      rw [hopn]; simp
    · exact hp
  · exact hp

theorem tk_setTask_at {s : State} {t : Nat} {f : Task → Task} (h0 : t ≠ 0) (hl : t - 1 < s.task.length) :
    (setTask s t f).tk t = f (s.tk t) := by
  simp only [setTask, State.tk, h0, ite_false]; rw [getD_modify]; simp [hl]
theorem nextTask_eq {s : State} {n : Nat} (h2 : n ≤ s.task.length) (h3 : ∀ u, (s.tk u).st ≠ .absent ↔ (0 < u ∧ u ≤ n)) :
    nextTask s = n + 1 := by
  unfold nextTask
  rw [filter_prefix _ _ n h2]
  intro i hi
  have := h3 (i + 1)
  simp [State.tk, List.getD_eq_getElem?_getD, hi] at this
  simp only [bne_iff_ne, ne_eq]
  rw [this]; omega

macro "pf_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible assumption
    | ((with_reducible refine pfx_setTask (fun _ => ?_) ?_); focus (simp_all [claimable, startable, ownsClaimed, held]; done))
    | ((with_reducible refine pfx_task (setAg_task ..) ?_))
    | ((with_reducible refine pfx_task (post_task ..) ?_))
    | ((with_reducible refine pfx_task (deliver_task ..) ?_))
    | ((with_reducible refine pfx_task (takes_task ..) ?_))
    | with_reducible apply pfx_endAgent
    | assumption))

theorem pfx_of_reachable {c : Cfg} {s : State} (h : Reachable c s) : Pfx s := by
  refine reachable_induct ?_ ?_ h
  · refine ⟨0, Nat.zero_le _, fun u => ?_⟩
    have : ((init c).tk u).st = .absent := by
      simp only [State.tk, init]; split
      · rfl
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
    simp [this]; omega
  intro s s' act _ hs hstep
  open_step hstep
  case unblock t =>
    split at hstep
    · rw [when_eq_some] at hstep; obtain ⟨hg, rfl⟩ := hstep
      exact pfx_task (s := setTask s t _) rfl (pfx_setTask (fun _ => by simp_all) hs)
    · cases hstep
  case tick =>
    obtain ⟨_, rfl⟩ := hstep
    exact tick_inv Pfx (fun _ _ => pfx_reapTask) (fun _ => pfx_task rfl) (fun _ _ => pfx_endAgent)
      (fun _ _ _ hx => pfx_task rfl hx) (fun _ _ _ hx hopn => pfx_spawnFor hopn hx) hs
  case lock a p => obtain ⟨_, rfl⟩ := hstep; exact pfx_task (s := s) rfl hs
  case unlock a p => obtain ⟨_, rfl⟩ := hstep; exact pfx_task (s := s) rfl hs
  case expireLock p => obtain ⟨_, rfl⟩ := hstep; exact pfx_task (s := s) rfl hs
  case world w op => obtain ⟨_, rfl⟩ := hstep; exact pfx_task (s := s) rfl hs
  case git a op => obtain ⟨_, rfl⟩ := hstep; exact pfx_task (s := s) rfl hs
  case wakeWrite a =>
    obtain ⟨_, rfl⟩ := hstep
    refine pfx_task (s := s) ?_ hs
    simp only [setAg_task, awake_task, deliver_task]; split <;> simp
  case claimWrite a =>
    obtain ⟨_, rfl⟩ := hstep
    split
    · rename_i h
      refine pfx_task (s := claimed s a (s.agt a).reading) (by simp) (pfx_setTask (fun _ => ?_) hs)
      simp_all
    · exact pfx_task (setAg_task ..) hs
  case hcPrompt a =>
    obtain ⟨_, rfl⟩ := hstep
    refine pfx_setTask (fun h0 => ?_) (pfx_task (setAg_task ..) hs)
    have : ownsClaimed s a (firstClaimed c s a) = true := by
      unfold firstClaimed at h0 ⊢
      cases hf : c.tasks.find? (ownsClaimed s a) with
      | none => simp [hf] at h0
      | some t => simpa using List.find?_some hf
    simp [ownsClaimed] at this
    show (s.tk _).st ≠ .absent ∧ _
    simp [this.1]
  case hcClear a =>
    obtain ⟨_, rfl⟩ := hstep
    refine pfx_task (setAg_task ..) (pfx_task (deliver_task ..) (pfx_map (s := s) (g := fun k =>
      if k.owner == some a && k.st == .blocked && k.hcq then { k with st := .claimed, hcq := false, lease := true } else k)
      (by simp) (fun k => ?_) rfl hs))
    split
    · rename_i h; simp at h; simp [h.1.2]
    · exact Iff.rfl
  case dropOwn a t =>
    obtain ⟨hg, rfl⟩ := hstep; simp [held] at hg
    exact pfx_task (unbelieve_task ..) (pfx_setTask (fun _ => ⟨by rcases hg.2.2 with e | e <;> simp [e], by simp⟩) hs)
  case releaseOther t =>
    obtain ⟨hg, rfl⟩ := hstep
    have hg' : (s.tk t).st = .claimed ∨ (s.tk t).st = .blocked := by simp at hg; exact hg.2
    exact pfx_task (post_task ..) (pfx_setTask (fun _ => ⟨by rcases hg' with e | e <;> simp [e], by simp⟩) hs)
  case add deps =>
    obtain ⟨hg, rfl⟩ := hstep
    obtain ⟨n, h2, h3⟩ := hs
    have hn := nextTask_eq h2 h3
    simp at hg
    rw [hn] at hg ⊢
    refine ⟨n + 1, by simp [setTask]; omega, fun u => ?_⟩
    by_cases hu : u = n + 1
    · subst hu; rw [tk_setTask_at (by omega) (by omega)]; simp
    · rw [tk_setTask_ne hu, h3 u]; omega
  all_goals
    obtain ⟨hg, rfl⟩ := hstep
    (try split) <;> (try simp only [unbelieve, awake, claimed]) <;> pf_tac

-- ---------- who believes they hold a task ----------
/-- a has an unread message that reap reopened its claim of t -/
def rel (s : State) (a t : Nat) : Prop :=
  ∃ i, s.cur a < i ∧ i ≤ s.log.length ∧ addressed s a i = true ∧ (s.msg i).kind = .released ∧ (s.msg i).task = t
/-- a's belief that it holds t is stale, and a will learn so before it works again -/
def idleRel (s : State) (a t : Nat) : Prop := active (s.agt a) = false ∧ rel s a t
def HD (s : State) (a t : Nat) : Prop := held (s.tk t) a = true ∨ (s.tk t).st = .dropped
/-- board #53: the user released t from a, and a hasn't read the stop the task records (`stopTo`, `stopMsg`) -/
def stopRel (s : State) (a t : Nat) : Prop :=
  (s.tk t).stopTo = some a ∧ s.cur a < (s.tk t).stopMsg ∧ (s.tk t).stopMsg ≤ s.log.length ∧
    addressed s a (s.tk t).stopMsg = true ∧ (s.msg (s.tk t).stopMsg).kind = .released ∧ (s.msg (s.tk t).stopMsg).task = t
/-- a's belief in t is backed by the stop it hasn't read, and no one has taken t since -/
def HS (s : State) (a t : Nat) : Prop := stopRel s a t ∧ (s.tk t).st = .opn
/-- The invariant behind S1. An agent that believes it holds t does hold it, or t was dropped, or the belief is
stale, or (board #53) the user released t from it and it hasn't read the stop, and no one has taken t since; and no two
agents have a belief in t that isn't stale. -/
def J (s : State) : Prop :=
  (∀ a t, t ∈ (s.agt a).believes → idleRel s a t ∨ HD s a t ∨ HS s a t) ∧
  (∀ a b t, t ∈ (s.agt a).believes → t ∈ (s.agt b).believes → ¬idleRel s a t → ¬idleRel s b t → a = b)

theorem rel_of_stopRel {s : State} {a t : Nat} (h : stopRel s a t) : rel s a t :=
  ⟨_, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- beliefs only go away, stale ones stay stale, and one that isn't stale is still backed by the board or the stop -/
theorem J_of {s s' : State} (h : J s)
    (hsub : ∀ a t, t ∈ (s'.agt a).believes → t ∈ (s.agt a).believes)
    (hir : ∀ a t, t ∈ (s'.agt a).believes → idleRel s a t → idleRel s' a t)
    (hhd : ∀ a t, t ∈ (s'.agt a).believes → ¬idleRel s a t → HD s a t → idleRel s' a t ∨ HD s' a t ∨ HS s' a t)
    (hhs : ∀ a t, t ∈ (s'.agt a).believes → ¬idleRel s a t → HS s a t → idleRel s' a t ∨ HD s' a t ∨ HS s' a t) :
    J s' := by
  refine ⟨fun a t ht => ?_, fun a b t ha hb na nb => ?_⟩
  · by_cases hi : idleRel s a t
    · exact Or.inl (hir a t ht hi)
    · rcases h.1 a t (hsub a t ht) with h1 | h1 | h1
      · exact absurd h1 hi
      · exact hhd a t ht hi h1
      · exact hhs a t ht hi h1
  · exact h.2 a b t (hsub a t ha) (hsub b t hb) (fun hi => na (hir a t ha hi)) (fun hi => nb (hir b t hb hi))

/-- the stop is still unread, from what the change leaves of the task, the log and a's cursor -/
theorem HS_of {s s' : State} {a t : Nat} (h : stopRel s a t) (h1 : (s'.tk t).stopTo = (s.tk t).stopTo)
    (h2 : (s'.tk t).stopMsg = (s.tk t).stopMsg) (h3 : (s'.tk t).st = .opn) (hlog : ∃ e, s'.log = s.log ++ e)
    (hcur : s'.cur a = s.cur a) : HS s' a t := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  obtain ⟨e, he⟩ := hlog
  have hm : s'.msg (s.tk t).stopMsg = s.msg (s.tk t).stopMsg := by
    have h0 : (s.tk t).stopMsg ≠ 0 := by omega
    simp [State.msg, h0, he, List.getD_eq_getElem?_getD, List.getElem?_append_left (show (s.tk t).stopMsg - 1 < s.log.length by omega)]
  refine ⟨⟨by rw [h1]; exact a1, by rw [h2, hcur]; exact a2, by rw [h2, he]; simp; omega, ?_, ?_, ?_⟩, h3⟩
  · simp only [addressed, h2, hm] at a4 ⊢; exact a4
  · rw [h2, hm]; exact a5
  · rw [h2, hm]; exact a6
theorem HS_congr {s s' : State} {a t : Nat} (ht : s'.task = s.task) (hlog : s'.log = s.log) (hcur : s'.cur a = s.cur a)
    (h : HS s a t) : HS s' a t :=
  have e : s'.tk t = s.tk t := by simp [State.tk, ht]
  HS_of h.1 (by rw [e]) (by rw [e]) (by rw [e]; exact h.2) ⟨[], by simp [hlog]⟩ hcur
/-- the guard (board #53): a task that isn't `stopped` backs no belief by its stop, unless that belief is stale -/
theorem not_HS_of_stopped {s : State} {b t : Nat} (hst : stopped s t = false) (hs : HS s b t) (hi : ¬idleRel s b t) : False := by
  have ha : active (s.agt b) = true := by
    cases e : active (s.agt b)
    · exact absurd ⟨e, rel_of_stopRel hs.1⟩ hi
    · rfl
  unfold stopped at hst; rw [hs.1.1] at hst; simp [ha, hs.1.2.1] at hst

theorem rel_congr {s s' : State} {a t : Nat} (hlog : s'.log = s.log) (hcur : s'.cur a = s.cur a) : rel s' a t ↔ rel s a t := by
  simp only [rel, hlog, hcur, addressed_congr hlog, msg_congr hlog]
theorem held_unique {k : Task} {a b : Nat} (h1 : held k a = true) (h2 : held k b = true) : a = b := by
  simp [held] at h1 h2; exact Option.some.inj (h1.1.symm.trans h2.1)
theorem held_not_dropped {k : Task} {a : Nat} (h : held k a = true) : k.st ≠ .dropped := by
  simp [held] at h; rcases h.2 with e | e <;> simp [e]

/-- only the board changed -/
theorem J_tasks {s s' : State} (hag : s'.ag = s.ag) (hlog : s'.log = s.log) (hcur : s'.cursor = s.cursor)
    (hhd : ∀ a u, u ∈ (s.agt a).believes → ¬idleRel s a u → HD s a u → HD s' a u)
    (hhs : ∀ a u, u ∈ (s.agt a).believes → ¬idleRel s a u → HS s a u → HD s' a u ∨ HS s' a u) (h : J s) : J s' := by
  have hagt : ∀ a, s'.agt a = s.agt a := fun a => by simp [State.agt, hag]
  have hir : ∀ a t, idleRel s' a t ↔ idleRel s a t := fun a t => by
    simp only [idleRel, hagt, rel_congr hlog (show s'.cur a = s.cur a by simp [State.cur, hcur])]
  exact J_of h (fun a t ht => hagt a ▸ ht) (fun a t _ hi => (hir a t).mpr hi)
    (fun a t ht hi hd => Or.inr (Or.inl (hhd a t (hagt a ▸ ht) hi hd))) (fun a t ht hi hs => Or.inr (hhs a t (hagt a ▸ ht) hi hs))
/-- a task whose stop no belief rests on (its state is not open), or t's own stop kept: what a change of the board
leaves of a belief resting on it -/
theorem J_tasks_same {s s' : State} {a u : Nat} (hlog : s'.log = s.log) (hcur : s'.cursor = s.cursor) (htk : s'.tk u = s.tk u)
    (hs : HS s a u) : HD s' a u ∨ HS s' a u :=
  Or.inr (HS_of hs.1 (by rw [htk]) (by rw [htk]) (by rw [htk]; exact hs.2) ⟨[], by simp [hlog]⟩ (by simp [State.cur, hcur]))
theorem J_frame {s s' : State} (hag : s'.ag = s.ag) (hlog : s'.log = s.log) (hcur : s'.cursor = s.cursor)
    (htask : s'.task = s.task) (h : J s) : J s' :=
  J_tasks hag hlog hcur (fun a u _ _ hd => by simpa [HD, State.tk, htask] using hd)
    (fun a u _ _ hs => J_tasks_same hlog hcur (by simp [State.tk, htask]) hs) h
/-- a change of task t: what backed a belief in t still does. `hs`: a belief resting on t's stop (t open) is held after
it, or t dropped, or still open with its stop -/
theorem J_setTask {s : State} {t : Nat} {f : Task → Task}
    (hm : ∀ b, HD s b t → held (f (s.tk t)) b = true ∨ (f (s.tk t)).st = .dropped)
    (hs : ∀ b, t ∈ (s.agt b).believes → HS s b t → ¬idleRel s b t → held (f (s.tk t)) b = true ∨ (f (s.tk t)).st = .dropped ∨
      ((f (s.tk t)).stopTo = (s.tk t).stopTo ∧ (f (s.tk t)).stopMsg = (s.tk t).stopMsg ∧ (f (s.tk t)).st = .opn))
    (h : J s) : J (setTask s t f) :=
  J_tasks (setTask_ag ..) (setTask_log ..) (setTask_cursor ..) (fun b u _ _ hd => by
    rcases tk_setTask_or s t u f with e | ⟨rfl, e⟩
    · unfold HD; rw [e]; exact hd
    · unfold HD; rw [e]; exact hm b hd) (fun b u _ hi hsu => by
    rcases tk_setTask_or s t u f with e | ⟨rfl, e⟩
    · exact J_tasks_same (by simp) (by simp) e hsu
    · rcases hs b ‹_› hsu hi with e1 | e1 | ⟨q1, q2, q3⟩
      · exact Or.inl (Or.inl (by rw [e]; exact e1))
      · exact Or.inl (Or.inr (by rw [e]; exact e1))
      · exact Or.inr (HS_of hsu.1 (by rw [e]; exact q1) (by rw [e]; exact q2) (by rw [e]; exact q3) ⟨[], by simp⟩ (by simp [State.cur]))) h
/-- no belief rests on the stop of a task that isn't open -/
theorem HS_not_opn {s : State} {b t : Nat} (h : (s.tk t).st ≠ .opn) : ¬ HS s b t := fun hs => h hs.2

/-- only agent a changed: it believes no more than before, and it isn't put to work on a stale belief -/
theorem J_setAg {s : State} {a : Nat} {f : Agent → Agent} (h1 : ∀ u, u ∈ (f (s.agt a)).believes → u ∈ (s.agt a).believes)
    (h2 : ∀ u, u ∈ (f (s.agt a)).believes → idleRel s a u → active (f (s.agt a)) = false) (h : J s) : J (setAg s a f) := by
  have hrel : ∀ b t, rel (setAg s a f) b t ↔ rel s b t := fun b t => rel_congr rfl rfl
  refine J_of h (fun b t ht => ?_) (fun b t ht hi => ?_) (fun b t _ _ hd => Or.inr (Or.inl hd))
    (fun b t _ _ hs => Or.inr (Or.inr (HS_congr (by simp) (by simp) (by simp [State.cur]) hs)))
  · by_cases hb : a = b ∧ b < s.ag.length
    · rw [agt_setAg, ite_eq_left hb] at ht; obtain ⟨rfl, _⟩ := hb; exact h1 t ht
    · rw [agt_setAg, ite_eq_right hb] at ht; exact ht
  · refine ⟨?_, (hrel b t).mpr hi.2⟩
    by_cases hb : a = b ∧ b < s.ag.length
    · rw [agt_setAg, ite_eq_left hb] at ht ⊢; obtain ⟨rfl, _⟩ := hb; exact h2 t ht hi
    · rw [agt_setAg, ite_eq_right hb]; exact hi.1
theorem J_setAg_same {s : State} {a : Nat} {f : Agent → Agent} (hb : ∀ g, (f g).believes = g.believes)
    (ha : ∀ g, active (f g) = active g) (h : J s) : J (setAg s a f) :=
  J_setAg (fun u hu => by rw [hb] at hu; exact hu) (fun u _ hi => by rw [ha]; exact hi.1) h
theorem J_setAg_act {s : State} {a : Nat} {f : Agent → Agent} (hb : ∀ g, (f g).believes = g.believes)
    (ha : active (s.agt a) = true) (h : J s) : J (setAg s a f) :=
  J_setAg (fun u hu => by rw [hb] at hu; exact hu) (fun u _ hi => by have := hi.1; rw [ha] at this; cases this) h

theorem J_post {s : State} {m : Msg} (h : J s) : J (post s m) := by
  refine J_of h (fun _ _ ht => ht) (fun b t _ hi => ⟨hi.1, ?_⟩) (fun _ _ _ _ hd => Or.inr (Or.inl hd))
    (fun b t _ _ hs => Or.inr (Or.inr (HS_of hs.1 rfl rfl hs.2 ⟨[m], rfl⟩ rfl)))
  obtain ⟨i, h1, h2, h3, h4, h5⟩ := hi.2
  exact ⟨i, h1, by rw [post_log_length]; omega, by rw [addressed_post h2]; exact h3, by rw [msg_post h2]; exact h4,
    by rw [msg_post h2]; exact h5⟩

/-- Showing ids to a, when they skip no message between a's cursor and their last. -/
theorem J_showAll {s : State} {a : Nat} {ids : List Nat}
    (hns : ∀ j ∈ ids, ∀ i, s.cur a < i → i ≤ j → addressed s a i = true → i ∈ ids) (h : J s) : J (showAll s a ids) := by
  have hact : ∀ b, active ((showAll s a ids).agt b) = active (s.agt b) := fun b => showAll_proj (active ·) (fun _ _ => rfl) ..
  have htk : ∀ t, (showAll s a ids).tk t = s.tk t := fun t => by simp [State.tk]
  -- a released message for t still unread by b stays unread, while b believes it holds t
  have hlt : ∀ b t i, t ∈ ((showAll s a ids).agt b).believes → s.cur b < i → addressed s b i = true →
      (s.msg i).kind = .released → (s.msg i).task = t → (showAll s a ids).cur b < i := by
    intro b t i ht i1 i3 i4 i5
    have hbel := (showAll_bel ..).mp ht
    rw [showAll_cur]; split
    · rename_i hb; obtain ⟨rfl, _⟩ := hb
      obtain ⟨_, _, m3⟩ := foldl_max ids (s.cur b)
      apply Nat.lt_of_not_le; intro hle
      rcases m3 with e | e
      · omega
      · exact hbel.2 ⟨rfl, i, hns _ e i i1 hle i3, i4, i5⟩
    · exact i1
  refine J_of h (fun b t ht => ((showAll_bel ..).mp ht).1) (fun b t ht hi => ?_)
    (fun b t _ _ hd => Or.inr (Or.inl (by unfold HD; rw [htk]; exact hd))) (fun b t ht _ hs => ?_)
  · refine ⟨by rw [hact]; exact hi.1, ?_⟩
    obtain ⟨i, i1, i2, i3, i4, i5⟩ := hi.2
    exact ⟨i, hlt b t i ht i1 i3 i4 i5, by rw [showAll_log]; exact i2, by rw [addressed_congr (showAll_log ..)]; exact i3,
      by rw [msg_congr (showAll_log ..)]; exact i4, by rw [msg_congr (showAll_log ..)]; exact i5⟩
  · obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, h3⟩ := hs
    refine Or.inr (Or.inr ⟨⟨by rw [htk]; exact a1, ?_, ?_, ?_, ?_, ?_⟩, by rw [htk]; exact h3⟩)
    · rw [htk]; exact hlt b t _ ht a2 a4 a5 a6
    · rw [htk, showAll_log]; exact a3
    · rw [htk, addressed_congr (showAll_log ..)]; exact a4
    · rw [htk, msg_congr (showAll_log ..)]; exact a5
    · rw [htk, msg_congr (showAll_log ..)]; exact a6
theorem J_deliver {s : State} {a : Nat} (h : J s) : J (deliver s a) :=
  J_showAll (fun _ hj i hi hij had => mem_unread.mpr ⟨hi, Nat.le_trans hij (mem_unread.mp hj).2.1, had⟩) h
/-- after a delivery no belief of a is stale -/
theorem norel_deliver {s : State} {a u : Nat} (hu : u ∈ ((deliver s a).agt a).believes) : ¬ rel (deliver s a) a u := by
  rintro ⟨i, i1, i2, i3, i4, i5⟩
  have hbel := (showAll_bel (unread s a) s a a u).mp hu
  rw [addressed_congr (deliver_log ..)] at i3; rw [msg_congr (deliver_log ..)] at i4 i5; rw [deliver_log] at i2
  have hc : s.cur a ≤ (showAll s a (unread s a)).cur a := by
    rw [showAll_cur]; split
    · exact (foldl_max _ _).1
    · exact Nat.le_refl _
  have i1' : (showAll s a (unread s a)).cur a < i := i1
  exact hbel.2 ⟨rfl, i, mem_unread.mpr ⟨by omega, i2, i3⟩, i4, i5⟩
/-- a turn starts: the prompt hook delivers, then the agent is at work -/
theorem J_wake {s : State} {a : Nat} {f : Agent → Agent} (hf : ∀ g, (f g).believes = g.believes) (h : J s) :
    J (setAg (deliver s a) a f) :=
  J_setAg (fun u hu => by rw [hf] at hu; exact hu)
    (fun u hu hi => absurd hi.2 (norel_deliver (by rw [hf] at hu; exact hu))) (J_deliver h)

/-- a takes a task it holds -/
theorem J_takes {c : Cfg} {s : State} {a t : Nat} (hheld : held (s.tk t) a = true) (h : J s) : J (takes c s a t) := by
  suffices hs : J (setAg s a fun g => { g with believes := t :: g.believes }) by
    unfold takes; simp only []; split
    · exact J_frame (s := setAg s a fun g => { g with believes := t :: g.believes }) rfl rfl rfl rfl hs
    · exact hs
  have hmem : ∀ b u, u ∈ ((setAg s a fun g => { g with believes := t :: g.believes }).agt b).believes →
      u ∈ (s.agt b).believes ∨ (b = a ∧ u = t) := by
    intro b u hu; rw [agt_setAg] at hu; split at hu
    · rename_i hb
      rcases List.mem_cons.mp hu with e | e
      · exact Or.inr ⟨hb.1.symm, e⟩
      · exact Or.inl e
    · exact Or.inl hu
  have hact : ∀ b, active ((setAg s a fun g => { g with believes := t :: g.believes }).agt b) = active (s.agt b) := by
    intro b; rw [agt_setAg]; split <;> rfl
  have hir : ∀ b u, idleRel (setAg s a fun g => { g with believes := t :: g.believes }) b u ↔ idleRel s b u := fun b u => by
    simp only [idleRel, hact, rel_congr (s := s) (s' := setAg s a fun g => { g with believes := t :: g.believes }) rfl rfl]
  have key : ∀ b, t ∈ (s.agt b).believes → ¬idleRel s b t → b = a := by
    intro b hb hn
    rcases h.1 b t hb with e | (e | e) | e
    · exact absurd e hn
    · exact held_unique e hheld
    · exact absurd e (held_not_dropped hheld)
    · exfalso; have := e.2; simp [held, this] at hheld
  refine ⟨fun b u hu => ?_, fun x y u hx hy nx ny => ?_⟩
  · rcases hmem b u hu with e | ⟨e1, e2⟩
    · rcases h.1 b u e with e' | e' | e'
      · exact Or.inl ((hir b u).mpr e')
      · exact Or.inr (Or.inl e')
      · exact Or.inr (Or.inr (HS_congr (by simp) (by simp) (by simp [State.cur]) e'))
    · subst e1 e2; exact Or.inr (Or.inl (Or.inl hheld))
  · rw [hir] at nx ny
    rcases hmem x u hx with ex | ⟨ex1, ex2⟩ <;> rcases hmem y u hy with ey | ⟨ey1, ey2⟩
    · exact h.2 x y u ex ey nx ny
    · subst ey2; rw [ey1]; exact key x ex nx
    · subst ex2; rw [ex1]; exact (key y ey ny).symm
    · rw [ex1, ey1]

/-- a gives up a task only it holds: released, done or dropped -/
theorem J_giveup {s : State} {a t : Nat} {f : Task → Task} (hown : ∀ b, held (s.tk t) b = true → b = a)
    (hnd : (s.tk t).st ≠ .dropped) (hno : (s.tk t).st ≠ .opn) (h : J s) : J (unbelieve (setTask s t f) a t) := by
  have hrel : ∀ b u, rel (unbelieve (setTask s t f) a t) b u ↔ rel s b u := fun b u =>
    rel_congr (by simp) (by simp [State.cur])
  have hagt : ∀ b, (setTask s t f).agt b = s.agt b := fun b => by simp [State.agt]
  have hact : ∀ b, active ((unbelieve (setTask s t f) a t).agt b) = active (s.agt b) := by
    intro b; unfold unbelieve; rw [agt_setAg, hagt]; split <;> rfl
  have hbel : ∀ b u, u ∈ ((unbelieve (setTask s t f) a t).agt b).believes → u ∈ (s.agt b).believes ∧ ¬(b = a ∧ u = t) := by
    intro b u hu; unfold unbelieve at hu; rw [agt_setAg, hagt] at hu
    split at hu
    · rename_i hb; simp [List.mem_filter] at hu; exact ⟨hu.1, fun e => hu.2 e.2⟩
    · rename_i hb; refine ⟨hu, fun e => ?_⟩
      obtain ⟨rfl, _⟩ := e
      have : s.ag.length ≤ b := Nat.le_of_not_lt (fun hl => hb ⟨rfl, by simpa using hl⟩)
      rw [agt_of_ge this] at hu; cases hu
  refine J_of h (fun b u hu => (hbel b u hu).1) (fun b u _ hi => ⟨by rw [hact]; exact hi.1, (hrel b u).mpr hi.2⟩)
    (fun b u hu _ hd => ?_) (fun b u hu _ hs => ?_)
  · have hne := (hbel b u hu).2
    by_cases hut : u = t
    · subst hut
      rcases hd with e | e
      · exact absurd ⟨hown b e, rfl⟩ hne
      · exact absurd e hnd
    · right; left
      show held ((setTask s t f).tk u) b = true ∨ ((setTask s t f).tk u).st = .dropped
      rw [tk_setTask_ne hut]; exact hd
  · by_cases hut : u = t
    · subst hut; exact absurd hs.2 hno
    · refine Or.inr (J_tasks_same (s := s) (by simp [unbelieve]) (by simp [unbelieve]) ?_ hs)
      rw [show (unbelieve (setTask s t f) a t).tk u = (setTask s t f).tk u by simp [unbelieve, State.tk], tk_setTask_ne hut]

/-- reap under the fix: the owner of a reopened claim isn't at work, and is told -/
theorem J_reapTask {c : Cfg} {x : State} {t : Nat} (hfix : c.release = .idle) (hcur : ∀ a, x.cur a ≤ x.log.length)
    (h : J x) : J (reapTask c x t) := by
  unfold reapTask; simp only []
  split
  · rename_i o ho
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      obtain ⟨⟨hst, _⟩, hk⟩ := hc
      have hna : active (x.agt o) = false := by
        cases hs : (x.agt o).st <;> simp_all [keeps, Agent.live, active]
      have e : ∀ (f : Task → Task) (m : Msg), post (setTask x t f) m = setTask (post x m) t f := by
        intro f m; unfold setTask; split <;> rfl
      rw [e]
      refine J_tasks (setTask_ag ..) (setTask_log ..) (setTask_cursor ..) (fun b u _ hi hd => ?_) (fun b u _ _ hs => ?_) (J_post h)
      rotate_left
      · rcases tk_setTask_or (post x ⟨none, o, false, .released, t⟩) t u (fun r => { r with st := .opn, owner := none, lease := false, reaped := some o }) with e1 | ⟨rfl, e1⟩
        · exact J_tasks_same (by simp) (by simp) e1 hs
        · exact absurd hs.2 (by simp [State.tk] at hst ⊢; simp [hst])
      rcases tk_setTask_or (post x ⟨none, o, false, .released, t⟩) t u _ with e1 | ⟨rfl, e1⟩
      · unfold HD; rw [e1]; exact hd
      · exfalso; apply hi
        have hd' : held (x.tk u) b = true ∨ (x.tk u).st = .dropped := hd
        rcases hd' with e2 | e2
        · have hb : o = b := by simp [held, ho] at e2; exact e2.1
          subst hb
          refine ⟨hna, x.log.length + 1, ?_, by simp, ?_, ?_, ?_⟩
          · have := hcur o; show x.cur o < _; omega
          · simp [addressed, msg_post_new]
          · rw [msg_post_new]
          · rw [msg_post_new]
        · rw [hst] at e2; cases e2
    · exact h
  · exact h

theorem bel_clear {s : State} {a : Nat} {f : Agent → Agent} (hf : ∀ g, (f g).believes = []) :
    ((setAg s a f).agt a).believes = [] := by
  rw [agt_setAg]; split
  · exact hf _
  · rename_i hb
    have : s.ag.length ≤ a := Nat.le_of_not_lt (fun hl => hb ⟨rfl, hl⟩)
    rw [agt_of_ge this]; rfl
theorem J_clear {s : State} {a : Nat} {f : Agent → Agent} (hf : ∀ g, (f g).believes = []) (h : J s) : J (setAg s a f) :=
  J_setAg (fun u hu => by rw [hf] at hu; cases hu) (fun u hu => by rw [hf] at hu; cases hu) h

theorem J_endAgent {s : State} {a : Nat} (h : J s) : J (endAgent s a) := by
  have hf : ∀ g : Agent, ({ g with st := .ended, boot := false, believes := [] } : Agent).believes = [] := fun _ => rfl
  have h1 := J_clear (s := s) (a := a) hf h
  have hbel := bel_clear (s := s) (a := a) hf
  refine J_tasks (s := setAg s a fun g => { g with st := .ended, boot := false, believes := [] }) rfl rfl rfl
    (fun b u hu _ hd => ?_) (fun b u _ _ hs => J_tasks_same (s' := endAgent s a) (by simp) (by simp) (by
      rw [endAgent_tk]; split
      · rename_i hh; have : (s.tk u).st = .opn := hs.2; simp [held, this] at hh
      · simp [State.tk]) hs) h1
  have hba : b ≠ a := by rintro rfl; rw [hbel] at hu; cases hu
  unfold HD; rw [endAgent_tk]
  have hd' : held (s.tk u) b = true ∨ (s.tk u).st = .dropped := hd
  split
  · rename_i hh
    rcases hd' with e | e
    · exact absurd (held_unique e hh) hba
    · exact absurd e (held_not_dropped hh)
  · exact hd'

/-- a spawn: a new agent in slot a, believing nothing, holding a task that was open -/
theorem J_spawnFor {c : Cfg} {pl : List Nat} {x : State} {t : Nat} (hopn : (x.tk t).st = .opn) (hst : stopped x t = false)
    (h : J x) : J (spawnFor c pl x t) := by
  unfold spawnFor; split
  · rename_i a _
    split
    · have hf : ∀ g : Agent, ((fun _ =>
          { (default : Agent) with
            st := .idle, boot := true, recorded := c.recordedWorkspaces,
            rhead := if c.recordedWorkspaces then some (x.git.tipOf (c.tbase t)) else none, rbase := c.tbase t }) g : Agent).believes = [] :=
        fun _ => rfl
      have h1 := J_clear (s := x) (a := a) hf h
      have hbel := bel_clear (s := x) (a := a) hf
      have h2 : J { setAg x a (fun _ =>
          { (default : Agent) with
            st := .idle, boot := true, recorded := c.recordedWorkspaces,
            rhead := if c.recordedWorkspaces then some (x.git.tipOf (c.tbase t)) else none, rbase := c.tbase t }) with
          cursor := x.cursor.set a x.log.length, start := x.start.set a x.log.length, seen := x.seen.set a [] } := by
        refine J_of h1 (fun _ _ ht => ht) (fun b u hu hi => ?_) (fun _ _ _ _ hd => Or.inr (Or.inl hd)) (fun b u hu _ hs => ?_)
        · have hu' : u ∈ ((setAg x a (fun _ =>
          { (default : Agent) with
            st := .idle, boot := true, recorded := c.recordedWorkspaces,
            rhead := if c.recordedWorkspaces then some (x.git.tipOf (c.tbase t)) else none, rbase := c.tbase t })).agt b).believes := hu
          have hba : ¬ a = b := by rintro rfl; rw [hbel] at hu'; cases hu'
          refine ⟨hi.1, ?_⟩
          obtain ⟨i, i1, r⟩ := hi.2
          refine ⟨i, ?_, r⟩
          show (x.cursor.set a x.log.length).getD b 0 < i
          rw [getD_set, ite_eq_right (fun e => hba e.1)]; exact i1
        · have hu' : u ∈ ((setAg x a (fun _ =>
          { (default : Agent) with
            st := .idle, boot := true, recorded := c.recordedWorkspaces,
            rhead := if c.recordedWorkspaces then some (x.git.tipOf (c.tbase t)) else none, rbase := c.tbase t })).agt b).believes := hu
          have hba : ¬ a = b := by rintro rfl; rw [hbel] at hu'; cases hu'
          refine Or.inr (Or.inr (HS_of hs.1 rfl rfl hs.2 ⟨[], by simp⟩ ?_))
          show (x.cursor.set a x.log.length).getD b 0 = _
          rw [getD_set, ite_eq_right (fun e => hba e.1)]; rfl
      refine J_setTask (fun b hd => ?_) (fun b hb hs hi => ?_) h2
      rotate_left
      · exfalso
        have hb' : t ∈ ((setAg x a (fun _ =>
          { (default : Agent) with
            st := .idle, boot := true, recorded := c.recordedWorkspaces,
            rhead := if c.recordedWorkspaces then some (x.git.tipOf (c.tbase t)) else none, rbase := c.tbase t })).agt b).believes := hb
        have hba : ¬ (a = b ∧ b < x.ag.length) := by rintro ⟨rfl, _⟩; rw [hbel] at hb'; cases hb'
        have hag : (setAg x a (fun _ =>
          { (default : Agent) with
            st := .idle, boot := true, recorded := c.recordedWorkspaces,
            rhead := if c.recordedWorkspaces then some (x.git.tipOf (c.tbase t)) else none, rbase := c.tbase t })).agt b = x.agt b := by
          rw [agt_setAg, if_neg hba]
        have hcur : (x.cursor.set a x.log.length).getD b 0 = x.cur b := by
          rw [getD_set]; split
          · rename_i hh; obtain ⟨rfl, _⟩ := hh
            have : x.ag.length ≤ a := Nat.le_of_not_lt fun hl => hba ⟨rfl, hl⟩
            rw [agt_of_ge this] at hag; rw [hbel] at hb'; cases hb'
          · rfl
        have h2 : (x.cursor.set a x.log.length).getD b 0 < (x.tk t).stopMsg := hs.1.2.1
        have h1 : (x.tk t).stopTo = some b := hs.1.1
        have ha : active (x.agt b) = true := by
          cases e : active (x.agt b)
          · exact absurd ⟨by rw [← e, ← hag]; rfl, rel_of_stopRel hs.1⟩ hi
          · rfl
        unfold stopped at hst; rw [h1] at hst; simp [ha] at hst; omega
      have hd' : held (x.tk t) b = true ∨ (x.tk t).st = .dropped := hd
      rcases hd' with e | e
      · simp [held, hopn] at e
      · rw [hopn] at e; cases e
    · exact h
  · exact h

theorem J_tickOf {c : Cfg} {s : State} (hfix : c.release = .idle) (hi : InbInv c s) (h : J s) :
    InbInv c (tickOf c s) ∧ J (tickOf c s) :=
  tick_inv2 (fun x => InbInv c x ∧ J x)
    (fun x t hx => ⟨ii_reapTask hx.1, J_reapTask hfix (fun a => (hx.1.2.2 a).1) hx.2⟩)
    (fun x hx => ⟨ii_frame rfl rfl rfl rfl rfl hx.1, J_frame rfl rfl rfl rfl hx.2⟩)
    (fun x a hx => ⟨ii_endAgent hx.1, J_endAgent hx.2⟩)
    (fun x a pl hx => ⟨ii_post (ii_setAg (fun _ => Or.inl rfl) hx.1), J_post (J_setAg_same (fun _ => rfl) (fun _ => rfl) hx.2)⟩)
    (fun pl x t hx hopn hst => ⟨ii_spawnFor hx.1, J_spawnFor hopn hst hx.2⟩) ⟨hi, h⟩

theorem fc_owns {c : Cfg} {s : State} {a : Nat} (h : firstClaimed c s a ≠ 0) :
    (s.tk (firstClaimed c s a)).st = .claimed ∧ (s.tk (firstClaimed c s a)).owner = some a := by
  unfold firstClaimed at h ⊢
  cases hf : c.tasks.find? (ownsClaimed s a) with
  | none => simp [hf] at h
  | some t => simpa [ownsClaimed] using List.find?_some hf
theorem own_unique {s : State} {a t : Nat} (h : (s.tk t).owner = some a) : ∀ b, held (s.tk t) b = true → b = a := by
  intro b hb; simp [held, h] at hb; exact hb.1.symm
theorem J_claim {c : Cfg} {s : State} {a t : Nat} (hopn : (s.tk t).st = .opn) (hst : stopped s t = false) (h : J s) :
    J (takes c (claimed s a t) a t) := by
  refine J_takes ?_ (J_setTask (fun b hd => ?_) (fun b _ hs hi => absurd (not_HS_of_stopped hst hs hi) id) h)
  · unfold claimed; rw [tk_setTask_self (by rw [hopn]; simp)]; simp [held]
  · rcases hd with e | e
    · simp [held, hopn] at e
    · rw [hopn] at e; cases e
/-- a change of a task no belief rests on by its stop: one not open -/
theorem J_setTask_no {s : State} {t : Nat} {f : Task → Task} (hno : (s.tk t).st ≠ .opn)
    (hm : ∀ b, HD s b t → held (f (s.tk t)) b = true ∨ (f (s.tk t)).st = .dropped) (h : J s) : J (setTask s t f) :=
  J_setTask hm (fun _ _ hs _ => absurd hs.2 hno) h

theorem msg_app {s s' : State} {e : List Msg} (h : s'.log = s.log ++ e) {i : Nat} (hi : i ≤ s.log.length) : s'.msg i = s.msg i := by
  by_cases h0 : i = 0
  · simp [State.msg, h0]
  · simp [State.msg, h0, h, List.getD_eq_getElem?_getD, List.getElem?_append_left (show i - 1 < s.log.length by omega)]

/-- H2 with the fix (board #53): the ex-owner's belief now rests on the stop the task records -/
theorem J_released {s s' : State} {t o : Nat} (hag : s'.ag = s.ag) (hcs : s'.cursor = s.cursor)
    (hlog : s'.log = s.log ++ [⟨none, o, true, .released, t⟩]) (htk : ∀ u, u ≠ t → s'.tk u = s.tk u)
    (ht : (s'.tk t).st = .opn ∧ (s'.tk t).stopTo = some o ∧ (s'.tk t).stopMsg = s.log.length + 1)
    (ho : (s.tk t).owner = some o) (hst : (s.tk t).st = .claimed ∨ (s.tk t).st = .blocked)
    (hcur : ∀ b, s.cur b ≤ s.log.length) (h : J s) : J s' := by
  have hagt : ∀ b, s'.agt b = s.agt b := fun b => by simp [State.agt, hag]
  have hc : ∀ b, s'.cur b = s.cur b := fun b => by simp [State.cur, hcs]
  refine J_of h (fun b u hu => by rw [hagt] at hu; exact hu) (fun b u _ hi => ?_) (fun b u _ hi hd => ?_) (fun b u _ hi hsu => ?_)
  · refine ⟨by rw [hagt]; exact hi.1, ?_⟩
    obtain ⟨i, i1, i2, i3, i4, i5⟩ := hi.2
    refine ⟨i, by rw [hc]; exact i1, by rw [hlog]; simp; omega, ?_, ?_, ?_⟩
    · simp only [addressed, msg_app hlog i2] at i3 ⊢; exact i3
    · rw [msg_app hlog i2]; exact i4
    · rw [msg_app hlog i2]; exact i5
  · by_cases hut : u = t
    · subst hut
      rcases hd with e | e
      · have hb : b = o := by simp [held, ho] at e; exact e.1.symm
        subst hb
        have hm : s'.msg (s.log.length + 1) = ⟨none, b, true, .released, u⟩ := by
          simp [State.msg, hlog, List.getD_eq_getElem?_getD]
        right; right
        refine ⟨⟨ht.2.1, by rw [hc, ht.2.2]; have := hcur b; omega, by rw [ht.2.2, hlog]; simp, ?_, ?_, ?_⟩, ht.1⟩ <;>
          rw [ht.2.2] <;> simp [addressed, hm]
      · rcases hst with e2 | e2 <;> rw [e2] at e <;> cases e
    · right; left
      unfold HD; rw [htk u hut]; exact hd
  · by_cases hut : u = t
    · subst hut; rcases hst with e | e <;> exact absurd hsu.2 (by rw [e]; simp)
    · have e := htk u hut
      exact Or.inr (Or.inr (HS_of hsu.1 (by rw [e]) (by rw [e]) (by rw [e]; exact hsu.2) ⟨_, hlog⟩ (hc b)))

theorem J_of_reachable {c : Cfg} (hfix : c.release = .idle) (hhr : c.humanRelease = false ∨ c.stopFirst = true) {s : State}
    (h : Reachable c s) :
    J s := by
  refine reachable_induct ?_ ?_ h
  · have hb : ∀ a, ((init c).agt a).believes = [] := fun a => by
      simp only [State.agt, init, List.getD_eq_getElem?_getD, List.getElem?_map]; cases c.agents[a]? <;> rfl
    exact ⟨fun a t ht => (by rw [hb] at ht; cases ht), fun a b t ht => (by rw [hb] at ht; cases ht)⟩
  intro s s' act hr hs hstep
  have hI := inbInv_of_reachable hr
  have hP := pfx_of_reachable hr
  open_step hstep
  case awayOn => obtain ⟨_, rfl⟩ := hstep; exact hs
  case back => obtain ⟨_, rfl⟩ := hstep; exact hs
  case commsRead => obtain ⟨_, rfl⟩ := hstep; exact hs
  case hnudge => obtain ⟨_, rfl⟩ := hstep; exact hs
  case claim a t =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [claimable, startable, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hg
    exact J_claim (by simp_all) (by simp_all) hs
  case claimRead a t => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case claimWrite a =>
    obtain ⟨_, rfl⟩ := hstep
    split
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      exact J_setAg_same (fun _ => rfl) (fun _ => rfl)
        (J_frame (s := takes c (claimed s a (s.agt a).reading) a (s.agt a).reading) rfl rfl rfl rfl (J_claim hc.1.1 hc.2 hs))
    · exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case renew a t =>
    obtain ⟨hg, rfl⟩ := hstep; simp [ownsClaimed] at hg
    exact J_setTask_no (by rw [hg.2.1]; simp) (fun b hd => by rcases hd with e | e; exact Or.inl (by simpa [held] using e); exact Or.inr e) hs
  case block a t =>
    obtain ⟨hg, rfl⟩ := hstep
    simp [ownsClaimed] at hg
    exact J_setTask_no (s := logEv s (.block t)) (by simp [hg.2.1]) (fun b hd => by
      rcases hd with e | e
      · left; simp [held] at e ⊢; exact e.1
      · simp [hg.2.1] at e) hs
  case release a t =>
    obtain ⟨hg, rfl⟩ := hstep; simp [ownsClaimed] at hg
    exact J_giveup (own_unique hg.2.2) (by rw [hg.2.1]; simp) (by rw [hg.2.1]; simp) hs
  case done a t ev =>
    obtain ⟨hg, rfl⟩ := hstep; simp [ownsClaimed] at hg
    exact J_giveup (s := logEv s (.done t)) (own_unique hg.1.2.2) (by simp [hg.1.2.1]) (by simp [hg.1.2.1]) hs
  case dropOwn a t =>
    obtain ⟨hg, rfl⟩ := hstep; simp at hg
    exact J_giveup (fun b hb => held_unique hb hg.2) (held_not_dropped hg.2)
      (by have := hg.2; simp [held] at this; rcases this.2 with e | e <;> simp [e]) hs
  case lock a p => obtain ⟨_, rfl⟩ := hstep; exact J_frame (s := s) rfl rfl rfl rfl hs
  case unlock a p => obtain ⟨_, rfl⟩ := hstep; exact J_frame (s := s) rfl rfl rfl rfl hs
  case expireLock p => obtain ⟨_, rfl⟩ := hstep; exact J_frame (s := s) rfl rfl rfl rfl hs
  case postTo a b u => obtain ⟨_, rfl⟩ := hstep; exact J_post hs
  case readAll a => obtain ⟨_, rfl⟩ := hstep; exact J_deliver hs
  case stop a big =>
    obtain ⟨hg, rfl⟩ := hstep; simp [busy] at hg
    exact J_setAg_act (fun _ => rfl) (by simp [active, hg.1.1]) hs
  case wake a => obtain ⟨_, rfl⟩ := hstep; exact J_wake (fun _ => rfl) hs
  case wakeRead a => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case wakeWrite a =>
    obtain ⟨_, rfl⟩ := hstep
    refine J_setAg_same (fun _ => rfl) (fun _ => rfl) (J_wake (fun _ => rfl) ?_)
    split
    · exact hs
    · exact J_showAll (fun j hj => ((hI.2.2 a).2.1 j hj).2) hs
  case prompt a => obtain ⟨_, rfl⟩ := hstep; exact J_wake (fun _ => rfl) hs
  case boot a =>
    obtain ⟨_, rfl⟩ := hstep
    split
    · rename_i ht
      refine J_takes ?_ (J_wake (fun _ => rfl) hs)
      have := fc_owns (c := c) (s := s) (a := a) (by omega)
      have htk : ∀ (x : State) (u : Nat), x.task = s.task → x.tk u = s.tk u := fun x u e => by simp [State.tk, e]
      rw [htk _ _ (by simp)]
      simp [held, this.1, this.2]
    · exact J_wake (fun _ => rfl) hs
  case waiterGone a => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case age a => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case bgStart a => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case bgEnd a => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case die a => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case cool a => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case git a op => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case world w op => obtain ⟨_, rfl⟩ := hstep; exact hs
  case stale a => obtain ⟨_, rfl⟩ := hstep; exact J_setAg_same (fun _ => rfl) (fun _ => rfl) hs
  case nudge a => obtain ⟨_, rfl⟩ := hstep; exact J_post (J_setAg_same (fun _ => rfl) (fun _ => rfl) hs)
  case expire t =>
    obtain ⟨hg, rfl⟩ := hstep; simp at hg
    exact J_setTask_no (by rw [hg.1.1]; simp) (fun b hd => by rcases hd with e | e; exact Or.inl (by simpa [held] using e); exact Or.inr e) hs
  case leave a =>
    obtain ⟨_, rfl⟩ := hstep
    exact J_endAgent (J_setAg_same (fun _ => rfl) (fun _ => rfl) hs)
  case reapGone a =>
    obtain ⟨_, rfl⟩ := hstep
    exact J_endAgent (J_setAg_same (fun _ => rfl) (fun _ => rfl) hs)
  case endOther a f =>
    obtain ⟨_, rfl⟩ := hstep
    exact J_endAgent (J_setAg_same (fun _ => rfl) (fun _ => rfl) hs)
  case hcPrompt a =>
    obtain ⟨hg, rfl⟩ := hstep; simp [busy] at hg
    have hfc : (s.tk (firstClaimed c s a)).st ≠ .opn := by
      by_cases h0 : firstClaimed c s a = 0
      · rw [h0]; simp [State.tk]
      · rw [(fc_owns h0).1]; simp
    refine J_setTask_no (by simpa [State.tk] using hfc) (fun b hd => ?_) (J_setAg_act (fun _ => rfl) (by simp [active, hg.1]) hs)
    have hd' : held (s.tk (firstClaimed c s a)) b = true ∨ (s.tk (firstClaimed c s a)).st = .dropped := hd
    rcases hd' with e | e
    · left; simp [held] at e ⊢; exact e.1
    · exfalso
      by_cases h0 : firstClaimed c s a = 0
      · rw [h0] at e; simp [State.tk] at e
      · rw [(fc_owns h0).1] at e; cases e
  case hcClear a =>
    obtain ⟨_, rfl⟩ := hstep
    refine J_wake (fun _ => rfl) (J_tasks (s := s) rfl rfl rfl (fun b u _ _ hd => ?_) (fun b u _ _ hsu => ?_) hs)
    rotate_left
    · refine J_tasks_same (s := s) rfl rfl ?_ hsu
      rw [tk_map (s := s) (g := fun k =>
        if k.owner == some a && k.st == .blocked && k.hcq then { k with st := .claimed, hcq := false, lease := true } else k)
        (by simp) rfl]
      have := hsu.2; split
      · rename_i hh; simp [this] at hh
      · rfl
    unfold HD
    rw [tk_map (s := s) (g := fun k =>
      if k.owner == some a && k.st == .blocked && k.hcq then { k with st := .claimed, hcq := false, lease := true } else k)
      (by simp) rfl]
    split
    · rcases hd with e | e
      · left; simp [held] at e ⊢; exact e.1
      · rename_i hh; simp [e] at hh
    · exact hd
  case add deps =>
    obtain ⟨hg, rfl⟩ := hstep
    obtain ⟨n, h2, h3⟩ := hP
    have habs : (s.tk (nextTask s)).st = .absent := by
      have := h3 (nextTask s)
      rw [nextTask_eq h2 h3] at this ⊢
      by_cases e : (s.tk (n + 1)).st = .absent
      · exact e
      · have := this.mp e; omega
    exact J_setTask_no (by rw [habs]; simp) (fun b hd => by
      rcases hd with e | e
      · simp [held, habs] at e
      · rw [habs] at e; cases e) hs
  case after t deps =>
    obtain ⟨hg, rfl⟩ := hstep; simp at hg
    exact J_setTask (fun b hd => by rcases hd with e | e; exact Or.inl (by simpa [held] using e); exact Or.inr e)
      (fun _ _ _ _ => Or.inr (Or.inr ⟨rfl, rfl, hg.1⟩)) hs
  case unblock t =>
    split at hstep
    · rename_i o ho
      rw [when_eq_some] at hstep; obtain ⟨hg, rfl⟩ := hstep; simp at hg
      refine J_frame (s := post (setTask s t _) _) rfl rfl rfl rfl (J_post (J_setTask_no (by rw [hg]; simp) (fun b hd => ?_) hs))
      rcases hd with e | e
      · left; simp [held] at e ⊢; exact e.1
      · rw [hg] at e; cases e
    · cases hstep
  case drop t => obtain ⟨_, rfl⟩ := hstep; exact J_setTask (fun b _ => Or.inr rfl) (fun _ _ _ _ => Or.inr (Or.inl rfl)) hs
  case releaseOther t =>
    rcases hhr with hhr | hsf
    · simp [hhr] at hstep
    obtain ⟨hg, rfl⟩ := hstep
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg
    obtain ⟨⟨_, hsome⟩, hst⟩ := hg
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp hsome
    have hna : (s.tk t).st ≠ .absent := by rcases hst with e | e <;> simp [e]
    refine J_released (o := o) (by simp) (by simp) (by simp [post, ho]) (fun u hu => by simp only [State.tk, post_task]; exact tk_setTask_ne hu)
      ?_ ho hst (fun b => (hI.2.2 b).1) hs
    rw [show ∀ (x : State) m, (post x m).tk t = x.tk t from fun _ _ => by simp [State.tk], tk_setTask_self hna]; simp [hsf, ho]
  case tick => obtain ⟨_, rfl⟩ := hstep; exact (J_tickOf hfix hI hs).2

/-- S1. With PR #111 (reap reopens a lapsed claim only when its owner is idle), and H2 (`humanRelease`, the user's
release of another's task) off or with its fix (`stopFirst`, board #53: no one takes the task while its ex-owner is at
work and hasn't read the stop; without it the release breaks S1, `not_S1_humanRelease`), no task has two agents at work
on it. -/
theorem oneWorker_of_reachable {c : Cfg} (hfix : c.release = .idle) (hhr : c.humanRelease = false ∨ c.stopFirst = true) {s : State}
    (h : Reachable c s) : oneWorker s = true := by
  have hJ := J_of_reachable hfix hhr h
  simp only [oneWorker, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq]
  intro a _ b _
  by_cases hab : a = b
  · exact Or.inl hab
  right
  cases ha : active (s.agt a) <;> cases hb : active (s.agt b) <;> simp
  intro t hta htb
  exact hab (hJ.2 a b t hta htb (fun hi => by have := hi.1; rw [ha] at this; cases this)
    (fun hi => by have := hi.1; rw [hb] at this; cases this))

end Swarm
