import SwarmModel.Fair

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

/-- What every reachable state satisfies that L1 needs: there are `nagents` slots, and only a big agent is cold. -/
def Inv (c : Cfg) (s : State) : Prop := s.ag.length = c.nagents ∧ ∀ b, (s.agt b).cold = true → (s.agt b).big = true

theorem inv_init (c : Cfg) : Inv c (init c) := by
  refine ⟨by simp [init, Cfg.agents], fun b hb => ?_⟩
  exfalso
  revert hb
  simp only [State.agt, init, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases c.agents[b]? <;> simp <;> rfl


-- ---------- watchd's tick fills a free slot when no agent is reusable ----------

theorem live_count_modify (l : List Agent) (i : Nat) (f : Agent → Agent) (hf : ∀ g, g.live = true → (f g).live = true) :
    (l.filter (·.live)).length ≤ ((l.modify i f).filter (·.live)).length := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero =>
      have e : (x :: xs).modify 0 f = f x :: xs := by simp
      rw [e]
      by_cases h : x.live = true
      · simp [List.filter_cons, h, hf x h]
      · by_cases h2 : (f x).live = true <;> simp [List.filter_cons, h, h2]
    | succ i =>
      have e : (x :: xs).modify (i+1) f = x :: xs.modify i f := by simp
      rw [e]
      have := ih i
      simp only [List.filter_cons]
      split <;> simp <;> omega

theorem spawnFor_members {c : Cfg} {pl : List Nat} {x : State} {t : Nat} : members x ≤ members (spawnFor c pl x t) := by
  unfold spawnFor; split
  · split
    · simp only [members, claimed_ag, setAg]
      exact live_count_modify _ _ _ (by intro g _; simp [Agent.live])
    · exact Nat.le_refl _
  · exact Nat.le_refl _

theorem members_full {c : Cfg} {x : State} (hl : x.ag.length = c.nagents) (hroster : c.roster ≤ c.nagents)
    (h : c.agents.find? (fun a => !(x.agt a).live) = none) : c.roster ≤ members x := by
  have hall : ∀ g ∈ x.ag, g.live = true := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have := List.find?_eq_none.mp h i (by simp [Cfg.agents]; omega)
    simpa [State.agt, List.getD_eq_getElem?_getD, hi] using this
  have : members x = x.ag.length := by
    unfold members; rw [List.filter_eq_self.mpr (fun g hg => hall g hg)]
  omega

theorem spawnFor_len {c : Cfg} {pl : List Nat} {x : State} {t : Nat} : (spawnFor c pl x t).ag.length = x.ag.length := by
  unfold spawnFor; split
  · split <;> simp [setAg]
  · rfl

theorem spawn_keep {c : Cfg} {pl : List Nat} {t : Nat} : ∀ {suf : List Nat}, t ∉ suf → ∀ {y : State},
    ((y.tk t).st ≠ .opn ∨ c.roster ≤ members y) → (((suf.foldl (spawnFor c pl) y).tk t).st ≠ .opn ∨ c.roster ≤ members (suf.foldl (spawnFor c pl) y))
  | [], _, y, h => h
  | u :: us, hn, y, h => by
    simp only [List.foldl_cons]
    have hu : u ≠ t := fun e => hn (e ▸ List.mem_cons_self ..)
    refine spawn_keep (fun e => hn (List.mem_cons_of_mem _ e)) ?_
    rw [spawnFor_tk_ne (Ne.symm hu)]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Nat.le_trans h spawnFor_members)

theorem claimed_not_opn (s : State) (a t : Nat) : ((claimed s a t).tk t).st ≠ .opn := by
  unfold claimed
  by_cases h : (s.tk t).st = .absent
  · rcases tk_setTask_or s t t (fun k => { k with st := .claimed, owner := some a, lease := true, reaped := if k.reaped == some a then k.reaped else none }) with e | ⟨_, e⟩
    · rw [e, h]; decide
    · rw [e]; simp
  · rw [tk_setTask_self h]; simp

/-- a spawn pass over the tasks leaves the task either taken or the roster full -/
theorem spawn_pass {c : Cfg} {pl : List Nat} {t : Nat} (hroster : c.roster ≤ c.nagents) (ht : t ∈ c.tasks)
    (hp : pl.contains t = true) {x : State} (hl : x.ag.length = c.nagents) :
    ((c.tasks.foldl (spawnFor c pl) x).tk t).st ≠ .opn ∨ c.roster ≤ members (c.tasks.foldl (spawnFor c pl) x) := by
  have hnd : c.tasks.Nodup := List.nodup_range' (s := 1) (n := c.ntasks)
  obtain ⟨pre, suf, hsplit⟩ := List.append_of_mem ht
  rw [hsplit] at hnd ⊢
  rw [List.foldl_append, List.foldl_cons]
  have hnot : t ∉ suf := by
    have := List.nodup_append.mp hnd
    have := (List.nodup_cons.mp this.2.1).1; exact this
  have hnot' : t ∉ pre := by
    have := List.nodup_append.mp hnd
    exact fun h => this.2.2 t h t (List.mem_cons_self ..) rfl
  have hl1 : (pre.foldl (spawnFor c pl) x).ag.length = c.nagents :=
    foldl_inv (spawnFor c pl) (fun y : State => y.ag.length = c.nagents) pre x hl (fun y u hy => by rw [spawnFor_len]; exact hy)
  generalize pre.foldl (spawnFor c pl) x = x1 at hl1 ⊢
  have key : ((spawnFor c pl x1 t).tk t).st ≠ .opn ∨ c.roster ≤ members (spawnFor c pl x1 t) := by
    by_cases hm : members x1 < c.roster
    · left
      have hn : ∃ a, nextAgent c x1 = some a := by
        cases hh : nextAgent c x1 with
        | some a => exact ⟨a, rfl⟩
        | none => exact absurd (members_full hl1 hroster hh) (by omega)
      obtain ⟨a, ha⟩ := hn
      unfold spawnFor; rw [ha]; simp only [hp, hm, decide_true, Bool.true_and, if_true]
      exact claimed_not_opn _ _ _
    · right
      exact Nat.le_trans (Nat.le_of_not_lt hm) spawnFor_members
  exact spawn_keep hnot key

/-- no reusable agent: the tick fills a free slot with the task, or the roster fills -/
theorem lifecycle_fills {c : Cfg} {z : State} {t : Nat} (hroster : c.roster ≤ c.nagents) (hl : z.ag.length = c.nagents)
    (ht : t ∈ c.tasks) (hst : claimable z t = true) (hnr : ∀ a ∈ c.agents, reusable c z a = false) :
    ¬ (startable (lifecycle c z) t = true ∧ members (lifecycle c z) < c.roster) := by
  have hany : c.agents.any (reusable c z) = false := by
    simp only [List.any_eq_false]; intro a ha; simp [hnr a ha]
  have hp : (pool c z).contains t = true := by
    simp only [pool, Cfg.tasks, List.contains_iff_mem, List.mem_filter] at ht ⊢; exact ⟨ht, hst⟩
  unfold lifecycle
  simp only [hany, Bool.false_eq_true, if_false]
  have h1 := foldl_inv (fun x a => if finished c z a && !reusable c z a then endAgent x a else x)
    (fun y : State => y.ag.length = c.nagents) c.agents z hl (fun y a hy => by split <;> simp_all [endAgent])
  have h2 := foldl_inv (fun x a =>
    if reusable c z a && !(pool c z).all (x.agt a).told.contains then
      post (setAg x a fun g => { g with told := pool c z ++ g.told }) ⟨none, a, false, .digest, 0⟩
    else x) (fun y : State => y.ag.length = c.nagents) c.agents _ h1 (fun y a hy => by split <;> simp_all [setAg])
  rcases spawn_pass hroster ht hp h2 with h | h
  · intro ⟨h3, _⟩
    simp [startable] at h3; simp_all
  · intro ⟨_, h3⟩; omega

-- ---------- reap keeps a startable task startable, and a claimable one claimable ----------

theorem reapTask_tk_unclaimed {c : Cfg} {x : State} {v u : Nat} (h : (x.tk u).st ≠ .claimed) : (reapTask c x v).tk u = x.tk u := by
  by_cases hu : u = v
  · subst hu
    unfold reapTask; simp only []
    split
    · split
      · exfalso; simp_all
      · rfl
    · rfl
  · exact reapTask_tk_ne hu

theorem startable_reap {c : Cfg} {s : State} {t : Nat} (h : startable s t = true) :
    startable (reapLocks (reapTasks c s)) t = true := by
  simp only [startable, depsDone, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  have key : ∀ (l : List Nat) (x : State), (∀ u, (x.tk u).st = .opn ∨ (x.tk u).st = .done → ((l.foldl (reapTask c) x).tk u) = x.tk u) := by
    intro l
    induction l with
    | nil => intro x u _; rfl
    | cons v vs ih =>
      intro x u hu
      simp only [List.foldl_cons]
      have e1 : (reapTask c x v).tk u = x.tk u := reapTask_tk_unclaimed (by rcases hu with h | h <;> simp [h])
      rw [ih (reapTask c x v) u (by rw [e1]; exact hu), e1]
  have e : ∀ u, (s.tk u).st = .opn ∨ (s.tk u).st = .done → (reapLocks (reapTasks c s)).tk u = s.tk u := by
    intro u hu
    simp only [reapTasks]
    rw [tk_of_task (reapLocks_task _)]
    exact key c.tasks s u hu
  refine ⟨?_, fun d hd => ?_⟩
  · rw [e t (Or.inl h1), h1]
  · have hd' := h2 d (by rw [e t (Or.inl h1)] at hd; exact hd)
    rw [e d (Or.inr hd'), hd']

-- ---------- a ready agent stays ready until it gets back to work ----------

theorem startable_of_claimable {s : State} {t : Nat} (h : claimable s t = true) : startable s t = true := by
  simp only [claimable, Bool.and_eq_true] at h; exact h.1
theorem claimable_reap {c : Cfg} {s : State} {t : Nat} (h : claimable s t = true) :
    claimable (reapLocks (reapTasks c s)) t = true := by
  have hsp1 : SP s (reapTasks c s) := by
    unfold reapTasks; exact foldl_inv (reapTask c) (SP s) c.tasks s (sp_refl s) (fun x v h => sp_trans h (sp_reapTask c x v))
  have hsp : SP s (reapLocks (reapTasks c s)) := sp_trans hsp1 (sp_tasks (fun u => ⟨rfl, rfl⟩) (fun b h => h) rfl)
  simp only [claimable, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
  exact ⟨startable_reap h.1, sp_stopped hsp h.2⟩

/-- idle, its waiter armed, a small context, and an unread message the waiter wakes it on -/
def Ready (s : State) (a : Nat) : Prop :=
  (s.agt a).st = .idle ∧ (s.agt a).waiter = true ∧ (s.agt a).big = false ∧ (s.agt a).cold = false ∧ unread s a ≠ []
/-- back at work with an empty inbox and a small context: `claim` is enabled for it -/
def Exit (s : State) (a : Nat) : Prop := (s.agt a).st = .working ∧ unread s a = [] ∧ (s.agt a).big = false

theorem unread_congr {s s' : State} (hl : s'.log = s.log) (hc : s'.cursor = s.cursor) (a : Nat) : unread s' a = unread s a := by
  simp only [unread, State.cur, hl, hc]
  congr 1
  funext i
  exact addressed_congr hl a i

theorem ready_of_log {s s' : State} {a : Nat} (hag : s'.agt a = s.agt a) (hl : s'.log = s.log) (hc : s'.cursor = s.cursor)
    (h : Ready s a) : Ready s' a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hag]; exact h1, by rw [hag]; exact h2, by rw [hag]; exact h3, by rw [hag]; exact h4, by rw [unread_congr hl hc]; exact h5⟩

@[simp] theorem deliver_waiter (s : State) (a b : Nat) : ((deliver s a).agt b).waiter = (s.agt b).waiter := by
  obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]
@[simp] theorem deliver_big (s : State) (a b : Nat) : ((deliver s a).agt b).big = (s.agt b).big := by
  obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]
@[simp] theorem deliver_cold (s : State) (a b : Nat) : ((deliver s a).agt b).cold = (s.agt b).cold := by
  obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]
@[simp] theorem takes_waiter (c : Cfg) (s : State) (a t b : Nat) : ((takes c s a t).agt b).waiter = (s.agt b).waiter := by
  obtain ⟨bl, e⟩ := takes_agt c s a t b; rw [e]
@[simp] theorem takes_big (c : Cfg) (s : State) (a t b : Nat) : ((takes c s a t).agt b).big = (s.agt b).big := by
  obtain ⟨bl, e⟩ := takes_agt c s a t b; rw [e]
@[simp] theorem takes_cold (c : Cfg) (s : State) (a t b : Nat) : ((takes c s a t).agt b).cold = (s.agt b).cold := by
  obtain ⟨bl, e⟩ := takes_agt c s a t b; rw [e]

/-- the log only grew and a's cursor stayed: an unread message is still unread -/
def Ext (s x : State) (a : Nat) : Prop := (∃ extra, x.log = s.log ++ extra) ∧ x.cur a = s.cur a

theorem ext_refl (s : State) (a : Nat) : Ext s s a := ⟨⟨[], by simp⟩, rfl⟩
theorem ext_trans {s x y : State} {a : Nat} (h1 : Ext s x a) (h2 : Ext x y a) : Ext s y a := by
  obtain ⟨⟨e1, p1⟩, q1⟩ := h1; obtain ⟨⟨e2, p2⟩, q2⟩ := h2
  exact ⟨⟨e1 ++ e2, by rw [p2, p1]; simp⟩, by rw [q2, q1]⟩

theorem msg_ext {s x : State} {e : List Msg} (h : x.log = s.log ++ e) {i : Nat} (hi : i ≤ s.log.length) : x.msg i = s.msg i := by
  by_cases h0 : i = 0
  · simp [State.msg, h0]
  · have : i - 1 < s.log.length := by omega
    simp [State.msg, h, h0, List.getD_eq_getElem?_getD, List.getElem?_append_left this]

theorem unread_ext {s x : State} {a : Nat} (h : Ext s x a) (hu : unread s a ≠ []) : unread x a ≠ [] := by
  obtain ⟨⟨e, p⟩, q⟩ := h
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hu
  rw [mem_unread] at hi
  obtain ⟨h1, h2, h3⟩ := hi
  refine fun h0 => ?_
  have : i ∈ unread x a := by
    rw [mem_unread]
    refine ⟨by rw [q]; exact h1, by rw [p, List.length_append]; omega, ?_⟩
    simp only [addressed] at h3 ⊢
    rw [msg_ext p h2]; exact h3
  rw [h0] at this; cases this

theorem ext_post (s : State) (m : Msg) (a : Nat) : Ext s (post s m) a := ⟨⟨[m], by simp [post]⟩, rfl⟩
theorem ext_frame {s x : State} (hl : x.log = s.log) (hc : x.cursor = s.cursor) (a : Nat) : Ext s x a :=
  ⟨⟨[], by simp [hl]⟩, by simp [State.cur, hc]⟩

theorem deliver_cur_ne (s : State) {a b : Nat} (hb : b ≠ a) : (deliver s b).cur a = s.cur a := by
  unfold deliver; rw [showAll_cur]; simp [Ne.symm hb]

theorem ext_deliver_ne (s : State) {a b : Nat} (hb : b ≠ a) : Ext s (deliver s b) a := ⟨⟨[], by simp⟩, deliver_cur_ne s hb⟩

theorem unread_deliver_self {s : State} {a : Nat} (hlen : a < s.cursor.length) : unread (deliver s a) a = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  rw [mem_unread] at hi
  obtain ⟨h1, h2, h3⟩ := hi
  have hcur : (deliver s a).cur a = (unread s a).foldl max (s.cur a) := by
    unfold deliver; rw [showAll_cur]; simp [hlen]
  rw [hcur] at h1
  have : i ∈ unread s a := by
    rw [mem_unread]
    have := (foldl_max (unread s a) (s.cur a)).1
    refine ⟨by omega, by simpa using h2, ?_⟩
    simpa [addressed, State.msg] using h3
  have := (foldl_max (unread s a) (s.cur a)).2.1 i ‹_›
  omega

theorem ready_of_fields {s s' : State} {a : Nat} (h : Ready s a) (h1 : (s'.agt a).st = (s.agt a).st)
    (h2 : (s'.agt a).waiter = (s.agt a).waiter) (h3 : (s'.agt a).big = (s.agt a).big) (h4 : (s'.agt a).cold = (s.agt a).cold)
    (h5 : unread s' a ≠ []) : Ready s' a := by
  obtain ⟨g1, g2, g3, g4, _⟩ := h
  exact ⟨by rw [h1]; exact g1, by rw [h2]; exact g2, by rw [h3]; exact g3, by rw [h4]; exact g4, h5⟩

theorem ready_frame {s x : State} {a : Nat} (h : Ready s a) (hag : x.ag = s.ag) (hl : x.log = s.log) (hc : x.cursor = s.cursor) :
    Ready x a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [agt_of_ag hag]; exact h1, by rw [agt_of_ag hag]; exact h2, by rw [agt_of_ag hag]; exact h3,
    by rw [agt_of_ag hag]; exact h4, by rw [unread_congr hl hc]; exact h5⟩

theorem ready_setAg_ne {x : State} {a b : Nat} {f : Agent → Agent} (hb : b ≠ a) (h : Ready x a) : Ready (setAg x b f) a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : (setAg x b f).agt a = x.agt a := by rw [agt_setAg]; simp [hb]
  exact ⟨by rw [e]; exact h1, by rw [e]; exact h2, by rw [e]; exact h3, by rw [e]; exact h4, by rw [unread_congr (setAg_log ..) (setAg_cursor ..)]; exact h5⟩

theorem ready_deliver_ne {x : State} {a b : Nat} (hb : b ≠ a) (h : Ready x a) : Ready (deliver x b) a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4, unread_ext (ext_deliver_ne x hb) h5⟩

theorem ready_post {x : State} {a : Nat} {m : Msg} (h : Ready x a) : Ready (post x m) a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4, unread_ext (ext_post x m a) h5⟩

theorem ready_takes {c : Cfg} {x : State} {a b t : Nat} (h : Ready x a) : Ready (takes c x b t) a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4, by rwa [unread_congr (takes_log ..) (takes_cursor ..)]⟩

theorem exit_awake {x : State} {a : Nat} {f : Agent → Agent} (hf : ∀ g, (f g).st = .working ∧ (f g).big = g.big)
    (hcl : a < x.cursor.length) (hlen : a < x.ag.length) (hb : (x.agt a).big = false) : Exit (setAg (deliver x a) a f) a := by
  refine ⟨?_, ?_, ?_⟩
  · rw [agt_setAg]; simp [hlen]; exact (hf _).1
  · rw [unread_congr (setAg_log ..) (setAg_cursor ..)]; exact unread_deliver_self hcl
  · rw [agt_setAg]; simp [hlen]; rw [(hf _).2]; simpa using hb

theorem exit_takes {c : Cfg} {x : State} {a b t : Nat} (h : Exit x a) : Exit (takes c x b t) a := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simpa using h1, by rwa [unread_congr (takes_log ..) (takes_cursor ..)], by simpa using h3⟩

-- ---------- the tick keeps a ready agent ----------

def Qa (z x : State) (a : Nat) : Prop :=
  (x.agt a).st = .idle ∧ (x.agt a).waiter = true ∧ (x.agt a).big = false ∧ (x.agt a).cold = false ∧ Ext z x a

theorem spawnFor_cur_ne {c : Cfg} {pl : List Nat} {x : State} {u a : Nat} (h : (x.agt a).live = true) :
    (spawnFor c pl x u).cur a = x.cur a := by
  unfold spawnFor; split
  · rename_i a' hna
    split
    · have := nextAgent_not_live hna
      have hne : a' ≠ a := by rintro rfl; simp_all
      simp only [claimed_cursor, State.cur, getD_set]
      simp [hne]
    · rfl
  · rfl

theorem qa_spawn {c : Cfg} {pl : List Nat} {z x : State} {u a : Nat} (h : Qa z x a) : Qa z (spawnFor c pl x u) a := by
  obtain ⟨h1, h2, h3, h4, ⟨⟨e, pe⟩, q⟩⟩ := h
  have hl : (x.agt a).live = true := by simp [Agent.live, h1]
  rcases spawnFor_agt c pl x u a with e1 | ⟨hn, _⟩
  · exact ⟨by rw [e1]; exact h1, by rw [e1]; exact h2, by rw [e1]; exact h3, by rw [e1]; exact h4,
      ⟨⟨e, by rw [spawnFor_log]; exact pe⟩, by rw [spawnFor_cur_ne hl]; exact q⟩⟩
  · have := nextAgent_not_live hn; simp_all

theorem qa_end {z x : State} {b a : Nat} (hb : b ≠ a) (h : Qa z x a) : Qa z (endAgent x b) a := by
  obtain ⟨h1, h2, h3, h4, ⟨⟨e, pe⟩, q⟩⟩ := h
  have ea : (endAgent x b).agt a = x.agt a := by rw [endAgent_agt]; simp [hb]
  refine ⟨by rw [ea]; exact h1, by rw [ea]; exact h2, by rw [ea]; exact h3, by rw [ea]; exact h4, ⟨⟨e, by simpa using pe⟩, by simpa [State.cur] using q⟩⟩

theorem qa_told {z x : State} {b a : Nat} {f : Agent → Agent} {m : Msg}
    (hf : ∀ g, (f g).st = g.st ∧ (f g).waiter = g.waiter ∧ (f g).big = g.big ∧ (f g).cold = g.cold) (h : Qa z x a) :
    Qa z (post (setAg x b f) m) a := by
  obtain ⟨h1, h2, h3, h4, ⟨⟨e, pe⟩, q⟩⟩ := h
  have ea : ∀ P : Agent → Prop, P (x.agt a) → (∀ g, P g → P (f g)) → P ((post (setAg x b f) m).agt a) := by
    intro P hP hPf
    simp only [post_agt, agt_setAg]
    split
    · exact hPf _ hP
    · exact hP
  refine ⟨ea (·.st = .idle) h1 (fun g hg => by rw [(hf g).1]; exact hg), ea (·.waiter = true) h2 (fun g hg => by rw [(hf g).2.1]; exact hg),
    ea (·.big = false) h3 (fun g hg => by rw [(hf g).2.2.1]; exact hg), ea (·.cold = false) h4 (fun g hg => by rw [(hf g).2.2.2]; exact hg),
    ⟨⟨e ++ [m], by simp [post, pe]⟩, by simpa [State.cur] using q⟩⟩

theorem reapTask_ext (c : Cfg) (x : State) (v : Nat) : ∃ e, (reapTask c x v).log = x.log ++ e := by
  unfold reapTask; simp only []; split
  · split
    · exact ⟨_, by simp only [post, setTask_log]; rfl⟩
    · exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩

/-- the log only grows: every step appends to it -/
theorem step_log {c : Cfg} {s s' : State} {act : Action} (hs : step c s act = some s') : ∃ e, s'.log = s.log ++ e := by
  open_step hs
  case tick =>
    obtain ⟨_, rfl⟩ := hs
    exact tick_inv (fun x => ∃ e, x.log = s.log ++ e)
      (fun x t ⟨e, he⟩ => let ⟨e2, h2⟩ := reapTask_ext c x t; ⟨e ++ e2, by rw [h2, he]; simp⟩)
      (fun x h => by simpa using h) (fun x a h => by simpa using h)
      (fun x a pl ⟨e, he⟩ => ⟨e ++ [⟨none, a, false, .digest, 0⟩], by simp [post, he]⟩) (fun pl x t h _ => by simpa using h)
      ⟨[], by simp⟩
  case unblock t =>
    split at hs
    · rename_i o _
      rw [when_eq_some] at hs; obtain ⟨_, rfl⟩ := hs; exact ⟨[⟨none, o, false, .answer, t⟩], by simp [post]⟩
    · cases hs
  case postTo a b u => obtain ⟨_, rfl⟩ := hs; exact ⟨[⟨some a, b, u, .dm, 0⟩], by simp [post]⟩
  case nudge a => obtain ⟨_, rfl⟩ := hs; exact ⟨[⟨none, a, true, .nudge, 0⟩], by simp [post]⟩
  case releaseOther t => obtain ⟨_, rfl⟩ := hs; exact ⟨[⟨none, (s.tk t).owner.getD 0, true, .released, t⟩], by simp [post]⟩
  all_goals obtain ⟨_, rfl⟩ := hs
  all_goals ((repeat' split) <;> first
    | (refine ⟨[], ?_⟩; simp [unbelieve, awake]; done)
    | (refine ⟨[_], ?_⟩; simp [post, unbelieve, awake]; done))

theorem reapTasks_ext (c : Cfg) (s : State) (a : Nat) : Ext s (reapLocks (reapTasks c s)) a := by
  have h : ∃ extra, (reapTasks c s).log = s.log ++ extra := by
    unfold reapTasks
    exact foldl_inv (reapTask c) (fun x : State => ∃ extra, x.log = s.log ++ extra) c.tasks s ⟨[], by simp⟩ (fun x v ⟨e, pe⟩ => by
      obtain ⟨e', pe'⟩ := reapTask_ext c x v
      exact ⟨e ++ e', by rw [pe', pe, List.append_assoc]⟩)
  obtain ⟨e, pe⟩ := h
  exact ⟨⟨e, by simpa using pe⟩, by simp [State.cur]⟩

theorem lifecycle_qa {c : Cfg} {z : State} {a : Nat} (hreus : finished c z a = true → reusable c z a = true)
    (h1 : (z.agt a).st = .idle) (h2 : (z.agt a).waiter = true) (h3 : (z.agt a).big = false) (h4 : (z.agt a).cold = false) :
    Qa z (lifecycle c z) a := by
  have hQ0 : Qa z z a := ⟨h1, h2, h3, h4, ext_refl z a⟩
  unfold lifecycle; simp only []
  have hend := foldl_inv (fun x b => if finished c z b && !reusable c z b then endAgent x b else x) (fun y : State => Qa z y a) c.agents z hQ0 (by
    intro y b hy
    split
    · rename_i hc
      by_cases hb : b = a
      · subst hb; simp [hreus] at hc; cases hf : finished c z b <;> simp_all
      · exact qa_end hb hy
    · exact hy)
  have hdig := foldl_inv (fun x b =>
    if reusable c z b && !(pool c z).all (x.agt b).told.contains then
      post (setAg x b fun g => { g with told := pool c z ++ g.told }) ⟨none, b, false, .digest, 0⟩
    else x) (fun y : State => Qa z y a) c.agents _ hend (by
    intro y b hy
    split
    · exact qa_told (fun g => ⟨rfl, rfl, rfl, rfl⟩) hy
    · exact hy)
  split
  · exact hdig
  · exact foldl_inv _ (fun y : State => Qa z y a) _ _ hdig (fun y u hy => qa_spawn hy)

theorem lifecycle_ready {c : Cfg} {z : State} {a t : Nat} (hp : c.passedOver = true) (hwa : c.waiterAlive = true)
    (ht : t ∈ c.tasks) (hst : claimable z t = true) (hR : Ready z a) : Ready (lifecycle c z) a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  have hpool : (pool c z).isEmpty = false := by
    have : t ∈ pool c z := by simp only [pool, Cfg.tasks, List.mem_filter] at ht ⊢; exact ⟨ht, hst⟩
    cases hh : (pool c z).isEmpty
    · rfl
    · simp [List.isEmpty_iff] at hh; simp [hh] at this
  have hu : (unread z a).isEmpty = false := by simpa using h5
  have hreus : finished c z a = true → reusable c z a = true := by
    intro hf
    simp [reusable, hf, h3, hpool, hu, h2]
  obtain ⟨q1, q2, q3, q4, qe⟩ := lifecycle_qa hreus h1 h2 h3 h4
  exact ⟨q1, q2, q3, q4, unread_ext qe h5⟩

-- ---------- a reusable agent has something to read after the tick ----------

def digStep (c : Cfg) (z : State) (x : State) (b : Nat) : State :=
  if reusable c z b && !(pool c z).all (x.agt b).told.contains then
    post (setAg x b fun g => { g with told := pool c z ++ g.told }) ⟨none, b, false, .digest, 0⟩
  else x

theorem digStep_agt_ne {c : Cfg} {z x : State} {a b : Nat} (hb : b ≠ a) : (digStep c z x b).agt a = x.agt a := by
  unfold digStep; split
  · simp only [post_agt, agt_setAg]; simp [hb]
  · rfl

theorem dig_log (c : Cfg) (z : State) : ∀ (l : List Nat) (x : State), ∃ e, (l.foldl (digStep c z) x).log = x.log ++ e
  | [], x => ⟨[], by simp⟩
  | b :: bs, x => by
    obtain ⟨e, pe⟩ := dig_log c z bs (digStep c z x b)
    have : ∃ e', (digStep c z x b).log = x.log ++ e' := by
      unfold digStep; split
      · exact ⟨[⟨none, b, false, .digest, 0⟩], by simp [post]⟩
      · exact ⟨[], by simp⟩
    obtain ⟨e', pe'⟩ := this
    exact ⟨e' ++ e, by simp only [List.foldl_cons]; rw [pe, pe', List.append_assoc]⟩

theorem dig_msg {c : Cfg} {z : State} {a : Nat} (hr : reusable c z a = true) : ∀ (l : List Nat) (x : State), l.Nodup → a ∈ l →
    (pool c z).all (x.agt a).told.contains = false →
    ∃ e m, (l.foldl (digStep c z) x).log = x.log ++ e ∧ m ∈ e ∧ m.to = a ∧ m.frm = none
  | [], x, _, h, _ => by cases h
  | b :: bs, x, hn, hm, ht => by
    simp only [List.foldl_cons]
    by_cases hb : b = a
    · subst hb
      have hc : (reusable c z b && !(pool c z).all (x.agt b).told.contains) = true := by simp [hr, ht]
      obtain ⟨e, pe⟩ := dig_log c z bs (digStep c z x b)
      refine ⟨⟨none, b, false, .digest, 0⟩ :: e, ⟨none, b, false, .digest, 0⟩, ?_, by simp, rfl, rfl⟩
      rw [pe]; unfold digStep; rw [if_pos hc]; simp [post]
    · have hm' : a ∈ bs := by
        rcases List.mem_cons.mp hm with e | e
        · exact absurd e.symm hb
        · exact e
      obtain ⟨e, m, pe, hme, h1, h2⟩ := dig_msg hr bs (digStep c z x b) (List.nodup_cons.mp hn).2 hm' (by rw [digStep_agt_ne hb]; exact ht)
      have : ∃ e', (digStep c z x b).log = x.log ++ e' := by
        unfold digStep; split
        · exact ⟨[⟨none, b, false, .digest, 0⟩], by simp [post]⟩
        · exact ⟨[], by simp⟩
      obtain ⟨e', pe'⟩ := this
      exact ⟨e' ++ e, m, by rw [pe, pe', List.append_assoc], by simp [hme], h1, h2⟩

def endFold (c : Cfg) (z : State) : State :=
  c.agents.foldl (fun x b => if finished c z b && !reusable c z b then endAgent x b else x) z

theorem lifecycle_eq (c : Cfg) (z : State) : lifecycle c z =
    (if c.agents.any (reusable c z) then c.agents.foldl (digStep c z) (endFold c z)
     else c.tasks.foldl (spawnFor c (pool c z)) (c.agents.foldl (digStep c z) (endFold c z))) := rfl

theorem lifecycle_log_dig (c : Cfg) (z : State) :
    (lifecycle c z).log = (c.agents.foldl (digStep c z) (endFold c z)).log := by
  rw [lifecycle_eq]; split
  · rfl
  · exact foldl_inv (spawnFor c (pool c z)) (fun y : State => y.log = (c.agents.foldl (digStep c z) (endFold c z)).log) _ _ rfl
      (fun y u hy => by rw [spawnFor_log]; exact hy)

theorem endFold_a {c : Cfg} {z : State} {a : Nat} (hreus : finished c z a = true → reusable c z a = true) :
    (endFold c z).agt a = z.agt a ∧ (endFold c z).log = z.log := by
  have := foldl_inv (fun x b => if finished c z b && !reusable c z b then endAgent x b else x)
    (fun y : State => y.agt a = z.agt a ∧ y.log = z.log) c.agents z ⟨rfl, rfl⟩ (by
      intro y b hy
      split
      · rename_i hc
        by_cases hb : b = a
        · subst hb; simp [hreus] at hc; cases hf : finished c z b <;> simp_all
        · refine ⟨by rw [endAgent_agt]; simp [hb]; exact hy.1, by simpa using hy.2⟩
      · exact hy)
  exact this

theorem lifecycle_unread {c : Cfg} {z : State} {a : Nat} (hp : c.passedOver = true) (ha : a ∈ c.agents) (hr : reusable c z a = true)
    (hcur : z.cur a ≤ z.log.length) (h1 : (z.agt a).st = .idle) (h2 : (z.agt a).waiter = true)
    (h3 : (z.agt a).big = false) (h4 : (z.agt a).cold = false) : unread (lifecycle c z) a ≠ [] := by
  have hreus : finished c z a = true → reusable c z a = true := fun _ => hr
  obtain ⟨q1, q2, q3, q4, qe⟩ := lifecycle_qa hreus h1 h2 h3 h4
  by_cases hu : unread z a = []
  · have hall : (pool c z).all (z.agt a).told.contains = false := by
      simp only [reusable, Bool.and_eq_true, Bool.not_eq_true'] at hr
      obtain ⟨⟨_, hnot⟩, _⟩ := hr
      cases hh : (pool c z).all (z.agt a).told.contains
      · rfl
      · exfalso; simp [hp, hh, hu] at hnot
    obtain ⟨hY1, hY2⟩ := endFold_a hreus
    have hnd : c.agents.Nodup := List.nodup_range
    obtain ⟨e, m, pe, hme, hm1, hm2⟩ := dig_msg hr c.agents (endFold c z) hnd ha (by rw [hY1]; exact hall)
    obtain ⟨⟨E, pE⟩, qc⟩ := qe
    have hlog : (lifecycle c z).log = z.log ++ e := by rw [lifecycle_log_dig, pe, hY2]
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hme
    intro h0
    have : z.log.length + j + 1 ∈ unread (lifecycle c z) a := by
      rw [mem_unread]
      refine ⟨by rw [qc]; omega, by rw [hlog]; simp; omega, ?_⟩
      simp only [addressed, State.msg, hlog]
      have : z.log.length + j + 1 ≠ 0 := by omega
      simp only [this, if_false, Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem hj, hje, Option.getD_some, hm1, hm2]
      simp
    rw [h0] at this; cases this
  · exact unread_ext qe hu

theorem tick_ready {c : Cfg} {s : State} {a t : Nat} (hp : c.passedOver = true) (hwa : c.waiterAlive = true)
    (ht : t ∈ c.tasks) (hs0 : claimable s t = true) (hR : Ready s a) : Ready (tickOf c s) a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  have hz : Ready (reapLocks (reapTasks c s)) a := by
    refine ⟨by simpa [State.agt] using h1, by simpa [State.agt] using h2, by simpa [State.agt] using h3,
      by simpa [State.agt] using h4, unread_ext (reapTasks_ext c s a) h5⟩
  exact lifecycle_ready hp hwa ht (claimable_reap hs0) hz

theorem ready_step {c : Cfg} {s s' : State} {a t : Nat} {act : Action} (hr : c.racy = false) (hp : c.passedOver = true) (hwa : c.waiterAlive = true) (hcl : a < s.cursor.length)
    (hq : ∀ b, act ≠ .leave b ∧ act ≠ .die b ∧ act ≠ .waiterGone b ∧ act ≠ .reapGone b
      ∧ ∀ f, act ≠ .endOther b f) (ht : t ∈ c.tasks)
    (hs0 : claimable s t = true) (hR : Ready s a) (hs : step c s act = some s') : Ready s' a ∨ Exit s' a := by
  have hR' := hR
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  have hlen : a < s.ag.length := by
    refine Classical.byContradiction fun hl => ?_
    rw [agt_of_ge (Nat.le_of_not_lt hl)] at h1; exact absurd h1 (by decide)
  open_step hs
  case leave b => exact absurd rfl (hq b).1
  case die b => exact absurd rfl (hq b).2.1
  case waiterGone b => exact absurd rfl (hq b).2.2.1
  case reapGone b => exact absurd rfl (hq b).2.2.2.1
  case endOther b f => exact absurd rfl ((hq b).2.2.2.2 f)
  case tick => obtain ⟨hg, rfl⟩ := hs; exact Or.inl (tick_ready hp hwa ht hs0 hR')
  case unblock t₀ =>
    split at hs
    · rw [when_eq_some] at hs; obtain ⟨hg, rfl⟩ := hs
      exact Or.inl (ready_frame (ready_post (ready_frame hR' (setTask_ag ..) (setTask_log ..) (setTask_cursor ..))) rfl rfl rfl)
    · cases hs
  case releaseOther t₀ =>
    obtain ⟨hg, rfl⟩ := hs
    exact Or.inl (ready_frame (ready_post (ready_frame hR' (setTask_ag ..) (setTask_log ..) (setTask_cursor ..))) rfl rfl rfl)
  case postTo b d u =>
    obtain ⟨hg, rfl⟩ := hs
    left; refine ready_of_fields hR' (by simp [State.agt]) (by simp [State.agt]) (by simp [State.agt]) (by simp [State.agt]) ?_
    exact unread_ext (ext_post _ _ _) h5
  case nudge b =>
    obtain ⟨hg, rfl⟩ := hs
    left; refine ready_of_fields hR' ?_ ?_ ?_ ?_ ?_
    all_goals first
      | (simp [agt_setAg]; split <;> simp_all; done)
      | skip
    exact unread_ext (ext_trans (s := s) (x := setAg s b _) (ext_frame (by simp) (by simp) _) (ext_post _ _ _)) h5
  case readAll b =>
    obtain ⟨hg, rfl⟩ := hs
    have hb : b ≠ a := by rintro rfl; simp_all [busy]
    exact Or.inl (ready_deliver_ne hb hR')
  case hcClear b =>
    obtain ⟨hg, rfl⟩ := hs
    have hb : b ≠ a := by rintro rfl; simp_all
    exact Or.inl (ready_setAg_ne hb (ready_deliver_ne hb (ready_frame hR' (by simp) (by simp) (by simp))))
  case wake b =>
    obtain ⟨hg, rfl⟩ := hs
    by_cases hb : b = a
    · subst hb; exact Or.inr (exit_awake (fun g => ⟨rfl, rfl⟩) hcl hlen h3)
    · exact Or.inl (ready_setAg_ne hb (ready_deliver_ne hb hR'))
  case prompt b =>
    obtain ⟨hg, rfl⟩ := hs
    by_cases hb : b = a
    · subst hb; exact Or.inr (exit_awake (fun g => ⟨rfl, rfl⟩) hcl hlen h3)
    · exact Or.inl (ready_setAg_ne hb (ready_deliver_ne hb hR'))
  case boot b =>
    obtain ⟨hg, rfl⟩ := hs
    by_cases hb : b = a
    · subst hb
      refine Or.inr ?_
      split
      · exact exit_takes (exit_awake (fun g => ⟨rfl, rfl⟩) hcl hlen h3)
      · exact exit_awake (fun g => ⟨rfl, rfl⟩) hcl hlen h3
    · refine Or.inl ?_
      split
      · exact ready_takes (ready_setAg_ne hb (ready_deliver_ne hb hR'))
      · exact ready_setAg_ne hb (ready_deliver_ne hb hR')
  case world w op => obtain ⟨hg, rfl⟩ := hs; exact Or.inl hR'
  case git b op =>
    obtain ⟨hg, rfl⟩ := hs
    have hb : b ≠ a := by rintro rfl; simp_all [working, busy]
    exact Or.inl (ready_setAg_ne hb hR')
  all_goals (obtain ⟨hg, rfl⟩ := hs)
  all_goals (left; refine ready_of_fields hR' ?_ ?_ ?_ ?_ ?_)
  all_goals first
    | (simpa [unread, State.cur, addressed, State.msg] using h5; done)
    | (simp; done)
    | (simp only [agt_setAg]; split <;> simp_all [busy]; done)
    | (simp [hr] at hg; done)
    | (simp [State.agt]; done)
    | (simp [agt_setAg, unbelieve]; split <;> simp_all [busy, working]; done)
    | (simp [agt_setAg, unbelieve]; done)
    | (simp_all [busy, working, State.agt, agt_setAg, unbelieve, awake]; done)
    | skip
  all_goals skip


-- ---------- L1 over fair runs ----------

/-- what every reachable state satisfies that this proof reads (proved in `rinv_of_reachable`), and no dead terminal -/
def RInv (c : Cfg) (s : State) : Prop :=
  s.ag.length = c.nagents ∧ s.cursor.length = c.nagents ∧ (∀ b, s.cur b ≤ s.log.length) ∧
  (∀ b, (s.agt b).cold = true → (s.agt b).big = true) ∧ (∀ b, (s.agt b).dead = false)


theorem reusable_ready {c : Cfg} {s : State} {a : Nat} (hp : c.passedOver = true) (hwa : c.waiterAlive = true)
    (hcur : ∀ b, s.cur b ≤ s.log.length) (hcold : ∀ b, (s.agt b).cold = true → (s.agt b).big = true)
    (ha : a ∈ c.agents) (hr : reusable c (reapLocks (reapTasks c s)) a = true) : Ready (tickOf c s) a := by
  have hag : ∀ b, (reapLocks (reapTasks c s)).agt b = s.agt b := fun b => by simp [State.agt]
  have hext := reapTasks_ext c s a
  have hr0 := hr
  simp only [reusable, finished, idleFree, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, hag, and_assoc] at hr
  obtain ⟨h1, _, _, _, _, _, _, _, h3, _, _, hw⟩ := hr
  have h2 : (s.agt a).waiter = true := by simpa [hwa] using hw
  have h4 : (s.agt a).cold = false := by
    cases hc : (s.agt a).cold
    · rfl
    · have := hcold a hc; simp_all
  have hz : ∀ P : Agent → Prop, P (s.agt a) → P ((reapLocks (reapTasks c s)).agt a) := fun P h => by rw [hag]; exact h
  have hcz : (reapLocks (reapTasks c s)).cur a ≤ (reapLocks (reapTasks c s)).log.length := by
    obtain ⟨⟨e, pe⟩, q⟩ := hext
    rw [q, pe, List.length_append]; have := hcur a; omega
  have hreus : finished c (reapLocks (reapTasks c s)) a = true → reusable c (reapLocks (reapTasks c s)) a = true := fun _ => hr0
  obtain ⟨q1, q2, q3, q4, _⟩ := lifecycle_qa hreus (hz (·.st = .idle) h1) (hz (·.waiter = true) h2) (hz (·.big = false) h3) (hz (·.cold = false) h4)
  exact ⟨q1, q2, q3, q4, lifecycle_unread hp ha hr0 hcz (hz (·.st = .idle) h1) (hz (·.waiter = true) h2) (hz (·.big = false) h3) (hz (·.cold = false) h4)⟩


theorem step_tick {c : Cfg} {s s' : State} (h : step c s .tick = some s') : c.watchd = true ∧ tickOf c s ≠ s ∧ s' = tickOf c s := by
  simp only [step, tick, when, Option.ite_none_right_eq_some, Option.some.injEq, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2.symm⟩

theorem nonreusable_fills {c : Cfg} {s : State} {t : Nat} (hroster : c.roster ≤ c.nagents) (hl : s.ag.length = c.nagents)
    (ht : t ∈ c.tasks) (hs0 : claimable s t = true) (hnr : ∀ a ∈ c.agents, reusable c (reapLocks (reapTasks c s)) a = false) :
    ¬ (startable (tickOf c s) t = true ∧ members (tickOf c s) < c.roster) :=
  lifecycle_fills hroster (by simpa using hl) ht (claimable_reap hs0) hnr

theorem wake_enabled {c : Cfg} {s : State} {a : Nat} (hr : c.racy = false) (h : Ready s a) : (step c s (.wake a)).isSome = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp [step, wake, when, hr, h1, h2, wakes, h4, h5]

theorem wake_exit {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.wake a) = some s') (hR : Ready s a) (hcl : a < s.cursor.length) :
    Exit s' a := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  have hlen : a < s.ag.length := by
    refine Classical.byContradiction fun hl => ?_
    rw [agt_of_ge (Nat.le_of_not_lt hl)] at h1; exact absurd h1 (by decide)
  simp only [step, wake, when, Option.ite_none_right_eq_some, Option.some.injEq] at h
  obtain ⟨_, rfl⟩ := h
  exact exit_awake (fun g => ⟨rfl, rfl⟩) hcl hlen h3

theorem claim_enabled {c : Cfg} {s : State} {a t : Nat} (hr : c.racy = false) (hE : Exit s a) (hs : claimable s t = true) :
    (step c s (.claim a t)).isSome = true := by
  obtain ⟨h1, h2, h3⟩ := hE
  simp [step, claim, when, hr, working, busy, h1, h2, hs, fenced, h3]

theorem exists_bound {P : Nat → Nat → Prop} : ∀ (l : List Nat), (∀ a ∈ l, ∃ N, ∀ m, N ≤ m → ¬ P m a) → ∃ N, ∀ a ∈ l, ∀ m, N ≤ m → ¬ P m a
  | [], _ => ⟨0, by simp⟩
  | a :: l, h => by
    obtain ⟨N1, h1⟩ := h a (by simp)
    obtain ⟨N2, h2⟩ := exists_bound l (fun b hb => h b (by simp [hb]))
    refine ⟨max N1 N2, fun b hb m hm => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1 m (by omega)
    · exact h2 b hb m (by omega)


theorem ready_lt {c : Cfg} {s : State} {a : Nat} (hI : RInv c s) (h : Ready s a) : a < s.cursor.length := by
  obtain ⟨hl, hcl, _⟩ := hI
  refine Classical.byContradiction fun hn => ?_
  have : s.ag.length ≤ a := by omega
  have h1 := h.1
  rw [agt_of_ge this] at h1; exact absurd h1 (by decide)

-- ---------- board #53: once lifted, the stop stays lifted ----------

theorem cur_showAll_le (s : State) (a o : Nat) (ids : List Nat) : s.cur o ≤ (showAll s a ids).cur o := by
  rw [showAll_cur]; split
  · rename_i h; obtain ⟨rfl, _⟩ := h; exact (foldl_max _ _).1
  · exact Nat.le_refl _
theorem cur_deliver_le (s : State) (a o : Nat) : s.cur o ≤ (deliver s a).cur o := cur_showAll_le ..

/-- what a step does to agent o's being at work: o was at work already, its cursor not moved back; or o has just read
every message, and the log only grew -/
def Grow (s s' : State) (o : Nat) : Prop :=
  active (s'.agt o) = true → (active (s.agt o) = true ∧ s.cur o ≤ s'.cur o) ∨ (unread s' o = [] ∧ ∃ e, s'.log = s.log ++ e)

theorem grow_nw {s s' : State} {o : Nat} (h1 : active (s'.agt o) = true → active (s.agt o) = true) (h2 : s.cur o ≤ s'.cur o) :
    Grow s s' o := fun h => Or.inl ⟨h1 h, h2⟩
/-- a turn of agent a starts with a delivery to it: x is s or a delivery to it, s' x delivered to a, with a's status set -/
theorem grow_turn {s x s' : State} {a o : Nat} (hx : x.log = s.log ∧ x.cursor.length = s.cursor.length ∧ ∀ b, s.cur b ≤ x.cur b)
    (hl : s.ag.length ≤ s.cursor.length) (hlog : s'.log = s.log) (hcur : s'.cursor = (deliver x a).cursor)
    (hag : ∀ b, b ≠ a → active (s'.agt b) = active (s.agt b)) (hout : s.ag.length ≤ a → active (s'.agt a) = false) : Grow s s' o := by
  intro h
  by_cases hoa : o = a
  · subst hoa
    by_cases hlt : o < s.ag.length
    · right
      refine ⟨?_, ⟨[], by simp [hlog]⟩⟩
      rw [unread_congr (s := deliver x o) (by simp [hlog, hx.1]) hcur]
      exact unread_deliver_self (by rw [hx.2.1]; omega)
    · rw [hout (Nat.le_of_not_lt hlt)] at h; cases h
  · left
    refine ⟨(hag o hoa) ▸ h, ?_⟩
    have e2 : s'.cur o = (deliver x a).cur o := by simp [State.cur, hcur]
    rw [e2]; exact Nat.le_trans (hx.2.2 o) (cur_deliver_le ..)
/-- agent b's status after a turn of a: as before -/
theorem act_turn {s : State} {a b : Nat} (f : Agent → Agent) (hb : b ≠ a) :
    active ((setAg (deliver s a) a f).agt b) = active (s.agt b) := by
  rw [agt_setAg, if_neg (fun e => hb e.1.symm)]; obtain ⟨bl, e⟩ := deliver_agt s a b; rw [e]; rfl
theorem act_out {s : State} {a : Nat} (f : Agent → Agent) (hle : s.ag.length ≤ a) :
    active ((setAg (deliver s a) a f).agt a) = false := by
  rw [agt_setAg, if_neg (fun e => by simp at e; omega)]; obtain ⟨bl, e⟩ := deliver_agt s a a; rw [e, agt_of_ge hle]; rfl

theorem grow_step {c : Cfg} {s s' : State} {act : Action} (hl : s.ag.length ≤ s.cursor.length) (hs : step c s act = some s')
    (o : Nat) : Grow s s' o := by
  open_step hs
  case tick => obtain ⟨_, rfl⟩ := hs; exact fun h => Or.inl (let ⟨h1, h2⟩ := (sp_tick c s).2 o h; ⟨h1, h2 ▸ Nat.le_refl _⟩)
  case wake a =>
    obtain ⟨_, rfl⟩ := hs
    exact grow_turn (a := a) (x := s) ⟨rfl, rfl, fun _ => Nat.le_refl _⟩ hl (by simp) (by simp [awake])
      (fun b hb => act_turn _ hb) (fun hle => act_out _ hle)
  case prompt a =>
    obtain ⟨_, rfl⟩ := hs
    exact grow_turn (a := a) (x := s) ⟨rfl, rfl, fun _ => Nat.le_refl _⟩ hl (by simp) (by simp)
      (fun b hb => act_turn _ hb) (fun hle => act_out _ hle)
  case boot a =>
    obtain ⟨_, rfl⟩ := hs
    split
    · refine grow_turn (a := a) (x := s) ⟨rfl, rfl, fun _ => Nat.le_refl _⟩ hl (by simp) (by simp) (fun b hb => ?_) (fun hle => ?_)
      · rw [show ∀ x : State, active ((takes c x a (firstClaimed c s a)).agt b) = active (x.agt b) from fun x => by simp [active]]
        exact act_turn _ hb
      · rw [show ∀ x : State, active ((takes c x a (firstClaimed c s a)).agt a) = active (x.agt a) from fun x => by simp [active]]
        exact act_out _ hle
    · exact grow_turn (a := a) (x := s) ⟨rfl, rfl, fun _ => Nat.le_refl _⟩ hl (by simp) (by simp)
        (fun b hb => act_turn _ hb) (fun hle => act_out _ hle)
  case wakeWrite a =>
    obtain ⟨_, rfl⟩ := hs
    have hx : ∀ x : State, x.log = s.log → x.cursor.length = s.cursor.length → (∀ b, s.cur b ≤ x.cur b) →
        (∀ b, active (x.agt b) = active (s.agt b)) → x.ag.length = s.ag.length →
        Grow s (setAg (awake (deliver x a) a) a fun g => { g with snap := [] }) o := fun x h1 h2 h4 h5 h6 =>
      grow_turn (a := a) (x := x) ⟨h1, h2, h4⟩ hl (by simp [h1]) (by simp [awake]) (fun b hb => by
          simp only [awake]; rw [agt_setAg, if_neg (fun e => hb e.1.symm), ← h5 b, ← act_turn (s := x) (a := a) _ hb])
        (fun hle => by
          simp only [awake]; rw [agt_setAg, if_neg (fun e => by simp at e; omega)]
          exact act_out (s := x) _ (by omega))
    split
    · exact hx s rfl rfl (fun _ => Nat.le_refl _) (fun _ => rfl) rfl
    · exact hx _ (by simp) (showAll_lens ..).1 (fun b => cur_showAll_le ..)
        (fun b => showAll_proj (active ·) (fun _ _ => rfl) ..) (showAll_ag_length ..)
  case readAll a =>
    obtain ⟨_, rfl⟩ := hs
    exact grow_nw (fun h => by obtain ⟨bl, e⟩ := deliver_agt s a o; rw [e] at h; simpa [active] using h) (cur_deliver_le ..)
  case hcClear a =>
    obtain ⟨hg, rfl⟩ := hs
    refine grow_nw (fun h => ?_) ?_
    · by_cases hoa : o = a
      · subst hoa; simp [active, hg]
      · rw [act_turn _ hoa] at h; simpa [State.agt] using h
    · exact Nat.le_trans (by simp [State.cur]) (cur_deliver_le ..)
  case claimWrite a =>
    obtain ⟨_, rfl⟩ := hs
    split
    · refine grow_nw (fun h => ?_) (by simp [State.cur])
      rw [agt_setAg] at h
      have e : ∀ g : Agent, active ((takes c (claimed s a (s.agt a).reading) a (s.agt a).reading).agt o) = active (s.agt o) :=
        fun _ => by simp [active]
      split at h
      · rename_i hh; obtain ⟨rfl, _⟩ := hh; rw [← e default]; simpa [active, State.agt] using h
      · rw [← e default]; simpa [active, State.agt] using h
    · exact grow_nw (fun h => by rw [agt_setAg] at h; split at h <;> simp_all [active]) (by simp [State.cur])
  case hcPrompt a =>
    obtain ⟨hg, rfl⟩ := hs
    refine grow_nw (fun h => ?_) (by simp [State.cur])
    simp only [setTask_agt] at h; rw [agt_setAg] at h; split at h
    · rename_i hh; obtain ⟨rfl, _⟩ := hh; simp [busy] at hg; simp [active, hg.1]
    · exact h
  case unblock t₀ =>
    split at hs
    · rw [when_eq_some] at hs; obtain ⟨_, rfl⟩ := hs
      exact grow_nw (fun h => by simpa [State.agt] using h) (by simp [State.cur])
    · cases hs
  case releaseOther t₀ =>
    obtain ⟨_, rfl⟩ := hs; exact grow_nw (fun h => by simpa [State.agt] using h) (by simp [State.cur])
  case leave a =>
    obtain ⟨_, rfl⟩ := hs
    refine grow_nw (fun h => ?_) (by simp [State.cur])
    rw [endAgent_agt, agt_setAg] at h; split at h
    · simp [active] at h
    · split at h <;> simp_all [active]
  case reapGone a =>
    obtain ⟨_, rfl⟩ := hs
    refine grow_nw (fun h => ?_) (by simp [State.cur])
    rw [endAgent_agt, agt_setAg] at h; split at h
    · simp [active] at h
    · split at h <;> simp_all [active]
  case endOther a f =>
    obtain ⟨_, rfl⟩ := hs
    refine grow_nw (fun h => ?_) (by simp [State.cur])
    rw [endAgent_agt, agt_setAg] at h; split at h
    · simp [active] at h
    · split at h <;> simp_all [active]
  all_goals (obtain ⟨hg, rfl⟩ := hs)
  all_goals (try split)
  all_goals refine grow_nw (fun h => ?_) ?_
  all_goals first
    | (simp [State.cur]; done)
    | (simpa [State.agt] using h; done)
    | (simpa [active] using h; done)
    | ((try simp only [unbelieve, awake, post_agt, setTask_agt, claimed_agt] at h); rw [agt_setAg] at h; split at h <;> simp_all [active, State.agt]; done)
    | ((try simp only [unbelieve, awake, post_agt, setTask_agt, claimed_agt] at h); rw [agt_setAg] at h; split at h <;> simp_all [active, State.agt, agt_setAg]; done)

theorem setTask_stop (s : State) (t u : Nat) (f : Task → Task) (hf : ∀ k, (f k).stopTo = k.stopTo ∧ (f k).stopMsg = k.stopMsg) :
    ((setTask s t f).tk u).stopTo = (s.tk u).stopTo ∧ ((setTask s t f).tk u).stopMsg = (s.tk u).stopMsg := by
  rcases tk_setTask_or s t u f with e | ⟨_, e⟩ <;> rw [e]
  · exact ⟨rfl, rfl⟩
  · exact hf _

/-- board #53: only the user's release of t changes its stop -/
theorem stop_kept {c : Cfg} {s s' : State} {act : Action} {t : Nat} (hn : act ≠ .releaseOther t) (hs : step c s act = some s') :
    (s'.tk t).stopTo = (s.tk t).stopTo ∧ (s'.tk t).stopMsg = (s.tk t).stopMsg := by
  open_step hs
  case tick => obtain ⟨_, rfl⟩ := hs; exact (sp_tick c s).1 t
  case releaseOther t₀ =>
    obtain ⟨_, rfl⟩ := hs
    have hne : t ≠ t₀ := fun e => hn (by rw [e])
    rw [post_tk, tk_setTask_ne hne]; exact ⟨rfl, rfl⟩
  case unblock t₀ =>
    split at hs
    · rw [when_eq_some] at hs; obtain ⟨_, rfl⟩ := hs
      simp only [State.tk] at ⊢; exact setTask_stop s t₀ t _ (fun _ => ⟨rfl, rfl⟩)
    · cases hs
  case hcClear a =>
    obtain ⟨_, rfl⟩ := hs
    simp only [setAg_tk, deliver_tk]
    rw [tk_map (s := s) (g := fun k =>
      if k.owner == some a && k.st == .blocked && k.hcq then { k with st := .claimed, hcq := false, lease := true } else k) (by simp) rfl]
    split <;> exact ⟨rfl, rfl⟩
  case claimWrite a =>
    obtain ⟨_, rfl⟩ := hs
    split
    · rw [setAg_tk, show ∀ (x : State) e, ({ x with early := e } : State).tk t = x.tk t from fun _ _ => rfl, takes_tk]
      exact claimed_stop ..
    · rw [setAg_tk]; exact ⟨rfl, rfl⟩
  case leave a =>
    obtain ⟨_, rfl⟩ := hs; rw [endAgent_tk]; split <;> simp
  case reapGone a =>
    obtain ⟨_, rfl⟩ := hs; rw [endAgent_tk]; split <;> simp
  case endOther a f =>
    obtain ⟨_, rfl⟩ := hs; rw [endAgent_tk]; split <;> simp
  all_goals (obtain ⟨hg, rfl⟩ := hs)
  all_goals (try split)
  all_goals (try simp only [unbelieve, awake, claimed, post_tk, setAg_tk, deliver_tk, takes_tk, unbelieve_tk, awake_tk])
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact setTask_stop _ _ t _ (fun _ => ⟨rfl, rfl⟩)
    | (simp only [State.tk] at ⊢; exact ⟨rfl, rfl⟩)
    | (simp [State.tk]; done)
    | exact (setTask_stop _ _ t _ (fun _ => ⟨rfl, rfl⟩))

/-- board #53, of a reachable state: a task's stop is a message of the log, to the agent it names -/
def SK (s : State) : Prop := ∀ t o, (s.tk t).stopTo = some o → (s.tk t).stopMsg ≤ s.log.length ∧ addressed s o (s.tk t).stopMsg = true

theorem sk_of_reachable {c : Cfg} {s : State} (h : Reachable c s) : SK s := by
  refine reachable_induct (P := SK) ?_ ?_ h
  · intro t o ho
    have : ((init c).tk t).stopTo = none := by
      simp only [State.tk, init]; split
      · rfl
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
    rw [this] at ho; cases ho
  intro s s' act _ hK hs t o ho
  obtain ⟨e, he⟩ := step_log hs
  by_cases hr : act = .releaseOther t
  · subst hr
    simp only [step, releaseOther, when_eq_some, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨⟨_, hsome⟩, hst⟩, rfl⟩ := hs
    have hna : (s.tk t).st ≠ .absent := by rcases hst with e | e <;> simp [e]
    rw [post_tk, tk_setTask_self hna] at ho ⊢
    simp only [] at ho ⊢
    have hm : (post (setTask s t fun k => { k with st := .opn, owner := none, lease := false, hcq := false, stopTo := if c.stopFirst then k.owner else none, stopMsg := s.log.length + 1 }) ⟨none, (s.tk t).owner.getD 0, true, .released, t⟩).msg (s.log.length + 1) = ⟨none, (s.tk t).owner.getD 0, true, .released, t⟩ := by
      simp [State.msg, post, List.getD_eq_getElem?_getD]
    refine ⟨by simp [post], ?_⟩
    simp only [addressed, hm]
    split at ho
    · simp [ho]
    · cases ho
  · obtain ⟨h1, h2⟩ := stop_kept hr hs
    rw [h1] at ho
    obtain ⟨k1, k2⟩ := hK t o ho
    rw [h2]
    refine ⟨by rw [he]; simp; omega, ?_⟩
    simp only [addressed] at k2 ⊢; rw [msg_ext he k1]; exact k2

/-- board #53: a stop that has lifted stays lifted, unless the user releases the task again -/
theorem stopped_step {c : Cfg} {s s' : State} {act : Action} {t : Nat} (hK : SK s) (hl : s.ag.length ≤ s.cursor.length)
    (hn : act ≠ .releaseOther t) (hs : step c s act = some s') (h : stopped s t = false) : stopped s' t = false := by
  obtain ⟨h1, h2⟩ := stop_kept hn hs
  unfold stopped at h ⊢
  rw [h1, h2]
  cases ho : (s.tk t).stopTo with
  | none => rfl
  | some o =>
    rw [ho] at h; simp only [] at h ⊢
    cases ha : active (s'.agt o)
    · rfl
    · rcases grow_step hl hs o ha with ⟨a1, a2⟩ | ⟨u1, ⟨e, he⟩⟩
      · rw [a1] at h; simp at h ⊢; omega
      · obtain ⟨k1, k2⟩ := hK t o ho
        simp only [Bool.true_and, decide_eq_false_iff_not, Nat.not_lt]
        refine Nat.le_of_not_lt fun hlt => ?_
        have : (s.tk t).stopMsg ∈ unread s' o := mem_unread.mpr ⟨hlt, by rw [he]; simp; omega, by
          simp only [addressed] at k2 ⊢; rw [msg_ext he k1]; exact k2⟩
        rw [u1] at this; cases this

/-- L1's core. In a fair run of an instance with PR #116 and PR #119, a claimable task doesn't stay claimable forever while
a slot is free: either it is taken, or the slot fills. Needs no agent to leave, die, lose its waiter or be reaped by
`hc ls` after the start, and the invariants of a reachable state (`hI`). -/
theorem claimable_taken {c : Cfg} (hr : c.racy = false) (hw : c.watchd = true) (hp : c.passedOver = true)
    (hwa : c.waiterAlive = true) (hroster : c.roster ≤ c.nagents) {t : Nat} (ht : t ∈ c.tasks) (r : Run c) (hf : r.Fair) {n : Nat}
    (hq : ∀ k, n ≤ k → ∀ b, r.act k ≠ .leave b ∧ r.act k ≠ .die b ∧ r.act k ≠ .waiterGone b ∧ r.act k ≠ .reapGone b
      ∧ ∀ f, r.act k ≠ .endOther b f)
    (hI : ∀ m, n ≤ m → RInv c (r.st m)) :
    ∃ m, n ≤ m ∧ ¬ (claimable (r.st m) t = true ∧ slotFree c (r.st m) = true) := by
  refine Classical.byContradiction fun hne => ?_
  have hB : ∀ m, n ≤ m → claimable (r.st m) t = true ∧ members (r.st m) < c.roster := by
    intro m hm
    refine Classical.byContradiction fun h => ?_
    exact hne ⟨m, hm, fun ⟨h1, h2⟩ => h ⟨h1, by simpa [slotFree] using h2⟩⟩
  have claim4 : ∀ N, n ≤ N → ∃ m, N ≤ m ∧ ∃ a ∈ c.agents, Ready (r.st m) a := by
    intro N hN
    refine Classical.byContradiction fun hno => ?_
    have hno' : ∀ m, N ≤ m → ∀ a ∈ c.agents, ¬ Ready (r.st m) a := fun m hm a ha hR => hno ⟨m, hm, a, ha, hR⟩
    have hen : ∀ m, N ≤ m → (step c (r.st m) .tick).isSome = true := by
      intro m hm
      by_cases hz : ∃ a ∈ c.agents, reusable c (reapLocks (reapTasks c (r.st m))) a = true
      · obtain ⟨a, ha, hra⟩ := hz
        refine Classical.byContradiction fun hdis => ?_
        have htick : tickOf c (r.st m) = r.st m := by
          cases hh : step c (r.st m) .tick with
          | some s' => simp [hh] at hdis
          | none =>
            simp only [step, tick, when] at hh
            refine Classical.byContradiction fun hne2 => ?_
            simp [hw, hne2] at hh
        have := reusable_ready hp hwa (hI m (by omega)).2.2.1 (hI m (by omega)).2.2.2.1 ha hra
        rw [htick] at this
        exact hno' m hm a ha this
      · have hnr : ∀ a ∈ c.agents, reusable c (reapLocks (reapTasks c (r.st m))) a = false := by
          intro a ha; cases hh : reusable c (reapLocks (reapTasks c (r.st m))) a
          · rfl
          · exact absurd ⟨a, ha, hh⟩ hz
        have hnf := nonreusable_fills hroster (hI m (by omega)).1 ht (hB m (by omega)).1 hnr
        have hne' : tickOf c (r.st m) ≠ r.st m := by
          intro e; apply hnf; rw [e]; exact ⟨startable_of_claimable (hB m (by omega)).1, (hB m (by omega)).2⟩
        simp [step, tick, when, hw, hne']
    obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .tick) (N0 := N) (fun _ _ => by simp [fair]) hen
    have hok := r.ok k
    rw [hact] at hok
    obtain ⟨_, _, hst⟩ := step_tick hok
    by_cases hz : ∃ a ∈ c.agents, reusable c (reapLocks (reapTasks c (r.st k))) a = true
    · obtain ⟨a, ha, hra⟩ := hz
      have := reusable_ready hp hwa (hI k (by omega)).2.2.1 (hI k (by omega)).2.2.2.1 ha hra
      rw [← hst] at this
      exact hno' (k+1) (by omega) a ha this
    · have hnr : ∀ a ∈ c.agents, reusable c (reapLocks (reapTasks c (r.st k))) a = false := by
        intro a ha; cases hh : reusable c (reapLocks (reapTasks c (r.st k))) a
        · rfl
        · exact absurd ⟨a, ha, hh⟩ hz
      have hnf := nonreusable_fills hroster (hI k (by omega)).1 ht (hB k (by omega)).1 hnr
      rw [← hst] at hnf
      exact hnf ⟨startable_of_claimable (hB (k+1) (by omega)).1, (hB (k+1) (by omega)).2⟩
  -- some agent is ready infinitely often
  have claim5 : ∃ a ∈ c.agents, ∀ N, ∃ m, N ≤ m ∧ Ready (r.st m) a := by
    refine Classical.byContradiction fun hno => ?_
    have h1 : ∀ a ∈ c.agents, ∃ N, ∀ m, N ≤ m → ¬ Ready (r.st m) a := by
      intro a ha
      refine Classical.byContradiction fun h2 => ?_
      exact hno ⟨a, ha, fun N => by
        refine Classical.byContradiction fun h3 => ?_
        exact h2 ⟨N, fun m hm hR => h3 ⟨m, hm, hR⟩⟩⟩
    obtain ⟨N, hN⟩ := exists_bound (P := fun m a => Ready (r.st m) a) c.agents h1
    obtain ⟨m, hm, a, ha, hR⟩ := claim4 (max N n) (by omega)
    exact hN a ha m (by omega) hR
  obtain ⟨a, ha, hinf⟩ := claim5
  have exit_of_ready : ∀ m, n ≤ m → Ready (r.st m) a → ∃ j, m < j ∧ Exit (r.st j) a := by
    intro m hm hR
    refine Classical.byContradiction fun hno => ?_
    have hno' : ∀ j, m < j → ¬ Exit (r.st j) a := fun j hj hE => hno ⟨j, hj, hE⟩
    have hall : ∀ k, m ≤ k → Ready (r.st k) a := by
      refine forever (fun k => Ready (r.st k) a) m hR (fun k hk ih => ?_)
      have := ready_step hr hp hwa (ready_lt (hI k (by omega)) ih) (hq k (by omega)) ht (hB k (by omega)).1 ih (r.ok k)
      rcases this with h | h
      · exact h
      · exact absurd h (hno' (k+1) (by omega))
    obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .wake a) (N0 := m)
      (fun k hk => by simp [fair, ha, (hI k (by omega)).2.2.2.2 a]) (fun k hk => wake_enabled hr (hall k hk))
    have hok := r.ok k
    rw [hact] at hok
    exact hno' (k+1) (by omega) (wake_exit hok (hall k hk) (ready_lt (hI k (by omega)) (hall k hk)))
  -- so claim a t is enabled infinitely often
  obtain ⟨k, hk, hact⟩ := hf (.claim a t) (fun N => by
    obtain ⟨m, hm, hR⟩ := hinf (max N n)
    obtain ⟨j, hj, hE⟩ := exit_of_ready m (by omega) hR
    exact ⟨j, by omega, by simp [fair, ha, ht, (hI j (by omega)).2.2.2.2 a], claim_enabled hr hE (hB j (by omega)).1⟩) n
  have hok := r.ok k
  rw [hact] at hok
  have h1 := (hB (k+1) (by omega)).1
  simp only [step, claim, when, Option.ite_none_right_eq_some, Option.some.injEq] at hok
  obtain ⟨_, hok⟩ := hok
  rw [← hok] at h1
  simp [claimable, startable] at h1
  exact claimed_not_opn _ _ _ (by simpa using h1.1.1)


/-- L1, given that the user's stop on t (board #53) lifts for good: a startable task doesn't stay startable forever while
a slot is free. `startable_leads_to` (Release.lean) proves the stop lifts. -/
theorem startable_taken {c : Cfg} (hr : c.racy = false) (hw : c.watchd = true) (hp : c.passedOver = true)
    (hwa : c.waiterAlive = true) (hroster : c.roster ≤ c.nagents) {t : Nat} (ht : t ∈ c.tasks) (r : Run c) (hf : r.Fair) {n : Nat}
    (hq : ∀ k, n ≤ k → ∀ b, r.act k ≠ .leave b ∧ r.act k ≠ .die b ∧ r.act k ≠ .waiterGone b ∧ r.act k ≠ .reapGone b
      ∧ ∀ f, r.act k ≠ .endOther b f)
    (hI : ∀ m, n ≤ m → RInv c (r.st m)) (hlift : ∃ N, n ≤ N ∧ ∀ m, N ≤ m → stopped (r.st m) t = false) :
    ∃ m, n ≤ m ∧ ¬ (startable (r.st m) t = true ∧ slotFree c (r.st m) = true) := by
  obtain ⟨N, hN, hs⟩ := hlift
  obtain ⟨m, hm, hn⟩ := claimable_taken hr hw hp hwa hroster ht r hf (n := N) (fun k hk => hq k (by omega)) (fun m hm => hI m (by omega))
  refine ⟨m, by omega, fun ⟨h1, h2⟩ => hn ⟨?_, h2⟩⟩
  simp [claimable, h1, hs m hm]

-- ---------- invariants of every reachable state ----------

def I1 (c : Cfg) (s : State) : Prop :=
  s.ag.length = c.nagents ∧ s.cursor.length = c.nagents ∧ ∀ b, (s.agt b).cold = true → (s.agt b).big = true

theorem i1_init (c : Cfg) : I1 c (init c) := by
  refine ⟨by simp [init, Cfg.agents], by simp [init, Cfg.agents], fun b hb => ?_⟩
  exfalso
  revert hb
  simp only [State.agt, init, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases c.agents[b]? <;> simp <;> rfl

theorem i1_frame {c : Cfg} {s s' : State} (hag : s'.ag = s.ag) (hc : s'.cursor = s.cursor) (h : I1 c s) : I1 c s' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [hag]; exact h1, by rw [hc]; exact h2, fun b hb => by rw [agt_of_ag hag] at hb ⊢; exact h3 b hb⟩

theorem i1_setAg' {c : Cfg} {s : State} {a : Nat} {f : Agent → Agent}
    (hf : (f (s.agt a)).cold = true → (f (s.agt a)).big = true) (h : I1 c s) : I1 c (setAg s a f) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, fun b hb => ?_⟩
  rw [agt_setAg] at hb ⊢
  split at hb
  · rename_i hab; rw [if_pos hab]; obtain ⟨rfl, _⟩ := hab; exact hf hb
  · rename_i hab; rw [if_neg hab]; exact h3 b hb

theorem i1_setAg {c : Cfg} {s : State} {a : Nat} {f : Agent → Agent}
    (hf : ((s.agt a).cold = true → (s.agt a).big = true) → (f (s.agt a)).cold = true → (f (s.agt a)).big = true)
    (h : I1 c s) : I1 c (setAg s a f) := i1_setAg' (hf (h.2.2 a)) h

theorem i1_deliver {c : Cfg} {s : State} {a : Nat} (h : I1 c s) : I1 c (deliver s a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa using h1, ?_, fun b hb => ?_⟩
  · show (showAll s a (unread s a)).cursor.length = c.nagents
    rw [(showAll_lens (unread s a) s a).1]; exact h2
  · simp only [deliver_cold, deliver_big] at hb ⊢; exact h3 b hb

theorem i1_showAll {c : Cfg} {s : State} {a : Nat} {ids : List Nat} (h : I1 c s) : I1 c (showAll s a ids) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun b hb => ?_⟩
  · rw [showAll_ag_length]; exact h1
  · rw [(showAll_lens ids s a).1]; exact h2
  · obtain ⟨bl, e⟩ := showAll_agt a ids b s
    rw [e] at hb ⊢; exact h3 b hb

theorem i1_takes {c : Cfg} {s : State} {a t : Nat} (h : I1 c s) : I1 c (takes c s a t) := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : (takes c s a t).ag.length = s.ag.length := by unfold takes; simp only []; split <;> simp
  have e2 : (takes c s a t).cursor.length = s.cursor.length := by unfold takes; simp only []; split <;> simp
  refine ⟨by rw [e1]; exact h1, by rw [e2]; exact h2, fun b hb => ?_⟩
  simp only [takes_cold, takes_big] at hb ⊢; exact h3 b hb

theorem i1_endAgent {c : Cfg} {s : State} {a : Nat} (h : I1 c s) : I1 c (endAgent s a) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa [endAgent] using h1, by simpa using h2, fun b hb => ?_⟩
  rw [endAgent_agt] at hb ⊢
  split at hb
  · rename_i hh; rw [if_pos hh]; simp at hb ⊢; exact h3 b hb
  · rename_i hh; rw [if_neg hh]; exact h3 b hb

theorem i1_spawnFor {c : Cfg} {pl : List Nat} {x : State} {t : Nat} (h : I1 c x) : I1 c (spawnFor c pl x t) := by
  unfold spawnFor; split
  · split
    · obtain ⟨h1, h2, h3⟩ := h
      refine ⟨by simp [setAg, h1], by simp [h2], fun b hb => ?_⟩
      simp only [claimed_agt, agt_mk, agt_def, agt_setAg] at hb ⊢
      split at hb
      · exact absurd hb Bool.false_ne_true
      · rename_i hh; rw [if_neg hh]; exact h3 b hb
    · exact h
  · exact h


theorem i1_tickOf {c : Cfg} {s : State} (h : I1 c s) : I1 c (tickOf c s) :=
  tick_inv (I1 c) (fun x t hx => i1_frame (by simp) (by simp) hx) (fun x hx => i1_frame (by simp) (by simp) hx)
    (fun _ _ => i1_endAgent) (fun x a pl hx => i1_frame (s := setAg x a fun g => { g with told := pl ++ g.told }) (by simp) (by simp)
      (i1_setAg' (fun hh => hx.2.2 a (by simpa using hh)) hx))
    (fun _ _ _ hx _ => i1_spawnFor hx) h

theorem i1_setTask {c : Cfg} {s : State} {t : Nat} {f : Task → Task} (h : I1 c s) : I1 c (setTask s t f) :=
  i1_frame (by simp) (by simp) h
theorem i1_post {c : Cfg} {s : State} {m : Msg} (h : I1 c s) : I1 c (post s m) := i1_frame (by simp) (by simp) h

macro "i1_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible assumption
    | (with_reducible apply i1_deliver)
    | (with_reducible apply i1_takes)
    | (with_reducible apply i1_setTask)
    | (with_reducible apply i1_post)
    | (refine i1_setAg ?_ ?_ <;> first | (intro hh hh2; simp_all [busy]; done) | skip)
    | (refine i1_frame ?_ ?_ ‹I1 _ _› <;> rfl)
    | (with_reducible apply i1_showAll)))

theorem i1_step {c : Cfg} {s s' : State} {act : Action} (hI : I1 c s) (hs : step c s act = some s') : I1 c s' := by
  open_step hs
  case tick => obtain ⟨_, rfl⟩ := hs; exact i1_tickOf hI
  case unblock t₀ =>
    split at hs
    · rw [when_eq_some] at hs; obtain ⟨_, rfl⟩ := hs; exact i1_frame (s := s) (by simp) (by simp) hI
    · cases hs
  case leave a => obtain ⟨_, rfl⟩ := hs; exact i1_endAgent (i1_setAg' (fun hh => hI.2.2 a (by simpa using hh)) hI)
  case reapGone a => obtain ⟨_, rfl⟩ := hs; exact i1_endAgent (i1_setAg' (fun hh => hI.2.2 a (by simpa using hh)) hI)
  case endOther a f => obtain ⟨_, rfl⟩ := hs; exact i1_endAgent (i1_setAg' (fun hh => hI.2.2 a (by simpa using hh)) hI)
  case claimWrite a =>
    obtain ⟨hg, rfl⟩ := hs
    split
    · have hI' : I1 c { takes c (claimed s a (s.agt a).reading) a (s.agt a).reading with early := s.early || !depsDone s (s.agt a).reading } :=
        i1_frame (s := takes c (claimed s a (s.agt a).reading) a (s.agt a).reading) rfl rfl (i1_takes (i1_setTask hI))
      exact i1_setAg' (fun hh => hI'.2.2 a (by simpa using hh)) hI'
    · i1_tac
  all_goals (obtain ⟨hg, rfl⟩ := hs)
  all_goals (try split)
  all_goals (try simp only [unbelieve, awake, claimed])
  all_goals i1_tac



theorem i1_of_reachable {c : Cfg} {s : State} (h : Reachable c s) : I1 c s :=
  reachable_induct (P := I1 c) (i1_init c) (fun s s' act _ hs hstep => i1_step hs hstep) h

-- ---------- no terminal dies ----------

def Dd (s : State) : Prop := ∀ b, (s.agt b).dead = false

theorem d_frame {s s' : State} (hag : s'.ag = s.ag) (h : Dd s) : Dd s' := fun b => by rw [agt_of_ag hag]; exact h b

theorem d_setAg' {s : State} {a : Nat} {f : Agent → Agent} (hf : (f (s.agt a)).dead = false) (h : Dd s) : Dd (setAg s a f) := by
  intro b
  rw [agt_setAg]
  split
  · rename_i hab; obtain ⟨rfl, _⟩ := hab; exact hf
  · exact h b

theorem d_setAg {s : State} {a : Nat} {f : Agent → Agent} (hf : (s.agt a).dead = false → (f (s.agt a)).dead = false) (h : Dd s) :
    Dd (setAg s a f) := d_setAg' (hf (h a)) h

theorem d_deliver {s : State} {a : Nat} (h : Dd s) : Dd (deliver s a) := fun b => by simp only [deliver_dead]; exact h b
theorem d_takes {c : Cfg} {s : State} {a t : Nat} (h : Dd s) : Dd (takes c s a t) := fun b => by simp only [takes_dead]; exact h b
theorem d_showAll {s : State} {a : Nat} {ids : List Nat} (h : Dd s) : Dd (showAll s a ids) := fun b => by
  obtain ⟨bl, e⟩ := showAll_agt a ids b s
  rw [e]; exact h b
theorem d_setTask {s : State} {t : Nat} {f : Task → Task} (h : Dd s) : Dd (setTask s t f) := d_frame (by simp) h
theorem d_post {s : State} {m : Msg} (h : Dd s) : Dd (post s m) := d_frame (by simp) h

theorem d_endAgent {s : State} {a : Nat} (h : Dd s) : Dd (endAgent s a) := fun b => by
  rw [endAgent_agt]; split
  · simp; exact h b
  · exact h b

theorem d_spawnFor {c : Cfg} {pl : List Nat} {x : State} {t : Nat} (h : Dd x) : Dd (spawnFor c pl x t) := by
  unfold spawnFor; split
  · split
    · intro b
      simp only [claimed_agt, agt_mk, agt_def, agt_setAg]
      split
      · rfl
      · exact h b
    · exact h
  · exact h

theorem d_tickOf {c : Cfg} {s : State} (h : Dd s) : Dd (tickOf c s) :=
  tick_inv (Dd) (fun x t hx => d_frame (by simp) hx) (fun x hx => d_frame (by simp) hx)
    (fun _ _ => d_endAgent) (fun x a pl hx => d_post (d_setAg (fun hh => by simpa using hh) hx))
    (fun _ _ _ hx _ => d_spawnFor hx) h

macro "d_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible assumption
    | (with_reducible apply d_deliver)
    | (with_reducible apply d_takes)
    | (with_reducible apply d_setTask)
    | (with_reducible apply d_post)
    | (with_reducible apply d_showAll)
    | (refine d_setAg ?_ ?_ <;> first | (intro hh; simp_all; done) | skip)
    | (refine d_frame ?_ ‹Dd _› <;> rfl)))

theorem d_step {c : Cfg} {s s' : State} {act : Action} (hq : ∀ b, act ≠ .die b) (hI : Dd s) (hs : step c s act = some s') : Dd s' := by
  open_step hs
  case tick => obtain ⟨_, rfl⟩ := hs; exact d_tickOf hI
  case die a => exact absurd rfl (hq a)
  case unblock t₀ =>
    split at hs
    · rw [when_eq_some] at hs; obtain ⟨_, rfl⟩ := hs; exact d_frame (s := s) (by simp) hI
    · cases hs
  case leave a => obtain ⟨_, rfl⟩ := hs; exact d_endAgent (d_setAg (fun hh => by simpa using hh) hI)
  case reapGone a => obtain ⟨_, rfl⟩ := hs; exact d_endAgent (d_setAg (fun hh => by simpa using hh) hI)
  case endOther a f => obtain ⟨_, rfl⟩ := hs; exact d_endAgent (d_setAg (fun hh => by simpa using hh) hI)
  case claimWrite a =>
    obtain ⟨hg, rfl⟩ := hs
    split
    · have hI' : Dd { takes c (claimed s a (s.agt a).reading) a (s.agt a).reading with early := s.early || !depsDone s (s.agt a).reading } :=
        d_frame (s := takes c (claimed s a (s.agt a).reading) a (s.agt a).reading) rfl (d_takes (d_setTask hI))
      exact d_setAg' (by simpa using hI' a) hI'
    · d_tac
  all_goals (obtain ⟨hg, rfl⟩ := hs)
  all_goals (try split)
  all_goals (try simp only [unbelieve, awake, claimed])
  all_goals d_tac


end Swarm
