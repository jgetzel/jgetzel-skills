import SwarmModel.Boot
import SwarmModel.Holder

/-! L3, joined: an unblock answer on a task reaches whoever holds the task, unless the task ends. `L3I` is the invariant
the two halves (`holder_leads_to`, `booting_reads`) took as hypotheses, proved of every reachable state; `answer_reaches`
is the one statement about a task. -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

/-- a spawned agent before its first turn is idle with no waiter, and holds at most one task, claimed with a live lease
(so no spawned agent blocks a task before its first turn, and `firstClaimed` is the task it holds) -/
def BootOk (s : State) : Prop := ∀ a, (s.agt a).boot = true → (s.agt a).st = .idle ∧ (s.agt a).waiter = false ∧
  ∀ u, held (s.tk u) a = true → (s.tk u).st = .claimed ∧ (s.tk u).lease = true ∧ ∀ v, held (s.tk v) a = true → v = u
/-- whoever holds a task is live -/
def HeldLive (s : State) : Prop := ∀ u a, held (s.tk u) a = true → (s.agt a).live = true
/-- an answer to `t` is unread in `o`'s inbox -/
def AnsIn (s : State) (o t : Nat) : Prop := ∃ i, i ∈ unread s o ∧ (s.msg i).kind = .answer ∧ (s.msg i).task = t
/-- an answer not yet seen is stored on the task, and whoever holds the task is booting (its first turn reads the task) or
has the answer unread in its inbox; if the task is blocked, it is an hc prompt the holder sits at -/
def PendOk (s : State) : Prop := ∀ t ∈ s.pend, (s.tk t).answer = true ∧ ∀ o, held (s.tk t) o = true →
  (s.agt o).boot = true ∨ (AnsIn s o t ∧ ((s.tk t).st = .blocked → (s.tk t).hcq = true ∧ (s.agt o).st = .blocked))
def L3I (s : State) : Prop := BootOk s ∧ HeldLive s ∧ PendOk s

theorem ansIn_ext {s x : State} {o t : Nat} (h : Ext s x o) (ha : AnsIn s o t) : AnsIn x o t := by
  obtain ⟨i, hi, hk, ht⟩ := ha
  obtain ⟨h1, h2⟩ := unread_ext_mem h hi
  exact ⟨i, h1, by rw [h2]; exact hk, by rw [h2]; exact ht⟩

theorem held_owner {k : Task} {a : Nat} (h : held k a = true) : k.owner = some a := by simp [held] at h; exact h.1

theorem live_of_st {g : Agent} (h : g.st = .working ∨ g.st = .idle ∨ g.st = .blocked) : g.live = true := by
  rcases h with e | e | e <;> simp [Agent.live, e]

/-- the general frame: tasks the same, the answers still pending a subset, the log only grown and cursors the same,
boots the same (a booting agent's turn state too), the live still live, an hc-blocked agent still blocked or holding no
pending task -/
theorem l3_of {s s' : State} (h : L3I s) (ht : ∀ u, s'.tk u = s.tk u) (hp : ∀ t, t ∈ s'.pend → t ∈ s.pend)
    (hx : ∀ o, Ext s s' o)
    (hb : ∀ a, (s'.agt a).boot = true → (s.agt a).boot = true ∧ (s'.agt a).st = (s.agt a).st ∧ (s'.agt a).waiter = (s.agt a).waiter)
    (hb2 : ∀ a, (s.agt a).boot = true → (s'.agt a).boot = true ∨ ∀ t ∈ s'.pend, held (s'.tk t) a = false)
    (hl : ∀ a, (s.agt a).live = true → (s'.agt a).live = true)
    (hbl : ∀ a, (s.agt a).st = .blocked → (s'.agt a).st = .blocked ∨ ∀ t ∈ s'.pend, held (s'.tk t) a = false) : L3I s' := by
  obtain ⟨hB, hH, hP⟩ := h
  refine ⟨fun a ha => ?_, fun u a hu => ?_, fun t htp => ?_⟩
  · obtain ⟨ha0, e1, e2⟩ := hb a ha
    obtain ⟨h1, h2, h3⟩ := hB a ha0
    simp only [ht]
    exact ⟨by rw [e1]; exact h1, by rw [e2]; exact h2, h3⟩
  · rw [ht] at hu; exact hl a (hH u a hu)
  · have hpt := hP t (hp t htp)
    refine ⟨by rw [ht]; exact hpt.1, fun o ho => ?_⟩
    rw [ht] at ho
    rcases hpt.2 o ho with e | ⟨e1, e2⟩
    · rcases hb2 o e with e' | e'
      · exact Or.inl e'
      · have := e' t htp; rw [ht] at this; rw [this] at ho; cases ho
    · right
      refine ⟨ansIn_ext (hx o) e1, fun hbk => ?_⟩
      rw [ht] at hbk ⊢
      refine ⟨(e2 hbk).1, ?_⟩
      rcases hbl o (e2 hbk).2 with e | e
      · exact e
      · have := e t htp; rw [ht] at this; rw [this] at ho; cases ho

theorem l3_setAg {s : State} {a : Nat} {f : Agent → Agent} (h : L3I s)
    (h1 : (f (s.agt a)).boot = (s.agt a).boot)
    (h2 : (s.agt a).boot = true → (f (s.agt a)).st = (s.agt a).st ∧ (f (s.agt a)).waiter = (s.agt a).waiter)
    (h3 : (s.agt a).live = true → (f (s.agt a)).live = true)
    (h4 : (s.agt a).st = .blocked → (f (s.agt a)).st = .blocked ∨ ∀ t ∈ s.pend, held (s.tk t) a = false) :
    L3I (setAg s a f) := by
  refine l3_of h (fun u => setAg_tk ..) (fun t ht => by simpa using ht) (fun o => ext_frame (by simp) (by simp) o)
    (fun b hb => ?_) (fun b hb => Or.inl ?_) (fun b hb => ?_) (fun b hb => ?_)
  all_goals simp only [agt_setAg, setAg_pend, setAg_tk] at hb ⊢
  all_goals split
  all_goals (try split at hb)
  all_goals first
    | (rename_i hh; obtain ⟨rfl, _⟩ := hh; first
        | exact ⟨by rw [← h1]; exact hb, h2 (by rw [← h1]; exact hb)⟩
        | (rw [h1]; exact hb) | exact h3 hb | exact h4 hb)
    | (rename_i hh _; obtain ⟨rfl, _⟩ := hh; first
        | exact ⟨by rw [← h1]; exact hb, h2 (by rw [← h1]; exact hb)⟩ | (rw [h1]; exact hb))
    | exact ⟨hb, rfl, rfl⟩ | exact hb | exact Or.inl hb
    | (rename_i hh; exact absurd hh ‹_›)
    | skip

theorem l3_post {s : State} {m : Msg} (h : L3I s) : L3I (post s m) :=
  l3_of h (fun u => post_tk ..) (fun t ht => by simpa using ht) (fun o => ext_post s m o) (fun b hb => by simpa using hb)
    (fun b hb => Or.inl (by simpa using hb)) (fun b hb => by simpa using hb) (fun b hb => Or.inl (by simpa using hb))

theorem l3_git {s : State} {g : Git} (h : L3I s) : L3I { s with git := g } := h

theorem deliver_live (s : State) (a b : Nat) : ((deliver s a).agt b).live = (s.agt b).live := by simp [Agent.live]

theorem pend_deliver_sub {s : State} {a t : Nat} (h : t ∈ (deliver s a).pend) : t ∈ s.pend :=
  Classical.byContradiction fun hn => showAll_pend_sub a t (unread s a) s hn h

/-- the holder of a pending answer that reads its inbox sees it -/
theorem deliver_clears' {s : State} {o t : Nat} (ho : (s.tk t).owner = some o) (ha : AnsIn s o t) : t ∉ (deliver s o).pend := by
  obtain ⟨i, hi, hk, ht⟩ := ha
  exact showAll_clears o t i (unread s o) s hi hk ht ho

theorem l3_deliver {s : State} {a : Nat} (h : L3I s) : L3I (deliver s a) := by
  obtain ⟨hB, hH, hP⟩ := h
  refine ⟨fun b hb => ?_, fun u b hu => ?_, fun t htp => ?_⟩
  · simp only [deliver_boot] at hb
    obtain ⟨h1, h2, h3⟩ := hB b hb
    simp only [deliver_st, deliver_waiter, deliver_tk]; exact ⟨h1, h2, h3⟩
  · simp only [deliver_tk] at hu; rw [deliver_live]; exact hH u b hu
  · have hp := hP t (pend_deliver_sub htp)
    simp only [deliver_tk, deliver_boot, deliver_st]
    refine ⟨hp.1, fun o ho => ?_⟩
    rcases hp.2 o ho with e | ⟨e1, e2⟩
    · exact Or.inl e
    · by_cases hoa : o = a
      · subst hoa; exact absurd htp (deliver_clears' (held_owner ho) e1)
      · exact Or.inr ⟨ansIn_ext (ext_deliver_ne s (fun e => hoa e.symm)) e1, e2⟩

/-- after an agent not booting reads its inbox, it holds no task whose answer is pending -/
theorem deliver_frees {s : State} {a : Nat} (h : L3I s) (hb : (s.agt a).boot = false) :
    ∀ t ∈ (deliver s a).pend, held ((deliver s a).tk t) a = false := by
  intro t htp
  rw [deliver_tk]
  cases hh : held (s.tk t) a
  · rfl
  · exfalso
    rcases (h.2.2 t (pend_deliver_sub htp)).2 a hh with e | ⟨e1, _⟩
    · rw [hb] at e; cases e
    · exact deliver_clears' (held_owner hh) e1 htp

theorem takes_pend_sub {c : Cfg} {s : State} {a u t : Nat} (h : t ∈ (takes c s a u).pend) : t ∈ s.pend := by
  unfold takes at h; simp only [] at h
  split at h
  · simp only [List.mem_filter, setAg_pend] at h; exact h.1
  · simpa using h

theorem takes_clears {c : Cfg} {s : State} {a u : Nat} (hao : c.answerOnTask = true) (hans : (s.tk u).answer = true) :
    u ∉ (takes c s a u).pend := by
  unfold takes; simp [hao, hans]

theorem takes_agt' (c : Cfg) (s : State) (a u b : Nat) :
    ((takes c s a u).agt b).boot = (s.agt b).boot ∧ ((takes c s a u).agt b).st = (s.agt b).st ∧
    ((takes c s a u).agt b).waiter = (s.agt b).waiter ∧ ((takes c s a u).agt b).live = (s.agt b).live := by
  obtain ⟨bl, e⟩ := takes_agt c s a u b; rw [e]; simp [Agent.live]

theorem l3_takes {c : Cfg} {s : State} {a u : Nat} (h : L3I s) : L3I (takes c s a u) :=
  l3_of h (fun v => takes_tk ..) (fun t ht => takes_pend_sub ht) (fun o => ext_frame (by simp) (by simp) o)
    (fun b hb => by rw [(takes_agt' c s a u b).1] at hb; exact ⟨hb, (takes_agt' c s a u b).2.1, (takes_agt' c s a u b).2.2.1⟩)
    (fun b hb => Or.inl (by rw [(takes_agt' c s a u b).1]; exact hb))
    (fun b hb => by rw [(takes_agt' c s a u b).2.2.2]; exact hb) (fun b hb => Or.inl (by rw [(takes_agt' c s a u b).2.1]; exact hb))

theorem endAgent_held {s : State} {a u b : Nat} (hu : held ((endAgent s a).tk u) b = true) :
    held (s.tk u) b = true ∧ b ≠ a ∧ (endAgent s a).tk u = s.tk u := by
  rw [endAgent_tk] at hu ⊢
  split at hu
  · simp [held] at hu
  · rename_i hh
    exact ⟨hu, by rintro rfl; exact hh hu, by rw [if_neg hh]⟩

theorem endAgent_agt_ne {s : State} {a b : Nat} (hb : b ≠ a) : (endAgent s a).agt b = s.agt b := by
  rw [endAgent_agt, if_neg (fun hh => hb hh.1.symm)]

theorem endAgent_boot_self (s : State) (a : Nat) : ((endAgent s a).agt a).boot = false := by
  rw [endAgent_agt]; split
  · rfl
  · rename_i hh
    have : s.ag.length ≤ a := by simp at hh; omega
    rw [agt_of_ge this]; rfl

theorem l3_endAgent {s : State} {a : Nat} (h : L3I s) : L3I (endAgent s a) := by
  obtain ⟨hB, hH, hP⟩ := h
  refine ⟨fun b hb => ?_, fun u b hu => ?_, fun t htp => ?_⟩
  · have hba : b ≠ a := by rintro rfl; rw [endAgent_boot_self] at hb; cases hb
    rw [endAgent_agt_ne hba] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hB b hb
    refine ⟨h1, h2, fun u hu => ?_⟩
    obtain ⟨hu1, _, hu3⟩ := endAgent_held hu
    rw [hu3]
    obtain ⟨g1, g2, g3⟩ := h3 u hu1
    exact ⟨g1, g2, fun v hv => g3 v (endAgent_held hv).1⟩
  · obtain ⟨hu1, hu2, _⟩ := endAgent_held hu
    rw [endAgent_agt_ne hu2]; exact hH u b hu1
  · rw [endAgent_pend] at htp
    have hpt := hP t htp
    refine ⟨?_, fun o ho => ?_⟩
    · rw [endAgent_tk]; split
      · exact hpt.1
      · exact hpt.1
    · obtain ⟨ho1, ho2, ho3⟩ := endAgent_held ho
      rw [ho3, endAgent_agt_ne ho2]
      rcases hpt.2 o ho1 with e | ⟨e1, e2⟩
      · exact Or.inl e
      · exact Or.inr ⟨ansIn_ext (ext_frame (by simp) (by simp) o) e1, e2⟩

/-- a change of one task that keeps every holder's view of it: whoever holds it after held it before, at the same state
and hc flag, a booting holder keeps its lease; the answer stays -/
theorem l3_setTask {s : State} {u : Nat} {f : Task → Task} (h : L3I s)
    (hf : ∀ o, held (f (s.tk u)) o = true → held (s.tk u) o = true ∧ (f (s.tk u)).st = (s.tk u).st ∧
      (f (s.tk u)).hcq = (s.tk u).hcq ∧ ((s.agt o).boot = true → (f (s.tk u)).lease = true))
    (hans : (s.tk u).answer = true → (f (s.tk u)).answer = true) : L3I (setTask s u f) := by
  obtain ⟨hB, hH, hP⟩ := h
  have key : ∀ v o, held ((setTask s u f).tk v) o = true → held (s.tk v) o = true ∧ ((setTask s u f).tk v).st = (s.tk v).st ∧
      ((setTask s u f).tk v).hcq = (s.tk v).hcq ∧ ((s.agt o).boot = true → ((setTask s u f).tk v).lease = true ∧ (s.tk v).lease = true) := by
    intro v o hv
    rcases tk_setTask_or s u v f with e | ⟨rfl, e⟩
    · rw [e] at hv ⊢
      refine ⟨hv, rfl, rfl, fun hb => ?_⟩
      have := ((hB o hb).2.2 v hv).2.1; exact ⟨this, this⟩
    · rw [e] at hv ⊢
      obtain ⟨g1, g2, g3, g4⟩ := hf o hv
      exact ⟨g1, g2, g3, fun hb => ⟨g4 hb, ((hB o hb).2.2 v g1).2.1⟩⟩
  refine ⟨fun a ha => ?_, fun v a hv => ?_, fun t htp => ?_⟩
  · simp only [setTask_agt] at ha ⊢
    obtain ⟨h1, h2, h3⟩ := hB a ha
    refine ⟨h1, h2, fun v hv => ?_⟩
    obtain ⟨k1, k2, _, k4⟩ := key v a hv
    obtain ⟨g1, _, g3⟩ := h3 v k1
    exact ⟨by rw [k2]; exact g1, (k4 ha).1, fun w hw => g3 w (key w a hw).1⟩
  · simp only [setTask_agt]; exact hH v a (key v a hv).1
  · rw [setTask_pend] at htp
    have hpt := hP t htp
    refine ⟨?_, fun o ho => ?_⟩
    · rcases tk_setTask_or s u t f with e | ⟨rfl, e⟩
      · rw [e]; exact hpt.1
      · rw [e]; exact hans hpt.1
    · obtain ⟨k1, k2, k3, _⟩ := key t o ho
      simp only [setTask_agt]
      rcases hpt.2 o k1 with e | ⟨e1, e2⟩
      · exact Or.inl e
      · exact Or.inr ⟨ansIn_ext (ext_frame (by simp) (by simp) o) e1, by rw [k2, k3]; exact e2⟩

/-- a change of one task held by an agent that is not booting, and that only it can hold after: an answer pending on it
stays in its inbox, so the hc flag and the agent's state must agree when the task is left blocked -/
theorem l3_setTask_nb {s : State} {u o : Nat} {f : Task → Task} (h : L3I s) (ho : held (s.tk u) o = true)
    (hb : (s.agt o).boot = false) (hheld : ∀ o', held (f (s.tk u)) o' = true → o' = o)
    (hans : (s.tk u).answer = true → (f (s.tk u)).answer = true)
    (hst : u ∈ s.pend → (f (s.tk u)).st = .blocked → (f (s.tk u)).hcq = true ∧ (s.agt o).st = .blocked) :
    L3I (setTask s u f) := by
  obtain ⟨hB, hH, hP⟩ := h
  have key : ∀ v o', held ((setTask s u f).tk v) o' = true → (v = u ∧ o' = o) ∨ ((setTask s u f).tk v = s.tk v ∧ held (s.tk v) o' = true) := by
    intro v o' hv
    rcases tk_setTask_or s u v f with e | ⟨rfl, e⟩
    · rw [e] at hv ⊢; exact Or.inr ⟨rfl, hv⟩
    · rw [e] at hv; exact Or.inl ⟨rfl, hheld o' hv⟩
  refine ⟨fun a ha => ?_, fun v a hv => ?_, fun t htp => ?_⟩
  · simp only [setTask_agt] at ha ⊢
    have hao : a ≠ o := by rintro rfl; rw [hb] at ha; cases ha
    obtain ⟨h1, h2, h3⟩ := hB a ha
    refine ⟨h1, h2, fun v hv => ?_⟩
    rcases key v a hv with ⟨_, e⟩ | ⟨e, hv'⟩
    · exact absurd e hao
    · obtain ⟨g1, g2, g3⟩ := h3 v hv'
      refine ⟨by rw [e]; exact g1, by rw [e]; exact g2, fun w hw => ?_⟩
      rcases key w a hw with ⟨_, e'⟩ | ⟨_, hw'⟩
      · exact absurd e' hao
      · exact g3 w hw'
  · simp only [setTask_agt]
    rcases key v a hv with ⟨rfl, rfl⟩ | ⟨_, hv'⟩
    · exact hH _ _ ho
    · exact hH v a hv'
  · rw [setTask_pend] at htp
    have hpt := hP t htp
    refine ⟨?_, fun o' ho' => ?_⟩
    · rcases tk_setTask_or s u t f with e | ⟨rfl, e⟩
      · rw [e]; exact hpt.1
      · rw [e]; exact hans hpt.1
    · simp only [setTask_agt]
      rcases key t o' ho' with ⟨rfl, rfl⟩ | ⟨e, hv'⟩
      · rcases hpt.2 _ ho with e | ⟨e1, _⟩
        · rw [hb] at e; cases e
        · refine Or.inr ⟨ansIn_ext (ext_frame (by simp) (by simp) _) e1, fun hbk => ?_⟩
          rw [tk_setTask_self (by intro ha; simp [held, ha] at ho)] at hbk ⊢
          exact hst htp hbk
      · rw [e]
        rcases hpt.2 o' hv' with e' | ⟨e1, e2⟩
        · exact Or.inl e'
        · exact Or.inr ⟨ansIn_ext (ext_frame (by simp) (by simp) o') e1, e2⟩

-- ---------- the actions that need more than a frame ----------

theorem nb_of_st {s : State} {a : Nat} (h : L3I s) (hst : (s.agt a).st ≠ .idle) : (s.agt a).boot = false := by
  cases hb : (s.agt a).boot
  · rfl
  · exact absurd (h.1 a hb).1 hst

theorem lt_of_st {s : State} {a : Nat} (hst : (s.agt a).st ≠ .unborn) : a < s.ag.length := by
  refine Classical.byContradiction fun hl => ?_
  rw [agt_of_ge (Nat.le_of_not_lt hl)] at hst; exact hst rfl

theorem setTask_len (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).task.length = s.task.length := by
  unfold setTask; split <;> simp

theorem mem_tasks {c : Cfg} {s : State} {t : Nat} (hl : s.task.length = c.ntasks) (h : (s.tk t).st ≠ .absent) : t ∈ c.tasks := by
  obtain ⟨h0, h1⟩ := tk_in_range h
  simp only [Cfg.tasks, List.mem_range'_1]; omega

theorem spawnFor_tlen {c : Cfg} {pl : List Nat} {x : State} {t : Nat} : (spawnFor c pl x t).task.length = x.task.length := by
  unfold spawnFor; split
  · split
    · unfold claimed; rw [setTask_len]; rfl
    · rfl
  · rfl

theorem tl_tickOf {c : Cfg} {s : State} (h : s.task.length = c.ntasks) : (tickOf c s).task.length = c.ntasks := by
  refine tick_inv (fun x => x.task.length = c.ntasks) (fun x t hx => ?_) (fun x hx => by simpa using hx)
    (fun x a hx => by simpa [endAgent, releaseAll] using hx) (fun x a pl hx => by simpa using hx)
    (fun pl x t hx _ => by rw [spawnFor_tlen]; exact hx) h
  unfold reapTask; simp only []
  split
  · split
    · simp [setTask_len, hx]
    · exact hx
  · exact hx

/-- every reachable state has `ntasks` task records -/
theorem tl_of_reachable {c : Cfg} {s : State} (h : Reachable c s) : s.task.length = c.ntasks := by
  refine reachable_induct (P := fun s => s.task.length = c.ntasks) (by simp [init]) ?_ h
  intro s s' act _ hs hstep
  open_step hstep
  case tick => obtain ⟨_, rfl⟩ := hstep; exact tl_tickOf hs
  case unblock t₀ =>
    split at hstep
    · rw [when_eq_some] at hstep; obtain ⟨_, rfl⟩ := hstep; simp [setTask_len, hs]
    · cases hstep
  all_goals (obtain ⟨_, rfl⟩ := hstep)
  all_goals (try split)
  all_goals (simp [setTask_len, unbelieve, awake, claimed, endAgent, releaseAll, hs])

theorem l3_claim {c : Cfg} {s : State} {a u : Nat} (hao : c.answerOnTask = true) (h : L3I s)
    (hw : (s.agt a).st = .working) (hopn : (s.tk u).st = .opn) : L3I (takes c (claimed s a u) a u) := by
  have hnb := nb_of_st h (by rw [hw]; decide)
  obtain ⟨hB, hH, hP⟩ := h
  have hne : (s.tk u).st ≠ .absent := by rw [hopn]; decide
  generalize hz : takes c (claimed s a u) a u = z
  have tu : (z.tk u).owner = some a ∧ (z.tk u).st = .claimed := by
    rw [← hz, takes_tk]; unfold claimed; rw [tk_setTask_self hne]; exact ⟨rfl, rfl⟩
  have tv : ∀ v, v ≠ u → z.tk v = s.tk v := fun v hv => by rw [← hz, takes_tk]; unfold claimed; exact tk_setTask_ne hv
  have ag : ∀ b, (z.agt b).boot = (s.agt b).boot ∧ (z.agt b).st = (s.agt b).st ∧ (z.agt b).waiter = (s.agt b).waiter ∧
      (z.agt b).live = (s.agt b).live := by
    intro b; rw [← hz]; have := takes_agt' c (claimed s a u) a u b; simp only [claimed_agt] at this; exact this
  have key : ∀ v b, held (z.tk v) b = true → (v = u ∧ b = a) ∨ (v ≠ u ∧ held (s.tk v) b = true) := by
    intro v b hv
    by_cases e : v = u
    · subst e; left; exact ⟨rfl, Option.some.inj ((held_owner hv).symm.trans tu.1)⟩
    · right; rw [tv v e] at hv; exact ⟨e, hv⟩
  have hext : ∀ o, Ext s z o := fun o => ext_frame (by rw [← hz]; simp) (by rw [← hz]; simp) o
  have hpu : u ∉ z.pend := by
    intro hu
    have hu' : u ∈ s.pend := by rw [← hz] at hu; simpa using takes_pend_sub hu
    have := takes_clears (s := claimed s a u) (a := a) (u := u) hao (by unfold claimed; rw [tk_setTask_self hne]; exact (hP u hu').1)
    rw [hz] at this; exact this hu
  refine ⟨fun b hb => ?_, fun v b hv => ?_, fun t htp => ?_⟩
  · rw [(ag b).1] at hb
    have hba : b ≠ a := by rintro rfl; rw [hnb] at hb; cases hb
    obtain ⟨h1, h2, h3⟩ := hB b hb
    refine ⟨by rw [(ag b).2.1]; exact h1, by rw [(ag b).2.2.1]; exact h2, fun v hv => ?_⟩
    rcases key v b hv with ⟨_, e⟩ | ⟨e, hv'⟩
    · exact absurd e hba
    · obtain ⟨g1, g2, g3⟩ := h3 v hv'
      rw [tv v e]
      refine ⟨g1, g2, fun w hw => ?_⟩
      rcases key w b hw with ⟨_, e'⟩ | ⟨_, hw'⟩
      · exact absurd e' hba
      · exact g3 w hw'
  · rw [(ag b).2.2.2]
    rcases key v b hv with ⟨_, rfl⟩ | ⟨_, hv'⟩
    · exact live_of_st (Or.inl hw)
    · exact hH v b hv'
  · have htu : t ≠ u := by rintro rfl; exact hpu htp
    have hts : t ∈ s.pend := by rw [← hz] at htp; simpa using takes_pend_sub htp
    have hpt := hP t hts
    rw [tv t htu]
    refine ⟨hpt.1, fun o ho => ?_⟩
    rcases hpt.2 o ho with e | ⟨e1, e2⟩
    · left; rw [(ag o).1]; exact e
    · right; refine ⟨ansIn_ext (hext o) e1, ?_⟩; rw [(ag o).2.1]; exact e2

theorem l3_block {s : State} {a u : Nat} (h : L3I s) (hw : (s.agt a).st = .working) (hu0 : unread s a = [])
    (ho1 : (s.tk u).st = .claimed) (ho2 : (s.tk u).owner = some a) :
    L3I (setTask s u ({ · with st := .blocked })) := by
  have hnb := nb_of_st h (by rw [hw]; decide)
  have hh : held (s.tk u) a = true := by simp [held, ho1, ho2]
  refine l3_setTask_nb h hh hnb (fun o' h' => Option.some.inj ((held_owner h').symm.trans ho2)) id (fun hu _ => ?_)
  exfalso
  rcases (h.2.2 u hu).2 a hh with e | ⟨⟨i, hi, _⟩, _⟩
  · rw [hnb] at e; cases e
  · rw [hu0] at hi; cases hi

theorem l3_hcPrompt {c : Cfg} {s : State} {a : Nat} (h : L3I s) (hw : (s.agt a).st = .working) :
    L3I (setTask (setAg s a ({ · with st := .blocked })) (firstClaimed c s a) ({ · with st := .blocked, hcq := true })) := by
  have hnb := nb_of_st h (by rw [hw]; decide)
  have hlt : a < s.ag.length := lt_of_st (by rw [hw]; decide)
  have h1 : L3I (setAg s a ({ · with st := .blocked })) :=
    l3_setAg h rfl (fun hb => by rw [hnb] at hb; cases hb) (fun _ => by simp [Agent.live]) (fun _ => Or.inl rfl)
  by_cases h0 : firstClaimed c s a = 0
  · rw [h0]; simpa [setTask] using h1
  · obtain ⟨hst, ho⟩ := fc_owns h0
    have hag : (setAg s a ({ · with st := .blocked })).agt a = { s.agt a with st := .blocked } := by rw [agt_setAg]; simp [hlt]
    refine l3_setTask_nb h1 (o := a) (by simp [held, hst, ho]) (by rw [hag]; exact hnb)
      (fun o' h' => Option.some.inj ((held_owner h').symm.trans (by simpa using ho))) id (fun _ _ => ⟨rfl, by rw [hag]⟩)

theorem l3_hcClear {s : State} {a : Nat} (h : L3I s) (hbl : (s.agt a).st = .blocked) :
    L3I (setAg (deliver { s with task := s.task.map fun k =>
      if (k.owner == some a && k.st == .blocked && k.hcq) = true then { k with st := .claimed, hcq := false, lease := true } else k } a) a
      ({ · with st := .working })) := by
  have hnb := nb_of_st h (by rw [hbl]; decide)
  obtain ⟨hB, hH, hP⟩ := h
  generalize hg : (fun k : Task => if (k.owner == some a && k.st == .blocked && k.hcq) = true then
      { k with st := .claimed, hcq := false, lease := true } else k) = g
  generalize hx : ({ s with task := s.task.map g } : State) = x
  have tx : ∀ v, x.tk v = g (s.tk v) := fun v => by
    rw [← hx]; exact tk_map (by rw [← hg]; simp) rfl v
  have ax : ∀ b, x.agt b = s.agt b := fun b => by rw [← hx]; rfl
  have hxp : x.pend = s.pend := by rw [← hx]
  have hxe : ∀ o, Ext s x o := fun o => ext_frame (by rw [← hx]) (by rw [← hx]) o
  have key : ∀ v o, held (x.tk v) o = true → held (s.tk v) o = true ∧
      (x.tk v = s.tk v ∨ (o = a ∧ (x.tk v).st = .claimed ∧ (x.tk v).lease = true ∧ (x.tk v).answer = (s.tk v).answer)) := by
    intro v o hv
    rw [tx, ← hg] at hv ⊢
    simp only [] at hv ⊢
    split at hv
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have : o = a := Option.some.inj ((held_owner hv).symm.trans hc.1.1)
      subst this
      refine ⟨by simp [held, hc.1.1, hc.1.2], Or.inr ⟨rfl, ?_⟩⟩
      rw [if_pos (by simp [hc.1.1, hc.1.2, hc.2])]; exact ⟨rfl, rfl, rfl⟩
    · rename_i hc
      rw [if_neg hc]; exact ⟨hv, Or.inl rfl⟩
  have hX : L3I x := by
    refine ⟨fun b hb => ?_, fun v b hv => ?_, fun t htp => ?_⟩
    · rw [ax] at hb ⊢
      have hba : b ≠ a := by rintro rfl; rw [hnb] at hb; cases hb
      obtain ⟨h1, h2, h3⟩ := hB b hb
      refine ⟨h1, h2, fun v hv => ?_⟩
      rcases key v b hv with ⟨hv', e | ⟨e, _⟩⟩
      · rw [e]
        obtain ⟨g1, g2, g3⟩ := h3 v hv'
        refine ⟨g1, g2, fun w hw => ?_⟩
        rcases key w b hw with ⟨hw', _⟩
        exact g3 w hw'
      · exact absurd e hba
    · rw [ax]; exact hH v b (key v b hv).1
    · rw [hxp] at htp
      have hpt := hP t htp
      have hans : (x.tk t).answer = true := by
        rw [tx, ← hg]; simp only []; split
        · exact hpt.1
        · exact hpt.1
      refine ⟨hans, fun o ho => ?_⟩
      rw [ax]
      rcases key t o ho with ⟨ho', e | ⟨rfl, e1, _, _⟩⟩
      · rw [e]
        rcases hpt.2 o ho' with e' | ⟨e1, e2⟩
        · exact Or.inl e'
        · exact Or.inr ⟨ansIn_ext (hxe o) e1, e2⟩
      · rcases hpt.2 _ ho' with e' | ⟨e1', _⟩
        · rw [hnb] at e'; cases e'
        · exact Or.inr ⟨ansIn_ext (hxe _) e1', fun hb => by rw [e1] at hb; cases hb⟩
  have hD := l3_deliver (a := a) hX
  have hfree := deliver_frees hX (by rw [ax]; exact hnb)
  exact l3_setAg hD rfl (fun hb => by rw [deliver_boot, ax, hnb] at hb; cases hb) (fun _ => by simp [Agent.live])
    (fun _ => Or.inr hfree)

theorem fc_eq {c : Cfg} {s : State} {a t : Nat} (ht : t ∈ c.tasks) (ho : ownsClaimed s a t = true)
    (hu : ∀ v, ownsClaimed s a v = true → v = t) : firstClaimed c s a = t := by
  unfold firstClaimed
  cases hf : c.tasks.find? (ownsClaimed s a) with
  | none => exact absurd ho (List.find?_eq_none.mp hf t ht)
  | some v => simp only [Option.getD_some]; exact hu v (List.find?_some hf)

/-- a booting agent's task is the one its first turn reads -/
theorem fc_booting {c : Cfg} {s : State} {a t : Nat} (htl : s.task.length = c.ntasks) (h : L3I s) (hb : (s.agt a).boot = true)
    (ht : held (s.tk t) a = true) : firstClaimed c s a = t := by
  obtain ⟨_, _, h3⟩ := h.1 a hb
  obtain ⟨g1, _, g3⟩ := h3 t ht
  have hne : (s.tk t).st ≠ .absent := by rw [g1]; decide
  refine fc_eq (mem_tasks htl hne) (by simp [ownsClaimed, g1, held_owner ht]) (fun v hv => g3 v ?_)
  simp only [ownsClaimed, Bool.and_eq_true, beq_iff_eq] at hv; simp [held, hv.1, hv.2]

theorem l3_boot_core {s z : State} {a : Nat} (h : L3I s)
    (ht : ∀ v, z.tk v = s.tk v) (hp : ∀ t ∈ z.pend, t ∈ s.pend) (hfree : ∀ t ∈ z.pend, held (s.tk t) a = false)
    (hag : ∀ b, b ≠ a → (z.agt b).boot = (s.agt b).boot ∧ (z.agt b).st = (s.agt b).st ∧ (z.agt b).waiter = (s.agt b).waiter ∧
      (z.agt b).live = (s.agt b).live)
    (ha : (z.agt a).boot = false ∧ (z.agt a).live = true) (hx : ∀ o, o ≠ a → Ext s z o) : L3I z := by
  obtain ⟨hB, hH, hP⟩ := h
  refine ⟨fun b hb => ?_, fun v b hv => ?_, fun t htp => ?_⟩
  · have hba : b ≠ a := by rintro rfl; rw [ha.1] at hb; cases hb
    obtain ⟨e1, e2, e3, _⟩ := hag b hba
    rw [e1] at hb
    simp only [ht, e2, e3]; exact hB b hb
  · rw [ht] at hv
    by_cases hba : b = a
    · subst hba; exact ha.2
    · rw [(hag b hba).2.2.2]; exact hH v b hv
  · have hpt := hP t (hp t htp)
    simp only [ht]
    refine ⟨hpt.1, fun o ho => ?_⟩
    have hoa : o ≠ a := by rintro rfl; rw [hfree t htp] at ho; cases ho
    obtain ⟨e1, e2, _, _⟩ := hag o hoa
    rw [e1, e2]
    rcases hpt.2 o ho with e | ⟨e1', e2'⟩
    · exact Or.inl e
    · exact Or.inr ⟨ansIn_ext (hx o hoa) e1', e2'⟩

theorem l3_boot {c : Cfg} {s : State} {a : Nat} (hao : c.answerOnTask = true) (htl : s.task.length = c.ntasks) (h : L3I s)
    (hb : (s.agt a).boot = true) :
    L3I (if firstClaimed c s a > 0 then takes c (setAg (deliver s a) a ({ · with st := .working, boot := false })) a (firstClaimed c s a)
      else setAg (deliver s a) a ({ · with st := .working, boot := false })) := by
  have hlt : a < s.ag.length := by
    refine Classical.byContradiction fun hl => ?_
    rw [agt_of_ge (Nat.le_of_not_lt hl)] at hb; cases hb
  generalize hX : setAg (deliver s a) a ({ · with st := .working, boot := false }) = X
  have hxa : (X.agt a).boot = false ∧ (X.agt a).live = true := by
    rw [← hX, agt_setAg]; simp [hlt, Agent.live]
  have hxb : ∀ b, b ≠ a → (X.agt b).boot = (s.agt b).boot ∧ (X.agt b).st = (s.agt b).st ∧ (X.agt b).waiter = (s.agt b).waiter ∧
      (X.agt b).live = (s.agt b).live := by
    intro b hb'; rw [← hX, agt_setAg, if_neg (fun hh => hb' hh.1.symm)]; simp [Agent.live]
  have hxe : ∀ o, o ≠ a → Ext s X o := fun o ho => by
    rw [← hX]; exact ext_trans (ext_deliver_ne s (fun e => ho e.symm)) (ext_frame (by simp) (by simp) o)
  have hxp : ∀ t ∈ X.pend, t ∈ s.pend := fun t ht => pend_deliver_sub (by rw [← hX] at ht; simpa using ht)
  have hxt : ∀ v, X.tk v = s.tk v := fun v => by rw [← hX]; simp
  split
  · rename_i hpos
    refine l3_boot_core h (fun v => by rw [takes_tk]; exact hxt v) (fun t ht => hxp t (takes_pend_sub ht)) (fun t ht => ?_)
      (fun b hb' => by have := takes_agt' c X a (firstClaimed c s a) b; rw [this.1, this.2.1, this.2.2.1, this.2.2.2]; exact hxb b hb')
      (by have := takes_agt' c X a (firstClaimed c s a) a; rw [this.1, this.2.2.2]; exact hxa)
      (fun o ho => ext_trans (hxe o ho) (ext_frame (by simp) (by simp) o))
    cases hh : held (s.tk t) a
    · rfl
    · exfalso
      have e := fc_booting htl h hb hh
      have hts := hxp t (takes_pend_sub ht)
      rw [e] at ht
      exact takes_clears hao (by rw [hxt]; exact (h.2.2 t hts).1) ht
  · rename_i hpos
    refine l3_boot_core h hxt hxp (fun t ht => ?_) hxb hxa hxe
    cases hh : held (s.tk t) a
    · rfl
    · exfalso
      have e := fc_booting htl h hb hh
      have : (s.tk t).st ≠ .absent := by
        obtain ⟨_, _, h3⟩ := h.1 a hb; rw [(h3 t hh).1]; decide
      have := (tk_in_range this).1
      omega

theorem l3_spawn_core {x y : State} {a u : Nat} (h : L3I x) (hopn : (x.tk u).st = .opn) (hnl : (x.agt a).live = false)
    (hyt : y.task = x.task) (hyp : y.pend = x.pend) (hyl : y.log = x.log)
    (hyb : ∀ b, b ≠ a → y.agt b = x.agt b ∧ y.cur b = x.cur b)
    (hya : (y.agt a).st = .idle ∧ (y.agt a).boot = true ∧ (y.agt a).waiter = false) : L3I (claimed y a u) := by
  obtain ⟨hB, hH, hP⟩ := h
  have hne : (y.tk u).st ≠ .absent := by rw [tk_of_task hyt, hopn]; decide
  have tu : ((claimed y a u).tk u).owner = some a ∧ ((claimed y a u).tk u).st = .claimed ∧
      ((claimed y a u).tk u).lease = true ∧ ((claimed y a u).tk u).answer = (x.tk u).answer := by
    unfold claimed; rw [tk_setTask_self hne, tk_of_task hyt]; exact ⟨rfl, rfl, rfl, rfl⟩
  have tv : ∀ v, v ≠ u → (claimed y a u).tk v = x.tk v := fun v hv => by
    unfold claimed; rw [tk_setTask_ne hv, tk_of_task hyt]
  have nh : ∀ v b, held (x.tk v) b = true → b ≠ a := by
    rintro v b hv rfl; rw [hH v b hv] at hnl; cases hnl
  have key : ∀ v b, held ((claimed y a u).tk v) b = true → (v = u ∧ b = a) ∨ (v ≠ u ∧ held (x.tk v) b = true ∧ b ≠ a) := by
    intro v b hv
    by_cases e : v = u
    · subst e; left; exact ⟨rfl, Option.some.inj ((held_owner hv).symm.trans tu.1)⟩
    · right; rw [tv v e] at hv; exact ⟨e, hv, nh v b hv⟩
  refine ⟨fun b hb => ?_, fun v b hv => ?_, fun t htp => ?_⟩
  · rw [claimed_agt] at hb ⊢
    by_cases hba : b = a
    · subst hba
      refine ⟨hya.1, hya.2.2, fun v hv => ?_⟩
      rcases key v b hv with ⟨rfl, _⟩ | ⟨_, _, hne'⟩
      · refine ⟨tu.2.1, tu.2.2.1, fun w hw => ?_⟩
        rcases key w _ hw with ⟨e, _⟩ | ⟨_, _, hne''⟩
        · exact e
        · exact absurd rfl hne''
      · exact absurd rfl hne'
    · rw [(hyb b hba).1] at hb ⊢
      obtain ⟨h1, h2, h3⟩ := hB b hb
      refine ⟨h1, h2, fun v hv => ?_⟩
      rcases key v b hv with ⟨_, e⟩ | ⟨e, hv', _⟩
      · exact absurd e hba
      · obtain ⟨g1, g2, g3⟩ := h3 v hv'
        rw [tv v e]
        refine ⟨g1, g2, fun w hw => ?_⟩
        rcases key w b hw with ⟨_, e'⟩ | ⟨_, hw', _⟩
        · exact absurd e' hba
        · exact g3 w hw'
  · rw [claimed_agt]
    rcases key v b hv with ⟨_, rfl⟩ | ⟨_, hv', hba⟩
    · exact live_of_st (Or.inr (Or.inl hya.1))
    · rw [(hyb b hba).1]; exact hH v b hv'
  · rw [claimed_pend, hyp] at htp
    have hpt := hP t htp
    by_cases htu : t = u
    · subst htu
      refine ⟨by rw [tu.2.2.2]; exact hpt.1, fun o ho => ?_⟩
      have : o = a := Option.some.inj ((held_owner ho).symm.trans tu.1)
      subst this
      exact Or.inl (by rw [claimed_agt]; exact hya.2.1)
    · rw [tv t htu]
      refine ⟨hpt.1, fun o ho => ?_⟩
      have hoa := nh t o ho
      rw [claimed_agt, (hyb o hoa).1]
      rcases hpt.2 o ho with e | ⟨e1, e2⟩
      · exact Or.inl e
      · refine Or.inr ⟨ansIn_ext ⟨⟨[], by simp [hyl]⟩, by simp only [State.cur, claimed_cursor]; exact (hyb o hoa).2⟩ e1, e2⟩

theorem l3_spawnFor {c : Cfg} {pl : List Nat} {x : State} {u : Nat} (h : L3I x) (hl : x.ag.length = c.nagents)
    (hopn : (x.tk u).st = .opn) : L3I (spawnFor c pl x u) := by
  unfold spawnFor
  split
  · rename_i a hna
    split
    · have hnl := nextAgent_not_live hna
      have hal : a < x.ag.length := by
        have := List.mem_of_find?_eq_some hna; simp [Cfg.agents] at this; omega
      refine l3_spawn_core h hopn hnl rfl rfl rfl (fun b hb => ⟨?_, ?_⟩) ?_
      · simp only [agt_mk, agt_def, agt_setAg, if_neg (fun hh : a = b ∧ _ => hb hh.1.symm)]
      · simp only [State.cur, getD_set]; simp [Ne.symm hb]
      · simp [agt_mk, agt_def, agt_setAg, hal]; rfl
    · exact h
  · exact h

theorem l3_reapTask {c : Cfg} {x : State} {u : Nat} (h : L3I x) : L3I (reapTask c x u) := by
  unfold reapTask; simp only []
  split
  · split
    · exact l3_post (l3_setTask h (fun o ho => by simp [held] at ho) id)
    · exact h
  · exact h

theorem l3_tickOf {c : Cfg} {s : State} (h : L3I s) (hl : s.ag.length = c.nagents) : L3I (tickOf c s) :=
  (tick_inv (fun y => L3I y ∧ y.ag.length = c.nagents)
    (fun x t hx => ⟨l3_reapTask hx.1, by simpa using hx.2⟩)
    (fun x hx => ⟨hx.1, by simpa using hx.2⟩)
    (fun x a hx => ⟨l3_endAgent hx.1, by simpa [endAgent] using hx.2⟩)
    (fun x a pl hx => ⟨l3_post (l3_setAg hx.1 rfl (fun _ => ⟨rfl, rfl⟩) id (fun hh => Or.inl hh)), by simpa using hx.2⟩)
    (fun pl x t hx ho => ⟨l3_spawnFor hx.1 hx.2 ho, by rw [spawnFor_len]; exact hx.2⟩) ⟨h, hl⟩).1

theorem l3_pend_cons {y : State} {u : Nat} (h : L3I y) (hans : (y.tk u).answer = true)
    (hu : ∀ o, held (y.tk u) o = true → (y.agt o).boot = true ∨
      (AnsIn y o u ∧ ((y.tk u).st = .blocked → (y.tk u).hcq = true ∧ (y.agt o).st = .blocked))) :
    L3I { y with pend := u :: y.pend } :=
  ⟨h.1, h.2.1, fun t ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨hans, hu⟩
    · exact h.2.2 t ht⟩

theorem l3_unblock {c : Cfg} {s : State} {u o : Nat} (hao : c.answerOnTask = true) (hcur : s.cur o ≤ s.log.length) (h : L3I s)
    (ho : (s.tk u).owner = some o) (hbl : (s.tk u).st = .blocked) :
    L3I { post (setTask s u fun k => { k with st := .claimed, lease := true, hcq := false, answer := k.answer || c.answerOnTask })
      ⟨none, o, false, .answer, u⟩ with
      pend := u :: (setTask s u fun k => { k with st := .claimed, lease := true, hcq := false, answer := k.answer || c.answerOnTask }).pend } := by
  have hheld : held (s.tk u) o = true := by simp [held, ho, hbl]
  have hnb : (s.agt o).boot = false := by
    cases hb : (s.agt o).boot
    · rfl
    · have := ((h.1 o hb).2.2 u hheld).1; rw [hbl] at this; cases this
  have hne : (s.tk u).st ≠ .absent := by rw [hbl]; decide
  have hx := l3_setTask_nb (f := fun k => { k with st := .claimed, lease := true, hcq := false, answer := k.answer || c.answerOnTask })
    h hheld hnb (fun o' h' => Option.some.inj ((held_owner h').symm.trans ho)) (fun ha => by simp [ha]) (fun _ hb => by simp at hb)
  have hy := l3_post (m := ⟨none, o, false, .answer, u⟩) hx
  have tu : (post (setTask s u fun k => { k with st := .claimed, lease := true, hcq := false, answer := k.answer || c.answerOnTask })
      ⟨none, o, false, .answer, u⟩).tk u = { s.tk u with st := .claimed, lease := true, hcq := false, answer := (s.tk u).answer || c.answerOnTask } := by
    rw [post_tk, tk_setTask_self hne]
  have hpc := l3_pend_cons (u := u) hy (by rw [tu]; simp [hao]) (fun o' ho' => Or.inr ⟨?_, fun hb => by rw [tu] at hb; cases hb⟩)
  · simpa using hpc
  · rw [tu] at ho'
    have : o' = o := Option.some.inj ((held_owner ho').symm.trans ho)
    subst this
    refine ⟨s.log.length + 1, ?_, ?_, ?_⟩
    · rw [mem_unread]
      simp only [State.cur, post_cursor, setTask_cursor, post_log_length, setTask_log, addressed, State.msg] at hcur ⊢
      refine ⟨by omega, Nat.le_refl _, ?_⟩
      simp [post]
    · simp [State.msg, post]
    · simp [State.msg, post]

-- ---------- every reachable state ----------

theorem l3_init (c : Cfg) : L3I (init c) := by
  have ht : ∀ u, (init c).tk u = default := by
    intro u; unfold State.tk; split
    · rfl
    · simp only [init, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
  have hb : ∀ a, ((init c).agt a).boot = false := by
    intro a; simp only [State.agt, init, List.getD_eq_getElem?_getD, List.getElem?_map]; cases c.agents[a]? <;> rfl
  refine ⟨fun a ha => ?_, fun u a hu => ?_, fun t htp => ?_⟩
  · rw [hb] at ha; cases ha
  · rw [ht] at hu; simp [held] at hu
  · simp [init] at htp

theorem ag_trivial {s : State} {a : Nat} {f : Agent → Agent} (h : L3I s) (h1 : ∀ g, (f g).boot = g.boot)
    (h2 : ∀ g, (f g).st = g.st) (h3 : (s.agt a).boot = true → (f (s.agt a)).waiter = (s.agt a).waiter) : L3I (setAg s a f) :=
  l3_setAg h (h1 _) (fun hb => ⟨h2 _, h3 hb⟩) (fun hl => by simpa [Agent.live, h2] using hl) (fun hh => Or.inl (by rw [h2]; exact hh))

theorem prK_held {c : Cfg} {s : State} {k : Task} {o : Nat} (h : held (prK c s k) o = true) :
    held k o = true ∧ (prK c s k).st = k.st ∧ (prK c s k).hcq = k.hcq ∧ (prK c s k).lease = k.lease := by
  rcases prK_cases c s k with e | ⟨h1, e⟩ | ⟨_, h1, e⟩ | ⟨_, h1, e⟩ <;> rw [e] at h ⊢
  · exact ⟨h, rfl, rfl, rfl⟩
  · simp [held, h1] at h
  · simp [held] at h
  · exact ⟨h, rfl, rfl, rfl⟩

/-- the poll keeps `L3I`: a task it changes stays as held, or is done and held by none -/
theorem l3_pollOf {c : Cfg} {s : State} (h : L3I s) : L3I (pollOf c s) := by
  obtain ⟨hB, hH, hP⟩ := h
  refine ⟨fun a ha => ?_, fun v a hv => ?_, fun t htp => ?_⟩
  · simp only [pollOf_agt] at ha ⊢
    obtain ⟨h1, h2, h3⟩ := hB a ha
    refine ⟨h1, h2, fun v hv => ?_⟩
    rw [pollOf_tk] at hv ⊢
    obtain ⟨k1, k2, -, k4⟩ := prK_held hv
    obtain ⟨g1, g2, g3⟩ := h3 v k1
    exact ⟨by rw [k2]; exact g1, by rw [k4]; exact g2, fun w hw => g3 w (by rw [pollOf_tk] at hw; exact (prK_held hw).1)⟩
  · rw [pollOf_tk] at hv; simp only [pollOf_agt]; exact hH v a (prK_held hv).1
  · rw [pollOf_pend] at htp
    have hpt := hP t htp
    refine ⟨by rw [pollOf_tk, (prK_owner c s (s.tk t)).2.2.2.2.2.1]; exact hpt.1, fun o ho => ?_⟩
    rw [pollOf_tk] at ho ⊢
    obtain ⟨k1, k2, k3, -⟩ := prK_held ho
    simp only [pollOf_agt]
    rcases hpt.2 o k1 with e | ⟨e1, e2⟩
    · exact Or.inl e
    · exact Or.inr ⟨ansIn_ext ⟨⟨_, pollOf_log c s⟩, rfl⟩ e1, by rw [k2, k3]; exact e2⟩

/-- `L3I` is kept by every step of an instance with the fixes on (`racy` off; PR #110's answer on the task; a boot beats
a lease) -/
theorem l3_step {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    {s s' : State} {act : Action} (hR : Reachable c s) (hs : L3I s) (hstep : step c s act = some s') : L3I s' := by
  have hii := inbInv_of_reachable hR
  have hi1 := i1_of_reachable hR
  have htl := tl_of_reachable hR
  have wf : ∀ a, (s.agt a).boot = true → (s.agt a).waiter = false := fun a hb => (hs.1 a hb).2.1
  open_step hstep
  case tick => obtain ⟨_, _, rfl⟩ := hstep; exact l3_tickOf hs hi1.1
  case awayOn => obtain ⟨_, rfl⟩ := hstep; exact hs
  case back => obtain ⟨_, rfl⟩ := hstep; exact hs
  case commsRead => obtain ⟨_, rfl⟩ := hstep; exact hs
  case hnudge => obtain ⟨_, rfl⟩ := hstep; exact hs
  case bgStart a => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case bgEnd a => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case age a => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case cool a => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case stale a => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case waiterGone a => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun hb => (wf a hb).symm)
  case die a => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun hb => (wf a hb).symm)
  case git a op => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial (l3_git hs) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case world w op => obtain ⟨_, rfl⟩ := hstep; exact hs
  case lock a p => obtain ⟨_, rfl⟩ := hstep; exact hs
  case unlock a p => obtain ⟨_, rfl⟩ := hstep; exact hs
  case expireLock p => obtain ⟨_, rfl⟩ := hstep; exact hs
  case postTo a b u => obtain ⟨_, rfl⟩ := hstep; exact l3_post hs
  case nudge a => obtain ⟨_, rfl⟩ := hstep; exact l3_post (ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  case stay a on => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case endStay a => obtain ⟨_, rfl⟩ := hstep; exact ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case stayCheck a => obtain ⟨_, rfl⟩ := hstep; exact l3_post (ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
  case stayHung a =>
    obtain ⟨_, rfl⟩ := hstep; exact ag_trivial (s := tellC (logEv s _) _) hs (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case readAll a => obtain ⟨_, rfl⟩ := hstep; exact l3_deliver hs
  case claimRead a t => simp [hr] at hstep
  case claimWrite a => simp [hr] at hstep
  case wakeRead a => simp [hr] at hstep
  case wakeWrite a => simp [hr] at hstep
  case stop a big =>
    obtain ⟨hg, rfl⟩ := hstep
    have hw : (s.agt a).st = .working := by simp [busy] at hg; exact hg.1.1
    have hnb := nb_of_st hs (by rw [hw]; decide)
    exact l3_setAg hs rfl (fun hb => by rw [hnb] at hb; cases hb) (fun _ => by simp [Agent.live])
      (fun hh => by rw [hw] at hh; cases hh)
  case wake a =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    exact l3_setAg (l3_deliver hs) rfl (fun hb => by rw [deliver_boot] at hb; have := wf a hb; simp_all)
      (fun _ => by simp [Agent.live]) (fun hh => by rw [deliver_st] at hh; simp_all)
  case prompt a =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hg
    exact l3_setAg (l3_deliver hs) rfl (fun hb => by rw [deliver_boot] at hb; simp_all)
      (fun _ => by simp [Agent.live]) (fun hh => by rw [deliver_st] at hh; simp_all)
  case boot a =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    exact l3_boot hao htl hs hg.1
  case renew a t =>
    obtain ⟨_, rfl⟩ := hstep
    exact l3_setTask hs (fun o ho => ⟨by simpa [held] using ho, rfl, rfl, fun _ => rfl⟩) id
  case openPr a t | push a t | finish t a =>
    obtain ⟨_, rfl⟩ := hstep
    exact l3_setTask hs (fun o ho => ⟨by simpa [held] using ho, rfl, rfl,
      fun hb => ((hs.1 o hb).2.2 t (by simpa [held] using ho)).2.1⟩) id
  case merge a t =>
    obtain ⟨_, rfl⟩ := hstep
    exact l3_setTask (s := logEv s (.merge t)) hs (fun o ho => ⟨by simpa [held] using ho, rfl, rfl,
      fun hb => ((hs.1 o hb).2.2 t (by simpa [held] using ho)).2.1⟩) id
  case ciRun v => obtain ⟨_, rfl⟩ := hstep; exact hs
  case poll => obtain ⟨_, rfl⟩ := hstep; exact l3_pollOf hs
  case expire t =>
    obtain ⟨hg, rfl⟩ := hstep
    refine l3_setTask hs (fun o ho => ⟨by simpa [held] using ho, rfl, rfl, fun hb => ?_⟩) id
    have := held_owner (k := s.tk t) (by simpa [held] using ho)
    simp [bootingOwner, this, hb, hbf] at hg
  case after t deps =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    exact l3_setTask hs (fun o ho => by simp [held, hg.1] at ho) id
  case add deps => obtain ⟨_, rfl⟩ := hstep; exact l3_setTask hs (fun o ho => by simp [held] at ho) id
  case drop t => obtain ⟨_, rfl⟩ := hstep; exact l3_setTask hs (fun o ho => by simp [held] at ho) id
  case releaseOther t => obtain ⟨_, rfl⟩ := hstep; exact l3_post (l3_setTask hs (fun o ho => by simp [held] at ho) id)
  case release a t =>
    obtain ⟨_, rfl⟩ := hstep
    exact ag_trivial (l3_setTask hs (fun o ho => by simp [held] at ho) id) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case done a t ev =>
    obtain ⟨_, rfl⟩ := hstep
    exact ag_trivial (l3_setTask hs (fun o ho => by simp [held] at ho) id) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case dropOwn a t =>
    obtain ⟨_, rfl⟩ := hstep
    exact ag_trivial (l3_setTask hs (fun o ho => by simp [held] at ho) id) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  case leave a =>
    obtain ⟨_, rfl⟩ := hstep
    exact l3_endAgent (ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun hb => (wf a hb).symm))
  case reapGone a =>
    obtain ⟨_, rfl⟩ := hstep
    exact l3_endAgent (ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun hb => (wf a hb).symm))
  case endOther a f =>
    obtain ⟨_, rfl⟩ := hstep
    exact l3_endAgent (ag_trivial hs (fun _ => rfl) (fun _ => rfl) (fun hb => (wf a hb).symm))
  case block a t =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [working, busy, ownsClaimed, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hg
    exact l3_block hs hg.1.1 hg.1.2 hg.2.1 hg.2.2
  case hcPrompt a =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [busy, Bool.and_eq_true, beq_iff_eq] at hg
    exact l3_hcPrompt hs hg.1
  case hcClear a =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [beq_iff_eq] at hg
    exact l3_hcClear hs hg
  case claim a t =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [working, busy, claimable, startable, Bool.and_eq_true, beq_iff_eq] at hg
    exact l3_claim hao hs hg.1.1.2.1 hg.1.2.1.1
  case unblock t =>
    split at hstep
    · rename_i o ho
      rw [when_eq_some] at hstep; obtain ⟨hg, rfl⟩ := hstep
      simp only [beq_iff_eq] at hg
      exact l3_unblock hao (hii.2.2 o).1 hs ho hg
    · cases hstep

/-- The invariant behind L3, of every reachable state. -/
theorem l3_of_reachable {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    {s : State} (h : Reachable c s) : L3I s :=
  reachable_induct (P := L3I) (l3_init c) (fun _ _ _ hR hs hstep => l3_step hr hbf hao hR hs hstep) h

-- ---------- a held task changes hands only to an agent spawned for it ----------

theorem ow_of {s s' : State} {t o o' : Nat} (h1 : held (s.tk t) o = true) (h2 : held (s'.tk t) o' = true)
    (h : (s'.tk t).owner = (s.tk t).owner) : o' = o :=
  Option.some.inj ((held_owner h2).symm.trans (h.trans (held_owner h1)))

theorem ow_setTask {s : State} {u t o o' : Nat} {f : Task → Task}
    (hf : held (f (s.tk u)) o' = true → held (s.tk u) o = true → (f (s.tk u)).owner = (s.tk u).owner)
    (h1 : held (s.tk t) o = true) (h2 : held ((setTask s u f).tk t) o' = true) : ((setTask s u f).tk t).owner = (s.tk t).owner := by
  rcases tk_setTask_or s u t f with e | ⟨rfl, e⟩
  · rw [e]
  · rw [e] at h2 ⊢; exact hf h2 h1

/-- no step but the tick moves a held task to another holder -/
theorem owner_keep {c : Cfg} (hr : c.racy = false) {s s' : State} {act : Action} (hn : act ≠ .tick)
    (hstep : step c s act = some s') {t o o' : Nat} (h1 : held (s.tk t) o = true) (h2 : held (s'.tk t) o' = true) : o' = o := by
  open_step hstep
  case tick => exact absurd rfl hn
  case claimRead a t => simp [hr] at hstep
  case claimWrite a => simp [hr] at hstep
  case wakeRead a => simp [hr] at hstep
  case wakeWrite a => simp [hr] at hstep
  case renew a u => obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (ow_setTask (fun _ _ => rfl) h1 h2)
  case block a u => obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (ow_setTask (fun _ _ => rfl) h1 h2)
  case expire u => obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (ow_setTask (fun _ _ => rfl) h1 h2)
  case after u deps => obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (ow_setTask (fun _ _ => rfl) h1 h2)
  case add deps => obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (ow_setTask (fun _ _ => rfl) h1 h2)
  case drop u => obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (ow_setTask (fun h _ => by simp [held] at h) h1 h2)
  case releaseOther u =>
    obtain ⟨_, rfl⟩ := hstep; rw [post_tk] at h2
    exact ow_of h1 h2 (ow_setTask (fun h _ => by simp [held] at h) h1 h2)
  case release a u =>
    obtain ⟨_, rfl⟩ := hstep; simp only [unbelieve_tk] at h2
    exact ow_of h1 h2 (ow_setTask (fun h _ => by simp [held] at h) h1 h2)
  case done a u ev =>
    obtain ⟨_, rfl⟩ := hstep; simp only [unbelieve_tk] at h2
    exact ow_of h1 h2 (ow_setTask (fun h _ => by simp [held] at h) h1 h2)
  case dropOwn a u =>
    obtain ⟨_, rfl⟩ := hstep; simp only [unbelieve_tk] at h2
    exact ow_of h1 h2 (ow_setTask (fun h _ => by simp [held] at h) h1 h2)
  case claim a u =>
    obtain ⟨hg, rfl⟩ := hstep
    simp only [claimable, startable, Bool.and_eq_true, beq_iff_eq] at hg
    rw [takes_tk] at h2; unfold claimed at h2
    exact ow_of h1 h2 (ow_setTask (fun _ h => by simp [held, hg.1.2.1.1] at h) h1 h2)
  case hcPrompt a =>
    obtain ⟨_, rfl⟩ := hstep
    have h1' : held ((setAg (tellC (hcLog s (firstClaimed c s a)) ⟨.blocked, firstClaimed c s a, urgentNow c s, []⟩) a
      ({ · with st := .blocked })).tk t) o = true := by simpa using h1
    have := ow_setTask (fun _ _ => rfl) h1' h2
    exact ow_of h1 h2 (by rw [this]; simp)
  case hcClear a =>
    obtain ⟨_, rfl⟩ := hstep
    refine ow_of h1 h2 ?_
    simp only [setAg_tk, deliver_tk]
    rw [tk_map (s := s) (g := fun k => if (k.owner == some a && k.st == .blocked && k.hcq) = true then
      { k with st := .claimed, hcq := false, lease := true } else k) (by simp) rfl]
    split <;> rfl
  case leave a =>
    obtain ⟨_, rfl⟩ := hstep
    exact ow_of h1 h2 (by rw [(endAgent_held h2).2.2]; simp)
  case reapGone a =>
    obtain ⟨_, rfl⟩ := hstep
    exact ow_of h1 h2 (by rw [(endAgent_held h2).2.2]; simp)
  case endOther a f =>
    obtain ⟨_, rfl⟩ := hstep
    exact ow_of h1 h2 (by rw [(endAgent_held h2).2.2]; simp)
  case unblock u =>
    split at hstep
    · rw [when_eq_some] at hstep; obtain ⟨_, rfl⟩ := hstep
      have e : ∀ (y : State) (p : List Nat), ({ y with pend := p } : State).tk t = y.tk t := fun _ _ => rfl
      rw [e, post_tk] at h2
      exact ow_of h1 h2 (ow_setTask (fun _ _ => rfl) h1 h2)
    · cases hstep
  case boot a =>
    obtain ⟨_, rfl⟩ := hstep
    refine ow_of h1 h2 ?_
    split <;> simp
  case poll => obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (by simp [(prK_owner ..).1])
  case openPr a u | push a u | finish u a =>
    obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (ow_setTask (fun _ _ => rfl) h1 h2)
  case merge a u => obtain ⟨_, rfl⟩ := hstep; exact ow_of h1 h2 (ow_setTask (s := logEv s (.merge u)) (fun _ _ => rfl) h1 h2)
  all_goals (obtain ⟨_, rfl⟩ := hstep)
  all_goals (exact ow_of h1 h2 (by first | rfl | simp))

theorem reapTask_held {c : Cfg} {x : State} {v u b : Nat} (h : held ((reapTask c x v).tk u) b = true) :
    held (x.tk u) b = true := by
  by_cases hv : u = v
  · subst hv
    unfold reapTask at h; simp only [] at h
    split at h
    · split at h
      · exfalso
        rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        rw [post_tk, tk_setTask_self (by rw [hc.1.1]; decide)] at h
        simp [held] at h
      · exact h
    · exact h
  · rwa [reapTask_tk_ne hv] at h

/-- the tick moves a held task only to an agent it spawns for it -/
theorem owner_tick {c : Cfg} {s : State} (hl : s.ag.length = c.nagents) (hL : L3I s) {t o o' : Nat}
    (h1 : held (s.tk t) o = true) (h2 : held ((tickOf c s).tk t) o' = true) : o' = o ∨ ((tickOf c s).agt o').boot = true := by
  have := tick_inv (c := c) (fun y => L3I y ∧ y.ag.length = c.nagents ∧ ∀ b, held (y.tk t) b = true → b = o ∨ (y.agt b).boot = true)
    (fun x v hx => ⟨l3_reapTask hx.1, by simpa using hx.2.1, fun b hb => by
      rcases hx.2.2 b (reapTask_held hb) with e' | e'
      · exact Or.inl e'
      · exact Or.inr (by simpa [State.agt] using e')⟩)
    (fun x hx => ⟨hx.1, by simpa using hx.2.1, fun b hb => by
      rw [tk_of_task (reapLocks_task x)] at hb; rw [agt_of_ag (reapLocks_ag x)]; exact hx.2.2 b hb⟩)
    (fun x a hx => ⟨l3_endAgent hx.1, by simpa [endAgent] using hx.2.1, fun b hb => by
      obtain ⟨hb1, hb2, _⟩ := endAgent_held hb
      rw [endAgent_agt_ne hb2]; exact hx.2.2 b hb1⟩)
    (fun x a pl hx => ⟨l3_post (l3_setAg hx.1 rfl (fun _ => ⟨rfl, rfl⟩) id (fun hh => Or.inl hh)), by simpa using hx.2.1,
      fun b hb => by
        have hb' : held (x.tk t) b = true := by simpa using hb
        rcases hx.2.2 b hb' with e | e
        · exact Or.inl e
        · right; simp only [post_agt, agt_setAg]; split <;> simpa using e⟩)
    (fun pl x u hx ho => by
      have hS := l3_spawnFor (pl := pl) hx.1 hx.2.1 ho
      refine ⟨hS, by rw [spawnFor_len]; exact hx.2.1, fun b hb => ?_⟩
      rcases spawnFor_agt c pl x u b with ea | ⟨_, _, eb, _⟩
      · rcases spawnFor_tk c pl x u t with et | et
        · rw [et] at hb; rw [ea]; exact hx.2.2 b hb
        · exfalso
          have e1 : nextAgent c x = some b := by rw [← et]; exact held_owner hb
          have := hS.2.1 t b hb
          rw [ea, nextAgent_not_live e1] at this; cases this
      · exact Or.inr eb)
    (s := s) ⟨hL, hl, fun b hb => Or.inl (Option.some.inj ((held_owner hb).symm.trans (held_owner h1)))⟩
  exact this.2.2 o' h2

theorem owner_step {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    {s s' : State} {act : Action} (hR : Reachable c s) (hstep : step c s act = some s') {t o o' : Nat}
    (h1 : held (s.tk t) o = true) (h2 : held (s'.tk t) o' = true) : o' = o ∨ (s'.agt o').boot = true := by
  by_cases ht : act = .tick
  · subst ht
    obtain ⟨_, _, rfl⟩ := step_tick hstep
    exact owner_tick (i1_of_reachable hR).1 (l3_of_reachable hr hbf hao hR) h1 h2
  · exact Or.inl (owner_keep hr ht hstep h1 h2)

-- ---------- the two halves' hypotheses, as facts ----------

/-- `unblock` finds the owner of a blocked task live and not booting (what `unblock_pa` took as hypotheses) -/
theorem unblock_owner {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    {s : State} (hR : Reachable c s) {t o : Nat} (ho : (s.tk t).owner = some o) (hbl : (s.tk t).st = .blocked) :
    (s.agt o).live = true ∧ (s.agt o).boot = false := by
  have hL := l3_of_reachable hr hbf hao hR
  have hh : held (s.tk t) o = true := by simp [held, ho, hbl]
  refine ⟨hL.2.1 t o hh, ?_⟩
  cases hb : (s.agt o).boot
  · rfl
  · have := ((hL.1 o hb).2.2 t hh).1; rw [hbl] at this; cases this

/-- a booting agent's task is the one `firstClaimed` names (what `booting_reads` took as a hypothesis) -/
theorem booting_fc {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    {s : State} (hR : Reachable c s) {a t : Nat} (h : Booting s a t) : firstClaimed c s a = t := by
  obtain ⟨hi, hb, _⟩ := h
  simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at hi
  exact fc_booting (tl_of_reachable hR) (l3_of_reachable hr hbf hao hR) hb (by simp [held, hi.1.1, hi.1.2])

theorem leaveIf_frees {ok : Bool} {s s' : State} {a t : Nat} (hs : leaveIf ok s a = some s') (h : held (s.tk t) a = true) :
    ∀ o, held (s'.tk t) o = false := by
  simp only [leaveIf, when_eq_some] at hs
  obtain ⟨_, rfl⟩ := hs
  intro o; rw [endAgent_tk, setAg_tk, if_pos h]; simp [held]

theorem drop_frees {c : Cfg} {s s' : State} {t : Nat} (hs : step c s (.drop t) = some s') : ∀ o, held (s'.tk t) o = false := by
  simp only [step, drop, when_eq_some] at hs
  obtain ⟨hg, rfl⟩ := hs
  have : (s.tk t).st ≠ .absent := by simp at hg; exact hg.1
  intro o; rw [tk_setTask_self this]; simp [held]

theorem releaseOther_frees {c : Cfg} {s s' : State} {t : Nat} (hs : step c s (.releaseOther t) = some s') :
    ∀ o, held (s'.tk t) o = false := by
  simp only [step, releaseOther, when_eq_some] at hs
  obtain ⟨hg, rfl⟩ := hs
  have : (s.tk t).st ≠ .absent := by simp at hg; rcases hg.2 with e | e <;> simp [e]
  intro o; rw [post_tk, tk_setTask_self this]; simp [held]

theorem hcClear_clears' {c : Cfg} {s s' : State} {o t : Nat} (hs : step c s (.hcClear o) = some s')
    (ho : (s.tk t).owner = some o) (ha : AnsIn s o t) : t ∉ s'.pend := by
  simp only [step, hcClear, when_eq_some] at hs
  obtain ⟨_, rfl⟩ := hs
  show t ∉ (deliver _ o).pend
  refine deliver_clears' ?_ (ansIn_ext (ext_frame rfl rfl o) ha)
  rw [tk_map (s := s) (g := fun k => if (k.owner == some o && k.st == .blocked && k.hcq) = true then
      { k with st := .claimed, hcq := false, lease := true } else k) (by simp) rfl t]
  split <;> exact ho

theorem readAll_clears' {c : Cfg} {s s' : State} {o t : Nat} (hs : step c s (.readAll o) = some s')
    (ho : (s.tk t).owner = some o) (ha : AnsIn s o t) : t ∉ s'.pend := by
  simp only [step, readAll, when_eq_some] at hs
  obtain ⟨_, rfl⟩ := hs
  exact deliver_clears' ho ha

theorem mem_agents {c : Cfg} {s : State} {a : Nat} (hR : Reachable c s) (hl : (s.agt a).live = true) : a ∈ c.agents := by
  have := lt_of_live hl
  rw [(i1_of_reachable hR).1] at this
  simpa [Cfg.agents] using this

/-- L3, one statement per task. In a fair run of an instance with the fixes on (PR #110's answer on the task, a boot beats a
lease, PR #110 or #111's reap), an answer pending on task `t` is eventually read by whoever holds `t`, or `t` ends: done,
dropped, or open again with nobody holding it (and whoever takes it next reads the answer on the task as it takes it:
`claim`'s `takes`, or a spawned agent's first turn, which this theorem covers again). From any reachable state: right after
an `unblock`, or at any later point. No agent dies or starts a background job after the start, none dead or running one
at it. -/
theorem answer_reaches {c : Cfg} (hr : c.racy = false) (hbf : c.bootFirst = true) (hao : c.answerOnTask = true)
    (hfix : c.release ≠ .ended) (hw : c.watchd = true) {t : Nat} (ht : t ∈ c.tasks) (r : Run c) (hf : r.Fair) {n : Nat}
    (hR : Reachable c (r.st n)) (hdd : ∀ b, ((r.st n).agt b).dead = false) (hbg : ∀ b, ((r.st n).agt b).bg = false)
    (hq : ∀ k, n ≤ k → ∀ b, r.act k ≠ .bgStart b ∧ r.act k ≠ .die b) :
    ∃ m, n ≤ m ∧ (answered (r.st m) t = true ∨ ∀ o, held ((r.st m).tk t) o = false) := by
  refine Classical.byContradiction fun hne => ?_
  have hJ : ∀ m, n ≤ m → t ∈ (r.st m).pend ∧ ∃ o, held ((r.st m).tk t) o = true := by
    intro m hm
    refine Classical.byContradiction fun hc => hne ⟨m, hm, ?_⟩
    by_cases hp : t ∈ (r.st m).pend
    · right; intro o
      cases hh : held ((r.st m).tk t) o
      · rfl
      · exact absurd ⟨hp, o, hh⟩ hc
    · left; simp [answered, hp]
  have notans : ∀ m, n ≤ m → answered (r.st m) t = false := by
    intro m hm
    obtain ⟨hp, o, ho⟩ := hJ m hm
    simp only [held, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at ho
    rcases ho.2 with e | e <;> simp [answered, hp, e]
  have hRk : ∀ k, n ≤ k → Reachable c (r.st k) :=
    forever (fun k => Reachable c (r.st k)) n hR (fun k _ ih => Reachable.step (r.act k) ih (r.ok k))
  have hL : ∀ k, n ≤ k → L3I (r.st k) := fun k hk => l3_of_reachable hr hbf hao (hRk k hk)
  have hD : ∀ k, n ≤ k → Dd (r.st k) :=
    forever (fun m => Dd (r.st m)) n hdd (fun k hk ih => d_step (fun b => (hq k hk b).2) ih (r.ok k))
  have hBf : ∀ k, n ≤ k → Bf (r.st k) :=
    forever (fun m => Bf (r.st m)) n hbg (fun k hk ih => bf_step (fun b => (hq k hk b).1) ih (r.ok k))
  by_cases hA : ∃ k, n ≤ k ∧ ∃ o, held ((r.st k).tk t) o = true ∧ ((r.st k).agt o).boot = true
  · -- a spawned agent holds the task: it boots, and its first turn reads the answer
    obtain ⟨k, hk, o, hh, hb⟩ := hA
    have hBt : Booting (r.st k) o t := by
      obtain ⟨b1, b2, b3⟩ := (hL k hk).1 o hb
      obtain ⟨g1, g2, _⟩ := b3 t hh
      exact ⟨by simp [idleClaim, ownsClaimed, g1, held_owner hh, b1], hb, g2,
        ((hL k hk).2.2 t (hJ k hk).1).1, b2, hD k hk o⟩
    have ha : o ∈ c.agents := mem_agents (hRk k hk) ((hL k hk).2.1 t o hh)
    by_cases hex : ∃ k', k ≤ k' ∧ r.act k' = .boot o ∧ Booting (r.st k') o t
    · obtain ⟨k', hk', hact, hB'⟩ := hex
      have := boot_reads hao (booting_fc hr hbf hao (hRk k' (by omega)) hB') (hact ▸ r.ok k') hB'
      rw [notans (k'+1) (by omega)] at this; cases this
    · have hall : ∀ k', k ≤ k' → Booting (r.st k') o t := by
        refine forever (fun k' => Booting (r.st k') o t) k hBt (fun k' hk' ih => ?_)
        have hok := r.ok k'
        have hheld : held ((r.st k').tk t) o = true := by
          obtain ⟨hi, _⟩ := ih; simp only [idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at hi
          simp [held, hi.1.1, hi.1.2]
        by_cases e1 : r.act k' = .tick
        · rw [e1] at hok; exact tick_keep hok ih
        by_cases e2 : r.act k' = .boot o
        · exact absurd ⟨k', hk', e2, ih⟩ hex
        by_cases e3 : r.act k' = .leave o
        · rw [e3] at hok
          obtain ⟨o', ho'⟩ := (hJ (k'+1) (by omega)).2
          rw [leaveIf_frees hok hheld o'] at ho'; cases ho'
        by_cases e4 : r.act k' = .reapGone o
        · rw [e4] at hok
          obtain ⟨o', ho'⟩ := (hJ (k'+1) (by omega)).2
          rw [leaveIf_frees hok hheld o'] at ho'; cases ho'
        by_cases e5 : r.act k' = .drop t
        · rw [e5] at hok
          obtain ⟨o', ho'⟩ := (hJ (k'+1) (by omega)).2
          rw [drop_frees hok o'] at ho'; cases ho'
        by_cases e6 : r.act k' = .releaseOther t
        · rw [e6] at hok
          obtain ⟨o', ho'⟩ := (hJ (k'+1) (by omega)).2
          rw [releaseOther_frees hok o'] at ho'; cases ho'
        by_cases e7 : r.act k' = .endOther o true
        · rw [e7] at hok
          obtain ⟨o', ho'⟩ := (hJ (k'+1) (by omega)).2
          rw [leaveIf_frees hok hheld o'] at ho'; cases ho'
        exact keep hr hbf ⟨e1, e2, e3, e4, e5, e6, e7⟩ (hq k' (by omega)) (pfx_of_reachable (hRk k' (by omega))) hok ih
          (fun e => by have := notans (k' + 1) (by omega); simp [answered, e] at this)
      obtain ⟨k', hk', hact⟩ := Run.fair_ev hf (f := .boot o) (N0 := k) (fun k' hk' => by
          have := (hall k' hk').2.2.2.2.2
          simp [fair, ha, this]) (fun k' hk' => by
          have h1 := hall k' hk'
          simp only [Booting, idleClaim, ownsClaimed, Bool.and_eq_true, beq_iff_eq] at h1
          simp [step, boot, when, h1.1.2, h1.2.1])
      exact hex ⟨k', hk', hact, hall k' hk'⟩
  · -- no holder ever boots: the holder stays the same, and the answer sits in its inbox
    have hnb : ∀ k, n ≤ k → ∀ o, held ((r.st k).tk t) o = true → ((r.st k).agt o).boot = false := by
      intro k hk o hh
      cases hb : ((r.st k).agt o).boot
      · rfl
      · exact absurd ⟨k, hk, o, hh, hb⟩ hA
    obtain ⟨o, ho⟩ := (hJ n (Nat.le_refl _)).2
    have hown : ∀ k, n ≤ k → held ((r.st k).tk t) o = true := by
      refine forever _ n ho (fun k hk ih => ?_)
      obtain ⟨o', ho'⟩ := (hJ (k+1) (by omega)).2
      rcases owner_step hr hbf hao (hRk k hk) (r.ok k) ih ho' with e | e
      · rw [← e]; exact ho'
      · rw [hnb (k+1) (by omega) o' ho'] at e; cases e
    have hP : ∀ k, n ≤ k → AnsIn (r.st k) o t ∧
        (((r.st k).tk t).st = .blocked → ((r.st k).tk t).hcq = true ∧ ((r.st k).agt o).st = .blocked) := by
      intro k hk
      rcases ((hL k hk).2.2 t (hJ k hk).1).2 o (hown k hk) with e | e
      · rw [hnb k hk o (hown k hk)] at e; cases e
      · exact e
    have hlive : ∀ k, n ≤ k → ((r.st k).agt o).live = true := fun k hk => (hL k hk).2.1 t o (hown k hk)
    have ha : o ∈ c.agents := mem_agents hR (hlive n (Nat.le_refl _))
    have hcl : ∀ k, n ≤ k → t ∉ (r.st (k+1)).pend → False := fun k hk h => h (hJ (k+1) (by omega)).1
    by_cases hwk : ∀ N, ∃ k ≥ N, ((r.st k).agt o).st = .working
    · obtain ⟨k, hk, hact⟩ := hf (.readAll o) (fun N => by
        obtain ⟨k, hk, hk2⟩ := hwk (max N n)
        refine ⟨k, by omega, by simp [fair, ha, hD k (by omega) o], ?_⟩
        obtain ⟨i, hi, _⟩ := (hP k (by omega)).1
        have : unread (r.st k) o ≠ [] := List.ne_nil_of_mem hi
        simp [step, readAll, when, busy, hk2, this]) n
      have hok := r.ok k; rw [hact] at hok
      exact hcl k hk (readAll_clears' hok (held_owner (hown k hk)) (hP k hk).1)
    obtain ⟨N0, hN0⟩ : ∃ N0, ∀ k, N0 ≤ k → ((r.st k).agt o).st ≠ .working := by
      refine Classical.byContradiction fun hh => hwk fun N => ?_
      exact Classical.byContradiction fun h2 => hh ⟨N, fun k hk hk2 => h2 ⟨k, hk, hk2⟩⟩
    by_cases hbk : ∀ N, ∃ k ≥ N, ((r.st k).agt o).st = .blocked
    · obtain ⟨k, hk, hact⟩ := hf (.hcClear o) (fun N => by
        obtain ⟨k, hk, hk2⟩ := hbk (max N n)
        exact ⟨k, by omega, by simp [fair, ha, hD k (by omega) o], by simp [step, hcClear, when, hk2]⟩) n
      have hok := r.ok k; rw [hact] at hok
      exact hcl k hk (hcClear_clears' hok (held_owner (hown k hk)) (hP k hk).1)
    obtain ⟨N1, hN1⟩ : ∃ N1, ∀ k, N1 ≤ k → ((r.st k).agt o).st ≠ .blocked := by
      refine Classical.byContradiction fun hh => hbk fun N => ?_
      exact Classical.byContradiction fun h2 => hh ⟨N, fun k hk hk2 => h2 ⟨k, hk, hk2⟩⟩
    -- idle from N on, holding `t` claimed: L2 says that doesn't last
    have hic : ∀ k, max n (max N0 N1) ≤ k → idleClaim (r.st k) o t = true := by
      intro k hk
      have hl := hlive k (by omega)
      have hi : ((r.st k).agt o).st = .idle := by
        have h1 := hN0 k (by omega); have h2 := hN1 k (by omega)
        simp only [Agent.live, Bool.and_eq_true, bne_iff_ne, ne_eq] at hl
        generalize ((r.st k).agt o).st = x at *
        cases x <;> simp_all
      have hh := hown k (by omega)
      have hcl' : ((r.st k).tk t).st = .claimed := by
        simp only [held, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hh
        rcases hh.2 with e | e
        · exact e
        · have := ((hP k (by omega)).2 e).2; rw [hi] at this; cases this
      simp [idleClaim, ownsClaimed, hcl', held_owner hh, hi]
    have hN : n ≤ max n (max N0 N1) := Nat.le_max_left ..
    obtain ⟨m, hm, hm2⟩ := idleClaim_leads_to hr hfix hw ha ht r hf (n := max n (max N0 N1))
      (fun k hk b => hq k (by omega) b) (hBf _ hN o) (hD _ hN o) (hic _ (Nat.le_refl _))
    rw [hic m hm] at hm2; cases hm2

end Swarm
