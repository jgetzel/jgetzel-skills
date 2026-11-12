import SwarmModel.Exists
import SwarmModel.End

/-! `swarm away` and `swarm away --back` (board #47, the panel CLI of board #40's item (d)), and the notice watchd sends
the communicator for a block (watchd.watchd_tick; the event task-blocked marks it sent). `awayOn`, `back` and
`commsRead` are actions of Model.lean's `step`, the notices part of its tick (`notices`) and of `hcPrompt`, so S1-S5, N1,
W1-W4 and L1-L4 are proved with them in. Here:

- Q1 (`told_of`): every block reaches the communicator's inbox: a tick leaves no blocked task untold; refuted with
  `renotify` off (finding #35, `not_Q1`): the same question asked again is never told.
- A1 (`back_questions`, `away_keeps_tasks`, `tick_keeps_blocked`): away loses no question: away and back change no
  task, the tick leaves a blocked task blocked with its question, and back's digest lists exactly the blocked tasks.
- A2 (`quiet_of`, `A2live_of`): while away no block notice to the communicator is urgent (and each is otherwise), refuted
  with `awayQuiet` off (`not_quiet`); and on a run where the communicator's waiter wakes it on an urgent message
  (`Run.CommsFair`), everything sent to it before `--back`, the questions asked while away among it, is read; refuted
  with `backTells` off (`not_A2live`), on a fair run.
- A3 (`A3`): non-interference: the away flag changes no staffing decision: the tick's reap, spawns, ends, git and
  events are the same with it on and off; only the notices' urgency differs.
- A4 (`away_twice`, `back_twice`, `since_kept`, `back_digest`, `questions_sorted`, `digest_done`, and board #80's
  `digest_merged`, `digest_ci`): away and back are
  idempotent (a second away is refused and keeps the first since); back's digest is the events since away. -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

-- ---------- the frames: which changes leave the communicator's side alone ----------
@[simp] theorem setTask_away (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).away = s.away := by frame setTask
@[simp] theorem setAg_away (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).away = s.away := rfl
@[simp] theorem post_away (s : State) (m : Msg) : (post s m).away = s.away := rfl
@[simp] theorem showMsg_away (s : State) (a i : Nat) : (showMsg s a i).away = s.away := by frame showMsg
@[simp] theorem showAll_away (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).away = s.away := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem deliver_away (s : State) (a : Nat) : (deliver s a).away = s.away := by simp [deliver]
@[simp] theorem takes_away (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).away = s.away := by frame takes
@[simp] theorem claimed_away (s : State) (a t : Nat) : (claimed s a t).away = s.away := by frame claimed
@[simp] theorem releaseAll_away (s : State) (a : Nat) : (releaseAll s a).away = s.away := rfl
@[simp] theorem endAgent_away (s : State) (a : Nat) : (endAgent s a).away = s.away := rfl
@[simp] theorem unbelieve_away (s : State) (a t : Nat) : (unbelieve s a t).away = s.away := rfl
@[simp] theorem awake_away (s : State) (a : Nat) : (awake s a).away = s.away := rfl
@[simp] theorem reapTask_away (c : Cfg) (x : State) (t : Nat) : (reapTask c x t).away = x.away := by frame reapTask
@[simp] theorem reapTasks_away (c : Cfg) (s : State) : (reapTasks c s).away = s.away := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.away = s.away) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapLocks_away (s : State) : (reapLocks s).away = s.away := rfl
@[simp] theorem spawnFor_away (c : Cfg) (pl : List Nat) (s : State) (t : Nat) : (spawnFor c pl s t).away = s.away := by frame spawnFor
@[simp] theorem lifecycle_away (c : Cfg) (s : State) : (lifecycle c s).away = s.away := by
  unfold lifecycle
  simp only []
  split
  · exact foldl_inv _ (fun x : State => x.away = s.away) _ _ (foldl_inv _ (fun x : State => x.away = s.away) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])
  · exact foldl_inv _ (fun x : State => x.away = s.away) _ _ (foldl_inv _ (fun x : State => x.away = s.away) _ _ (foldl_inv _ (fun x : State => x.away = s.away) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])) (fun b a h => by simp [h])
@[simp] theorem tickS_away (c : Cfg) (s : State) : (tickS c s).away = s.away := by simp [tickS]
@[simp] theorem setTask_cbox (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).cbox = s.cbox := by frame setTask
@[simp] theorem setAg_cbox (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).cbox = s.cbox := rfl
@[simp] theorem post_cbox (s : State) (m : Msg) : (post s m).cbox = s.cbox := rfl
@[simp] theorem showMsg_cbox (s : State) (a i : Nat) : (showMsg s a i).cbox = s.cbox := by frame showMsg
@[simp] theorem showAll_cbox (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).cbox = s.cbox := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem deliver_cbox (s : State) (a : Nat) : (deliver s a).cbox = s.cbox := by simp [deliver]
@[simp] theorem takes_cbox (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).cbox = s.cbox := by frame takes
@[simp] theorem claimed_cbox (s : State) (a t : Nat) : (claimed s a t).cbox = s.cbox := by frame claimed
@[simp] theorem releaseAll_cbox (s : State) (a : Nat) : (releaseAll s a).cbox = s.cbox := rfl
@[simp] theorem endAgent_cbox (s : State) (a : Nat) : (endAgent s a).cbox = s.cbox := rfl
@[simp] theorem unbelieve_cbox (s : State) (a t : Nat) : (unbelieve s a t).cbox = s.cbox := rfl
@[simp] theorem awake_cbox (s : State) (a : Nat) : (awake s a).cbox = s.cbox := rfl
@[simp] theorem reapTask_cbox (c : Cfg) (x : State) (t : Nat) : (reapTask c x t).cbox = x.cbox := by frame reapTask
@[simp] theorem reapTasks_cbox (c : Cfg) (s : State) : (reapTasks c s).cbox = s.cbox := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.cbox = s.cbox) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapLocks_cbox (s : State) : (reapLocks s).cbox = s.cbox := rfl
@[simp] theorem spawnFor_cbox (c : Cfg) (pl : List Nat) (s : State) (t : Nat) : (spawnFor c pl s t).cbox = s.cbox := by frame spawnFor
@[simp] theorem lifecycle_cbox (c : Cfg) (s : State) : (lifecycle c s).cbox = s.cbox := by
  unfold lifecycle
  simp only []
  split
  · exact foldl_inv _ (fun x : State => x.cbox = s.cbox) _ _ (foldl_inv _ (fun x : State => x.cbox = s.cbox) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])
  · exact foldl_inv _ (fun x : State => x.cbox = s.cbox) _ _ (foldl_inv _ (fun x : State => x.cbox = s.cbox) _ _ (foldl_inv _ (fun x : State => x.cbox = s.cbox) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])) (fun b a h => by simp [h])
@[simp] theorem tickS_cbox (c : Cfg) (s : State) : (tickS c s).cbox = s.cbox := by simp [tickS]
@[simp] theorem setTask_ccur (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).ccur = s.ccur := by frame setTask
@[simp] theorem setAg_ccur (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).ccur = s.ccur := rfl
@[simp] theorem post_ccur (s : State) (m : Msg) : (post s m).ccur = s.ccur := rfl
@[simp] theorem showMsg_ccur (s : State) (a i : Nat) : (showMsg s a i).ccur = s.ccur := by frame showMsg
@[simp] theorem showAll_ccur (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).ccur = s.ccur := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem deliver_ccur (s : State) (a : Nat) : (deliver s a).ccur = s.ccur := by simp [deliver]
@[simp] theorem takes_ccur (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).ccur = s.ccur := by frame takes
@[simp] theorem claimed_ccur (s : State) (a t : Nat) : (claimed s a t).ccur = s.ccur := by frame claimed
@[simp] theorem releaseAll_ccur (s : State) (a : Nat) : (releaseAll s a).ccur = s.ccur := rfl
@[simp] theorem endAgent_ccur (s : State) (a : Nat) : (endAgent s a).ccur = s.ccur := rfl
@[simp] theorem unbelieve_ccur (s : State) (a t : Nat) : (unbelieve s a t).ccur = s.ccur := rfl
@[simp] theorem awake_ccur (s : State) (a : Nat) : (awake s a).ccur = s.ccur := rfl
@[simp] theorem reapTask_ccur (c : Cfg) (x : State) (t : Nat) : (reapTask c x t).ccur = x.ccur := by frame reapTask
@[simp] theorem reapTasks_ccur (c : Cfg) (s : State) : (reapTasks c s).ccur = s.ccur := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.ccur = s.ccur) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapLocks_ccur (s : State) : (reapLocks s).ccur = s.ccur := rfl
@[simp] theorem spawnFor_ccur (c : Cfg) (pl : List Nat) (s : State) (t : Nat) : (spawnFor c pl s t).ccur = s.ccur := by frame spawnFor
@[simp] theorem lifecycle_ccur (c : Cfg) (s : State) : (lifecycle c s).ccur = s.ccur := by
  unfold lifecycle
  simp only []
  split
  · exact foldl_inv _ (fun x : State => x.ccur = s.ccur) _ _ (foldl_inv _ (fun x : State => x.ccur = s.ccur) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])
  · exact foldl_inv _ (fun x : State => x.ccur = s.ccur) _ _ (foldl_inv _ (fun x : State => x.ccur = s.ccur) _ _ (foldl_inv _ (fun x : State => x.ccur = s.ccur) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])) (fun b a h => by simp [h])
@[simp] theorem tickS_ccur (c : Cfg) (s : State) : (tickS c s).ccur = s.ccur := by simp [tickS]
@[simp] theorem setTask_digest (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).digest = s.digest := by frame setTask
@[simp] theorem setAg_digest (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).digest = s.digest := rfl
@[simp] theorem post_digest (s : State) (m : Msg) : (post s m).digest = s.digest := rfl
@[simp] theorem showMsg_digest (s : State) (a i : Nat) : (showMsg s a i).digest = s.digest := by frame showMsg
@[simp] theorem showAll_digest (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).digest = s.digest := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem deliver_digest (s : State) (a : Nat) : (deliver s a).digest = s.digest := by simp [deliver]
@[simp] theorem takes_digest (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).digest = s.digest := by frame takes
@[simp] theorem claimed_digest (s : State) (a t : Nat) : (claimed s a t).digest = s.digest := by frame claimed
@[simp] theorem releaseAll_digest (s : State) (a : Nat) : (releaseAll s a).digest = s.digest := rfl
@[simp] theorem endAgent_digest (s : State) (a : Nat) : (endAgent s a).digest = s.digest := rfl
@[simp] theorem unbelieve_digest (s : State) (a t : Nat) : (unbelieve s a t).digest = s.digest := rfl
@[simp] theorem awake_digest (s : State) (a : Nat) : (awake s a).digest = s.digest := rfl
@[simp] theorem reapTask_digest (c : Cfg) (x : State) (t : Nat) : (reapTask c x t).digest = x.digest := by frame reapTask
@[simp] theorem reapTasks_digest (c : Cfg) (s : State) : (reapTasks c s).digest = s.digest := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.digest = s.digest) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapLocks_digest (s : State) : (reapLocks s).digest = s.digest := rfl
@[simp] theorem spawnFor_digest (c : Cfg) (pl : List Nat) (s : State) (t : Nat) : (spawnFor c pl s t).digest = s.digest := by frame spawnFor
@[simp] theorem lifecycle_digest (c : Cfg) (s : State) : (lifecycle c s).digest = s.digest := by
  unfold lifecycle
  simp only []
  split
  · exact foldl_inv _ (fun x : State => x.digest = s.digest) _ _ (foldl_inv _ (fun x : State => x.digest = s.digest) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])
  · exact foldl_inv _ (fun x : State => x.digest = s.digest) _ _ (foldl_inv _ (fun x : State => x.digest = s.digest) _ _ (foldl_inv _ (fun x : State => x.digest = s.digest) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])) (fun b a h => by simp [h])
@[simp] theorem tickS_digest (c : Cfg) (s : State) : (tickS c s).digest = s.digest := by simp [tickS]

-- ---------- the notices ----------
theorem notify_cbox (c : Cfg) (x : State) (t : Nat) : ∃ ns, (notify c x t).cbox = x.cbox ++ ns ∧
    ∀ n ∈ ns, n.kind = .blocked ∧ n.urgent = urgentNow c x := by
  unfold notify; split
  · exact ⟨[_], rfl, by simp⟩
  · exact ⟨[], by simp, by simp⟩
theorem notices_cbox (c : Cfg) (x : State) : ∃ ns, (notices c x).cbox = x.cbox ++ ns ∧
    ∀ n ∈ ns, n.kind = .blocked ∧ n.urgent = urgentNow c x := by
  unfold notices
  have := foldl_inv (notify c) (fun y : State => y.away = x.away ∧ ∃ ns, y.cbox = x.cbox ++ ns ∧
      ∀ n ∈ ns, n.kind = .blocked ∧ n.urgent = urgentNow c x) c.tasks x ⟨rfl, [], by simp, by simp⟩ (fun y t hy => by
    obtain ⟨ha, ns, hc, hn⟩ := hy
    obtain ⟨ms, hc', hm⟩ := notify_cbox c y t
    refine ⟨by unfold notify; split <;> simp [ha], ns ++ ms, by rw [hc', hc, List.append_assoc], fun n hn' => ?_⟩
    rcases List.mem_append.1 hn' with h | h
    · exact hn n h
    · obtain ⟨h1, h2⟩ := hm n h; exact ⟨h1, by rw [h2]; simp [urgentNow, ha]⟩)
  exact this.2

/-- what one step does to the communicator's side: its cursor moves only by its read (to the end of its inbox), the away
flag only by `swarm away` and `--back`, and its inbox only grows, every block notice urgent exactly as `urgentNow` -/
theorem side_step {c : Cfg} {s s' : State} {act : Action} (h : step c s act = some s') :
    (s'.ccur = s.ccur ∨ (act = .commsRead ∧ s'.ccur = s.cbox.length)) ∧
    (s'.away = s.away ∨ act = .awayOn ∨ act = .back) ∧
    ∃ ns, s'.cbox = s.cbox ++ ns ∧ ∀ n ∈ ns, n.kind = .blocked → n.urgent = urgentNow c s := by
  open_step h
  case tick =>
    obtain ⟨_, _, rfl⟩ := h
    obtain ⟨ns, hc, hn⟩ := notices_cbox c (tickS c s)
    refine ⟨Or.inl (by simp [tickOf]), Or.inl (by simp [tickOf]), ns, by simpa [tickOf] using hc, fun n hm _ => ?_⟩
    rw [(hn n hm).2]; simp [urgentNow]
  case hcPrompt a =>
    obtain ⟨_, rfl⟩ := h
    exact ⟨Or.inl (by simp), Or.inl (by simp), [⟨.blocked, firstClaimed c s a, urgentNow c s, []⟩], by simp [tellC], by simp⟩
  case stayHung a =>
    obtain ⟨_, rfl⟩ := h
    exact ⟨Or.inl (by simp), Or.inl (by simp), [⟨.hung, a, true, []⟩], by simp [tellC], by simp⟩
  case awayOn => obtain ⟨_, rfl⟩ := h; exact ⟨Or.inl rfl, Or.inr (Or.inl rfl), [_], rfl, by simp⟩
  case back =>
    obtain ⟨_, rfl⟩ := h
    refine ⟨Or.inl rfl, Or.inr (Or.inr rfl), ?_⟩
    split
    · exact ⟨[_], rfl, by simp⟩
    · exact ⟨[], by simp, by simp⟩
  case commsRead => obtain ⟨_, rfl⟩ := h; exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl rfl, [], by simp, by simp⟩
  case unblock t =>
    split at h
    · rw [when_eq_some] at h; obtain ⟨_, rfl⟩ := h; exact ⟨Or.inl (by simp), Or.inl (by simp), [], by simp, by simp⟩
    · cases h
  all_goals
    obtain ⟨_, rfl⟩ := h
    refine ⟨Or.inl ?_, Or.inl ?_, [], ?_, by simp⟩ <;> (repeat' split) <;> simp

-- ---------- Q1: every block reaches the communicator ----------

-- ---------- Q1: every block reaches the communicator ----------
theorem toldAfter_ne {evs : List Ev} {t : Nat} {e : Ev} (h : isQ t e = false) : toldAfter (evs ++ [e]) t = toldAfter evs t := by
  simp [toldAfter, List.filter_append, h]
theorem toldAfter_tb (evs : List Ev) (t : Nat) (hc : Bool) : toldAfter (evs ++ [.tblocked t hc]) t = true := by
  cases hc <;> simp [toldAfter, List.filter_append, isQ]
theorem notify_task (c : Cfg) (y : State) (u : Nat) : (notify c y u).task = y.task := by
  obtain ⟨_, _, h⟩ := notify_ex c y u; rw [h]
/-- a notice of u keeps what was told of t -/
theorem notify_keeps {c : Cfg} {y : State} {t u : Nat} (h : toldAfter y.evs t = true) : toldAfter (notify c y u).evs t = true := by
  unfold notify; split
  · simp only [tellC_evs, logEv]
    by_cases e : u = t
    · subst e; exact toldAfter_tb ..
    · rw [toldAfter_ne (by cases (y.tk u).hcq <;> simp [isQ, e])]; exact h
  · exact h
/-- with `renotify`, the notice loop's turn at a blocked t leaves it told -/
theorem notify_tells {c : Cfg} (hr : c.renotify = true) {y : State} {t : Nat} (hb : (y.tk t).st = .blocked) :
    toldAfter (notify c y t).evs t = true := by
  unfold notify
  by_cases hs : sent c y t
  · simp only [hb, hs, beq_self_eq_true, Bool.not_true, Bool.and_false]; simpa [sent, hr] using hs
  · simp only [hb, hs, beq_self_eq_true, Bool.not_false, Bool.and_self, if_true, tellC_evs, logEv]; exact toldAfter_tb ..
theorem notices_tells {c : Cfg} (hr : c.renotify = true) {t : Nat} : ∀ (l : List Nat) (y : State), (t ∈ l → (y.tk t).st = .blocked →
    toldAfter (l.foldl (notify c) y).evs t = true) ∧ (toldAfter y.evs t = true → toldAfter (l.foldl (notify c) y).evs t = true)
  | [], y => ⟨fun h => absurd h (List.not_mem_nil), id⟩
  | u :: us, y => by
    have ih := notices_tells (t := t) hr us (notify c y u)
    have htk : ∀ v, (notify c y u).tk v = y.tk v := fun v => tk_of_task (notify_task ..) v
    refine ⟨fun hm hb => ?_, fun h => ih.2 (notify_keeps h)⟩
    rcases List.mem_cons.1 hm with e | e
    · subst e; exact ih.2 (notify_tells hr hb)
    · exact ih.1 e (by rw [htk]; exact hb)

/-- Q1: every block reaches the communicator: after a tick, the latest question of every blocked task was told (a
task-blocked event, logged with its notice to the communicator, after its latest `task block`) -/
def Q1 (c : Cfg) : Prop := ∀ s t, t ∈ c.tasks → ((tickOf c s).tk t).st = .blocked → toldAfter (tickOf c s).evs t = true

theorem Q1_of {c : Cfg} (hr : c.renotify = true) : Q1 c := by
  intro s t ht hb
  have e : ∀ v, (tickOf c s).tk v = (tickS c s).tk v := fun v => tickOf_tk c s v
  rw [e] at hb
  exact (notices_tells hr c.tasks (tickS c s)).1 ht hb

/-- what breaks Q1: after `acts`, a tick leaves task t blocked with its latest question untold -/
def q1Breaks (c : Cfg) (acts : List Action) (t : Nat) : Bool :=
  (run c acts).any fun s => ((tickOf c s).tk t).st == .blocked && !toldAfter (tickOf c s).evs t
theorem not_Q1_of {c : Cfg} {acts : List Action} {t : Nat} (ht : t ∈ c.tasks) (h : q1Breaks c acts t = true) : ¬ Q1 c := by
  intro hq
  unfold q1Breaks at h
  cases e : run c acts with
  | none => simp [e] at h
  | some s =>
    simp only [e, Option.any_some, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    rw [hq s t ht h.1] at h; cases h.2
/-- #35: agent 0 blocks #1 and the tick tells the communicator; the answer comes, agent 0 reads it, and blocks #1 again
with the same question (`task block 1 "which way?"` twice, as the replay does). The notice was marked sent by the first
task-blocked event with that text, so the second question is never told -/
def cfg35 : Cfg := { nagents := 1, roster := 1, renotify := false }
def pre35 : List Action := [.add [], .claim 0 1, .block 0 1, .tick, .unblock 1, .readAll 0, .block 0 1]
theorem not_Q1 : ¬ Q1 cfg35 := not_Q1_of (by decide) (by decide +kernel : q1Breaks cfg35 pre35 1 = true)
-- with `renotify` the same run tells it
example : q1Breaks { cfg35 with renotify := true } pre35 1 = false := by decide +kernel

-- ---------- A1: away loses no question ----------
/-- `swarm away`, `--back` and the communicator's read change no task, agent, lock, message, cursor, git ref or event -/
theorem away_keeps {c : Cfg} {s s' : State} {act : Action} (ha : act = .awayOn ∨ act = .back ∨ act = .commsRead)
    (h : step c s act = some s') : s'.task = s.task ∧ s'.ag = s.ag ∧ s'.lock = s.lock ∧ s'.log = s.log ∧
      s'.cursor = s.cursor ∧ s'.git = s.git ∧ s'.evs = s.evs := by
  rcases ha with rfl | rfl | rfl <;> simp only [step, awayOn, back, commsRead, when_eq_some] at h <;> obtain ⟨_, rfl⟩ := h <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem holds_of_blocked {s : State} {a t : Nat} (hst : (s.tk t).st = .blocked) (ho : (s.tk t).owner = some a) :
    holds s a = true := by
  have h := tk_in_range (s := s) (t := t) (by rw [hst]; simp)
  simp only [holds, List.any_eq_true]
  refine ⟨s.task[t - 1], List.getElem_mem h.2, ?_⟩
  have e : s.tk t = s.task[t - 1] := by
    simp [State.tk, h.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h.2]
  rw [e] at hst ho
  simp [held, hst, ho]

/-- lifecycle leaves a blocked task alone: its owner holds it, so it is neither ended nor reused, and a spawn takes only
pool tasks -/
theorem lifecycle_blocked {c : Cfg} {z : State} {t : Nat} (hst : (z.tk t).st = .blocked) :
    (lifecycle c z).tk t = z.tk t := by
  have hnh : ∀ b, finished c z b = true → held (z.tk t) b = false := fun b hb => by
    cases hh : held (z.tk t) b
    · rfl
    · exfalso
      have : (z.tk t).owner = some b := by simp [held] at hh; exact hh.1
      simp [finished, idleFree, holds_of_blocked hst this] at hb
  have hpl : (pool c z).contains t = false := by simp [pool, claimable, startable, hst]
  have h2 : (endFold c z).tk t = z.tk t := by
    unfold endFold
    exact foldl_inv _ (fun y : State => y.tk t = z.tk t) c.agents z rfl (fun y b hy => by
      split
      · rename_i hh
        simp only [Bool.and_eq_true] at hh
        rw [endAgent_tk, hy]; simp [hnh b hh.1]
      · exact hy)
  have h3 : (c.agents.foldl (digStep c z) (endFold c z)).tk t = z.tk t :=
    foldl_inv (digStep c z) (fun y : State => y.tk t = z.tk t) c.agents _ h2 (fun y b hy => by
      unfold digStep; split
      · simp only [post_tk, setAg_tk]; exact hy
      · exact hy)
  rw [lifecycle_eq]; split
  · exact h3
  · exact foldl_inv _ (fun y : State => y.tk t = z.tk t) _ _ h3 (fun y t' hy => by
      by_cases e : t = t'
      · subst e; rw [spawnFor_not hpl]; exact hy
      · rw [spawnFor_tk_ne e]; exact hy)

/-- A1, watchd's half: the tick, away or not, leaves a blocked task blocked with its owner and its question -/
theorem tick_keeps_blocked {c : Cfg} {s : State} {t : Nat} (hst : (s.tk t).st = .blocked) : (tickOf c s).tk t = s.tk t := by
  have hr : (reapTasks c s).tk t = s.tk t := by
    unfold reapTasks
    exact foldl_inv (reapTask c) (fun y : State => y.tk t = s.tk t) c.tasks s rfl (fun y u hy => by
      by_cases e : t = u
      · subst e; unfold reapTask; simp only [hy, hst]; split <;> simp_all
      · rw [reapTask_tk_ne e, hy])
  have hz : (reapLocks (reapTasks c s)).tk t = s.tk t := by rw [tk_of_task (reapLocks_task _), hr]
  rw [tickOf_tk]
  show (lifecycle c (reapLocks (reapTasks c s))).tk t = s.tk t
  rw [lifecycle_blocked (by rw [hz]; exact hst), hz]

/-- A1, the digest's half: `--back`'s digest lists exactly the blocked tasks -/
theorem back_questions {c : Cfg} {s s' : State} (h : step c s .back = some s') :
    ∃ g, s'.digest = some g ∧ ∀ t, t ∈ g.qs ↔ t ∈ c.tasks ∧ (s.tk t).st = .blocked := by
  simp only [step, back, when_eq_some] at h
  obtain ⟨_, rfl⟩ := h
  refine ⟨_, rfl, fun t => ?_⟩
  simp only [digestOf, questions, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ((List.mergeSort_perm _ _).mem_iff.1 hp)
    simpa using hu
  · intro hu
    exact ⟨_, (List.mergeSort_perm _ _).mem_iff.2 (List.mem_map.2 ⟨t, by simpa using hu, rfl⟩), rfl⟩

-- ---------- A2: while away no question is urgent, and after back each reaches the communicator ----------
/-- A2, safety: a block notice sent to the communicator is urgent exactly when the user is not away -/
def A2quiet (c : Cfg) : Prop := ∀ s act s', step c s act = some s' →
  ∀ n ∈ s'.cbox.drop s.cbox.length, n.kind = .blocked → (n.urgent = true ↔ s.away = none)
theorem A2quiet_of {c : Cfg} (h : c.awayQuiet = true) : A2quiet c := by
  intro s act s' hs n hn hk
  obtain ⟨_, _, ns, hc, hu⟩ := side_step hs
  rw [hc, List.drop_left] at hn
  rw [hu n hn hk]; cases e : s.away <;> simp [urgentNow, h, e]
/-- what breaks A2's safety: a step after `acts` sends an urgent block notice while away, or a quiet one while not -/
def quietBreaks (c : Cfg) (acts : List Action) (act : Action) : Bool :=
  (run c acts).any fun s => (step c s act).any fun s' =>
    (s'.cbox.drop s.cbox.length).any fun n => n.kind == .blocked && n.urgent != s.away.isNone
theorem not_A2quiet_of {c : Cfg} {acts : List Action} {act : Action} (h : quietBreaks c acts act = true) : ¬ A2quiet c := by
  intro hq
  unfold quietBreaks at h
  cases e : run c acts with
  | none => simp [e] at h
  | some s =>
    simp only [e, Option.any_some] at h
    cases e2 : step c s act with
    | none => simp [e2] at h
    | some s' =>
      simp only [e2, Option.any_some, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨n, hn, hk, hu⟩ := h
      have := hq s act s' e2 n hn hk
      cases hs : s.away <;> cases hnu : n.urgent <;> simp_all
/-- with `awayQuiet` off, a block while away is told urgently -/
def cfgAQ : Cfg := { nagents := 1, roster := 1, awayQuiet := false }
theorem not_A2quiet : ¬ A2quiet cfgAQ :=
  not_A2quiet_of (by decide +kernel : quietBreaks cfgAQ [.add [], .claim 0 1, .awayOn, .block 0 1] .tick = true)

/-- the communicator has an urgent message it hasn't read: its waiter wakes it -/
def urgentUnread (s : State) : Bool := (s.cbox.drop s.ccur).any (·.urgent)
/-- the communicator's waiter is fair: an urgent message unread at infinitely many steps is read at infinitely many -/
def Run.CommsFair {c : Cfg} (r : Run c) : Prop :=
  (∀ N, ∃ n ≥ N, urgentUnread (r.st n) = true) → ∀ N, ∃ n ≥ N, r.act n = .commsRead
/-- A2, liveness: everything sent to the communicator before `--back` (the questions asked while away among it) is read -/
def A2live (c : Cfg) : Prop := ∀ r : Run c, r.CommsFair → ∀ m i, r.act m = .back → i < (r.st m).cbox.length →
  ∃ k, i < (r.st k).ccur

theorem cbox_grows {c : Cfg} (r : Run c) (j : Nat) : ∀ k, j ≤ k → ∃ ns, (r.st k).cbox = (r.st j).cbox ++ ns
  | k, hk => by
    induction k with
    | zero => exact ⟨[], by rw [show j = 0 by omega]; simp⟩
    | succ k ih =>
      by_cases e : j = k + 1
      · subst e; exact ⟨[], by simp⟩
      obtain ⟨ns, h⟩ := ih (by omega)
      obtain ⟨_, _, ms, h2, _⟩ := side_step (r.ok k)
      exact ⟨ns ++ ms, by rw [h2, h, List.append_assoc]⟩

theorem A2live_of {c : Cfg} (hbt : c.backTells = true) : A2live c := by
  intro r hf m i hm hi
  refine Classical.byContradiction fun hne => ?_
  have hle : ∀ k, (r.st k).ccur ≤ i := fun k => Nat.le_of_not_lt fun h => hne ⟨k, h⟩
  have hb := r.ok m
  rw [hm] at hb
  simp only [step, back, when_eq_some, hbt, if_true] at hb
  obtain ⟨_, hb⟩ := hb
  have hc1 : (r.st (m + 1)).cbox = (r.st m).cbox ++ [⟨.back, 0, true, (digestOf c (r.st m) ((r.st m).away.getD 0)).qs⟩] := by
    rw [← hb]
  have hu : ∀ k, m + 1 ≤ k → urgentUnread (r.st k) = true := fun k hk => by
    obtain ⟨ns, h⟩ := cbox_grows r (m + 1) k hk
    have hl : (r.st k).ccur ≤ (r.st m).cbox.length := by have := hle k; omega
    simp only [urgentUnread, h, hc1, List.append_assoc, List.singleton_append, List.drop_append_of_le_length hl,
      List.any_append, List.any_cons, Bool.true_or, Bool.or_true]
  obtain ⟨n, hn, ha⟩ := hf (fun N => ⟨max N (m + 1), Nat.le_max_left .., hu _ (Nat.le_max_right ..)⟩) (m + 1)
  have hok := r.ok n
  rw [ha] at hok
  simp only [step, commsRead, when_eq_some] at hok
  obtain ⟨_, hok⟩ := hok
  obtain ⟨ns, h⟩ := cbox_grows r (m + 1) n hn
  have := hle (n + 1)
  rw [← hok] at this
  simp only [h, hc1, List.length_append, List.length_singleton] at this
  omega

theorem st_take {c : Cfg} (r : Run c) {acts : List Action} (h0 : r.st 0 = init c)
    (ha : ∀ n, n < acts.length → r.act n = acts.getD n .tick) : ∀ k, k ≤ acts.length → run c (acts.take k) = some (r.st k)
  | 0, _ => by simp [run, h0]
  | k + 1, hk => by
    have ih := st_take r h0 ha k (by omega)
    rw [List.take_succ, show acts[k]? = some (acts.getD k .tick) by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < acts.length)]]
    simp only [run, List.foldlM_append, Option.toList_some] at ih ⊢
    rw [ih]; simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil]
    rw [← ha k (by omega), r.ok k]; rfl

/-- with `backTells` off: agent 0 blocks #1 while the user is away; the notice is not urgent, `--back` tells nothing, and
the run goes on (agent 0's background job starts and ends) with the communicator never woken: a fair run on which the
question never reaches it -/
def cfgBT : Cfg := { nagents := 1, roster := 1, backTells := false }
def preBT : List Action := [.add [], .claim 0 1, .awayOn, .block 0 1, .tick, .back]
theorem lassoBT : lassoRun cfgBT (fun s => s.ccur == 0 && !urgentUnread s) (fun _ => true) preBT [.bgStart 0, .bgEnd 0] = true := by
  decide +kernel
theorem not_A2live : ¬ A2live cfgBT := by
  intro h
  obtain ⟨r, -, h0, hp, -, ha⟩ := lasso_run lassoBT
  have hcf : r.CommsFair := fun hu => by
    obtain ⟨n, -, hn⟩ := hu 0
    have := hp n; simp [hn] at this
  have h5 := st_take r h0 ha 5 (by decide)
  have hlen : 1 < (r.st 5).cbox.length := by
    have : (run cfgBT (preBT.take 5)).any (fun s => decide (1 < s.cbox.length)) = true := by decide +kernel
    rw [h5] at this; simpa using this
  obtain ⟨k, hk⟩ := h r hcf 5 1 (by rw [ha 5 (by decide)]; rfl) hlen
  have := hp k; simp at this; omega

-- ---------- A3: the away flag changes no staffing decision ----------
/-- the away flag set to v -/
def withAway (s : State) (v : Option Nat) : State := { s with away := v }
/-- the state but the away flag and the urgency of what the communicator was sent -/
def blind (s : State) : State := { s with away := none, cbox := s.cbox.map fun n => { n with urgent := false } }

section
variable {v : Option Nat}
@[simp] theorem tk_wa (x : State) (t : Nat) : (withAway x v).tk t = x.tk t := rfl
@[simp] theorem agt_wa (x : State) (a : Nat) : (withAway x v).agt a = x.agt a := rfl
@[simp] theorem setTask_wa (x : State) (t : Nat) (f : Task → Task) : setTask (withAway x v) t f = withAway (setTask x t f) v := by
  unfold setTask; split <;> rfl
@[simp] theorem setAg_wa (x : State) (a : Nat) (f : Agent → Agent) : setAg (withAway x v) a f = withAway (setAg x a f) v := rfl
@[simp] theorem post_wa (x : State) (m : Msg) : post (withAway x v) m = withAway (post x m) v := rfl
@[simp] theorem endAgent_wa (x : State) (a : Nat) : endAgent (withAway x v) a = withAway (endAgent x a) v := rfl
@[simp] theorem reapLocks_wa (x : State) : reapLocks (withAway x v) = withAway (reapLocks x) v := rfl
@[simp] theorem claimed_wa (x : State) (a t : Nat) : claimed (withAway x v) a t = withAway (claimed x a t) v := by
  unfold claimed; simp
@[simp] theorem reapTask_wa (c : Cfg) (x : State) (t : Nat) : reapTask c (withAway x v) t = withAway (reapTask c x t) v := by
  unfold reapTask
  simp only [tk_wa, agt_wa]
  cases h : (x.tk t).owner with
  | none => rfl
  | some o =>
    dsimp only
    by_cases hc : ((x.tk t).st == .claimed && !(x.tk t).lease && !keeps c (x.agt o)) = true
    · simp only [hc, ↓reduceIte, post_wa, setTask_wa]
    · simp only [hc, ↓reduceIte, Bool.false_eq_true]
theorem foldl_wa {α : Type} (f : State → α → State) (hf : ∀ x a, f (withAway x v) a = withAway (f x a) v) :
    ∀ (l : List α) (x : State), l.foldl f (withAway x v) = withAway (l.foldl f x) v
  | [], _ => rfl
  | a :: l, x => by simp only [List.foldl_cons, hf]; exact foldl_wa f hf l _
@[simp] theorem reapTasks_wa (c : Cfg) (x : State) : reapTasks c (withAway x v) = withAway (reapTasks c x) v :=
  foldl_wa _ (reapTask_wa c) _ _
@[simp] theorem spawnFor_wa (c : Cfg) (pl : List Nat) (x : State) (t : Nat) :
    spawnFor c pl (withAway x v) t = withAway (spawnFor c pl x t) v := by
  unfold spawnFor
  show (match nextAgent c x with
    | some a => if pl.contains t && members x < c.roster then _ else withAway x v
    | none => withAway x v) = _
  cases nextAgent c x with
  | none => rfl
  | some a =>
    dsimp only
    by_cases h : (pl.contains t && members x < c.roster) = true
    · simp only [h, ↓reduceIte]; rw [← claimed_wa]; rfl
    · simp only [h, ↓reduceIte, Bool.false_eq_true]
@[simp] theorem lifecycle_wa (c : Cfg) (x : State) : lifecycle c (withAway x v) = withAway (lifecycle c x) v := by
  unfold lifecycle
  show (let pl := pool c x
    let ended := c.agents.foldl (fun y a => if finished c x a && !reusable c x a then endAgent y a else y) (withAway x v)
    let told := c.agents.foldl (fun y a =>
      if reusable c x a && !pl.all (y.agt a).told.contains then
        post (setAg y a fun g => { g with told := pl ++ g.told }) ⟨none, a, false, .digest, 0⟩
      else y) ended
    if c.agents.any (reusable c x) then told else c.tasks.foldl (spawnFor c pl) told) = _
  have e1 := foldl_wa (v := v) (fun y a => if finished c x a && !reusable c x a then endAgent y a else y)
    (fun y a => by split <;> simp) c.agents x
  have e2 := foldl_wa (v := v) (fun y a =>
      if reusable c x a && !(pool c x).all (y.agt a).told.contains then
        post (setAg y a fun g => { g with told := pool c x ++ g.told }) ⟨none, a, false, .digest, 0⟩
      else y) (fun y a => by
        simp only [agt_wa]
        by_cases hc : (reusable c x a && !(pool c x).all (y.agt a).told.contains) = true <;>
          simp only [hc, ↓reduceIte, post_wa, setAg_wa, Bool.false_eq_true]) c.agents
  have e3 := foldl_wa (v := v) (spawnFor c (pool c x)) (fun y t => spawnFor_wa c _ y t) c.tasks
  simp only [e1, e2, e3]
  split <;> rfl
theorem tickS_wa (c : Cfg) (x : State) : tickS c (withAway x v) = withAway (tickS c x) v := by
  simp only [tickS, reapTasks_wa, reapLocks_wa, lifecycle_wa]; rfl
end

theorem blind_notify {c : Cfg} {y y' : State} (h : blind y = blind y') (t : Nat) : blind (notify c y t) = blind (notify c y' t) := by
  have ht : y.task = y'.task := by have := congrArg State.task h; exact this
  have he : y.evs = y'.evs := by have := congrArg State.evs h; exact this
  have htk : ∀ u, y.tk u = y'.tk u := fun u => by simp [State.tk, ht]
  have hs : sent c y t = sent c y' t := by simp [sent, he, htk]
  unfold notify
  rw [htk, hs]
  split
  · have hc : y.cbox.map (fun n => { n with urgent := false }) = y'.cbox.map (fun n => { n with urgent := false }) :=
      congrArg State.cbox h
    revert h hc he; cases y; cases y'; simp [blind, tellC, logEv]; intros; simp_all
  · exact h
theorem blind_notices {c : Cfg} : ∀ (l : List Nat) {y y' : State}, blind y = blind y' →
    blind (l.foldl (notify c) y) = blind (l.foldl (notify c) y')
  | [], _, _, h => h
  | t :: l, _, _, h => blind_notices l (blind_notify h t)

/-- A3: non-interference. The away flag changes no staffing decision: the tick with the flag set to anything ends where
the tick with it as it is ends (reap, spawns, ends, digests, git, the event log), but for the urgency of the notices -/
theorem A3 (c : Cfg) (s : State) (v : Option Nat) : blind (tickOf c (withAway s v)) = blind (tickOf c s) := by
  unfold tickOf notices
  rw [tickS_wa]
  exact blind_notices c.tasks rfl

-- ---------- A4: idempotent, and the digest is the events since away ----------
/-- a second away is refused: it keeps the first since -/
theorem away_twice {c : Cfg} {s s' : State} (h : step c s .awayOn = some s') :
    s'.away = some s.evs.length ∧ step c s' .awayOn = none := by
  simp only [step, awayOn, when_eq_some] at h
  obtain ⟨_, rfl⟩ := h
  simp [step, awayOn, when]
/-- `--back` when not away is refused: nothing changes -/
theorem back_twice {c : Cfg} {s s' : State} (h : step c s .back = some s') : s'.away = none ∧ step c s' .back = none := by
  simp only [step, back, when_eq_some] at h
  obtain ⟨_, rfl⟩ := h
  simp [step, back, when]
/-- while away, every step but `--back` keeps the since -/
theorem since_kept {c : Cfg} {s s' : State} {act : Action} (h : step c s act = some s') (hb : act ≠ .back) {n : Nat}
    (ha : s.away = some n) : s'.away = some n := by
  rcases (side_step h).2.1 with e | e | e
  · rw [e, ha]
  · subst e; simp [step, awayOn, when, ha] at h
  · exact absurd e hb
/-- `--back` keeps the digest of the events since away and clears the flag -/
theorem back_digest {c : Cfg} {s s' : State} (h : step c s .back = some s') :
    ∃ since, s.away = some since ∧ s'.away = none ∧ s'.digest = some (digestOf c s since) := by
  simp only [step, back, when_eq_some] at h
  obtain ⟨ha, rfl⟩ := h
  cases e : s.away with
  | none => simp [e] at ha
  | some n => exact ⟨n, rfl, rfl, by simp [e]⟩
/-- the digest's questions are oldest first: by their latest question event, then id -/
theorem questions_sorted (c : Cfg) (s : State) (since : Nat) : (questions c s since).Pairwise fun a b =>
    qtime s since a < qtime s since b ∨ (qtime s since a = qtime s since b ∧ a ≤ b) := by
  unfold questions
  have hs := List.pairwise_mergeSort (le := fun (x y : Nat × Nat) => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega)
    (((c.tasks.filter fun t => (s.tk t).st == .blocked).map fun t => (qtime s since t, t)))
  have hm : ∀ p ∈ (((c.tasks.filter fun t => (s.tk t).st == .blocked).map fun t => (qtime s since t, t))).mergeSort
      (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2)), p.1 = qtime s since p.2 := fun p hp => by
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 ((List.mergeSort_perm _ _).mem_iff.1 hp); rfl
  rw [List.pairwise_map]
  refine hs.imp_of_mem fun {a b} ha hb hab => ?_
  rw [← hm a ha, ← hm b hb]
  simp at hab; omega
/-- the digest's done: the tasks whose done is an event since away, still done -/
theorem digest_done (c : Cfg) (s : State) (since t : Nat) :
    t ∈ (digestOf c s since).done ↔ Ev.done t ∈ s.evs.drop since ∧ (s.tk t).st = .done := by
  simp only [digestOf, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    cases e <;> simp at h
    obtain ⟨h1, rfl⟩ := h; exact ⟨he, h1⟩
  · rintro ⟨he, h⟩; exact ⟨_, he, by simp [h]⟩
/-- the digest's merged (board #80): the tasks whose PR merged since away by GitHub's clock (its merge's place in `evs`,
the Lua's merged_at), with the merge recorded by watchd (task.merged_at set). So a PR merged before away and polled after
is not since, and one merged since away but not yet polled is not listed -/
theorem digest_merged (c : Cfg) (s : State) (since t : Nat) :
    t ∈ (digestOf c s since).merged ↔ Ev.merge t ∈ s.evs.drop since ∧ (s.tk t).merged = true := by
  simp only [digestOf, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    cases e <;> simp at h
    obtain ⟨h1, rfl⟩ := h; exact ⟨he, h1⟩
  · rintro ⟨he, h⟩; exact ⟨_, he, by simp [h]⟩
/-- the digest's ci: main's latest CI run as watchd last polled it -/
theorem digest_ci (c : Cfg) (s : State) (since : Nat) : (digestOf c s since).ci = s.ci := rfl
/-- the digest's ended: the slots whose agent ended since away -/
theorem digest_ended (c : Cfg) (s : State) (since a : Nat) :
    a ∈ (digestOf c s since).ended ↔ Ev.ended a ∈ s.evs.drop since := by
  simp only [digestOf, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, h⟩
    cases e <;> simp at h
    subst h; exact he
  · intro he; exact ⟨_, he, rfl⟩

end Swarm
