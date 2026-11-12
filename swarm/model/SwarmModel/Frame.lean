import SwarmModel.Model

/-! Frame lemmas: which fields of the state each change leaves alone. Every proof about a property of one
field starts from these. -/

namespace Swarm

theorem foldl_inv {α β : Type} (f : β → α → β) (P : β → Prop) (l : List α) (b : β)
    (hb : P b) (hf : ∀ b a, P b → P (f b a)) : P (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact hb
  | cons x xs ih => exact ih _ (hf _ _ hb)

/-- unfold one change and split its cases -/
macro "frame" defs:Lean.Parser.Tactic.simpLemma,* : tactic =>
  `(tactic| first | rfl | (simp only [$defs,*]; (repeat' split) <;> simp_all))

-- the event log and the communicator's inbox: `logEv`, `tellC`, `hcLog` change nothing else
theorem logEv_ex (s : State) (e : Ev) : ∃ e', logEv s e = { s with evs := e' } := ⟨_, rfl⟩
theorem tellC_ex (s : State) (n : Note) : ∃ n', tellC s n = { s with cbox := n' } := ⟨_, rfl⟩
theorem hcLog_ex (s : State) (t : Nat) : ∃ e', hcLog s t = { s with evs := e' } := ⟨_, rfl⟩
@[simp] theorem logEv_task (s : State) (e : Ev) : (logEv s e).task = s.task := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_ag (s : State) (e : Ev) : (logEv s e).ag = s.ag := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_lock (s : State) (e : Ev) : (logEv s e).lock = s.lock := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_log (s : State) (e : Ev) : (logEv s e).log = s.log := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_cursor (s : State) (e : Ev) : (logEv s e).cursor = s.cursor := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_start (s : State) (e : Ev) : (logEv s e).start = s.start := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_seen (s : State) (e : Ev) : (logEv s e).seen = s.seen := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_pend (s : State) (e : Ev) : (logEv s e).pend = s.pend := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_early (s : State) (e : Ev) : (logEv s e).early = s.early := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_git (s : State) (e : Ev) : (logEv s e).git = s.git := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_away (s : State) (e : Ev) : (logEv s e).away = s.away := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_ccur (s : State) (e : Ev) : (logEv s e).ccur = s.ccur := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_digest (s : State) (e : Ev) : (logEv s e).digest = s.digest := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_cbox (s : State) (e : Ev) : (logEv s e).cbox = s.cbox := by obtain ⟨_, h⟩ := logEv_ex s e; rw [h]
@[simp] theorem logEv_tk (s : State) (e : Ev) (u : Nat) : (logEv s e).tk u = s.tk u := by simp [State.tk]
@[simp] theorem logEv_agt (s : State) (e : Ev) (b : Nat) : (logEv s e).agt b = s.agt b := by simp [State.agt]
@[simp] theorem logEv_cur (s : State) (e : Ev) (b : Nat) : (logEv s e).cur b = s.cur b := by simp [State.cur]
@[simp] theorem logEv_msg (s : State) (e : Ev) (i : Nat) : (logEv s e).msg i = s.msg i := by simp [State.msg]
@[simp] theorem logEv_unread (s : State) (e : Ev) (b : Nat) : unread (logEv s e) b = unread s b := rfl
@[simp] theorem tellC_task (s : State) (n : Note) : (tellC s n).task = s.task := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_ag (s : State) (n : Note) : (tellC s n).ag = s.ag := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_lock (s : State) (n : Note) : (tellC s n).lock = s.lock := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_log (s : State) (n : Note) : (tellC s n).log = s.log := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_cursor (s : State) (n : Note) : (tellC s n).cursor = s.cursor := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_start (s : State) (n : Note) : (tellC s n).start = s.start := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_seen (s : State) (n : Note) : (tellC s n).seen = s.seen := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_pend (s : State) (n : Note) : (tellC s n).pend = s.pend := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_early (s : State) (n : Note) : (tellC s n).early = s.early := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_git (s : State) (n : Note) : (tellC s n).git = s.git := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_away (s : State) (n : Note) : (tellC s n).away = s.away := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_ccur (s : State) (n : Note) : (tellC s n).ccur = s.ccur := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_digest (s : State) (n : Note) : (tellC s n).digest = s.digest := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_evs (s : State) (n : Note) : (tellC s n).evs = s.evs := by obtain ⟨_, h⟩ := tellC_ex s n; rw [h]
@[simp] theorem tellC_tk (s : State) (n : Note) (u : Nat) : (tellC s n).tk u = s.tk u := by simp [State.tk]
@[simp] theorem tellC_agt (s : State) (n : Note) (b : Nat) : (tellC s n).agt b = s.agt b := by simp [State.agt]
@[simp] theorem tellC_cur (s : State) (n : Note) (b : Nat) : (tellC s n).cur b = s.cur b := by simp [State.cur]
@[simp] theorem tellC_msg (s : State) (n : Note) (i : Nat) : (tellC s n).msg i = s.msg i := by simp [State.msg]
@[simp] theorem tellC_unread (s : State) (n : Note) (b : Nat) : unread (tellC s n) b = unread s b := rfl
@[simp] theorem hcLog_task (s : State) (t : Nat) : (hcLog s t).task = s.task := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_ag (s : State) (t : Nat) : (hcLog s t).ag = s.ag := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_lock (s : State) (t : Nat) : (hcLog s t).lock = s.lock := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_log (s : State) (t : Nat) : (hcLog s t).log = s.log := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_cursor (s : State) (t : Nat) : (hcLog s t).cursor = s.cursor := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_start (s : State) (t : Nat) : (hcLog s t).start = s.start := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_seen (s : State) (t : Nat) : (hcLog s t).seen = s.seen := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_pend (s : State) (t : Nat) : (hcLog s t).pend = s.pend := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_early (s : State) (t : Nat) : (hcLog s t).early = s.early := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_git (s : State) (t : Nat) : (hcLog s t).git = s.git := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_away (s : State) (t : Nat) : (hcLog s t).away = s.away := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_ccur (s : State) (t : Nat) : (hcLog s t).ccur = s.ccur := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_digest (s : State) (t : Nat) : (hcLog s t).digest = s.digest := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_cbox (s : State) (t : Nat) : (hcLog s t).cbox = s.cbox := by obtain ⟨_, h⟩ := hcLog_ex s t; rw [h]
@[simp] theorem hcLog_tk (s : State) (t : Nat) (u : Nat) : (hcLog s t).tk u = s.tk u := by simp [State.tk]
@[simp] theorem hcLog_agt (s : State) (t : Nat) (b : Nat) : (hcLog s t).agt b = s.agt b := by simp [State.agt]
@[simp] theorem hcLog_cur (s : State) (t : Nat) (b : Nat) : (hcLog s t).cur b = s.cur b := by simp [State.cur]
@[simp] theorem hcLog_msg (s : State) (t : Nat) (i : Nat) : (hcLog s t).msg i = s.msg i := by simp [State.msg]
@[simp] theorem hcLog_unread (s : State) (t : Nat) (b : Nat) : unread (hcLog s t) b = unread s b := rfl

@[simp] theorem setTask_ag (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).ag = s.ag := by frame setTask
@[simp] theorem setTask_lock (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).lock = s.lock := by frame setTask
@[simp] theorem setTask_log (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).log = s.log := by frame setTask
@[simp] theorem setTask_cursor (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).cursor = s.cursor := by frame setTask
@[simp] theorem setTask_start (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).start = s.start := by frame setTask
@[simp] theorem setTask_seen (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).seen = s.seen := by frame setTask
@[simp] theorem setTask_pend (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).pend = s.pend := by frame setTask
@[simp] theorem setTask_early (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).early = s.early := by frame setTask

@[simp] theorem setAg_task (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).task = s.task := by frame setAg
@[simp] theorem setAg_lock (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).lock = s.lock := by frame setAg
@[simp] theorem setAg_log (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).log = s.log := by frame setAg
@[simp] theorem setAg_cursor (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).cursor = s.cursor := by frame setAg
@[simp] theorem setAg_start (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).start = s.start := by frame setAg
@[simp] theorem setAg_seen (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).seen = s.seen := by frame setAg
@[simp] theorem setAg_pend (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).pend = s.pend := by frame setAg
@[simp] theorem setAg_early (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).early = s.early := by frame setAg

@[simp] theorem post_task (s : State) (m : Msg) : (post s m).task = s.task := by frame post
@[simp] theorem post_ag (s : State) (m : Msg) : (post s m).ag = s.ag := by frame post
@[simp] theorem post_lock (s : State) (m : Msg) : (post s m).lock = s.lock := by frame post
@[simp] theorem post_cursor (s : State) (m : Msg) : (post s m).cursor = s.cursor := by frame post
@[simp] theorem post_start (s : State) (m : Msg) : (post s m).start = s.start := by frame post
@[simp] theorem post_seen (s : State) (m : Msg) : (post s m).seen = s.seen := by frame post
@[simp] theorem post_pend (s : State) (m : Msg) : (post s m).pend = s.pend := by frame post
@[simp] theorem post_early (s : State) (m : Msg) : (post s m).early = s.early := by frame post

@[simp] theorem showMsg_task (s : State) (a i : Nat) : (showMsg s a i).task = s.task := by frame showMsg
@[simp] theorem showMsg_lock (s : State) (a i : Nat) : (showMsg s a i).lock = s.lock := by frame showMsg
@[simp] theorem showMsg_log (s : State) (a i : Nat) : (showMsg s a i).log = s.log := by frame showMsg
@[simp] theorem showMsg_start (s : State) (a i : Nat) : (showMsg s a i).start = s.start := by frame showMsg
@[simp] theorem showMsg_early (s : State) (a i : Nat) : (showMsg s a i).early = s.early := by frame showMsg

@[simp] theorem showAll_task (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).task = s.task := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem showAll_lock (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).lock = s.lock := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem showAll_log (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).log = s.log := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem showAll_start (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).start = s.start := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem showAll_early (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).early = s.early := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp

@[simp] theorem deliver_task (s : State) (a : Nat) : (deliver s a).task = s.task := by simp [deliver]
@[simp] theorem deliver_lock (s : State) (a : Nat) : (deliver s a).lock = s.lock := by simp [deliver]
@[simp] theorem deliver_log (s : State) (a : Nat) : (deliver s a).log = s.log := by simp [deliver]
@[simp] theorem deliver_start (s : State) (a : Nat) : (deliver s a).start = s.start := by simp [deliver]
@[simp] theorem deliver_early (s : State) (a : Nat) : (deliver s a).early = s.early := by simp [deliver]

@[simp] theorem takes_task (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).task = s.task := by frame takes
@[simp] theorem takes_lock (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).lock = s.lock := by frame takes
@[simp] theorem takes_log (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).log = s.log := by frame takes
@[simp] theorem takes_cursor (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).cursor = s.cursor := by frame takes
@[simp] theorem takes_start (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).start = s.start := by frame takes
@[simp] theorem takes_seen (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).seen = s.seen := by frame takes
@[simp] theorem takes_early (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).early = s.early := by frame takes

@[simp] theorem claimed_ag (s : State) (a t : Nat) : (claimed s a t).ag = s.ag := by frame claimed
@[simp] theorem claimed_lock (s : State) (a t : Nat) : (claimed s a t).lock = s.lock := by frame claimed
@[simp] theorem claimed_log (s : State) (a t : Nat) : (claimed s a t).log = s.log := by frame claimed
@[simp] theorem claimed_cursor (s : State) (a t : Nat) : (claimed s a t).cursor = s.cursor := by frame claimed
@[simp] theorem claimed_start (s : State) (a t : Nat) : (claimed s a t).start = s.start := by frame claimed
@[simp] theorem claimed_seen (s : State) (a t : Nat) : (claimed s a t).seen = s.seen := by frame claimed
@[simp] theorem claimed_pend (s : State) (a t : Nat) : (claimed s a t).pend = s.pend := by frame claimed
@[simp] theorem claimed_early (s : State) (a t : Nat) : (claimed s a t).early = s.early := by frame claimed

@[simp] theorem releaseAll_ag (s : State) (a : Nat) : (releaseAll s a).ag = s.ag := by frame releaseAll
@[simp] theorem releaseAll_log (s : State) (a : Nat) : (releaseAll s a).log = s.log := by frame releaseAll
@[simp] theorem releaseAll_cursor (s : State) (a : Nat) : (releaseAll s a).cursor = s.cursor := by frame releaseAll
@[simp] theorem releaseAll_start (s : State) (a : Nat) : (releaseAll s a).start = s.start := by frame releaseAll
@[simp] theorem releaseAll_seen (s : State) (a : Nat) : (releaseAll s a).seen = s.seen := by frame releaseAll
@[simp] theorem releaseAll_pend (s : State) (a : Nat) : (releaseAll s a).pend = s.pend := by frame releaseAll
@[simp] theorem releaseAll_early (s : State) (a : Nat) : (releaseAll s a).early = s.early := by frame releaseAll

@[simp] theorem reapTask_ag (c : Cfg) (s : State) (t : Nat) : (reapTask c s t).ag = s.ag := by frame reapTask
@[simp] theorem reapTask_lock (c : Cfg) (s : State) (t : Nat) : (reapTask c s t).lock = s.lock := by frame reapTask
@[simp] theorem reapTask_cursor (c : Cfg) (s : State) (t : Nat) : (reapTask c s t).cursor = s.cursor := by frame reapTask
@[simp] theorem reapTask_start (c : Cfg) (s : State) (t : Nat) : (reapTask c s t).start = s.start := by frame reapTask
@[simp] theorem reapTask_seen (c : Cfg) (s : State) (t : Nat) : (reapTask c s t).seen = s.seen := by frame reapTask
@[simp] theorem reapTask_pend (c : Cfg) (s : State) (t : Nat) : (reapTask c s t).pend = s.pend := by frame reapTask
@[simp] theorem reapTask_early (c : Cfg) (s : State) (t : Nat) : (reapTask c s t).early = s.early := by frame reapTask

@[simp] theorem reapTasks_ag (c : Cfg) (s : State) : (reapTasks c s).ag = s.ag := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.ag = s.ag) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapTasks_lock (c : Cfg) (s : State) : (reapTasks c s).lock = s.lock := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.lock = s.lock) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapTasks_cursor (c : Cfg) (s : State) : (reapTasks c s).cursor = s.cursor := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.cursor = s.cursor) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapTasks_start (c : Cfg) (s : State) : (reapTasks c s).start = s.start := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.start = s.start) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapTasks_seen (c : Cfg) (s : State) : (reapTasks c s).seen = s.seen := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.seen = s.seen) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapTasks_pend (c : Cfg) (s : State) : (reapTasks c s).pend = s.pend := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.pend = s.pend) _ _ rfl (fun b t h => by simp [h])
@[simp] theorem reapTasks_early (c : Cfg) (s : State) : (reapTasks c s).early = s.early := by
  unfold reapTasks
  exact foldl_inv _ (fun x : State => x.early = s.early) _ _ rfl (fun b t h => by simp [h])

@[simp] theorem reapLocks_task (s : State) : (reapLocks s).task = s.task := by frame reapLocks
@[simp] theorem reapLocks_ag (s : State) : (reapLocks s).ag = s.ag := by frame reapLocks
@[simp] theorem reapLocks_log (s : State) : (reapLocks s).log = s.log := by frame reapLocks
@[simp] theorem reapLocks_cursor (s : State) : (reapLocks s).cursor = s.cursor := by frame reapLocks
@[simp] theorem reapLocks_start (s : State) : (reapLocks s).start = s.start := by frame reapLocks
@[simp] theorem reapLocks_seen (s : State) : (reapLocks s).seen = s.seen := by frame reapLocks
@[simp] theorem reapLocks_pend (s : State) : (reapLocks s).pend = s.pend := by frame reapLocks
@[simp] theorem reapLocks_early (s : State) : (reapLocks s).early = s.early := by frame reapLocks

@[simp] theorem endAgent_log (s : State) (a : Nat) : (endAgent s a).log = s.log := by simp [endAgent]
@[simp] theorem endAgent_cursor (s : State) (a : Nat) : (endAgent s a).cursor = s.cursor := by simp [endAgent]
@[simp] theorem endAgent_start (s : State) (a : Nat) : (endAgent s a).start = s.start := by simp [endAgent]
@[simp] theorem endAgent_seen (s : State) (a : Nat) : (endAgent s a).seen = s.seen := by simp [endAgent]
@[simp] theorem endAgent_pend (s : State) (a : Nat) : (endAgent s a).pend = s.pend := by simp [endAgent]
@[simp] theorem endAgent_early (s : State) (a : Nat) : (endAgent s a).early = s.early := by simp [endAgent]

@[simp] theorem spawnFor_lock (c : Cfg) (pl : List Nat) (s : State) (t : Nat) : (spawnFor c pl s t).lock = s.lock := by frame spawnFor
@[simp] theorem spawnFor_log (c : Cfg) (pl : List Nat) (s : State) (t : Nat) : (spawnFor c pl s t).log = s.log := by frame spawnFor
@[simp] theorem spawnFor_pend (c : Cfg) (pl : List Nat) (s : State) (t : Nat) : (spawnFor c pl s t).pend = s.pend := by frame spawnFor
@[simp] theorem spawnFor_early (c : Cfg) (pl : List Nat) (s : State) (t : Nat) : (spawnFor c pl s t).early = s.early := by frame spawnFor

@[simp] theorem lifecycle_pend (c : Cfg) (s : State) : (lifecycle c s).pend = s.pend := by
  unfold lifecycle
  simp only []
  split
  · exact foldl_inv _ (fun x : State => x.pend = s.pend) _ _ (foldl_inv _ (fun x : State => x.pend = s.pend) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])
  · exact foldl_inv _ (fun x : State => x.pend = s.pend) _ _ (foldl_inv _ (fun x : State => x.pend = s.pend) _ _ (foldl_inv _ (fun x : State => x.pend = s.pend) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])) (fun b a h => by simp [h])
@[simp] theorem lifecycle_early (c : Cfg) (s : State) : (lifecycle c s).early = s.early := by
  unfold lifecycle
  simp only []
  split
  · exact foldl_inv _ (fun x : State => x.early = s.early) _ _ (foldl_inv _ (fun x : State => x.early = s.early) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])
  · exact foldl_inv _ (fun x : State => x.early = s.early) _ _ (foldl_inv _ (fun x : State => x.early = s.early) _ _ (foldl_inv _ (fun x : State => x.early = s.early) _ _ rfl (fun b a h => by split <;> simp [h])) (fun b a h => by split <;> simp [h])) (fun b a h => by simp [h])

-- the block notices change the event log and the communicator's inbox alone
theorem notify_ex (c : Cfg) (s : State) (t : Nat) : ∃ e n, notify c s t = { s with evs := e, cbox := n } := by
  unfold notify; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨s.evs, s.cbox, rfl⟩
theorem notices_ex (c : Cfg) (s : State) : ∃ e n, notices c s = { s with evs := e, cbox := n } := by
  unfold notices
  exact foldl_inv _ (fun x : State => ∃ e n, x = { s with evs := e, cbox := n }) _ _ ⟨s.evs, s.cbox, rfl⟩ (fun b t h => by
    obtain ⟨e, n, rfl⟩ := h
    obtain ⟨e', n', h'⟩ := notify_ex c { s with evs := e, cbox := n } t
    exact ⟨e', n', h'⟩)
theorem tickOf_ex (c : Cfg) (s : State) : ∃ e n, tickOf c s = { tickS c s with evs := e, cbox := n } := notices_ex c _
@[simp] theorem notices_task (c : Cfg) (s : State) : (notices c s).task = s.task := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_ag (c : Cfg) (s : State) : (notices c s).ag = s.ag := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_lock (c : Cfg) (s : State) : (notices c s).lock = s.lock := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_log (c : Cfg) (s : State) : (notices c s).log = s.log := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_cursor (c : Cfg) (s : State) : (notices c s).cursor = s.cursor := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_start (c : Cfg) (s : State) : (notices c s).start = s.start := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_seen (c : Cfg) (s : State) : (notices c s).seen = s.seen := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_pend (c : Cfg) (s : State) : (notices c s).pend = s.pend := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_early (c : Cfg) (s : State) : (notices c s).early = s.early := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_git (c : Cfg) (s : State) : (notices c s).git = s.git := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_away (c : Cfg) (s : State) : (notices c s).away = s.away := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_ccur (c : Cfg) (s : State) : (notices c s).ccur = s.ccur := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem notices_digest (c : Cfg) (s : State) : (notices c s).digest = s.digest := by obtain ⟨e, n, h⟩ := notices_ex c s; rw [h]
@[simp] theorem tickOf_task (c : Cfg) (s : State) : (tickOf c s).task = (tickS c s).task := notices_task ..
@[simp] theorem tickOf_ag (c : Cfg) (s : State) : (tickOf c s).ag = (tickS c s).ag := notices_ag ..
@[simp] theorem tickOf_lock (c : Cfg) (s : State) : (tickOf c s).lock = (tickS c s).lock := notices_lock ..
@[simp] theorem tickOf_log (c : Cfg) (s : State) : (tickOf c s).log = (tickS c s).log := notices_log ..
@[simp] theorem tickOf_cursor (c : Cfg) (s : State) : (tickOf c s).cursor = (tickS c s).cursor := notices_cursor ..
@[simp] theorem tickOf_start (c : Cfg) (s : State) : (tickOf c s).start = (tickS c s).start := notices_start ..
@[simp] theorem tickOf_seen (c : Cfg) (s : State) : (tickOf c s).seen = (tickS c s).seen := notices_seen ..
@[simp] theorem tickOf_git' (c : Cfg) (s : State) : (tickOf c s).git = (tickS c s).git := notices_git ..
@[simp] theorem tickOf_pend (c : Cfg) (s : State) : (tickOf c s).pend = s.pend := by simp [tickOf, tickS]
@[simp] theorem tickOf_early (c : Cfg) (s : State) : (tickOf c s).early = s.early := by simp [tickOf, tickS]
@[simp] theorem tickOf_tk (c : Cfg) (s : State) (t : Nat) : (tickOf c s).tk t = (tickS c s).tk t := by simp [State.tk]
@[simp] theorem tickOf_agt (c : Cfg) (s : State) (a : Nat) : (tickOf c s).agt a = (tickS c s).agt a := by simp [State.agt]
@[simp] theorem tickOf_cur (c : Cfg) (s : State) (a : Nat) : (tickOf c s).cur a = (tickS c s).cur a := by simp [State.cur]

@[simp] theorem unbelieve_task (s : State) (a t : Nat) : (unbelieve s a t).task = s.task := by frame unbelieve
@[simp] theorem unbelieve_lock (s : State) (a t : Nat) : (unbelieve s a t).lock = s.lock := by frame unbelieve
@[simp] theorem unbelieve_log (s : State) (a t : Nat) : (unbelieve s a t).log = s.log := by frame unbelieve
@[simp] theorem unbelieve_cursor (s : State) (a t : Nat) : (unbelieve s a t).cursor = s.cursor := by frame unbelieve
@[simp] theorem unbelieve_start (s : State) (a t : Nat) : (unbelieve s a t).start = s.start := by frame unbelieve
@[simp] theorem unbelieve_seen (s : State) (a t : Nat) : (unbelieve s a t).seen = s.seen := by frame unbelieve
@[simp] theorem unbelieve_pend (s : State) (a t : Nat) : (unbelieve s a t).pend = s.pend := by frame unbelieve
@[simp] theorem unbelieve_early (s : State) (a t : Nat) : (unbelieve s a t).early = s.early := by frame unbelieve

@[simp] theorem awake_task (s : State) (a : Nat) : (awake s a).task = s.task := by frame awake
@[simp] theorem awake_lock (s : State) (a : Nat) : (awake s a).lock = s.lock := by frame awake
@[simp] theorem awake_log (s : State) (a : Nat) : (awake s a).log = s.log := by frame awake
@[simp] theorem awake_cursor (s : State) (a : Nat) : (awake s a).cursor = s.cursor := by frame awake
@[simp] theorem awake_start (s : State) (a : Nat) : (awake s a).start = s.start := by frame awake
@[simp] theorem awake_seen (s : State) (a : Nat) : (awake s a).seen = s.seen := by frame awake
@[simp] theorem awake_pend (s : State) (a : Nat) : (awake s a).pend = s.pend := by frame awake
@[simp] theorem awake_early (s : State) (a : Nat) : (awake s a).early = s.early := by frame awake

-- a change of git alone: the tick's git step, an agent's git command, the world in a worktree
@[simp] theorem agt_withGit (s : State) (g : Git) (a : Nat) : ({ s with git := g } : State).agt a = s.agt a := rfl
@[simp] theorem tk_withGit (s : State) (g : Git) (t : Nat) : ({ s with git := g } : State).tk t = s.tk t := rfl
@[simp] theorem cur_withGit (s : State) (g : Git) (a : Nat) : ({ s with git := g } : State).cur a = s.cur a := rfl
@[simp] theorem msg_withGit (s : State) (g : Git) (i : Nat) : ({ s with git := g } : State).msg i = s.msg i := rfl
@[simp] theorem unread_withGit (s : State) (g : Git) (a : Nat) : unread ({ s with git := g } : State) a = unread s a := rfl
-- a change of the new fields alone: the event log, the away flag, the communicator's inbox and cursor, the digest
@[simp high] theorem tk_withNew (s : State) (e w n k d) (t : Nat) :
    ({ s with evs := e, away := w, cbox := n, ccur := k, digest := d } : State).tk t = s.tk t := rfl
@[simp high] theorem agt_withNew (s : State) (e w n k d) (a : Nat) :
    ({ s with evs := e, away := w, cbox := n, ccur := k, digest := d } : State).agt a = s.agt a := rfl
@[simp high] theorem cur_withNew (s : State) (e w n k d) (a : Nat) :
    ({ s with evs := e, away := w, cbox := n, ccur := k, digest := d } : State).cur a = s.cur a := rfl
@[simp high] theorem msg_withNew (s : State) (e w n k d) (i : Nat) :
    ({ s with evs := e, away := w, cbox := n, ccur := k, digest := d } : State).msg i = s.msg i := rfl
@[simp high] theorem unread_withNew (s : State) (e w n k d) (a : Nat) :
    unread ({ s with evs := e, away := w, cbox := n, ccur := k, digest := d } : State) a = unread s a := rfl

theorem tickS_git (c : Cfg) (s : State) :
    tickS c s = { lifecycle c (reapLocks (reapTasks c s)) with git := gitTick c (reapLocks (reapTasks c s)) } := rfl
theorem tickOf_git (c : Cfg) (s : State) :
    tickOf c s = { lifecycle c (reapLocks (reapTasks c s)) with git := gitTick c (reapLocks (reapTasks c s)), evs := (tickOf c s).evs, cbox := (tickOf c s).cbox } := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem used_tickOf (c : Cfg) (s : State) (w : Nat) : used c (tickOf c s) w = used c (tickS c s) w := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem idleFree_tickOf (c : Cfg) (s : State) (a : Nat) : idleFree (tickOf c s) a = idleFree (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem holds_tickOf (c : Cfg) (s : State) (a : Nat) : holds (tickOf c s) a = holds (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem lockHeld_tickOf (c : Cfg) (s : State) (a : Nat) : lockHeld (tickOf c s) a = lockHeld (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem wtmap_tickOf (c : Cfg) (s : State) (a : Nat) : wtmap c (tickOf c s) a = wtmap c (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem unlanded_tickOf (c : Cfg) (s : State) (a : Nat) : unlanded c (tickOf c s) a = unlanded c (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem members_tickOf (c : Cfg) (s : State) : members (tickOf c s) = members (tickS c s) := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem pool_tickOf (c : Cfg) (s : State) : pool c (tickOf c s) = pool c (tickS c s) := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem startable_tickOf (c : Cfg) (s : State) (t : Nat) : startable (tickOf c s) t = startable (tickS c s) t := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem claimable_tickOf (c : Cfg) (s : State) (t : Nat) : claimable (tickOf c s) t = claimable (tickS c s) t := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem finished_tickOf (c : Cfg) (s : State) (a : Nat) : finished c (tickOf c s) a = finished c (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem reusable_tickOf (c : Cfg) (s : State) (a : Nat) : reusable c (tickOf c s) a = reusable c (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem unread_tickOf (c : Cfg) (s : State) (a : Nat) : unread (tickOf c s) a = unread (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem msg_tickOf (c : Cfg) (s : State) (i : Nat) : (tickOf c s).msg i = (tickS c s).msg i := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl
@[simp] theorem ends_tickOf (c : Cfg) (s : State) (a : Nat) : ends c (tickOf c s) a = ends c (tickS c s) a := by
  obtain ⟨_, _, h⟩ := tickOf_ex c s; rw [h]; rfl

end Swarm
