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

@[simp] theorem tickOf_pend (c : Cfg) (s : State) : (tickOf c s).pend = s.pend := by simp [tickOf]
@[simp] theorem tickOf_early (c : Cfg) (s : State) : (tickOf c s).early = s.early := by simp [tickOf]

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

end Swarm
