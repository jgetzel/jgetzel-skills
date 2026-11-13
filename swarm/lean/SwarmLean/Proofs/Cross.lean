import SwarmLean.Proofs.Tasks
import SwarmLean.Proofs.Msgs
import SwarmLean.Proofs.Locks
import SwarmLean.Proofs.Watchd

/-! Board task #109: the cross-area properties. #103-#106 each proved their area's invariant under their area's
transactions: the board's (`Board.BInv`: ids unique, owners fit states, S5) under the task commands, the inbox's
(`Inbox.MInv`, S4's invariant) under the message transactions, S3's (`Locks.Good`) under lock, unlock, leave, join and
three task commands. swarm/model proves S1-S5 with every action of every area in one `step`; here that is `XCmd`, every
transaction of all four areas (task commands, post, read, deliver, lock, unlock, leave, join, `swarm end`/lifecycle's
end, and reap's three), interleaved in any order: each invariant holds after any of them (`run_xinv`), so S2-S5 and one
owner per task hold of the whole swarm, and with processes at once under `Atomic` (`atomic_xinv`). -/

namespace SwarmLean.Cross
open Board Agents

/-! ## The frames: what each area's step leaves of the others' tables -/

/-- What a step leaves of the message log, its cursors, the locks and the agents. -/
def Same (db db' : Db) : Prop :=
  db'.msgs = db.msgs ∧ db'.cursors = db.cursors ∧ db'.msgNext = db.msgNext ∧ db'.locks = db.locks ∧ db'.agents = db.agents

theorem same_refl (db db' : Db) (h : db' = db) : Same db db' := by subst h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem same_trans {a b c : Db} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem setDeps_same {db db' : Db} {i : Int} {l : List Int} {ds : List String} (h : Tasks.setDeps db i l = .ok (db', ds)) :
    Same db db' := by
  unfold Tasks.setDeps at h; split at h
  · cases h
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem grows_same {db db' : Db} (h : Same db db') : Inbox.Grows db db' := Inbox.grows_of_eq h.1 h.2.1 h.2.2.1

/-- `task release` posts at most the stop and changes no lock or agent: the db before its post is `Same`. -/
theorem release_parts (c : Tasks.Ctx) (i : Int) (af : Option (List Int)) (db : Db) :
    Same db (Tasks.release c i af db).1 ∨ ∃ X now frm dest body u, ∃ f : Task → Task, Same db X ∧
      (Tasks.release c i af db).1 = (Msgs.post X now frm dest body u).1.set i f := by
  unfold Tasks.release
  split
  · exact .inl (same_refl _ _ rfl)
  · dsimp only
    split
    · exact .inl (same_refl _ _ rfl)
    · rename_i db1 h1
      have e1 : Same db db1 := by
        split at h1 <;> (split at h1 <;> first | (cases h1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) | cases h1)
      split
      · exact .inl (same_refl _ _ rfl)
      · rename_i db2 h2
        have e2 : Same db1 db2 := by
          split at h2
          · cases h' : Tasks.setDeps db1 i _ with
            | error e => rw [h'] at h2; cases h2
            | ok p => rw [h'] at h2; cases h2; exact setDeps_same h'
          · cases h2; exact same_refl _ _ rfl
        split
        · refine .inr ⟨_, _, _, _, _, _, _, ?_, rfl⟩
          exact same_trans (same_trans e1 e2) ⟨rfl, rfl, rfl, rfl, rfl⟩
        · exact .inl (same_trans (same_trans e1 e2) ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- One step of a task command keeps the message log growing only, with fresh ids (`Inbox.Grows`). -/
theorem tcmd_grows (c : TCmd) (db : Db) (h0 : 0 < db.msgNext) : Inbox.Grows db (c.step db).1 := by
  cases c <;> simp only [TCmd.step]
  case release c i af =>
    rcases release_parts c i af db with h | ⟨X, _, _, _, _, _, _, hX, e⟩
    · exact grows_same h
    · rw [e]; exact Inbox.grows_trans (grows_same hX) (Inbox.grows_post _ _ _ _ _ _ _)
  all_goals first
    | (unfold Tasks.add; repeat' split) | (unfold Tasks.claim; dsimp only; repeat' split)
    | (unfold Tasks.after; repeat' split) | (unfold Tasks.priority; repeat' split)
    | (unfold Tasks.renew; repeat' split) | (unfold Tasks.done; repeat' split)
    | (unfold Tasks.block; repeat' split) | (unfold Tasks.unblock; dsimp only; repeat' split)
    | (unfold Tasks.edit; dsimp only; repeat' split)
    | (unfold Tasks.drop; repeat' split) | skip
  all_goals first
    | exact Inbox.grows_refl _
    | exact Inbox.grows_of_eq rfl rfl rfl
    | exact Inbox.grows_trans (Inbox.grows_of_eq rfl rfl rfl) (Inbox.grows_post _ _ _ _ _ _ _)
    | exact Inbox.grows_trans (Inbox.grows_trans (Inbox.grows_of_eq rfl rfl rfl) (Inbox.grows_post _ _ _ _ _ _ _))
        (Inbox.grows_of_eq rfl rfl rfl)
    | exact Inbox.grows_trans (Inbox.grows_touch _ _ _ _ _ h0) (Inbox.grows_of_eq rfl rfl rfl)
    | exact Inbox.grows_touch _ _ _ _ _ h0
    | (have hs := setDeps_same ‹Tasks.setDeps _ _ _ = .ok _›
       exact Inbox.grows_trans (grows_same hs) (Inbox.grows_of_eq rfl rfl rfl))

/-- One step of a task command leaves the locks and makes no agent stop being live (only its own `touch` adds one). -/
theorem tcmd_frame (c : TCmd) (db : Db) : (c.step db).1.locks = db.locks ∧ Locks.Grows db (c.step db).1 := by
  cases c
  case board => exact ⟨rfl, Locks.grows_refl rfl⟩
  all_goals simp only [TCmd.step]
  case release c i af =>
    rcases release_parts c i af db with h | ⟨X, _, _, _, _, _, _, hX, e⟩
    · exact ⟨h.2.2.2.1, Locks.grows_refl h.2.2.2.2⟩
    · rw [e]; exact ⟨hX.2.2.2.1, Locks.grows_refl hX.2.2.2.2⟩
  all_goals first
    | (unfold Tasks.add; repeat' split) | (unfold Tasks.claim; dsimp only; repeat' split)
    | (unfold Tasks.after; repeat' split) | (unfold Tasks.priority; repeat' split)
    | (unfold Tasks.renew; repeat' split) | (unfold Tasks.done; repeat' split)
    | (unfold Tasks.block; repeat' split) | (unfold Tasks.unblock; dsimp only; repeat' split)
    | (unfold Tasks.edit; dsimp only; repeat' split)
    | (unfold Tasks.drop; repeat' split) | skip
  all_goals first
    | exact ⟨rfl, Locks.grows_refl rfl⟩
    | exact Locks.grows_refl rfl
    | exact ⟨Locks.touch_locks _ _ _ _ _, Locks.grows_of_agents rfl (Locks.touch_grows _ _ _ _ _)⟩
    | (have hs := setDeps_same ‹Tasks.setDeps _ _ _ = .ok _›
       exact ⟨hs.2.2.2.1, Locks.grows_refl hs.2.2.2.2⟩)

/-- `touch` leaves the tasks. -/
theorem touch_tasks (db : Db) n cwd here now : (touch db n cwd here now).tasks = db.tasks ∧
    (touch db n cwd here now).taskNext = db.taskNext := by
  unfold touch Agents.newInbox; split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

/-- A step that maps the tasks by a function that keeps ids and well-owned tasks keeps the board's invariant. -/
theorem binv_map {db db' : Db} {f : Task → Task} (ht : db'.tasks = db.tasks.map f) (hn : db'.taskNext = db.taskNext)
    (hid : ∀ u, (f u).id = u.id) (hok : ∀ u, TaskOk u → TaskOk (f u)) (h : BInv db) : BInv db' := by
  have hids : db'.tasks.map (·.id) = db.tasks.map (·.id) := by
    rw [ht, List.map_map]; exact List.map_congr_left fun u _ => hid u
  have mem : ∀ t ∈ db'.tasks, ∃ u ∈ db.tasks, t = f u := fun t ht' => by
    rw [ht] at ht'; obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht'; exact ⟨u, hu, rfl⟩
  unfold BInv Inv at *
  refine ⟨⟨hids ▸ h.1.1, fun t ht' => ?_, fun t ht' => ?_⟩, fun t ht' => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := mem t ht'; rw [hid, hn]; exact h.1.2.1 u hu
  · obtain ⟨u, hu, rfl⟩ := mem t ht'; exact (hok u ⟨h.1.2.2 u hu, h.2 u hu⟩).1
  · obtain ⟨u, hu, rfl⟩ := mem t ht'; exact (hok u ⟨h.1.2.2 u hu, h.2 u hu⟩).2

/-- `Agents.release` (leave, end, reap) keeps the board's invariant: what it reopens is open with no owner. -/
theorem binv_release {db db' : Db} {n : String} (ht : db'.tasks = (release db n).tasks)
    (hn : db'.taskNext = db.taskNext) (h : BInv db) : BInv db' := by
  refine binv_map (f := fun t => if t.owner == some n && (t.state = .claimed || t.state = .blocked) then
    { t with state := .open, owner := none, lease_until := none, question := none } else t) ht hn
    (fun u => by split <;> rfl) (fun u hu => ?_) h
  split
  · simp [TaskOk, Task.Owned, DoneEv]
  · exact hu

/-- An end (`Agents.release` and the row ended) keeps S3: it drops the agent's locks, ends no other agent, starts none. -/
theorem good_end {db db' : Db} {n : String} {t : Int} (hl : ∀ l ∈ db'.locks, l ∈ db.locks ∧ l.agent ≠ some n)
    (hdown : ∀ a, Locks.Live db' a = true → Locks.Live db a = true)
    (hother : ∀ a, a ≠ n → Locks.Live db a = true → Locks.Live db' a = true) (h : Locks.Good db t) : Locks.Good db' t :=
  Locks.good_sub (fun l h' => (hl l h').1) hdown
    (fun l h' a e hv => hother a (fun e' => (hl l h').2 (e ▸ e' ▸ rfl)) hv) h

/-- `Locks.Live` after two row updates that keep names and end rows at most. -/
theorem live_two {db : Db} {n a : String} {f g : Agent → Agent} (hf : ∀ x, (f x).name = x.name) (hg : ∀ x, (g x).name = x.name)
    (hfe : ∀ x, (f x).ended.isNone = true → x.ended.isNone = true) (hge : ∀ x, (g x).ended.isNone = true → x.ended.isNone = true) :
    (Locks.Live ((db.setAgent n f).setAgent n g) a = true → Locks.Live db a = true) ∧
    (a ≠ n → Locks.Live ((db.setAgent n f).setAgent n g) a = Locks.Live db a) :=
  ⟨fun h => Locks.live_setAgent_le hf hfe (Locks.live_setAgent_le hg hge h),
   fun e => by rw [Locks.live_setAgent hg e, Locks.live_setAgent hf e]⟩

/-! ## Every transaction of every area -/

/-- Every transaction the theorems of #103-#106 cover, of all four areas: the task commands, the message transactions,
the lock commands with leave and join, and watchd's end and reaps. -/
inductive XCmd
  | task (c : TCmd)
  | post (now : Int) (frm dest body : String) (urgent : Bool) (kind : Option String)
  | read (n : String)
  | deliver (n : String) (budget : Nat)
  | lock (c : Locks.LCmd)
  | end_ (n : String) (hc : Option String) (force : Bool) (by_ : Option String) (now : Int)
  | reapTask (r : Task) (t now : Int)
  | reapLock (l : Lock) (t now : Int)
  | reapGone (n h : String) (t : Int)

/-- Each transaction's effect on the db: the CLI's own steps, as each area's theorems run them. -/
def XCmd.step : XCmd → Db → Db
  | .task c, db => (c.step db).1
  | .post now f d b u k, db => (Inbox.MCmd.step (.post now f d b u k) db).1
  | .read n, db => (Inbox.MCmd.step (.read n) db).1
  | .deliver n b, db => (Inbox.MCmd.step (.deliver n b) db).1
  | .lock c, db => (c.step db).1
  | .end_ n hc force by_ now, db => (Lifecycle.endStep n hc force by_ now db).1
  | .reapTask r t now, db => (Watchd.reapTask r t now db).1
  | .reapLock l t now, db => (Watchd.reapLock l t now db).1
  | .reapGone n h t, db => (Watchd.reapGone n h t db).1

/-- Every area's invariant at time `t`: the board's (ids, owners, S5), the inbox's (S4's) and the locks' (S3). -/
def XInv (db : Db) (t : Int) : Prop := BInv db ∧ Inbox.MInv db ∧ Locks.Good db t

/-- `t` is no earlier than the clock of each `swarm lock` among `cs` (`Locks.Before`). -/
def XBefore (t : Int) (cs : List XCmd) : Prop := ∀ x ∈ cs, ∀ c p r l, x = .lock (.lock c p r l) → c.now ≤ t

/-- `take` (read, deliver) moves a cursor only. -/
theorem take_keep (n : String) (pick : List Msg → List Msg) (db : Db) : (Msgs.take n pick db).1.tasks = db.tasks ∧
    (Msgs.take n pick db).1.taskNext = db.taskNext ∧ (Msgs.take n pick db).1.locks = db.locks ∧
    (Msgs.take n pick db).1.agents = db.agents := by
  unfold Msgs.take; dsimp only; split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- The lock commands' task steps are the task commands'. -/
def toT : Cmd → TCmd
  | .add c a => .add c a
  | .claim c i l => .claim c i l
  | .release c i af => .release c i af
  | .board => .board

theorem toT_step (c : Cmd) (db : Db) : (c.step db).1 = ((toT c).step db).1 := by cases c <;> rfl

theorem grows_parts {a X c : Db} (h : Inbox.Grows a X) (hm : c.msgs = X.msgs) (hc : c.cursors = X.cursors)
    (hn : c.msgNext = X.msgNext) : Inbox.Grows a c := Inbox.grows_trans h (Inbox.grows_of_eq hm hc hn)

theorem grows_ni (db X : Db) (n : String) (hm : X.msgs = db.msgs) (hc : X.cursors = db.cursors)
    (hn : X.msgNext = db.msgNext) (h0 : 0 < db.msgNext) : Inbox.Grows db (newInbox X n) :=
  Inbox.grows_trans (Inbox.grows_of_eq hm hc hn) (Inbox.grows_newInbox X n (hn ▸ h0))

theorem bind_grows (db : Db) n cwd hc model r now (h0 : 0 < db.msgNext) :
    Inbox.Grows db (Agents.bind db n cwd hc model r now).1 := by
  unfold Agents.bind; dsimp only
  repeat' split
  all_goals first
    | exact Inbox.grows_refl _
    | exact Inbox.grows_of_eq rfl rfl rfl
    | exact grows_parts (X := newInbox _ n) (grows_ni _ _ n (by rfl) (by rfl) (by rfl) h0) rfl rfl rfl

theorem bind_tasks (db : Db) n cwd hc model r now : (Agents.bind db n cwd hc model r now).1.tasks = db.tasks ∧
    (Agents.bind db n cwd hc model r now).1.taskNext = db.taskNext := by
  unfold Agents.bind Agents.newInbox; dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

/-- The board's invariant after a lock command. -/
theorem lcmd_binv (c : Locks.LCmd) (db : Db) (h : BInv db) : BInv (c.step db).1 := by
  cases c with
  | lock c p r l =>
    simp only [Locks.LCmd.step]; unfold Locks.lock; dsimp only
    repeat' split
    all_goals first | exact h | exact binv_same (touch_tasks _ _ _ _ _).1 (touch_tasks _ _ _ _ _).2 h
  | unlock me p now => exact binv_same rfl rfl h
  | leave n now => exact binv_release rfl rfl h
  | join n cwd hc model r now =>
    simp only [Locks.LCmd.step]; split
    · exact h
    · exact binv_same (bind_tasks ..).1 (bind_tasks ..).2 h
  | task c => simp only [Locks.LCmd.step]; rw [toT_step]; exact step_binv _ _ h

/-- The inbox's growth under a lock command. -/
theorem lcmd_grows (c : Locks.LCmd) (db : Db) (h0 : 0 < db.msgNext) : Inbox.Grows db (c.step db).1 := by
  cases c with
  | lock c p r l =>
    simp only [Locks.LCmd.step]; unfold Locks.lock; dsimp only
    repeat' split
    all_goals first
      | exact Inbox.grows_refl _
      | exact Inbox.grows_trans (Inbox.grows_touch _ _ _ _ _ h0) (Inbox.grows_of_eq rfl rfl rfl)
  | unlock me p now => exact Inbox.grows_of_eq rfl rfl rfl
  | leave n now => exact Inbox.grows_of_eq rfl rfl rfl
  | join n cwd hc model r now =>
    simp only [Locks.LCmd.step]; split
    · exact Inbox.grows_refl _
    · exact bind_grows _ _ _ _ _ _ _ h0
  | task c => simp only [Locks.LCmd.step]; rw [toT_step]; exact tcmd_grows _ _ h0

/-- What `swarm end`'s and lifecycle's end write when they go through keeps every invariant. -/
theorem end_body (n : String) (now : Int) (x : Option String) {db : Db} {t : Int} (h : XInv db t) :
    XInv (((release db n).setAgent n fun x => { x with ended := some now, status := some "ended" }).log now (some n)
      "end" none x) t := by
  obtain ⟨hb, hm, hg⟩ := h
  refine ⟨binv_release rfl rfl hb, Inbox.grows_inv (Inbox.grows_of_eq rfl rfl rfl) hm, ?_⟩
  have L := fun a => live_two (db := db) (n := n) (a := a) (f := fun x => { x with stay := none })
    (g := fun x => { x with ended := some now, status := some "ended" }) (fun _ => rfl) (fun _ => rfl) (fun _ e => e)
    (fun _ e => by simp at e)
  exact good_end (db := db) (n := n) (fun l hl => ⟨(List.mem_filter.1 hl).1, WatchdProofs.release_locks db n l hl⟩)
    (fun a ha => (L a).1 ha) (fun a e ha => ((L a).2 e).trans ha) hg

/-- What reap's end of a gone row writes keeps every invariant. -/
theorem gone_body (n : String) (t' : Int) (y : Db → Db) (hy : ∀ d, Inbox.Grows d (y d)) (hyt : ∀ d, (y d).tasks = d.tasks)
    (hyn : ∀ d, (y d).taskNext = d.taskNext) (hyl : ∀ d, (y d).locks = d.locks) (hya : ∀ d, (y d).agents = d.agents)
    {db : Db} {t : Int} (h : XInv db t) :
    XInv (y (release (db.setAgent n fun x => { x with ended := some t', status := some "ended" }) n)) t := by
  obtain ⟨hb, hm, hg⟩ := h
  refine ⟨binv_release (hyt _) (hyn _) hb, Inbox.grows_inv (Inbox.grows_trans (Inbox.grows_of_eq rfl rfl rfl) (hy _)) hm, ?_⟩
  have L := fun a => live_two (db := db) (n := n) (a := a)
    (f := fun x => { x with ended := some t', status := some "ended" }) (g := fun x => { x with stay := none })
    (fun _ => rfl) (fun _ => rfl) (fun _ e => by simp at e) (fun _ e => e)
  have hl' : ∀ l ∈ (y (release (db.setAgent n fun x => { x with ended := some t', status := some "ended" }) n)).locks,
      l ∈ db.locks ∧ l.agent ≠ some n := fun l hl => by
    rw [hyl] at hl; exact ⟨(List.mem_filter.1 hl).1, WatchdProofs.release_locks _ n l hl⟩
  have hL : ∀ a, Locks.Live (y (release (db.setAgent n fun x => { x with ended := some t', status := some "ended" }) n)) a =
      Locks.Live ((db.setAgent n fun x => { x with ended := some t', status := some "ended" }).setAgent n
        fun x => { x with stay := none }) a := fun a => by simp only [Locks.Live, hya]; rfl
  exact good_end (db := db) (n := n) hl' (fun a ha => (L a).1 ((hL a) ▸ ha)) (fun a e ha => (hL a).symm ▸ ((L a).2 e).trans ha) hg

/-- Each transaction keeps every area's invariant. -/
theorem step_xinv (x : XCmd) {db : Db} {t : Int} (ht : XBefore t [x]) (h : XInv db t) : XInv (x.step db) t := by
  obtain ⟨hb, hm, hg⟩ := h
  have h0 : 0 < db.msgNext := hm.2.2.2
  cases x with
  | task c =>
    exact ⟨step_binv c db hb, Inbox.grows_inv (tcmd_grows c db h0) hm,
      Locks.good_grow (tcmd_frame c db).1 (tcmd_frame c db).2 hg⟩
  | post now f d b u k =>
    exact ⟨binv_same rfl rfl hb, Inbox.step_inv _ hm, Locks.good_grow rfl (Locks.grows_refl rfl) hg⟩
  | read n =>
    have k := take_keep n id db
    exact ⟨binv_same k.1 k.2.1 hb, Inbox.step_inv (.read n) hm, Locks.good_grow k.2.2.1 (Locks.grows_refl k.2.2.2) hg⟩
  | deliver n b =>
    have k := take_keep n (Msgs.fits b) db
    exact ⟨binv_same k.1 k.2.1 hb, Inbox.step_inv (.deliver n b) hm,
      Locks.good_grow k.2.2.1 (Locks.grows_refl k.2.2.2) hg⟩
  | lock c =>
    refine ⟨lcmd_binv c db hb, Inbox.grows_inv (lcmd_grows c db h0) hm, Locks.step_good c (fun y hy => ?_) hg⟩
    intro c' p r l e; rw [List.mem_singleton] at hy; subst hy; exact ht _ (List.mem_singleton_self _) c' p r l (by rw [e])
  | end_ n hc force by_ now =>
    simp only [XCmd.step]; unfold Lifecycle.endStep; dsimp only
    repeat' split
    all_goals first | exact ⟨hb, hm, hg⟩ | exact end_body n now _ ⟨hb, hm, hg⟩
  | reapTask r t' now =>
    simp only [XCmd.step]; unfold Watchd.reapTask; dsimp only
    split
    · split
      · refine ⟨binv_set (i := r.id) (f := fun x => { x with state := .open, owner := none, lease_until := none })
          (fun _ => rfl) (fun _ _ _ _ => by simp [TaskOk, Task.Owned, DoneEv]) rfl rfl hb,
          Inbox.grows_inv (Inbox.grows_trans (Inbox.grows_of_eq rfl rfl rfl) (Inbox.grows_post _ _ _ _ _ _ _)) hm,
          Locks.good_grow rfl (Locks.grows_refl rfl) hg⟩
      · exact ⟨hb, hm, hg⟩
    · exact ⟨hb, hm, hg⟩
  | reapLock l t' now =>
    simp only [XCmd.step]; unfold Watchd.reapLock; dsimp only
    split
    · exact ⟨binv_same rfl rfl hb, Inbox.grows_inv (Inbox.grows_of_eq rfl rfl rfl) hm,
        Locks.good_sub (fun _ hl => (List.mem_filter.1 hl).1) (fun _ h => h) (fun _ _ _ _ h => h) hg⟩
    · exact ⟨hb, hm, hg⟩
  | reapGone n hh t' =>
    simp only [XCmd.step]; unfold Watchd.reapGone; dsimp only
    split
    · exact gone_body n t' (fun d => (Watchd.say d t' "@all" _ false "system").log t' (some n) "reap" none (some "agent gone"))
        (fun d => Inbox.grows_trans (Inbox.grows_post _ _ _ _ _ _ _) (Inbox.grows_of_eq rfl rfl rfl))
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ⟨hb, hm, hg⟩
    · exact ⟨hb, hm, hg⟩

/-- The db after `cs` from `db`. -/
def run (db : Db) (cs : List XCmd) : Db := cs.foldl (fun d x => x.step d) db

theorem xinv_empty (t : Int) : XInv {} t := ⟨binv_empty, Inbox.inv_empty, Locks.good_empty t⟩

theorem run_xinv_from (cs : List XCmd) {db : Db} {t : Int} (ht : XBefore t cs) (h : XInv db t) : XInv (run db cs) t := by
  induction cs generalizing db with
  | nil => exact h
  | cons x xs ih =>
    exact ih (fun y hy => ht y (List.mem_cons_of_mem _ hy))
      (step_xinv x (fun y hy => ht y (by rw [List.mem_singleton.1 hy]; exact List.mem_cons_self ..)) h)

/-- Cross-area safety: after any transactions of any areas, by any agents, in any order, from the empty db, every area's
invariant holds at any time `t` no earlier than each lock's clock: task ids unique, a claimed task has an owner and an
open one none, every done task has evidence (S5); the message log and cursors in order (S4's invariant); no two locks
of different agents that hold at `t` overlap (S3). -/
theorem run_xinv (cs : List XCmd) (t : Int) (ht : XBefore t cs) : XInv (run {} cs) t :=
  run_xinv_from cs ht (xinv_empty t)

/-- No task has two owners, whatever every area did (`Board.one_owner_all` over all transactions). -/
theorem one_owner_x (cs : List XCmd) (t : Int) (ht : XBefore t cs) (i : Int) (a b : String)
    (ha : Owns (run {} cs) i a) (hb : Owns (run {} cs) i b) : a = b := by
  obtain ⟨u, hu, e1, hua⟩ := ha
  obtain ⟨v, hv, e2, hvb⟩ := hb
  have := nodup_inj (run_xinv cs t ht).1.1.1 hu hv (by omega)
  subst this; simpa [hua] using hvb

/-- S5 whatever every area did: every done task has evidence. -/
theorem done_has_evidence_x (cs : List XCmd) (t : Int) (ht : XBefore t cs) :
    ∀ u ∈ (run {} cs).tasks, u.state = .done → EvOk u.evidence := (run_xinv cs t ht).1.2

/-- S3 whatever every area did: two locks of different agents that hold at `t` don't overlap. -/
theorem locks_disjoint_x (cs : List XCmd) (t : Int) (ht : XBefore t cs) : Locks.Disjoint (run {} cs) t :=
  (run_xinv cs t ht).2.2.2

/-- With processes at once: under `Atomic`, transactions of all areas that ran together from a db keeping every
invariant leave one that keeps them. -/
theorem atomic_xinv {before after : Db} {ran : List (XCmd × Unit)} {t : Int}
    (h : Atomic (fun x d => (XCmd.step x d, ())) before after ran) (ht : XBefore t (ran.map (·.1)))
    (hi : XInv before t) : XInv after t := by
  obtain ⟨order, hp, hr⟩ := h
  have e : ∀ (cs : List XCmd) (d : Db), (replay (fun x d => (XCmd.step x d, ())) d cs).1 = run d cs := by
    intro cs; induction cs with
    | nil => intro d; rfl
    | cons x xs ih => intro d; simp only [replay, run, List.foldl]; exact ih _
  have := congrArg Prod.fst hr; simp only at this
  rw [← this, e]
  exact run_xinv_from _ (fun y hy => ht y (by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy; exact List.mem_map.2 ⟨q, hp.mem_iff.1 hq, rfl⟩)) hi

/-! ## Liveness on runs of transactions (L2's and L4's reap halves)

An infinite run is a transaction per moment (`r k`), each on what the ones before left (`at_`). Fairness is a
hypothesis of each statement: watchd's reap reaches the task (or row) with the facts it judged. Which transactions the
reap pass issues is decided in its monadic loop (`Watchd.reap`), not proved here. -/

/-- The db after the first `k` transactions of the run `r` from `db`. -/
def at_ (db : Db) (r : Nat → XCmd) : Nat → Db
  | 0 => db
  | k + 1 => (r k).step (at_ db r k)

/-- Task `i` is claimed by `o` with lease `L`. -/
def ClaimedBy (db : Db) (i : Int) (o : String) (L : Int) : Prop :=
  ∃ u, db.find i = some u ∧ u.owner = some o ∧ u.state = .claimed ∧ u.lease_until = some L

/-- L2 (model: `idleClaim_leads_to`), reap's half: on a run where reap, judging task `i` claimed by `o`, runs at some
point from `n` on with a clock past the lease `L`, the claim `(o, L)` does not last: at some point from `n` on the task
is no longer claimed by `o` with that lease (done, released, renewed, dropped, or reopened by that reap). -/
theorem claim_lapses (db : Db) (r : Nat → XCmd) (n : Nat) {i : Int} {o : String} {L : Int} {x : Task}
    (hx : (x.id : Int) = i) (ho : x.owner = some o)
    (hfair : ∃ m ≥ n, ∃ t now, r m = .reapTask x t now ∧ L < t) :
    ∃ m ≥ n, ¬ ClaimedBy (at_ db r m) i o L := by
  obtain ⟨m, hm, t, now, hr, hL⟩ := hfair
  by_cases hc : ClaimedBy (at_ db r m) i o L
  · refine ⟨m + 1, by omega, ?_⟩
    obtain ⟨u, hu, huo, hus, hul⟩ := hc
    have hu' : (at_ db r m).find x.id = some u := by rw [hx]; exact hu
    have hfire : (Watchd.reapTask x t now (at_ db r m)).2 = true := by
      unfold Watchd.reapTask; rw [hu']; simp [ho, huo, hus, hul, hL]
    have e : (at_ db r (m + 1)).find i = ((at_ db r m).set x.id
        fun y => { y with state := .open, owner := none, lease_until := none }).find i := by
      simp only [at_, hr, XCmd.step, Db.find, (WatchdProofs.reapTask_spec hfire).2]
    rintro ⟨v, hv, -, hvs, -⟩
    rw [e, ← hx, find_set_self (f := fun y => { y with state := .open, owner := none, lease_until := none })
      (fun _ => rfl) hu'] at hv
    cases hv; cases hvs
  · exact ⟨m, hm, hc⟩

/-- Row `a` is live and bound to terminal `h`. -/
def BoundLive (db : Db) (a h : String) : Prop := ∃ g, db.agent a = some g ∧ g.hc = some h ∧ g.ended = none

/-- L4 (model: `deadLive_leads_to`), reap's half: on a run where reap, finding terminal `h` gone from `hc ls`, runs on
row `a` at some point from `n` on, the row does not stay live and bound to `h`: at some point it is ended (its claims
and locks released, `WatchdProofs.reapGone_spec`) or bound elsewhere. -/
theorem gone_ends (db : Db) (r : Nat → XCmd) (n : Nat) {a h : String}
    (hfair : ∃ m ≥ n, ∃ t, r m = .reapGone a h t) : ∃ m ≥ n, ¬ BoundLive (at_ db r m) a h := by
  obtain ⟨m, hm, t, hr⟩ := hfair
  by_cases hc : BoundLive (at_ db r m) a h
  · refine ⟨m + 1, by omega, ?_⟩
    obtain ⟨g, hg, hgh, hge⟩ := hc
    have hfire : (Watchd.reapGone a h t (at_ db r m)).2 = true := by
      unfold Watchd.reapGone; simp [hg, hgh, hge]
    rintro ⟨g', hg', -, hge'⟩
    simp only [at_, hr, XCmd.step] at hg'
    have hmem := List.mem_of_find?_eq_some hg'
    have hname : g'.name = a := by simpa using List.find?_some hg'
    rw [(WatchdProofs.reapGone_spec hfire).2.1 g' hmem hname] at hge'
    cases hge'
  · exact ⟨m, hm, hc⟩

/-! ## Stays and away (model: Stay.lean's St4, Away.lean's A1) -/

/-- St4 (model: `endStay_frame`, `Contract.end_stay_changes_only_the_stay`): `swarm stay --end A` by the user or the
communicator changes A's stay alone: every table but the agents and the event log as it was, every agent row as it was
but A's, and A's but for its stay, now none; or, refused, nothing. -/
theorem endStay_frame (db : Db) (me n : String) (now : Int) :
    let d := (endStay db me n now).1
    d.tasks = db.tasks ∧ d.locks = db.locks ∧ d.msgs = db.msgs ∧ d.cursors = db.cursors ∧ d.metas = db.metas ∧
      (d.agents = db.agents ∨ d.agents = db.agents.map fun a => if a.name = n then { a with stay := none } else a) := by
  unfold endStay
  repeat' split
  all_goals first | exact ⟨rfl, rfl, rfl, rfl, rfl, .inl rfl⟩ | exact ⟨rfl, rfl, rfl, rfl, rfl, .inr rfl⟩

/-- `swarm stay --end A` that went through found A live with a stay. -/
theorem endStay_enabled {db : Db} {me n : String} {now : Int} (h : (endStay db me n now).2 = .ok ()) :
    ∃ r ∈ live db, r.name = n ∧ r.stay.isSome := by
  unfold endStay at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · rename_i s hs
      exact ⟨r, List.mem_of_find?_eq_some hr, by simpa using List.find?_some hr, by simp [hs]⟩

/-- A1 (model: `away_keeps`): `swarm away` and `--back` change no task, lock, agent or cursor; the message log only
grows (the line to the communicator). -/
theorem away_keeps (db : Db) (me : String) (comms : Option String) (note line : String) (now : Int) :
    let d := (goAway db me comms note line now).1
    d.tasks = db.tasks ∧ d.locks = db.locks ∧ d.agents = db.agents ∧ Inbox.Grows db d := by
  unfold goAway delMeta Db.setMeta
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl, rfl, Inbox.grows_refl _⟩
    | exact ⟨rfl, rfl, rfl, Inbox.grows_trans (Inbox.grows_of_eq rfl rfl rfl) (Inbox.grows_post _ _ _ _ _ _ _)⟩
    | exact ⟨rfl, rfl, rfl, Inbox.grows_of_eq rfl rfl rfl⟩

theorem back_keeps (db : Db) (me : String) (comms : Option String) (now : Int) :
    let d := (goBack db me comms now).1
    d.tasks = db.tasks ∧ d.locks = db.locks ∧ d.agents = db.agents ∧ Inbox.Grows db d := by
  unfold goBack delMeta Db.setMeta
  repeat' split
  all_goals first
    | exact ⟨rfl, rfl, rfl, Inbox.grows_refl _⟩
    | exact ⟨rfl, rfl, rfl, Inbox.grows_trans (Inbox.grows_of_eq rfl rfl rfl) (Inbox.grows_post _ _ _ _ _ _ _)⟩
    | exact ⟨rfl, rfl, rfl, Inbox.grows_of_eq rfl rfl rfl⟩

/-- A4 (model: `away_twice`, `back_twice`): a second `swarm away` is refused and keeps the first (the db unchanged, the
flag it found returned); `--back` when not away is refused and changes nothing. -/
theorem away_twice (db : Db) (me : String) (comms : Option String) (note line : String) (now : Int) (aw)
    (h : away db = some aw) : goAway db me comms note line now = (db, some aw) := by
  unfold goAway; rw [h]

theorem back_twice (db : Db) (me : String) (comms : Option String) (now : Int) (h : away db = none) :
    goBack db me comms now = (db, none) := by
  unfold goBack; rw [h]

/-! ## S4 with every area's transactions -/

/-- Every transaction but a delivery only grows the message log and the cursors. -/
theorem xcmd_grows (x : XCmd) (hr : ∀ n, x ≠ .read n) (hd : ∀ n b, x ≠ .deliver n b) {db : Db} (h : Inbox.MInv db) :
    Inbox.Grows db (x.step db) := by
  have h0 : 0 < db.msgNext := h.2.2.2
  cases x with
  | task c => exact tcmd_grows c db h0
  | post now f d b u k => exact Inbox.grows_post _ _ _ _ _ _ _
  | read n => exact absurd rfl (hr n)
  | deliver n b => exact absurd rfl (hd n b)
  | lock c => exact lcmd_grows c db h0
  | end_ n hc force by_ now =>
    simp only [XCmd.step]; unfold Lifecycle.endStep; dsimp only
    repeat' split
    all_goals first | exact Inbox.grows_refl _ | exact Inbox.grows_of_eq rfl rfl rfl
  | reapTask r t now =>
    simp only [XCmd.step]; unfold Watchd.reapTask; dsimp only
    split
    · split
      · exact Inbox.grows_trans (Inbox.grows_of_eq rfl rfl rfl) (Inbox.grows_post _ _ _ _ _ _ _)
      · exact Inbox.grows_refl _
    · exact Inbox.grows_refl _
  | reapLock l t now =>
    simp only [XCmd.step]; unfold Watchd.reapLock; dsimp only
    repeat' split
    all_goals first | exact Inbox.grows_refl _ | exact Inbox.grows_of_eq rfl rfl rfl
  | reapGone n hh t =>
    simp only [XCmd.step]; unfold Watchd.reapGone; dsimp only
    split
    · exact Inbox.grows_trans (Inbox.grows_of_eq rfl rfl rfl)
        (Inbox.grows_trans (Inbox.grows_post _ _ _ _ _ _ _) (Inbox.grows_of_eq rfl rfl rfl))
    · exact Inbox.grows_refl _

/-- A transaction as S4's theorems take it: a post, `swarm read`, a delivery, or another step that only grows the log
(`Inbox.MCmd.other`, by `xcmd_grows`). -/
def toM : XCmd → Inbox.MCmd
  | .post now f d b u k => .post now f d b u k
  | .read n => .read n
  | .deliver n b => .deliver n b
  | .task c => .other (XCmd.task c).step fun _ h => xcmd_grows (XCmd.task c) (fun _ => nofun) (fun _ _ => nofun) h
  | .lock c => .other (XCmd.lock c).step fun _ h => xcmd_grows (XCmd.lock c) (fun _ => nofun) (fun _ _ => nofun) h
  | .end_ n hc f b w => .other (XCmd.end_ n hc f b w).step fun _ h => xcmd_grows (XCmd.end_ n hc f b w) (fun _ => nofun) (fun _ _ => nofun) h
  | .reapTask r t w => .other (XCmd.reapTask r t w).step fun _ h => xcmd_grows (XCmd.reapTask r t w) (fun _ => nofun) (fun _ _ => nofun) h
  | .reapLock l t w => .other (XCmd.reapLock l t w).step fun _ h => xcmd_grows (XCmd.reapLock l t w) (fun _ => nofun) (fun _ _ => nofun) h
  | .reapGone n hh t => .other (XCmd.reapGone n hh t).step fun _ h => xcmd_grows (XCmd.reapGone n hh t) (fun _ => nofun) (fun _ _ => nofun) h

theorem toM_step (x : XCmd) (db : Db) : ((toM x).step db).1 = x.step db := by cases x <;> rfl

/-- S4 with every area's transactions (model: `inboxExact_of_reachable` with all of `step`): over any transactions of
all four areas, the deliveries to `n` show, in order, exactly the messages for `n` between its cursor before and after
(`Inbox.exactly_once` on `cs.map toM`, whose db is the same: `toM_step`). -/
theorem exactly_once_x (db : Db) (cs : List XCmd) (n : String) (h : Inbox.MInv db) (hn : (db.cursor n).isSome) :
    Inbox.shownTo n (Inbox.trace db (cs.map toM)) =
      Inbox.window (Inbox.run db (cs.map toM)) n (Msgs.cursorOf db n) (Msgs.cursorOf (Inbox.run db (cs.map toM)) n) :=
  Inbox.exactly_once db (cs.map toM) n h hn

theorem run_toM (db : Db) (cs : List XCmd) : Inbox.run db (cs.map toM) = run db cs := by
  induction cs generalizing db with
  | nil => rfl
  | cons x xs ih =>
    show (replay Inbox.MCmd.step ((toM x).step db).1 (xs.map toM)).1 = run (x.step db) xs
    rw [toM_step]; exact ih _

end SwarmLean.Cross
