import SwarmLean.Proofs

/-! Board task #103: swarm/model's properties of tasks and the board, proved of the real steps (Db/Tasks.lean's `add`,
`claim`, `after`, `priority`, `renew`, `done`, `block`, `unblock`, `release`, `edit`, `drop`, `pool`, `boardLe`), the
functions Cmd/Tasks.lean runs in `Store.txn`. Concurrency is any order of whole transactions (`Atomic`, Store.lean),
the one assumption. -/

namespace SwarmLean.Board
open Tasks

/-- `v` is `u` with its id, state, owner and evidence as they were. -/
def Keeps (u v : Task) : Prop := v.id = u.id ∧ v.state = u.state ∧ v.owner = u.owner ∧ v.evidence = u.evidence

/-- `v` is `u` with its id, status, owner and evidence as they were. -/
def KeepsSo (u v : Task) : Prop := v.id = u.id ∧ v.status = u.status ∧ v.owner = u.owner ∧ v.evidence = u.evidence

theorem Keeps.so {u v : Task} (h : Keeps u v) : KeepsSo u v := by
  obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, by unfold Task.status; rw [h2], h3, h4⟩

/-- A lease moved keeps the status and the owner. -/
theorem renew_so (l : Int) (s : TaskState) : (s.renew l).status = s.status ∧ (s.renew l).owner = s.owner := by
  cases s <;> exact ⟨rfl, rfl⟩

/-! What each step does to the task table. -/

theorem set_tasks (db : Db) (i : Int) (f : Task → Task) : (db.set i f).tasks = db.tasks.map
    (fun t => if (t.id : Int) = i then f t else t) := rfl

@[simp] theorem post_msgs (db : Db) n f d' b u k :
    (Msgs.post db n f d' b u k).1.agents = db.agents ∧ (Msgs.post db n f d' b u k).1.cursors = db.cursors :=
  ⟨rfl, rfl⟩

theorem after_spec (c : Ctx) (i : Int) (l : List Int) (db : Db) :
    ((Tasks.after c i l db).1.tasks = db.tasks ∧ (Tasks.after c i l db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, Keeps u (f u)) ∧ (Tasks.after c i l db).1.tasks = (db.set i f).tasks ∧
      (Tasks.after c i l db).1.taskNext = db.taskNext := by
  unfold Tasks.after
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    · split
      · exact .inl ⟨rfl, rfl⟩
      · rename_i h
        unfold setDeps at h
        split at h
        · cases h
        · cases h; refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl, rfl⟩

theorem priority_spec (c : Ctx) (i : Int) (p : Priority) (db : Db) :
    ((Tasks.priority c i p db).1.tasks = db.tasks ∧ (Tasks.priority c i p db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, Keeps u (f u)) ∧ (Tasks.priority c i p db).1.tasks = (db.set i f).tasks ∧
      (Tasks.priority c i p db).1.taskNext = db.taskNext := by
  unfold Tasks.priority
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl, rfl⟩

/-- `task renew` moves only the lease: the state is `u.state.renew` at the new end, the rest as it was. -/
theorem renew_spec (c : Ctx) (i : Int) (l : String) (db : Db) :
    ((Tasks.renew c i l db).1.tasks = db.tasks ∧ (Tasks.renew c i l db).1.taskNext = db.taskNext) ∨
    ∃ (r : Task) (u0 : Int) (f : Task → Task), db.find i = some r ∧ r.status = .inProgress ∧ r.owner = some c.me ∧
      dur l = some u0 ∧
      (∀ u, (f u).id = u.id ∧ (f u).state = u.state.renew (c.now + u0) ∧ (f u).evidence = u.evidence) ∧
      (Tasks.renew c i l db).1.tasks = (db.set i f).tasks ∧ (Tasks.renew c i l db).1.taskNext = db.taskNext := by
  unfold Tasks.renew
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    · split
      · exact .inl ⟨rfl, rfl⟩
      · rename_i _ r hr _ u0 hu hm
        have hm' : mine r c.me = true := by simpa using hm
        simp only [mine, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm'
        refine .inr ⟨r, u0, _, hr, hm'.2, hm'.1, hu, ?_, rfl, rfl⟩
        intro _; exact ⟨rfl, rfl, rfl⟩

/-- `renew_spec` read as status, owner and evidence kept. -/
theorem renew_spec_so (c : Ctx) (i : Int) (l : String) (db : Db) :
    ((Tasks.renew c i l db).1.tasks = db.tasks ∧ (Tasks.renew c i l db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, KeepsSo u (f u)) ∧ (Tasks.renew c i l db).1.tasks = (db.set i f).tasks ∧
      (Tasks.renew c i l db).1.taskNext = db.taskNext := by
  rcases renew_spec c i l db with h | ⟨-, u0, f, -, -, -, -, hf, ht, hn⟩
  · exact .inl h
  · refine .inr ⟨f, fun u => ⟨(hf u).1, ?_, ?_, (hf u).2.2⟩, ht, hn⟩
    · unfold Task.status; rw [(hf u).2.1]; exact (renew_so _ u.state).1
    · unfold Task.owner; rw [(hf u).2.1]; exact (renew_so _ u.state).2

theorem edit_spec (c : Ctx) (i : Int) (a : EditArgs) (db : Db) :
    ((Tasks.edit c i a db).1.tasks = db.tasks ∧ (Tasks.edit c i a db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, Keeps u (f u)) ∧ (Tasks.edit c i a db).1.tasks = (db.set i f).tasks ∧
      (Tasks.edit c i a db).1.taskNext = db.taskNext := by
  unfold Tasks.edit
  dsimp only
  repeat' split
  all_goals first
    | exact .inl ⟨rfl, rfl⟩
    | (refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl, rfl⟩)

theorem toCompleted_owner (s : TaskState) : s.toCompleted.owner = s.owner := by cases s <;> rfl

theorem done_spec (c : Ctx) (i : Int) (e : String) (db : Db) :
    ((Tasks.done c i e db).1.tasks = db.tasks ∧ (Tasks.done c i e db).1.taskNext = db.taskNext) ∨
    (∃ f : Task → Task, (∀ u, (f u).id = u.id ∧ (f u).owner = u.owner ∧ EvOk (f u).evidence ∧
        (f u).state = u.state.toCompleted) ∧
      (Tasks.done c i e db).1.tasks = (db.set i f).tasks ∧ (Tasks.done c i e db).1.taskNext = db.taskNext) ∨
    -- a red task: released to Backlog, reserved for no one
    ∃ (f : Task → Task) (x : Tasks.DoneOut) (r : Task), db.find i = some r ∧ r.status = .inProgress ∧
      (∀ u, (f u).id = u.id ∧ (f u).state = .backlog none) ∧
      (Tasks.done c i e db).1.tasks = (db.set i f).tasks ∧ (Tasks.done c i e db).1.taskNext = db.taskNext ∧
      (Tasks.done c i e db).2 = .ok x := by
  unfold Tasks.done
  split
  · exact .inl ⟨rfl, rfl⟩
  · rename_i r hr
    split
    · exact .inl ⟨rfl, rfl⟩
    · rename_i hs
      have ev : EvOk (some e) := ⟨e, rfl, by simpa using hs⟩
      split
      · -- a landing task: its lander closes it
        split
        · exact .inl ⟨rfl, rfl⟩
        · split
          · exact .inl ⟨rfl, rfl⟩
          · refine .inr (.inl ⟨_, ?_, rfl, rfl⟩); intro u; exact ⟨rfl, toCompleted_owner u.state, ev, rfl⟩
      split
      · exact .inl ⟨rfl, rfl⟩
      · rename_i hm
        split
        · let f : Task → Task := fun t => { t with state := .backlog none, evidence := some e, note := some (strip e ++ " awaiting a green run") }
          refine .inr (.inr ⟨f, .red, r, hr, ?_, fun _ => ⟨rfl, rfl⟩, rfl, rfl, rfl⟩)
          simp [mine] at hm; exact hm.2
        · refine .inr (.inl ⟨_, ?_, rfl, rfl⟩); intro u; exact ⟨rfl, toCompleted_owner u.state, ev, rfl⟩

/-- Blocking keeps the owner and moves only In Progress, to Needs Input. -/
theorem block_so (q : String) (s : TaskState) :
    (s.block q).owner = s.owner ∧ ((s.block q).status = s.status ∨ (s.block q).status = .needsInput) := by
  cases s <;> simp [TaskState.block, TaskState.status, TaskState.owner]

/-- Unblocking keeps the owner and moves only Needs Input, to In Progress. -/
theorem unblock_so (l : Int) (s : TaskState) :
    (s.unblock l).owner = s.owner ∧ ((s.unblock l).status = s.status ∨ (s.unblock l).status = .inProgress) := by
  cases s <;> simp [TaskState.unblock, TaskState.status, TaskState.owner]

theorem block_in (q : String) {s : TaskState} (h : s.status = .inProgress) : (s.block q).status = .needsInput := by
  cases s <;> simp_all [TaskState.block, TaskState.status]

theorem unblock_in (l : Int) {s : TaskState} (h : s.status = .needsInput) : (s.unblock l).status = .inProgress := by
  cases s <;> simp_all [TaskState.unblock, TaskState.status]

/-- `task block` by the owner of an In Progress task: its state is `u.state.block q` (Needs Input, owner and lease
kept), the rest as it was. -/
theorem block_spec (c : Ctx) (i : Int) (q : String) (db : Db) :
    ((Tasks.block c i q db).1.tasks = db.tasks ∧ (Tasks.block c i q db).1.taskNext = db.taskNext) ∨
    ∃ (r : Task) (f : Task → Task), db.find i = some r ∧ r.status = .inProgress ∧ r.owner = some c.me ∧
      (∀ u, (f u).id = u.id ∧ (f u).owner = u.owner ∧ (f u).evidence = u.evidence ∧ (f u).state = u.state.block q) ∧
      (f r).status = .needsInput ∧
      (Tasks.block c i q db).1.tasks = (db.set i f).tasks ∧ (Tasks.block c i q db).1.taskNext = db.taskNext := by
  unfold Tasks.block
  split
  · exact .inl ⟨rfl, rfl⟩
  · rename_i r hr
    split
    · exact .inl ⟨rfl, rfl⟩
    · rename_i hm
      have hm' : mine r c.me = true := by simpa using hm
      simp only [mine, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm'
      refine .inr ⟨r, _, hr, hm'.2, hm'.1, ?_, ?_, rfl, rfl⟩
      · intro u; exact ⟨rfl, (block_so q u.state).1, rfl, rfl⟩
      · exact block_in q hm'.2

/-- `block_spec` read as owner and evidence kept, and the status kept or Needs Input. -/
theorem block_spec_so (c : Ctx) (i : Int) (q : String) (db : Db) :
    ((Tasks.block c i q db).1.tasks = db.tasks ∧ (Tasks.block c i q db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, (f u).id = u.id ∧ (f u).owner = u.owner ∧ (f u).evidence = u.evidence ∧
        ((f u).status = u.status ∨ (f u).status = .needsInput)) ∧
      (Tasks.block c i q db).1.tasks = (db.set i f).tasks ∧ (Tasks.block c i q db).1.taskNext = db.taskNext := by
  rcases block_spec c i q db with h | ⟨-, f, -, -, -, hf, -, ht, hn⟩
  · exact .inl h
  · refine .inr ⟨f, fun u => ⟨(hf u).1, (hf u).2.1, (hf u).2.2.1, ?_⟩, ht, hn⟩
    unfold Task.status; rw [(hf u).2.2.2]; exact (block_so q u.state).2

/-- `task unblock` of a Needs Input task by its owner or someone in charge: its state is `u.state.unblock` at a
fresh lease (In Progress, owner kept), the rest but the answer as it was. -/
theorem unblock_spec (c : Ctx) (i : Int) (ans : String) (db : Db) :
    ((Tasks.unblock c i ans db).1.tasks = db.tasks ∧ (Tasks.unblock c i ans db).1.taskNext = db.taskNext) ∨
    ∃ r f, db.find i = some r ∧ r.status = .needsInput ∧ r.owner.isSome ∧
      (∀ u, (f u).id = u.id ∧ (f u).owner = u.owner ∧ (f u).evidence = u.evidence ∧
        (f u).state = u.state.unblock (c.now + LEASE)) ∧
      (f r).status = .inProgress ∧
      (Tasks.unblock c i ans db).1.tasks = (db.set i f).tasks ∧ (Tasks.unblock c i ans db).1.taskNext = db.taskNext := by
  unfold Tasks.unblock
  split
  · exact .inl ⟨rfl, rfl⟩
  · rename_i r hr
    split
    · exact .inl ⟨rfl, rfl⟩
    · rename_i hn0
      have hb : r.status = .needsInput := by simpa using hn0
      split
      · exact .inl ⟨rfl, rfl⟩
      · split
        · exact .inl ⟨rfl, rfl⟩
        · rename_i ho
          have hs : r.owner.isSome := Option.isSome_iff_ne_none.2 (by simpa using ho)
          dsimp only
          repeat' split
          all_goals
            refine .inr ⟨r, _, hr, hb, hs, ?_, ?_, rfl, rfl⟩
            · intro u; exact ⟨rfl, (unblock_so _ u.state).1, rfl, rfl⟩
            · exact unblock_in _ hb

/-- `unblock_spec` read as owner and evidence kept, and the status kept or In Progress. -/
theorem unblock_spec_so (c : Ctx) (i : Int) (ans : String) (db : Db) :
    ((Tasks.unblock c i ans db).1.tasks = db.tasks ∧ (Tasks.unblock c i ans db).1.taskNext = db.taskNext) ∨
    ∃ r f, db.find i = some r ∧ r.owner.isSome ∧
      (∀ u, (f u).id = u.id ∧ (f u).owner = u.owner ∧ (f u).evidence = u.evidence ∧
        ((f u).status = u.status ∨ (f u).status = .inProgress)) ∧
      (Tasks.unblock c i ans db).1.tasks = (db.set i f).tasks ∧ (Tasks.unblock c i ans db).1.taskNext = db.taskNext := by
  rcases unblock_spec c i ans db with h | ⟨r, f, hr, -, hs, hf, -, ht, hn⟩
  · exact .inl h
  · refine .inr ⟨r, f, hr, hs, fun u => ⟨(hf u).1, (hf u).2.1, (hf u).2.2.1, ?_⟩, ht, hn⟩
    unfold Task.status; rw [(hf u).2.2.2]; exact (unblock_so _ u.state).2

/-- `task drop`: Duplicate with `dup`, Cancelled without, no owner. -/
theorem drop_spec (c : Ctx) (i : Int) (dup : Option Int) (note : Option String) (db : Db) :
    ((Tasks.drop c i dup note db).1.tasks = db.tasks ∧ (Tasks.drop c i dup note db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, (f u).id = u.id ∧ (f u).owner = none ∧
        (f u).status = (match dup with | some _ => .duplicate | none => .cancelled)) ∧
      (Tasks.drop c i dup note db).1.tasks = (db.set i f).tasks ∧
      (Tasks.drop c i dup note db).1.taskNext = db.taskNext := by
  unfold Tasks.drop
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    split
    · exact .inl ⟨rfl, rfl⟩
    split
    · exact .inl ⟨rfl, rfl⟩
    split
    · exact .inl ⟨rfl, rfl⟩
    split
    · exact .inl ⟨rfl, rfl⟩
    · cases dup
      · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl⟩
      · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl⟩

theorem drop_closed (dup : Option Int) :
    (match dup with | some _ => Status.duplicate | none => Status.cancelled) = .cancelled ∨
      (match dup with | some _ => Status.duplicate | none => Status.cancelled) = .duplicate := by
  cases dup <;> simp

/-! The invariant, over every command. -/

/-- The part of the invariant about one task: its owner fits its state, and if done it has evidence. -/
def TaskOk (t : Task) : Prop := t.Owned ∧ DoneEv t

theorem find_mem {db : Db} {i : Int} {r : Task} (h : db.find i = some r) : r ∈ db.tasks := List.mem_of_find?_eq_some h

theorem find_unique {db : Db} (h : (db.tasks.map (·.id)).Nodup) {i : Int} {r u : Task} (hf : db.find i = some r)
    (hu : u ∈ db.tasks) (hi : (u.id : Int) = i) : u = r :=
  nodup_inj h hu (find_mem hf) (by have := find_id hf; omega)

theorem set_all {P : Task → Prop} {db : Db} {i : Int} {f : Task → Task} (h : ∀ u ∈ db.tasks, P u)
    (hf : ∀ u ∈ db.tasks, (u.id : Int) = i → P (f u)) : ∀ u ∈ (db.set i f).tasks, P u := by
  intro v hv
  simp only [Db.set, List.mem_map] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  by_cases e : (u.id : Int) = i
  · simp only [e, ↓reduceIte]; exact hf u hu e
  · simp only [e, ↓reduceIte]; exact h u hu

theorem binv_same {db db' : Db} (ht : db'.tasks = db.tasks) (hn : db'.taskNext = db.taskNext) (h : BInv db) :
    BInv db' := by
  unfold BInv Inv; rw [ht, hn]; exact h

theorem binv_set {db db' : Db} {i : Int} {f : Task → Task} (hid : ∀ u, (f u).id = u.id)
    (hok : ∀ u ∈ db.tasks, (u.id : Int) = i → TaskOk u → TaskOk (f u))
    (ht : db'.tasks = (db.set i f).tasks) (hn : db'.taskNext = db.taskNext) (h : BInv db) : BInv db' := by
  obtain ⟨⟨hnd, hb, hw⟩, he⟩ := h
  have all : ∀ u ∈ (db.set i f).tasks, TaskOk u ∧ u.id < db.taskNext :=
    set_all (P := fun u => TaskOk u ∧ u.id < db.taskNext) (fun u hu => ⟨⟨hw u hu, he u hu⟩, hb u hu⟩)
      (fun u hu e => ⟨hok u hu e ⟨hw u hu, he u hu⟩, (hid u).symm ▸ hb u hu⟩)
  unfold BInv Inv; rw [ht, hn]
  exact ⟨⟨set_tasks_ids db i f hid ▸ hnd, fun u hu => (all u hu).2, fun u hu => (all u hu).1.1⟩,
    fun u hu => (all u hu).1.2⟩

/-- A task whose evidence is kept and whose status is kept or not Completed fits the invariant if it did. -/
theorem ok_of_ev {u v : Task} (hu : TaskOk u) (he : v.evidence = u.evidence)
    (hs : v.status = u.status ∨ v.status ≠ .completed) : TaskOk v := by
  refine ⟨owned_all v, fun e => ?_⟩
  rcases hs with hs | hs
  · rw [he]; exact hu.2 (hs.symm.trans e)
  · exact absurd e hs

/-- A task not Completed fits the invariant. -/
theorem ok_of_ne {v : Task} (h : v.status ≠ .completed) : TaskOk v := ⟨owned_all v, fun e => absurd e h⟩

theorem keeps_ok {u v : Task} (h : KeepsSo u v) (hu : TaskOk u) : TaskOk v := by
  obtain ⟨-, hs, ho, he⟩ := h
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  exact ⟨⟨fun e => by rw [ho]; exact h1 (hs.symm.trans e), fun e => by rw [ho]; exact h2 (hs.symm.trans e)⟩,
    fun e => by rw [he]; exact h3 (hs.symm.trans e)⟩

/-- An open task without an owner fits the invariant. -/
theorem ok_of_open {v : Task} (h : v.status = .ready) (ho : v.owner = none) : TaskOk v := by
  simp [TaskOk, Task.Owned, DoneEv, h, ho]

/-- A task in a state other than open and claimed fits any owner and, unless done, needs no evidence. -/
theorem ok_of_state {v : Task} (h : v.status = .needsInput ∨ v.status = .cancelled ∨ v.status = .inReview) : TaskOk v := by
  rcases h with h | h | h <;> exact ⟨⟨fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e)⟩,
    fun e => (by rw [h] at e; cases e)⟩

theorem keeps_so {A : Prop} {B : (Task → Task) → Prop} (h : A ∨ ∃ f : Task → Task, (∀ u, Keeps u (f u)) ∧ B f) :
    A ∨ ∃ f : Task → Task, (∀ u, KeepsSo u (f u)) ∧ B f :=
  h.imp_right fun ⟨f, hf, hb⟩ => ⟨f, fun u => (hf u).so, hb⟩

theorem keeps_step {db db' : Db} {i : Int}
    (h : (db'.tasks = db.tasks ∧ db'.taskNext = db.taskNext) ∨ ∃ f : Task → Task, (∀ u, KeepsSo u (f u)) ∧
      db'.tasks = (db.set i f).tasks ∧ db'.taskNext = db.taskNext) (hi : BInv db) : BInv db' := by
  rcases h with ⟨ht, hn⟩ | ⟨f, hk, ht, hn⟩
  · exact binv_same ht hn hi
  · exact binv_set (fun u => (hk u).1) (fun u _ _ => keeps_ok (hk u)) ht hn hi

theorem step_binv (c : TCmd) (db : Db) (h : BInv db) : BInv (c.step db).1 := by
  cases c with
  | add c a =>
    refine ⟨step_inv (.add c a) db h.1, ?_⟩
    show ∀ t ∈ (Tasks.add c a db).1.tasks, DoneEv t
    rcases add_spec c a db with ⟨ht, -, -⟩ | ⟨t, ht, -, hs, -⟩
    · rw [ht]; exact h.2
    · rw [ht]; intro u hu; simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact h.2 u hu
      · intro e; rw [(ready_none hs).1] at e; cases e
  | claim c i l =>
    obtain ⟨hn, hs⟩ := claim_spec c i l db
    rcases hs with ⟨ht, -⟩ | ⟨-, g, -, -, hg, ht, -⟩
    · exact binv_same ht hn h
    · refine binv_set (fun u => (hg u).1) (fun u _ _ _ => ?_) ht hn h
      obtain ⟨-, hs, ho⟩ := hg u
      exact ⟨⟨fun _ => by rw [ho]; rfl, fun e => (by rw [hs] at e; cases e)⟩, fun e => (by rw [hs] at e; cases e)⟩
  | release c i af =>
    obtain ⟨hn, hs⟩ := release_spec c i af db
    rcases hs with ⟨ht, -⟩ | ⟨g, hg, ht, -⟩
    · exact binv_same ht hn h
    · refine binv_set (fun u => (hg u).1) (fun u _ _ _ => ?_) ht hn h
      obtain ⟨hs, ho, -⟩ := ready_none (hg u).2
      exact ⟨⟨fun e => (by rw [hs] at e; cases e), fun _ => ho⟩, fun e => (by rw [hs] at e; cases e)⟩
  | after c i l => exact keeps_step (keeps_so (after_spec c i l db)) h
  | priority c i p => exact keeps_step (keeps_so (priority_spec c i p db)) h
  | renew c i l => exact keeps_step (renew_spec_so c i l db) h
  | edit c i a => exact keeps_step (keeps_so (edit_spec c i a db)) h
  | done c i e =>
    rcases done_spec c i e db with ⟨ht, hn⟩ | ⟨f, hf, ht, hn⟩ | ⟨f, -, -, -, -, hf, ht, hn, -⟩
    · exact binv_same ht hn h
    · exact binv_set (fun u => (hf u).1) (fun u _ _ _ => ⟨owned_all _, fun _ => (hf u).2.2.1⟩) ht hn h
    · exact binv_set (fun u => (hf u).1) (fun u _ _ _ => ok_of_ne (by unfold Task.status; rw [(hf u).2]; nofun)) ht hn h
  | block c i q =>
    rcases block_spec_so c i q db with ⟨ht, hn⟩ | ⟨f, hf, ht, hn⟩
    · exact binv_same ht hn h
    · exact binv_set (fun u => (hf u).1) (fun u _ _ hu => ok_of_ev hu (hf u).2.2.1
        ((hf u).2.2.2.imp_right fun e => by rw [e]; nofun)) ht hn h
  | unblock c i a =>
    rcases unblock_spec_so c i a db with ⟨ht, hn⟩ | ⟨r, f, hr, hs, hf, ht, hn⟩
    · exact binv_same ht hn h
    · exact binv_set (fun u => (hf u).1) (fun u _ _ hu => ok_of_ev hu (hf u).2.2.1
        ((hf u).2.2.2.imp_right fun e => by rw [e]; nofun)) ht hn h
  | drop c i d n =>
    rcases drop_spec c i d n db with ⟨ht, hn⟩ | ⟨f, hf, ht, hn⟩
    · exact binv_same ht hn h
    · exact binv_set (fun u => (hf u).1)
        (fun u _ _ _ => ok_of_ne (by rcases drop_closed d with e | e <;> rw [(hf u).2.2, e] <;> nofun)) ht hn h
  | land c i s l =>
    obtain ⟨hn, hs⟩ := land_spec c i s l db
    rcases hs with ⟨ht, -⟩ | ⟨r, g, hr, hrs, -, hg, ht, -⟩
    · exact binv_same ht hn h
    · refine binv_set (fun u => (hg u).1) (fun u hu e _ => ?_) ht hn h
      obtain rfl := find_unique h.1.1 hr hu e
      exact ok_of_ne (by rw [((hg u).2.2.1 hrs).1]; nofun)
  | unland c i w =>
    obtain ⟨hn, hs⟩ := unland_spec c i w db
    rcases hs with ⟨ht, -⟩ | ⟨-, g, -, -, hg, ht, -⟩
    · exact binv_same ht hn h
    · exact binv_set (fun u => (hg u).1) (fun u _ _ _ => ok_of_open (ready_none (hg u).2).1 (ready_none (hg u).2).2.1) ht hn h
  | board => exact h

theorem binv_empty : BInv {} := ⟨inv_empty, by simp⟩

theorem replay_binv (db : Db) (cs : List TCmd) (h : BInv db) : BInv (replay TCmd.step db cs).1 := by
  induction cs generalizing db with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_binv c db h)

/-- The invariant holds after any task commands by any agents from the empty db. -/
theorem run_binv (cs : List TCmd) : BInv (run {} cs) := replay_binv _ cs binv_empty

/-- No task has two owners, after any task commands by any agents in any order from the empty db. -/
theorem one_owner_all (cs : List TCmd) (i : Int) (a b : String) (ha : Owns (run {} cs) i a)
    (hb : Owns (run {} cs) i b) : a = b := by
  obtain ⟨t, ht, e1, hta⟩ := ha
  obtain ⟨t', ht', e2, htb⟩ := hb
  have := nodup_inj (run_binv cs).1.1 ht ht' (by omega)
  subst this; simpa [hta] using htb

/-- S5 (model: `done_task_has_evidence`): after any task commands from the empty db, every done task has evidence:
text that is not all whitespace. -/
theorem done_has_evidence (cs : List TCmd) : ∀ t ∈ (run {} cs).tasks, t.status = .completed → EvOk t.evidence :=
  (run_binv cs).2

/-- S2 (model: `no_claim_before_dependencies_done`): a successful `task claim i` finds every task `i` is after done. -/
theorem claim_deps_done {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) :
    ∀ j ∈ depsOf r, ∀ u, db.find j = some u → u.status = .completed := by
  have hu : undone db r = [] := by
    unfold Tasks.claim at h
    rw [hr] at h
    dsimp only at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    · assumption
  intro j hj u hfu
  unfold undone at hu
  have := List.filterMap_eq_nil_iff.1 hu j hj
  rw [hfu] at this
  simpa [Option.filter] using this

/-! One claim wins, over every task command. -/

/-- Task `i` is on the board and not open. -/
def Taken (db : Db) (i : Int) : Prop := ∃ t, db.find i = some t ∧ t.status ≠ .ready ∧ t.status ≠ .backlog

theorem taken_same {db db' : Db} {i : Int} (ht : db'.tasks = db.tasks) (h : Taken db i) : Taken db' i := by
  obtain ⟨t, hf, hs⟩ := h; exact ⟨t, by rw [find_congr ht]; exact hf, hs⟩

theorem taken_set {db db' : Db} {i j : Int} {f : Task → Task} (hid : ∀ u, (f u).id = u.id)
    (hno : j = i → ∀ u, u.status ≠ .ready ∧ u.status ≠ .backlog → (f u).status ≠ .ready ∧ (f u).status ≠ .backlog) (ht : db'.tasks = (db.set j f).tasks)
    (h : Taken db i) : Taken db' i := by
  obtain ⟨t, hf, hs⟩ := h
  unfold Taken
  rw [find_congr ht, find_set _ _ _ _ hid, hf]
  by_cases e : (t.id : Int) = j
  · exact ⟨f t, by simp [e], hno (e.symm.trans (find_id hf)) t hs⟩
  · exact ⟨t, by simp [e], hs⟩

theorem toBool_false {α : Type} {r : Except String α} (h : ∀ x, r ≠ .ok x) : r.toBool = false := by
  cases r with
  | ok x => exact absurd rfl (h x)
  | error _ => rfl

theorem releasedOf_done (i j : Int) (cc : Ctx) (e : String) (b : Bool) :
    ReleasedOf i (.done cc j e, b) = (b && (j == i)) := by cases b <;> rfl

theorem claimedOf_claim (i j : Int) (cc : Ctx) (l : String) (b : Bool) :
    ClaimedOf i (.claim cc j l, b) = (b && (j == i)) := by cases b <;> rfl

theorem releasedOf_release (i j : Int) (cc : Ctx) (af : Option (List Int)) (b : Bool) :
    ReleasedOf i (.release cc j af, b) = (b && (j == i)) := by cases b <;> rfl

theorem releasedOf_unland (i j : Int) (cc : Ctx) (w : String) (b : Bool) :
    ReleasedOf i (.unland cc j w, b) = (b && (j == i)) := by cases b <;> rfl

/-- From a db where task `i` is taken, a command other than its successful release keeps it taken and is not a
successful claim of it. -/
theorem taken_step (db : Db) (i : Int) (c : TCmd) (h : Taken db i) (hr : ReleasedOf i (c, (c.step db).2) = false) :
    Taken (c.step db).1 i ∧ ClaimedOf i (c, (c.step db).2) = false := by
  cases c with
  | add c a =>
    refine ⟨?_, rfl⟩
    show Taken (Tasks.add c a db).1 i
    rcases add_spec c a db with ⟨ht, -, -⟩ | ⟨t, ht, -⟩
    · exact taken_same ht h
    · obtain ⟨u, hf, hs⟩ := h
      refine ⟨u, ?_, hs⟩
      simp only [Db.find] at hf ⊢; rw [ht, List.find?_append, hf]; rfl
  | claim cc j l =>
    show Taken (Tasks.claim cc j l db).1 i ∧ ClaimedOf i (.claim cc j l, (Tasks.claim cc j l db).2.toBool) = false
    rw [claimedOf_claim]
    obtain ⟨-, hs⟩ := claim_spec cc j l db
    rcases hs with ⟨ht, hne⟩ | ⟨t, g, hf, ho, hg, ht, -⟩
    · exact ⟨taken_same ht h, by rw [toBool_false hne]; rfl⟩
    · have hij : j ≠ i := fun e => by
        subst e; obtain ⟨u, hu, hs⟩ := h; rw [hf] at hu; cases hu; rcases ho with ho | ho; exact hs.1 ho; exact hs.2 ho
      exact ⟨taken_set (fun u => (hg u).1) (fun e => absurd e hij) ht h, by simp [hij]⟩
  | release cc j af =>
    show Taken (Tasks.release cc j af db).1 i ∧ false = false
    refine ⟨?_, rfl⟩
    obtain ⟨-, hs⟩ := release_spec cc j af db
    rcases hs with ⟨ht, -⟩ | ⟨g, hg, ht, x, hx⟩
    · exact taken_same ht h
    · have hij : j ≠ i := fun e => by
        subst e
        have : ReleasedOf j (.release cc j af, (Tasks.release cc j af db).2.toBool) = true := by
          rw [releasedOf_release, hx]; simp [Except.toBool]
        exact absurd this (by rw [show ((TCmd.release cc j af).step db).2 = (Tasks.release cc j af db).2.toBool from rfl] at hr; simp [hr])
      exact taken_set (fun u => (hg u).1) (fun e => absurd e hij) ht h
  | after cc j l =>
    refine ⟨?_, rfl⟩
    rcases after_spec cc j l db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u hu => (hf u).so.2.1 ▸ hu) ht h
  | priority cc j p =>
    refine ⟨?_, rfl⟩
    rcases priority_spec cc j p db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u hu => (hf u).so.2.1 ▸ hu) ht h
  | renew cc j l =>
    refine ⟨?_, rfl⟩
    rcases renew_spec_so cc j l db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u hu => (hf u).2.1 ▸ hu) ht h
  | edit cc j a =>
    refine ⟨?_, rfl⟩
    rcases edit_spec cc j a db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u hu => (hf u).so.2.1 ▸ hu) ht h
  | done cc j e =>
    refine ⟨?_, rfl⟩
    rcases done_spec cc j e db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩ | ⟨f, x, -, -, -, hf, ht, -, hx⟩
    · exact taken_same ht h
    · refine taken_set (fun u => (hf u).1) (fun _ u hu => ?_) ht h
      unfold Task.status; rw [(hf u).2.2.2]; exact ⟨nofun, nofun⟩
    · have hij : j ≠ i := fun e' => by
        subst e'
        have : ReleasedOf j (.done cc j e, (Tasks.done cc j e db).2.toBool) = true := by
          rw [releasedOf_done, hx]; simp [Except.toBool]
        exact absurd this (by rw [show ((TCmd.done cc j e).step db).2 = (Tasks.done cc j e db).2.toBool from rfl] at hr; simp [hr])
      exact taken_set (fun u => (hf u).1) (fun e' => absurd e' hij) ht h
  | block cc j q =>
    refine ⟨?_, rfl⟩
    rcases block_spec_so cc j q db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1)
        (fun _ u hu => by rcases (hf u).2.2.2 with e | e <;> rw [e] <;> first | exact hu | exact ⟨nofun, nofun⟩) ht h
  | unblock cc j a =>
    refine ⟨?_, rfl⟩
    rcases unblock_spec_so cc j a db with ⟨ht, -⟩ | ⟨-, f, -, -, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1)
        (fun _ u hu => by rcases (hf u).2.2.2 with e | e <;> rw [e] <;> first | exact hu | exact ⟨nofun, nofun⟩) ht h
  | drop cc j d n =>
    refine ⟨?_, rfl⟩
    rcases drop_spec cc j d n db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1)
        (fun _ u _ => by rcases drop_closed d with e | e <;> rw [(hf u).2.2, e] <;> exact ⟨nofun, nofun⟩) ht h
  | land cc j s l =>
    refine ⟨?_, rfl⟩
    obtain ⟨-, hs⟩ := land_spec cc j s l db
    rcases hs with ⟨ht, -⟩ | ⟨-, g, -, -, -, hg, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hg u).1)
        (fun _ u hu => by
          by_cases e : u.status = .inProgress
          · rw [((hg u).2.2.1 e).1]; exact ⟨nofun, nofun⟩
          · rw [(hg u).2.1 e]; exact hu) ht h
  | unland cc j w =>
    show Taken (Tasks.unland cc j w db).1 i ∧ false = false
    refine ⟨?_, rfl⟩
    obtain ⟨-, hs⟩ := unland_spec cc j w db
    rcases hs with ⟨ht, -⟩ | ⟨-, g, -, -, hg, ht, x, hx⟩
    · exact taken_same ht h
    · have hij : j ≠ i := fun e => by
        subst e
        have : ReleasedOf j (.unland cc j w, (Tasks.unland cc j w db).2.toBool) = true := by
          rw [releasedOf_unland, hx]; simp [Except.toBool]
        exact absurd this (by rw [show ((TCmd.unland cc j w).step db).2 = (Tasks.unland cc j w db).2.toBool from rfl] at hr; simp [hr])
      exact taken_set (fun u => (hg u).1) (fun e => absurd e hij) ht h
  | board => exact ⟨h, rfl⟩

theorem trace_cons (db : Db) (c : TCmd) (cs : List TCmd) :
    trace db (c :: cs) = (c, (c.step db).2) :: trace (c.step db).1 cs := rfl

theorem claimedOf_true {i : Int} {c : TCmd} {b : Bool} (h : ClaimedOf i (c, b) = true) :
    ∃ cc l, c = .claim cc i l ∧ b = true := by
  cases c with
  | claim cc j l =>
    rw [claimedOf_claim] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨cc, l, rfl, rfl⟩
  | _ => cases b <;> simp [ClaimedOf] at h

/-- A successful claim leaves its task taken. -/
theorem claimed_taken (cc : Ctx) (i : Int) (l : String) (db : Db) (h : (Tasks.claim cc i l db).2.toBool = true) :
    Taken (Tasks.claim cc i l db).1 i := by
  obtain ⟨-, ⟨-, hne⟩ | ⟨t, g, hf, -, hg, ht, -⟩⟩ := claim_spec cc i l db
  · rw [toBool_false hne] at h; cases h
  · refine ⟨g t, ?_, by rw [(hg t).2.1]; exact ⟨nofun, nofun⟩⟩
    rw [find_congr ht, find_set _ _ _ _ fun u => (hg u).1, hf]
    simp [find_id hf]

theorem taken_claimed (db : Db) (i : Int) (cs : List TCmd) (h : Taken db i) (t2 t3 : List (TCmd × Bool))
    (b : TCmd × Bool) (hb : ClaimedOf i b = true) (e : trace db cs = t2 ++ b :: t3) : ∃ x ∈ t2, ReleasedOf i x := by
  induction cs generalizing db t2 with
  | nil => cases t2 <;> simp [trace, replay] at e
  | cons c cs ih =>
    rw [trace_cons] at e
    cases t2 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      obtain ⟨cc, l, rfl, hx⟩ := claimedOf_true hb
      have := (taken_step db i (.claim cc i l) h rfl).2
      rw [hb] at this; cases this
    | cons x t2 =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      by_cases hr : ReleasedOf i (c, (c.step db).2)
      · exact ⟨_, List.mem_cons_self .., hr⟩
      · obtain ⟨y, hy, hy'⟩ := ih _ (taken_step db i c h (by simpa using hr)).1 t2 e
        exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-- Of any task commands by any agents from any db, two successful claims of one task have a successful release of it
between them: a claim succeeds for at most one agent until the task is released. -/
theorem claimed_once_all (db : Db) (cs : List TCmd) (i : Int) (a b : TCmd × Bool) (ha : ClaimedOf i a = true)
    (hb : ClaimedOf i b = true) (t1 t2 t3 : List (TCmd × Bool)) (e : trace db cs = t1 ++ a :: t2 ++ b :: t3) :
    ∃ x ∈ t2, ReleasedOf i x := by
  induction cs generalizing db t1 with
  | nil => cases t1 <;> simp [trace, replay] at e
  | cons c cs ih =>
    rw [trace_cons] at e
    cases t1 with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      obtain ⟨cc, l, rfl, hx⟩ := claimedOf_true ha
      exact taken_claimed _ i cs (claimed_taken cc i l db hx) t2 t3 b hb e
    | cons y t1 =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at e
      exact ih _ t1 (by simpa using e.2)

theorem claims_taken (db : Db) (i : Int) (cs : List TCmd) (h : Taken db i)
    (hr : ∀ x ∈ trace db cs, ReleasedOf i x = false) : (trace db cs).filter (ClaimedOf i) = [] := by
  induction cs generalizing db with
  | nil => rfl
  | cons c cs ih =>
    rw [trace_cons] at hr ⊢
    have ⟨h', hc⟩ := taken_step db i c h (hr _ (List.mem_cons_self ..))
    simp only [List.filter_cons, hc, Bool.false_eq_true, ↓reduceIte]
    exact ih _ h' fun x hx => hr x (List.mem_cons_of_mem _ hx)

theorem claims_le_all (db : Db) (i : Int) (cs : List TCmd) (hr : ∀ x ∈ trace db cs, ReleasedOf i x = false) :
    ((trace db cs).filter (ClaimedOf i)).length ≤ 1 := by
  induction cs generalizing db with
  | nil => simp [trace, replay]
  | cons c cs ih =>
    rw [trace_cons] at hr ⊢
    have hr' := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    cases hcl : ClaimedOf i (c, (c.step db).2)
    · simp only [List.filter_cons, hcl, Bool.false_eq_true, ↓reduceIte]; exact ih _ hr'
    · obtain ⟨cc, l, rfl, hx⟩ := claimedOf_true hcl
      have e := claims_taken _ i cs (claimed_taken cc i l db hx) hr'
      rw [List.filter_cons_of_pos hcl]
      show (_ :: List.filter (ClaimedOf i) (trace (Tasks.claim cc i l db).1 cs)).length ≤ 1
      rw [e]; simp

/-- Under the store's assumption (`Atomic`), when processes ran any task commands at once with no successful release
of task `i` among them, at most one of them successfully claimed it. -/
theorem one_winner_all (before after : Db) (ran : List (TCmd × Bool)) (i : Int)
    (h : Atomic TCmd.step before after ran) (hr : ∀ x ∈ ran, ReleasedOf i x = false) :
    (ran.filter (ClaimedOf i)).length ≤ 1 := by
  obtain ⟨order, hp, e⟩ := h
  have ht : trace before (order.map (·.1)) = order := congrArg Prod.snd e
  rw [← (hp.filter _).length_eq, ← ht]
  exact claims_le_all before i _ (by rw [ht]; exact fun x hx => hr x (hp.mem_iff.1 hx))

/-! The pool and the board's order. -/

/-- The order `task board` and the pool sort by (`boardLe`) is total, for any way of telling a red task. -/
theorem boardLe_total (red : Task → Nat) (a b : Task) : (boardLe red a b || boardLe red b a) = true := by
  unfold boardLe
  generalize red a = x; generalize red b = y
  generalize (a.pos.map (· + 1)).getD 0 = p; generalize (b.pos.map (· + 1)).getD 0 = q
  dsimp only
  repeat' split
  all_goals simp_all <;> omega

/-- The order `task board` and the pool sort by is transitive. -/
theorem boardLe_trans (red : Task → Nat) (a b c : Task) (h1 : boardLe red a b = true) (h2 : boardLe red b c = true) :
    boardLe red a c = true := by
  unfold boardLe at *
  generalize red a = x at *; generalize red b = y at *; generalize red c = z at *
  generalize (a.pos.map (· + 1)).getD 0 = p at *; generalize (b.pos.map (· + 1)).getD 0 = q at *
  generalize (c.pos.map (· + 1)).getD 0 = r at *
  dsimp only at *
  repeat' split at h1
  all_goals (repeat' split at h2)
  all_goals (repeat' split)
  all_goals simp_all <;> omega

/-- Rows sorted as `task board` sorts them (`mergeSort (boardLe red)`) are in board order: a red task before any
other, then the earlier place (no place first), then the lower id (model: `ranked_sorted`, `before_total`). -/
theorem board_sorted (red : Task → Nat) (l : List Task) : (l.mergeSort (boardLe red)).Pairwise (boardLe red · · = true) :=
  List.pairwise_mergeSort (le := boardLe red) (fun a b c h1 h2 => boardLe_trans red a b c h1 h2) (boardLe_total red) l

/-- The pool is in board order (model: `ranked_sorted`). -/
theorem pool_sorted (db : Db) : (pool db).Pairwise (boardLe redKey · · = true) :=
  (board_sorted redKey _).filter _

/-- The pool is exactly the open tasks that wait on no task not done and have no stop pending (model: `pool`,
`claimable`). -/
theorem mem_pool (db : Db) (t : Task) : t ∈ pool db ↔
    t ∈ db.tasks ∧ t.status = .ready ∧ blockedByDeps db t = false ∧ stopPending db t = false := by
  simp only [pool, List.mem_filter, List.mem_mergeSort, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, and_assoc]

theorem blockedByDeps_iff (db : Db) (t : Task) :
    blockedByDeps db t = true ↔ ∃ x ∈ db.tasks, x.status ≠ .completed ∧ WaitsOn t x := by
  unfold blockedByDeps WaitsOn
  cases h : t.deps <;> simp

theorem stopPending_congr {db db' : Db} (ha : db'.agents = db.agents) (hc : db'.cursors = db.cursors) (t : Task) :
    stopPending db' t = stopPending db t := by
  unfold stopPending Db.agent Db.cursor
  rw [ha, hc]

theorem find_set_ne {db : Db} {i j : Int} {f : Task → Task} (hf : ∀ u, (f u).id = u.id) (h : j ≠ i) :
    (db.set i f).find j = db.find j := by
  rw [find_set _ _ _ _ hf]
  cases e : db.find j with
  | none => rfl
  | some t => simp [find_id e, h]

theorem find_set_self {db : Db} {i : Int} {f : Task → Task} {r : Task} (hf : ∀ u, (f u).id = u.id)
    (h : db.find i = some r) : (db.set i f).find i = some (f r) := by
  rw [find_set _ _ _ _ hf, h]; simp [find_id h]

/-- F1, `done_frees`: a `task done` of `x` puts in the pool an open task with no stop pending that waits on no task
not done but `x`. -/
theorem done_frees {c : Ctx} {x : Int} {e : String} {db : Db} {k : Int} {st : Option String} {n : Nat}
    (hi : Inv db) (hd : (Tasks.done c x e db).2 = .ok (.done k st n)) {h : Task} (hm : h ∈ db.tasks)
    (ho : h.status = .ready) (hs : stopPending db h = false)
    (hw : ∀ y ∈ db.tasks, y.status ≠ .completed → WaitsOn h y → (y.id : Int) = x) : h ∈ pool (Tasks.done c x e db).1 := by
  unfold Tasks.done at hd ⊢
  split at hd
  · cases hd
  rename_i r hr
  split at hd
  · cases hd
  rename_i h1
  split at hd
  · split at hd
    · cases hd
    split at hd
    · cases hd
    cases hd
  rename_i hl
  split at hd
  · cases hd
  rename_i h2
  split at hd
  · cases hd
  rename_i h3
  simp only [h1, hl, h2, h3, Bool.false_eq_true, ↓reduceIte]
  have hrc : r.status = .inProgress := by simp [mine] at h2; exact h2.2
  have hne : (h.id : Int) ≠ x := fun e => by
    obtain rfl := find_unique hi.1 hr hm e; rw [ho] at hrc; cases hrc
  rw [mem_pool]
  refine ⟨?_, ho, ?_, ?_⟩
  · show h ∈ (db.set x _).tasks
    simp only [Db.set, List.mem_map]
    exact ⟨h, hm, by simp [hne]⟩
  · cases hb : blockedByDeps _ h
    · rfl
    · obtain ⟨y', hy', hyd, hwy⟩ := (blockedByDeps_iff _ _).1 hb
      simp only [Db.log, Db.set, List.mem_map] at hy'
      obtain ⟨y, hy, rfl⟩ := hy'
      by_cases e : (y.id : Int) = x
      · simp [e, Task.status, TaskState.toCompleted, TaskState.status] at hyd
      · simp only [e, ↓reduceIte] at hyd hwy
        exact absurd (hw y hy hyd hwy) e
  · rw [stopPending_congr rfl rfl]; exact hs

/-- F1 for a lander's close (board #200): a `task done` of landing task `x` puts in the pool an open task with no stop
pending that waits on no task not done but `x`. -/
theorem landed_frees {c : Ctx} {x : Int} {e : String} {db : Db} {o : Option String}
    (hi : Inv db) (hd : (Tasks.done c x e db).2 = .ok (.landed o)) {h : Task} (hm : h ∈ db.tasks)
    (ho : h.status = .ready) (hs : stopPending db h = false)
    (hw : ∀ y ∈ db.tasks, y.status ≠ .completed → WaitsOn h y → (y.id : Int) = x) : h ∈ pool (Tasks.done c x e db).1 := by
  unfold Tasks.done at hd ⊢
  split at hd
  · cases hd
  rename_i r hr
  split at hd
  · cases hd
  rename_i h1
  split at hd
  · rename_i hl
    split at hd
    · cases hd
    rename_i h2
    split at hd
    · cases hd
    rename_i h3
    simp only [h1, hl, h2, h3, Bool.false_eq_true, ↓reduceIte]
    have hne : (h.id : Int) ≠ x := fun e => by
      obtain rfl := find_unique hi.1 hr hm e; rw [ho] at hl; cases hl
    rw [mem_pool]
    refine ⟨?_, ho, ?_, ?_⟩
    · show h ∈ (db.set x _).tasks
      simp only [Db.set, List.mem_map]
      exact ⟨h, hm, by simp [hne]⟩
    · cases hb : blockedByDeps _ h
      · rfl
      · obtain ⟨y', hy', hyd, hwy⟩ := (blockedByDeps_iff _ _).1 hb
        simp only [Db.log, Db.set, List.mem_map] at hy'
        obtain ⟨y, hy, rfl⟩ := hy'
        by_cases e : (y.id : Int) = x
        · simp [e, Task.status, TaskState.toCompleted, TaskState.status] at hyd
        · simp only [e, ↓reduceIte] at hyd hwy
          exact absurd (hw y hy hyd hwy) e
    · rw [stopPending_congr rfl rfl]; exact hs
  · split at hd
    · cases hd
    split at hd
    · cases hd
    · simp at hd

/-- F1, `release_waits`: a `task release` of `x` frees nothing: a task that waits on `x` is not in the pool after it. -/
theorem release_waits {c : Ctx} {x : Int} {af : Option (List Int)} {db : Db} {o : Option String}
    (hrel : (Tasks.release c x af db).2 = .ok o) {h : Task}
    (hw : ∃ ds, h.deps = some ds ∧ hasSub ("," ++ ds ++ ",") ("," ++ d x ++ ",") = true) :
    h ∉ pool (Tasks.release c x af db).1 := by
  obtain ⟨y, hy⟩ : ∃ y, db.find x = some y := by
    unfold Tasks.release at hrel
    split at hrel
    · cases hrel
    · exact ⟨_, ‹_›⟩
  obtain ⟨-, ⟨-, hne⟩ | ⟨g, hg, ht, -⟩⟩ := release_spec c x af db
  · exact absurd hrel (hne o)
  intro hp
  have hb := ((mem_pool _ _).1 hp).2.2.1
  have : blockedByDeps (Tasks.release c x af db).1 h = true := by
    refine (blockedByDeps_iff _ _).2 ⟨g y, ?_, by rw [(ready_none (hg y).2).1]; exact nofun, ?_⟩
    · rw [ht]; simp only [Db.set, List.mem_map]
      exact ⟨y, find_mem hy, by simp [find_id hy]⟩
    · obtain ⟨ds, hds, hs⟩ := hw
      exact ⟨ds, hds, by rw [(hg y).1, find_id hy]; exact hs⟩
  rw [hb] at this; cases this

/-- The conditions under which `task release` answers that it took the task from `f`. -/
theorem release_other_conds {c : Ctx} {i : Int} {af : Option (List Int)} {db : Db} {f : String}
    (h : (Tasks.release c i af db).2 = .ok (some f)) :
    ∃ r, db.find i = some r ∧ r.owner = some f ∧ f ≠ "" ∧ f ≠ c.me ∧ Agents.inCharge db c.comms c.me = true ∧
      (r.status = .inProgress ∨ r.status = .needsInput) := by
  unfold Tasks.release at h
  split at h
  · cases h
  rename_i r hr
  dsimp only at h
  split at h
  · cases h
  rename_i db1 h1
  split at h
  · cases h
  split at h1
  · rename_i f' hfa
    split at h1
    · rename_i hs
      rw [hfa] at h
      obtain rfl : f' = f := by simpa using h
      split at hfa
      · rename_i hc
        have ⟨ho, hne⟩ : r.owner = some f' ∧ f' ≠ "" := by simpa [py] using hfa
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, ho, Option.some.injEq] at hc
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hs
        exact ⟨r, hr, ho, hne, hc.1, hc.2, hs.2⟩
      · cases hfa
    · cases h1
  · rename_i hfa
    rw [hfa] at h
    simp at h

/-- What `task release i` (no `--after`) by the communicator or the user leaves when the task was held by another
agent `f`, as a state: `task release` on the conditions of `release_other_conds`. -/
theorem release_other_eq {c : Ctx} {i : Int} {db : Db} {r : Task} {f : String} (hr : db.find i = some r)
    (ho : r.owner = some f) (hne : f ≠ "") (hme : f ≠ c.me) (hc : Agents.inCharge db c.comms c.me = true)
    (hs : r.status = .inProgress ∨ r.status = .needsInput) :
    Tasks.release c i none db =
      let p := Msgs.post ((db.set i reopenFromF).log c.now (some c.me) "release" none (some ("#" ++ d i ++ (" from " ++ f))))
        c.now (Msgs.Who.ofText c.me) (.agent f) s!"{if c.me == Agents.HUMAN then "the user" else c.me} released #{d i}: stop work on it" true
      (p.1.set i ({ · with stop_to := some f, stop_msg := some p.2 }), .ok (some f)) := by
  have hA : (if (r.owner != some c.me && Agents.inCharge db c.comms c.me) = true then py r.owner else none) = some f := by
    simp [ho, hme, hc, py, hne]
  have h2 : (r.owner == some f && (decide (r.status = Status.inProgress) || decide (r.status = Status.needsInput))) = true := by
    simp [ho]; exact hs
  unfold Tasks.release
  simp only [hr, hA, h2, ↓reduceIte]

/-- H2, enabled (model: `releaseOther_enabled`): the communicator's or the user's `task release i` of a task another
agent holds, claimed or blocked, succeeds and names that agent. -/
theorem release_other_enabled {c : Ctx} {i : Int} {db : Db} {r : Task} {f : String} (hr : db.find i = some r)
    (ho : r.owner = some f) (hne : f ≠ "") (hme : f ≠ c.me) (hc : Agents.inCharge db c.comms c.me = true)
    (hs : r.status = .inProgress ∨ r.status = .needsInput) : (Tasks.release c i none db).2 = .ok (some f) := by
  rw [release_other_eq hr ho hne hme hc hs]

/-- H2, what it does (model: `releaseOther_spec`): a `task release i` that took the task from `f` found it held by
`f` (claimed or blocked) and run by the communicator or the user; afterwards the task is open with no owner, lease or
question, records the stop (`stop_to`, `stop_msg`), and `f` is sent that stop, urgent, as the one new message; no
other task, no agent row and no cursor changes. -/
theorem release_other_spec {c : Ctx} {i : Int} {db : Db} {f : String}
    (h : (Tasks.release c i none db).2 = .ok (some f)) :
    ∃ r, db.find i = some r ∧ r.owner = some f ∧ (r.status = .inProgress ∨ r.status = .needsInput) ∧ f ≠ c.me ∧
      Agents.inCharge db c.comms c.me = true ∧
      ∃ r' m, (Tasks.release c i none db).1.find i = some r' ∧ r'.state = .ready none ∧
        r'.lease_until = none ∧ r'.question = none ∧ r'.stop_to = some f ∧
        (Tasks.release c i none db).1.msgs = db.msgs ++ [m] ∧ m.dest = some f ∧ m.urgent = some 1 ∧
        r'.stop_msg = some (m.id : Int) ∧
        (∀ j, j ≠ i → (Tasks.release c i none db).1.find j = db.find j) ∧
        (Tasks.release c i none db).1.agents = db.agents ∧ (Tasks.release c i none db).1.cursors = db.cursors := by
  obtain ⟨r, hr, ho, hne, hme, hc, hs⟩ := release_other_conds h
  refine ⟨r, hr, ho, hs, hme, hc, ?_⟩
  rw [release_other_eq hr ho hne hme hc hs]
  dsimp only
  generalize hP : Msgs.post _ _ _ _ _ _ = P
  have hX : P.1.find i = some (reopenFromF r) := by
    rw [← hP, find_congr (post_tasks ..), find_congr (log_tasks ..)]; exact find_set_self (fun _ => rfl) hr
  let g := fun x : Task => { x with stop_to := some f, stop_msg := some (P.2 : Int) }
  rw [find_set_self (f := g) (fun _ => rfl) hX]
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, by subst hP; rfl, rfl, rfl, by subst hP; rfl, fun j hj => ?_, by subst hP; rfl, by subst hP; rfl⟩
  rw [find_set_ne (f := g) (fun _ => rfl) hj, ← hP, find_congr (post_tasks ..), find_congr (log_tasks ..),
    find_set_ne (f := reopenFromF) (fun _ => rfl) hj]

/-! Stop first (board #53). -/

theorem stopPending_touch (db : Db) (n : String) (cwd here : Option String) (now : Int) (r : Task) :
    stopPending (Agents.touch db n cwd here now) r = stopPending db r := by
  unfold Agents.touch
  split
  · rfl
  split
  · rfl
  rename_i hn
  unfold stopPending Agents.newInbox
  cases py r.stop_to with
  | none => rfl
  | some to =>
    by_cases e : to = n
    · subst e
      have : db.agent to = none := by
        simp only [Db.agent, List.find?_eq_none]; simpa using hn
      simp only [Db.agent] at this ⊢
      by_cases hc : (db.cursors.any fun x => x.agent == to) = true <;> simp [hc, List.find?_append, this]
    · have ha : ∀ (l : List Agent) (x : Agent), x.name = n → (l ++ [x]).find? (·.name == to) = l.find? (·.name == to) :=
        fun l x hx => by simp [List.find?_append, hx, Ne.symm e]
      have hc : ∀ (l : List Cursor) (x : Cursor), x.agent = n → (l ++ [x]).find? (·.agent == to) = l.find? (·.agent == to) :=
        fun l x hx => by simp [List.find?_append, hx, Ne.symm e]
      by_cases hc' : (db.cursors.any fun x => x.agent == n) = true
      · simp only [hc', ↓reduceIte, Db.agent, Db.cursor]
        rw [ha _ _ rfl]; rfl
      · simp only [hc', Bool.false_eq_true, ↓reduceIte, Db.agent, Db.cursor]
        rw [ha _ _ rfl, hc _ _ rfl]; rfl

/-- Stop first (model: `claimable`, `stopped`): `task claim` refuses a task released from an agent still at work that
has not read the stop. -/
theorem claim_not_stopped {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) : stopPending db r = false := by
  obtain ⟨tt, -⟩ := touch_frame db c.me none c.here c.now
  unfold Tasks.claim at h
  rw [hr] at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rw [find_congr tt, hr] at h
  dsimp only at h
  split at h
  · cases h
  rename_i hs
  rw [stopPending_touch] at hs
  simpa using hs

theorem touch_events (db : Db) (n : String) (cwd here : Option String) (now : Int) :
    (Agents.touch db n cwd here now).events = db.events := by
  unfold Agents.touch Agents.newInbox
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem touch_metas (db : Db) (n : String) (cwd here : Option String) (now : Int) :
    (Agents.touch db n cwd here now).metas = db.metas := by
  unfold Agents.touch Agents.newInbox
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem nudgeAt_touch (db : Db) (n : String) (cwd here : Option String) (now : Int) :
    Compact.nudgeAt (Agents.touch db n cwd here now) = Compact.nudgeAt db := by
  simp only [Compact.nudgeAt, Agents.metaNum, Db.getMeta, touch_metas]

theorem ctxOf_touch (db : Db) (n : String) (cwd here : Option String) (now : Int) :
    ctxOf (Agents.touch db n cwd here now) n = ctxOf db n := by
  unfold Agents.touch
  split
  · rfl
  split
  · rfl
  rename_i hn
  have : db.agent n = none := by simp only [Db.agent, List.find?_eq_none]; simpa using hn
  unfold ctxOf Agents.newInbox
  rw [this]
  split <;> simp [Db.agent, List.find?_append, (show db.agents.find? (·.name == n) = none from this)]

theorem reapedFrom_events {db db' : Db} (h : db'.events = db.events) (n : String) (i : Int) :
    reapedFrom db' n i = reapedFrom db n i := by
  simp only [reapedFrom, taskEvents, h]

/-- `task claim` is enabled for a Ready task reserved for no one else, or a Backlog one (or either claimed with the
communicator's --force, board #128; a Backlog task only so), that waits on no task not Completed, has no stop pending, and is not behind the context fence (model: `claim_enabled`,
`claimable`, `fenced`; N1's retake: an agent reap took the task from may claim it back), with a lease text it reads. -/
theorem claim_enabled {c : Ctx} {i : Int} {l : String} {db : Db} {r : Task} {u : Int} (hr : db.find i = some r)
    (hbk : (decide (r.status = .backlog) && !(c.force && Agents.inCharge db c.comms c.me)) = false)
    (hh : ((py r.assignee).any (· != c.me) && !(c.force && Agents.inCharge db c.comms c.me)) = false)
    (ho : r.status = .ready ∨ r.status = .backlog) (hu : undone db r = []) (hb : blockedByDeps db r = false) (hs : stopPending db r = false)
    (hk : Compact.over (ctxOf db c.me) (Compact.nudgeAt db) = false ∨ reapedFrom db c.me i = true) (hl : dur l = some u) :
    ∃ x, (Tasks.claim c i l db).2 = .ok x := by
  obtain ⟨tt, -⟩ := touch_frame db c.me none c.here c.now
  have hb' : blockedByDeps (Agents.touch db c.me none c.here c.now) r = false := by
    unfold blockedByDeps at hb ⊢; rw [tt]; exact hb
  have hk' : (Compact.over (ctxOf (Agents.touch db c.me none c.here c.now) c.me)
      (Compact.nudgeAt (Agents.touch db c.me none c.here c.now)) &&
      !reapedFrom (Agents.touch db c.me none c.here c.now) c.me i) = false := by
    rw [ctxOf_touch, nudgeAt_touch, reapedFrom_events (touch_events ..)]
    rcases hk with hk | hk <;> simp [hk]
  unfold Tasks.claim
  rcases ho with ho | ho
  · simp only [hr, ho, reduceCtorEq, decide_false, decide_true, Bool.false_and, Bool.true_or, Bool.true_and, Bool.or_false,
      hh, hu, hk', Bool.false_eq_true, ↓reduceIte, hl, find_congr tt, stopPending_touch, hs, hb',
      Bool.not_false, Bool.and_true]
    exact ⟨_, rfl⟩
  · have hf : (c.force && Agents.inCharge db c.comms c.me) = true := by simpa [ho] using hbk
    simp only [hr, ho, reduceCtorEq, decide_false, decide_true, Bool.false_and, Bool.or_true, Bool.true_and, Bool.or_false,
      hf, Bool.not_true, Bool.and_false, hu, hk', Bool.false_eq_true, ↓reduceIte, hl, find_congr tt, stopPending_touch, hs,
      hb', Bool.not_false, Bool.and_true]
    exact ⟨_, rfl⟩

/-! A done task stays done. -/

/-- The commands' one change to a task's state is at `j` on a row `f` can't have been given done. -/
theorem done_set {db db' : Db} {i j : Int} {f : Task → Task} (hid : ∀ u, (f u).id = u.id)
    (hj : ∀ r, db.find j = some r → r.status ≠ .completed) (ht : db'.tasks = (db.set j f).tasks)
    (h : (db.find i).map (·.status) = some .completed) : (db'.find i).map (·.status) = some .completed := by
  obtain ⟨t, hf, hs⟩ : ∃ t, db.find i = some t ∧ t.status = .completed := by
    cases e : db.find i with
    | none => simp [e] at h
    | some t => simp [e] at h; exact ⟨t, rfl, h⟩
  rw [find_congr ht, find_set _ _ _ _ hid, hf]
  by_cases e : (t.id : Int) = j
  · have hij : i = j := (find_id hf).symm.trans e
    exact absurd hs (hj t (hij ▸ hf))
  · simp [e, hs]

theorem done_same {db db' : Db} {i : Int} (ht : db'.tasks = db.tasks)
    (h : (db.find i).map (·.status) = some .completed) : (db'.find i).map (·.status) = some .completed := by
  rw [find_congr ht]; exact h

/-- A command that keeps every task's state or makes it done leaves a done task done. -/
theorem done_keeps {db db' : Db} {i : Int} {f : Task → Task} (hid : ∀ u, (f u).id = u.id)
    (hs : ∀ u, u.status = .completed → (f u).status = .completed) {j : Int} (ht : db'.tasks = (db.set j f).tasks)
    (h : (db.find i).map (·.status) = some .completed) : (db'.find i).map (·.status) = some .completed := by
  obtain ⟨t, hf, hd⟩ : ∃ t, db.find i = some t ∧ t.status = .completed := by
    cases e : db.find i with
    | none => simp [e] at h
    | some t => simp [e] at h; exact ⟨t, rfl, h⟩
  rw [find_congr ht, find_set _ _ _ _ hid, hf]
  by_cases e : (t.id : Int) = j
  · simp [e, hs t hd]
  · simp [e, hd]

theorem block_done (c : Ctx) (i : Int) (q : String) (db : Db) (j : Int) (h : (db.find j).map (·.status) = some .completed) :
    (((Tasks.block c i q db).1).find j).map (·.status) = some .completed := by
  have hg : (Tasks.block c i q db).1.tasks = db.tasks ∨ ∃ r, db.find i = some r ∧ r.status = .inProgress := by
    unfold Tasks.block
    split
    · exact .inl rfl
    · rename_i r hr
      by_cases hm : mine r c.me = true
      · exact .inr ⟨r, hr, by simp [mine] at hm; exact hm.2⟩
      · exact .inl (by simp [hm])
  rcases hg with ht | ⟨r, hr, hb⟩
  · exact done_same ht h
  · rcases block_spec_so c i q db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact done_same ht h
    · refine done_set (i := j) (fun u => (hf u).1) (fun r' hr' => ?_) ht h
      rw [hr] at hr'; cases hr'; rw [hb]; nofun

theorem unblock_done (c : Ctx) (i : Int) (a : String) (db : Db) (j : Int) (h : (db.find j).map (·.status) = some .completed) :
    (((Tasks.unblock c i a db).1).find j).map (·.status) = some .completed := by
  have hg : (Tasks.unblock c i a db).1.tasks = db.tasks ∨ ∃ r, db.find i = some r ∧ r.status = .needsInput := by
    unfold Tasks.unblock
    dsimp only
    split
    · exact .inl rfl
    · rename_i r hr
      by_cases hb : r.status = .needsInput
      · exact .inr ⟨r, hr, hb⟩
      · exact .inl (by simp [hb])
  rcases hg with ht | ⟨r, hr, hb⟩
  · exact done_same ht h
  · rcases unblock_spec_so c i a db with ⟨ht, -⟩ | ⟨-, f, -, -, hf, ht, -⟩
    · exact done_same ht h
    · refine done_set (i := j) (fun u => (hf u).1) (fun r' hr' => ?_) ht h
      rw [hr] at hr'; cases hr'; rw [hb]; nofun

theorem drop_done (c : Ctx) (i : Int) (dup : Option Int) (note : Option String) (db : Db) (j : Int)
    (h : (db.find j).map (·.status) = some .completed) :
    (((Tasks.drop c i dup note db).1).find j).map (·.status) = some .completed := by
  have hg : (Tasks.drop c i dup note db).1.tasks = db.tasks ∨ ∃ r, db.find i = some r ∧ r.status ≠ .completed := by
    unfold Tasks.drop
    split
    · exact .inl rfl
    · rename_i r hr
      by_cases hd : r.status = .completed
      · exact .inl (by simp [hd])
      · exact .inr ⟨r, hr, hd⟩
  rcases hg with ht | ⟨r, hr, hd⟩
  · exact done_same ht h
  · rcases drop_spec c i dup note db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact done_same ht h
    · refine done_set (i := j) (fun u => (hf u).1) (fun r' hr' => ?_) ht h
      rw [hr] at hr'; cases hr'; exact hd

/-- If `task release` succeeds, the task was claimed or blocked. -/
theorem release_ok_state {c : Ctx} {i : Int} {af : Option (List Int)} {db : Db} {x : Option String}
    (h : (Tasks.release c i af db).2 = .ok x) : ∃ r, db.find i = some r ∧ (r.status = .inProgress ∨ r.status = .needsInput) := by
  unfold Tasks.release at h
  split at h
  · cases h
  · rename_i r hr
    refine ⟨r, hr, ?_⟩
    dsimp only at h
    split at h
    · cases h
    · rename_i db1 h1
      split at h1
      · split at h1
        · rename_i hc; simp at hc; exact hc.2
        · cases h1
      · split at h1
        · rename_i hc; simp [mine] at hc; exact .inl hc.2
        · cases h1

/-- A done task stays done under every command: `task drop` refuses one, and no other command changes a done task's state. -/
theorem done_final (c : TCmd) (db : Db) (i : Int) (h : (db.find i).map (·.status) = some .completed) :
    (((c.step db).1).find i).map (·.status) = some .completed := by
  cases c with
  | add cc a =>
    show (((Tasks.add cc a db).1).find i).map (·.status) = some .completed
    rcases add_spec cc a db with ⟨ht, -, -⟩ | ⟨t, ht, -⟩
    · exact done_same ht h
    · obtain ⟨u, hf, hs⟩ : ∃ u, db.find i = some u ∧ u.status = .completed := by
        cases e : db.find i with
        | none => simp [e] at h
        | some t => simp [e] at h; exact ⟨t, rfl, h⟩
      rw [show ((Tasks.add cc a db).1).find i = some u by
        simp only [Db.find] at hf ⊢; rw [ht, List.find?_append, hf]; rfl]
      simp [hs]
  | claim cc j l =>
    obtain ⟨-, hs⟩ := claim_spec cc j l db
    rcases hs with ⟨ht, -⟩ | ⟨t, g, hf, ho, hg, ht, -⟩
    · exact done_same ht h
    · exact done_set (fun u => (hg u).1) (fun r hr => by rw [hf] at hr; cases hr; rcases ho with ho | ho <;> rw [ho] <;> nofun) ht h
  | release cc j af =>
    obtain ⟨-, hs⟩ := release_spec cc j af db
    rcases hs with ⟨ht, -⟩ | ⟨g, hg, ht, x, hx⟩
    · exact done_same ht h
    · obtain ⟨r, hr, hs⟩ := release_ok_state hx
      refine done_set (i := i) (fun u => (hg u).1) (fun r' hr' => ?_) ht h
      rw [hr] at hr'; cases hr'; rcases hs with e | e <;> rw [e] <;> nofun
  | after cc j l =>
    rcases after_spec cc j l db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact done_same ht h
    · exact done_keeps (fun u => (hf u).1) (fun u hu => by rw [(hf u).so.2.1]; exact hu) ht h
  | priority cc j p =>
    rcases priority_spec cc j p db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact done_same ht h
    · exact done_keeps (fun u => (hf u).1) (fun u hu => by rw [(hf u).so.2.1]; exact hu) ht h
  | renew cc j l =>
    rcases renew_spec_so cc j l db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact done_same ht h
    · exact done_keeps (fun u => (hf u).1) (fun u hu => by rw [(hf u).2.1]; exact hu) ht h
  | edit cc j a =>
    rcases edit_spec cc j a db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact done_same ht h
    · exact done_keeps (fun u => (hf u).1) (fun u hu => by rw [(hf u).so.2.1]; exact hu) ht h
  | done cc j e =>
    rcases done_spec cc j e db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩ | ⟨f, -, r, hr, hrs, hf, ht, -, -⟩
    · exact done_same ht h
    · refine done_keeps (fun u => (hf u).1) (fun u hu => ?_) ht h
      unfold Task.status; rw [(hf u).2.2.2]; rfl
    · exact done_set (i := i) (fun u => (hf u).1) (fun r' hr' => by rw [hr] at hr'; cases hr'; rw [hrs]; nofun) ht h
  | block cc j q => exact block_done cc j q db i h
  | unblock cc j a => exact unblock_done cc j a db i h
  | drop cc j d n => exact drop_done cc j d n db i h
  | land cc j s l =>
    obtain ⟨-, hs⟩ := land_spec cc j s l db
    rcases hs with ⟨ht, -⟩ | ⟨r, g, hr, hrs, -, hg, ht, -⟩
    · exact done_same ht h
    · exact done_set (i := i) (fun u => (hg u).1) (fun r' hr' => by rw [hr] at hr'; cases hr'; rw [hrs]; nofun) ht h
  | unland cc j w =>
    obtain ⟨-, hs⟩ := unland_spec cc j w db
    rcases hs with ⟨ht, -⟩ | ⟨r, g, hr, hrs, hg, ht, -⟩
    · exact done_same ht h
    · exact done_set (i := i) (fun u => (hg u).1) (fun r' hr' => by rw [hr] at hr'; cases hr'; rw [hrs]; nofun) ht h
  | board => exact h

/-! Landing (board #200). -/

/-- A landing task is not claimable: `task claim` of it fails. -/
theorem claim_landing {c : Ctx} {i : Int} {l : String} {db : Db} {r : Task} (hr : db.find i = some r)
    (hs : r.status = .inReview) (x : Claimed) : (Tasks.claim c i l db).2 ≠ .ok x := by
  intro hx
  obtain ⟨-, ⟨-, hne⟩ | ⟨t, -, hf, ho, -⟩⟩ := claim_spec c i l db
  · exact hne x hx
  · rw [hr] at hf; cases hf; rw [hs] at ho; rcases ho with ho | ho <;> cases ho

/-- A landing task's dependants keep waiting: a task that waits on it is not in the pool. -/
theorem landing_waits {db : Db} {x h : Task} (hx : x ∈ db.tasks) (hs : x.status = .inReview) (hw : WaitsOn h x) :
    h ∉ pool db := by
  intro hp
  have hb := ((mem_pool _ _).1 hp).2.2.1
  rw [(blockedByDeps_iff _ _).2 ⟨x, hx, by rw [hs]; nofun, hw⟩] at hb; cases hb

/-- A landing task is closed only by its lander (the one named, an agent with role lander, or the communicator), and
only with evidence git found on the task's base. -/
theorem done_landing {c : Ctx} {i : Int} {e : String} {db : Db} {r : Task} {x : DoneOut} (hr : db.find i = some r)
    (hs : r.status = .inReview) (h : (Tasks.done c i e db).2 = .ok x) :
    isLander db c.comms c.me r = true ∧ c.onBase = true ∧ x = .landed r.owner := by
  unfold Tasks.done at h
  rw [hr] at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hl
      split at h
      · cases h
      · rename_i ho
        simp at h hl ho
        exact ⟨hl, ho, h.symm⟩

/-- `task land` hands over only its owner's claimed task, and leaves it landing with that owner. -/
theorem land_ok {c : Ctx} {i : Int} {s : String} {l : Option String} {db : Db} (h : (Tasks.land c i s l db).2 = .ok ()) :
    ∃ r, db.find i = some r ∧ r.status = .inProgress ∧ r.owner = some c.me ∧
      ∃ r', (Tasks.land c i s l db).1.find i = some r' ∧ r'.status = .inReview ∧ r'.owner = some c.me := by
  obtain ⟨-, ⟨-, hne⟩ | ⟨r, g, hr, hs, ho, hg, ht, -⟩⟩ := land_spec c i s l db
  · exact absurd h (hne ())
  · refine ⟨r, hr, hs, ho, g r, ?_, ((hg r).2.2.1 hs).1, ((hg r).2.2.1 hs).2.trans ho⟩
    rw [find_congr ht, find_set _ _ _ _ fun u => (hg u).1, hr]
    simp [find_id hr]

end SwarmLean.Board
