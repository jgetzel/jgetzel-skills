import SwarmLean.Proofs

/-! Board task #103: swarm/model's properties of tasks and the board, proved of the real steps (Db/Tasks.lean's `add`,
`claim`, `after`, `priority`, `renew`, `done`, `block`, `unblock`, `release`, `edit`, `drop`, `pool`, `boardLe`), the
functions Cmd/Tasks.lean runs in `Store.txn`. Concurrency is any order of whole transactions (`Atomic`, Store.lean),
the one assumption. -/

namespace SwarmLean.Board
open Tasks

/-- Every task command, with everything it reads of the world. -/
inductive TCmd
  | add (c : Ctx) (a : AddArgs)
  | claim (c : Ctx) (i : Int) (lease : String)
  | after (c : Ctx) (i : Int) (deps : List Int)
  | priority (c : Ctx) (i : Int) (p : Int)
  | renew (c : Ctx) (i : Int) (lease : String)
  | done (c : Ctx) (i : Int) (evidence : String)
  | block (c : Ctx) (i : Int) (question : String)
  | unblock (c : Ctx) (i : Int) (answer : String)
  | release (c : Ctx) (i : Int) (after : Option (List Int))
  | edit (c : Ctx) (i : Int) (a : EditArgs)
  | drop (c : Ctx) (i : Int)
  | board

/-- A command's effect on the db and whether it succeeded: the CLI's own step functions. -/
def TCmd.step : TCmd → Db → Db × Bool
  | .add c a, db => ((Tasks.add c a db).1, (Tasks.add c a db).2.toBool)
  | .claim c i l, db => ((Tasks.claim c i l db).1, (Tasks.claim c i l db).2.toBool)
  | .after c i l, db => ((Tasks.after c i l db).1, (Tasks.after c i l db).2.toBool)
  | .priority c i p, db => ((Tasks.priority c i p db).1, (Tasks.priority c i p db).2.toBool)
  | .renew c i l, db => ((Tasks.renew c i l db).1, (Tasks.renew c i l db).2.toBool)
  | .done c i e, db => ((Tasks.done c i e db).1, (Tasks.done c i e db).2.toBool)
  | .block c i q, db => ((Tasks.block c i q db).1, (Tasks.block c i q db).2.toBool)
  | .unblock c i a, db => ((Tasks.unblock c i a db).1, (Tasks.unblock c i a db).2.toBool)
  | .release c i af, db => ((Tasks.release c i af db).1, (Tasks.release c i af db).2.toBool)
  | .edit c i a, db => ((Tasks.edit c i a db).1, (Tasks.edit c i a db).2.toBool)
  | .drop c i, db => ((Tasks.drop c i db).1, (Tasks.drop c i db).2.toBool)
  | .board, db => (db, true)

/-- The db after `cs` from `db`. -/
def run (db : Db) (cs : List TCmd) : Db := (replay TCmd.step db cs).1

/-- Each command of `cs`, from `db`, with whether it succeeded. -/
def trace (db : Db) (cs : List TCmd) : List (TCmd × Bool) := (replay TCmd.step db cs).2

/-- Evidence `task done` accepts: some text that is not all whitespace. -/
def EvOk (e : Option String) : Prop := ∃ s, e = some s ∧ strip s ≠ ""

/-- S5 of one task: if it is done it has evidence. -/
def DoneEv (t : Task) : Prop := t.state = .done → EvOk t.evidence

/-- The board's invariant: `Inv` (ids unique and below the next id, owners fit states) and every done task has
evidence. -/
def BInv (db : Db) : Prop := Inv db ∧ ∀ t ∈ db.tasks, DoneEv t

/-- `v` is `u` with its id, state, owner and evidence as they were. -/
def Keeps (u v : Task) : Prop := v.id = u.id ∧ v.state = u.state ∧ v.owner = u.owner ∧ v.evidence = u.evidence

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

theorem priority_spec (c : Ctx) (i p : Int) (db : Db) :
    ((Tasks.priority c i p db).1.tasks = db.tasks ∧ (Tasks.priority c i p db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, Keeps u (f u)) ∧ (Tasks.priority c i p db).1.tasks = (db.set i f).tasks ∧
      (Tasks.priority c i p db).1.taskNext = db.taskNext := by
  unfold Tasks.priority
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl, rfl⟩

theorem renew_spec (c : Ctx) (i : Int) (l : String) (db : Db) :
    ((Tasks.renew c i l db).1.tasks = db.tasks ∧ (Tasks.renew c i l db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, Keeps u (f u)) ∧ (Tasks.renew c i l db).1.tasks = (db.set i f).tasks ∧
      (Tasks.renew c i l db).1.taskNext = db.taskNext := by
  unfold Tasks.renew
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    · split
      · exact .inl ⟨rfl, rfl⟩
      · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl, rfl⟩

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

theorem done_spec (c : Ctx) (i : Int) (e : String) (db : Db) :
    ((Tasks.done c i e db).1.tasks = db.tasks ∧ (Tasks.done c i e db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, (f u).id = u.id ∧ (f u).owner = u.owner ∧ EvOk (f u).evidence ∧
        ((f u).state = u.state ∨ (f u).state = .done)) ∧
      (Tasks.done c i e db).1.tasks = (db.set i f).tasks ∧ (Tasks.done c i e db).1.taskNext = db.taskNext := by
  unfold Tasks.done
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    · rename_i hs
      have ev : EvOk (some e) := ⟨e, rfl, by simpa using hs⟩
      split
      · exact .inl ⟨rfl, rfl⟩
      · split
        · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, ev, .inl rfl⟩
        · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, ev, .inr rfl⟩

theorem block_spec (c : Ctx) (i : Int) (q : String) (db : Db) :
    ((Tasks.block c i q db).1.tasks = db.tasks ∧ (Tasks.block c i q db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, (f u).id = u.id ∧ (f u).owner = u.owner ∧ (f u).state = .blocked) ∧
      (Tasks.block c i q db).1.tasks = (db.set i f).tasks ∧ (Tasks.block c i q db).1.taskNext = db.taskNext := by
  unfold Tasks.block
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl⟩

theorem unblock_spec (c : Ctx) (i : Int) (ans : String) (db : Db) :
    ((Tasks.unblock c i ans db).1.tasks = db.tasks ∧ (Tasks.unblock c i ans db).1.taskNext = db.taskNext) ∨
    ∃ r f, db.find i = some r ∧ r.owner.isSome ∧
      (∀ u, (f u).id = u.id ∧ (f u).owner = u.owner ∧ (f u).state = .claimed) ∧
      (Tasks.unblock c i ans db).1.tasks = (db.set i f).tasks ∧ (Tasks.unblock c i ans db).1.taskNext = db.taskNext := by
  unfold Tasks.unblock
  split
  · exact .inl ⟨rfl, rfl⟩
  · rename_i r hr
    split
    · exact .inl ⟨rfl, rfl⟩
    · split
      · exact .inl ⟨rfl, rfl⟩
      · split
        · exact .inl ⟨rfl, rfl⟩
        · rename_i ho
          have hs : r.owner.isSome := Option.isSome_iff_ne_none.2 (by simpa using ho)
          dsimp only
          repeat' split
          all_goals (refine .inr ⟨r, _, hr, hs, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl⟩)

theorem drop_spec (c : Ctx) (i : Int) (db : Db) :
    ((Tasks.drop c i db).1.tasks = db.tasks ∧ (Tasks.drop c i db).1.taskNext = db.taskNext) ∨
    ∃ f : Task → Task, (∀ u, (f u).id = u.id ∧ (f u).owner = none ∧ (f u).state = .dropped) ∧
      (Tasks.drop c i db).1.tasks = (db.set i f).tasks ∧ (Tasks.drop c i db).1.taskNext = db.taskNext := by
  unfold Tasks.drop
  split
  · exact .inl ⟨rfl, rfl⟩
  · split
    · exact .inl ⟨rfl, rfl⟩
    · refine .inr ⟨_, ?_, rfl, rfl⟩; intro; exact ⟨rfl, rfl, rfl⟩

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

theorem keeps_ok {u v : Task} (h : Keeps u v) (hu : TaskOk u) : TaskOk v := by
  obtain ⟨-, hs, ho, he⟩ := h
  obtain ⟨⟨h1, h2⟩, h3⟩ := hu
  exact ⟨⟨fun e => by rw [ho]; exact h1 (hs.symm.trans e), fun e => by rw [ho]; exact h2 (hs.symm.trans e)⟩,
    fun e => by rw [he]; exact h3 (hs.symm.trans e)⟩

/-- A task in a state other than open and claimed fits any owner and, unless done, needs no evidence. -/
theorem ok_of_state {v : Task} (h : v.state = .blocked ∨ v.state = .dropped) : TaskOk v := by
  rcases h with h | h <;> exact ⟨⟨fun e => (by rw [h] at e; cases e), fun e => (by rw [h] at e; cases e)⟩,
    fun e => (by rw [h] at e; cases e)⟩

theorem keeps_step {db db' : Db} {i : Int}
    (h : (db'.tasks = db.tasks ∧ db'.taskNext = db.taskNext) ∨ ∃ f : Task → Task, (∀ u, Keeps u (f u)) ∧
      db'.tasks = (db.set i f).tasks ∧ db'.taskNext = db.taskNext) (hi : BInv db) : BInv db' := by
  rcases h with ⟨ht, hn⟩ | ⟨f, hk, ht, hn⟩
  · exact binv_same ht hn hi
  · exact binv_set (fun u => (hk u).1) (fun u _ _ => keeps_ok (hk u)) ht hn hi

theorem step_binv (c : TCmd) (db : Db) (h : BInv db) : BInv (c.step db).1 := by
  cases c with
  | add c a =>
    refine ⟨step_inv (.add c a) db h.1, ?_⟩
    show ∀ t ∈ (Tasks.add c a db).1.tasks, DoneEv t
    rcases add_spec c a db with ⟨ht, -, -⟩ | ⟨t, ht, -, hs, -, -⟩
    · rw [ht]; exact h.2
    · rw [ht]; intro u hu; simp only [List.mem_append, List.mem_singleton] at hu
      rcases hu with hu | rfl
      · exact h.2 u hu
      · intro e; rw [hs] at e; cases e
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
      obtain ⟨-, hs, ho⟩ := hg u
      exact ⟨⟨fun e => (by rw [hs] at e; cases e), fun _ => ho⟩, fun e => (by rw [hs] at e; cases e)⟩
  | after c i l => exact keeps_step (after_spec c i l db) h
  | priority c i p => exact keeps_step (priority_spec c i p db) h
  | renew c i l => exact keeps_step (renew_spec c i l db) h
  | edit c i a => exact keeps_step (edit_spec c i a db) h
  | done c i e =>
    rcases done_spec c i e db with ⟨ht, hn⟩ | ⟨f, hf, ht, hn⟩
    · exact binv_same ht hn h
    · refine binv_set (fun u => (hf u).1) (fun u _ _ hu => ?_) ht hn h
      obtain ⟨-, ho, hev, hs⟩ := hf u
      refine ⟨?_, fun _ => hev⟩
      rcases hs with hs | hs
      · exact ⟨fun e => by rw [ho]; exact hu.1.1 (hs.symm.trans e), fun e => by rw [ho]; exact hu.1.2 (hs.symm.trans e)⟩
      · exact ⟨fun e => (by rw [hs] at e; cases e), fun e => (by rw [hs] at e; cases e)⟩
  | block c i q =>
    rcases block_spec c i q db with ⟨ht, hn⟩ | ⟨f, hf, ht, hn⟩
    · exact binv_same ht hn h
    · exact binv_set (fun u => (hf u).1) (fun u _ _ _ => ok_of_state (.inl (hf u).2.2)) ht hn h
  | unblock c i a =>
    rcases unblock_spec c i a db with ⟨ht, hn⟩ | ⟨r, f, hr, hs, hf, ht, hn⟩
    · exact binv_same ht hn h
    · refine binv_set (fun u => (hf u).1) (fun u hu e _ => ?_) ht hn h
      obtain rfl := find_unique h.1.1 hr hu e
      obtain ⟨-, ho, hst⟩ := hf u
      exact ⟨⟨fun _ => by rw [ho]; exact hs, fun e => (by rw [hst] at e; cases e)⟩, fun e => (by rw [hst] at e; cases e)⟩
  | drop c i =>
    rcases drop_spec c i db with ⟨ht, hn⟩ | ⟨f, hf, ht, hn⟩
    · exact binv_same ht hn h
    · exact binv_set (fun u => (hf u).1) (fun u _ _ _ => ok_of_state (.inr (hf u).2.2)) ht hn h
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
theorem done_has_evidence (cs : List TCmd) : ∀ t ∈ (run {} cs).tasks, t.state = .done → EvOk t.evidence :=
  (run_binv cs).2

/-- S2 (model: `no_claim_before_dependencies_done`): a successful `task claim i` finds every task `i` is after done. -/
theorem claim_deps_done {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) :
    ∀ j ∈ depsOf r, ∀ u, db.find j = some u → u.state = .done := by
  have hu : undone db r = [] := by
    unfold Tasks.claim at h
    rw [hr] at h
    dsimp only at h
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

/-- A successful claim of task `i`. -/
def ClaimedOf (i : Int) : TCmd × Bool → Bool
  | (.claim _ j _, true) => j == i
  | _ => false

/-- A successful release of task `i`. -/
def ReleasedOf (i : Int) : TCmd × Bool → Bool
  | (.release _ j _, true) => j == i
  | _ => false

/-- Task `i` is on the board and not open. -/
def Taken (db : Db) (i : Int) : Prop := ∃ t, db.find i = some t ∧ t.state ≠ .open

theorem taken_same {db db' : Db} {i : Int} (ht : db'.tasks = db.tasks) (h : Taken db i) : Taken db' i := by
  obtain ⟨t, hf, hs⟩ := h; exact ⟨t, by rw [find_congr ht]; exact hf, hs⟩

theorem taken_set {db db' : Db} {i j : Int} {f : Task → Task} (hid : ∀ u, (f u).id = u.id)
    (hno : j = i → ∀ u, u.state ≠ .open → (f u).state ≠ .open) (ht : db'.tasks = (db.set j f).tasks)
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

theorem claimedOf_claim (i j : Int) (cc : Ctx) (l : String) (b : Bool) :
    ClaimedOf i (.claim cc j l, b) = (b && (j == i)) := by cases b <;> rfl

theorem releasedOf_release (i j : Int) (cc : Ctx) (af : Option (List Int)) (b : Bool) :
    ReleasedOf i (.release cc j af, b) = (b && (j == i)) := by cases b <;> rfl

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
        subst e; obtain ⟨u, hu, hs⟩ := h; rw [hf] at hu; cases hu; exact hs ho
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
    · exact taken_set (fun u => (hf u).1) (fun _ u hu => (hf u).2.1 ▸ hu) ht h
  | priority cc j p =>
    refine ⟨?_, rfl⟩
    rcases priority_spec cc j p db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u hu => (hf u).2.1 ▸ hu) ht h
  | renew cc j l =>
    refine ⟨?_, rfl⟩
    rcases renew_spec cc j l db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u hu => (hf u).2.1 ▸ hu) ht h
  | edit cc j a =>
    refine ⟨?_, rfl⟩
    rcases edit_spec cc j a db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u hu => (hf u).2.1 ▸ hu) ht h
  | done cc j e =>
    refine ⟨?_, rfl⟩
    rcases done_spec cc j e db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · refine taken_set (fun u => (hf u).1) (fun _ u hu => ?_) ht h
      rcases (hf u).2.2.2 with e | e <;> rw [e]
      · exact hu
      · exact nofun
  | block cc j q =>
    refine ⟨?_, rfl⟩
    rcases block_spec cc j q db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u _ => by rw [(hf u).2.2]; exact nofun) ht h
  | unblock cc j a =>
    refine ⟨?_, rfl⟩
    rcases unblock_spec cc j a db with ⟨ht, -⟩ | ⟨-, f, -, -, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u _ => by rw [(hf u).2.2]; exact nofun) ht h
  | drop cc j =>
    refine ⟨?_, rfl⟩
    rcases drop_spec cc j db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · exact taken_same ht h
    · exact taken_set (fun u => (hf u).1) (fun _ u _ => by rw [(hf u).2.2]; exact nofun) ht h
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
  · refine ⟨g t, ?_, by rw [(hg t).2.1]; exact nofun⟩
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
  generalize (a.priority.map (· + 1)).getD 0 = p; generalize (b.priority.map (· + 1)).getD 0 = q
  dsimp only
  repeat' split
  all_goals simp_all <;> omega

/-- The order `task board` and the pool sort by is transitive. -/
theorem boardLe_trans (red : Task → Nat) (a b c : Task) (h1 : boardLe red a b = true) (h2 : boardLe red b c = true) :
    boardLe red a c = true := by
  unfold boardLe at *
  generalize red a = x at *; generalize red b = y at *; generalize red c = z at *
  generalize (a.priority.map (· + 1)).getD 0 = p at *; generalize (b.priority.map (· + 1)).getD 0 = q at *
  generalize (c.priority.map (· + 1)).getD 0 = r at *
  dsimp only at *
  repeat' split at h1
  all_goals (repeat' split at h2)
  all_goals (repeat' split)
  all_goals simp_all <;> omega

/-- Rows sorted as `task board` sorts them (`mergeSort (boardLe red)`) are in board order: a red task before any
other, then the lower priority number, then the lower id (model: `ranked_sorted`, `before_total`). -/
theorem board_sorted (red : Task → Nat) (l : List Task) : (l.mergeSort (boardLe red)).Pairwise (boardLe red · · = true) :=
  List.pairwise_mergeSort (le := boardLe red) (fun a b c h1 h2 => boardLe_trans red a b c h1 h2) (boardLe_total red) l

/-- The pool is in board order (model: `ranked_sorted`). -/
theorem pool_sorted (db : Db) : (pool db).Pairwise (boardLe redKey · · = true) :=
  (board_sorted redKey _).filter _

/-- The pool is exactly the open tasks that wait on no task not done and have no stop pending (model: `pool`,
`claimable`). -/
theorem mem_pool (db : Db) (t : Task) : t ∈ pool db ↔
    t ∈ db.tasks ∧ t.state = .open ∧ blockedByDeps db t = false ∧ stopPending db t = false := by
  simp only [pool, List.mem_filter, List.mem_mergeSort, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, and_assoc]

/-- `t` waits on `x` in the pool's sense: `x`'s id is one of the ids in `t`'s deps text. -/
def WaitsOn (t x : Task) : Prop := ∃ ds, t.deps = some ds ∧ hasSub ("," ++ ds ++ ",") ("," ++ d x.id ++ ",") = true

theorem blockedByDeps_iff (db : Db) (t : Task) :
    blockedByDeps db t = true ↔ ∃ x ∈ db.tasks, x.state ≠ .done ∧ WaitsOn t x := by
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
    (ho : h.state = .open) (hs : stopPending db h = false)
    (hw : ∀ y ∈ db.tasks, y.state ≠ .done → WaitsOn h y → (y.id : Int) = x) : h ∈ pool (Tasks.done c x e db).1 := by
  unfold Tasks.done at hd ⊢
  split at hd
  · cases hd
  rename_i r hr
  split at hd
  · cases hd
  rename_i h1
  split at hd
  · cases hd
  rename_i h2
  split at hd
  · cases hd
  rename_i h3
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte]
  have hrc : r.state = .claimed := by simp [mine] at h2; exact h2.2
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
      · simp [e] at hyd
      · simp only [e, ↓reduceIte] at hyd hwy
        exact absurd (hw y hy hyd hwy) e
  · rw [stopPending_congr rfl rfl]; exact hs

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
    refine (blockedByDeps_iff _ _).2 ⟨g y, ?_, by rw [(hg y).2.1]; exact nofun, ?_⟩
    · rw [ht]; simp only [Db.set, List.mem_map]
      exact ⟨y, find_mem hy, by simp [find_id hy]⟩
    · obtain ⟨ds, hds, hs⟩ := hw
      exact ⟨ds, hds, by rw [(hg y).1, find_id hy]; exact hs⟩
  rw [hb] at this; cases this

/-- The conditions under which `task release` answers that it took the task from `f`. -/
theorem release_other_conds {c : Ctx} {i : Int} {af : Option (List Int)} {db : Db} {f : String}
    (h : (Tasks.release c i af db).2 = .ok (some f)) :
    ∃ r, db.find i = some r ∧ r.owner = some f ∧ f ≠ "" ∧ f ≠ c.me ∧ Agents.inCharge db c.comms c.me = true ∧
      (r.state = .claimed ∨ r.state = .blocked) := by
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
    (hs : r.state = .claimed ∨ r.state = .blocked) :
    Tasks.release c i none db =
      let p := Msgs.post ((db.set i reopenFromF).log c.now (some c.me) "release" none (some ("#" ++ d i ++ (" from " ++ f))))
        c.now c.me f s!"{if c.me == Agents.HUMAN then "the user" else c.me} released #{d i}: stop work on it" true
      (p.1.set i ({ · with stop_to := some f, stop_msg := some p.2 }), .ok (some f)) := by
  have hA : (if (r.owner != some c.me && Agents.inCharge db c.comms c.me) = true then py r.owner else none) = some f := by
    simp [ho, hme, hc, py, hne]
  have h2 : (r.owner == some f && (decide (r.state = Status.claimed) || decide (r.state = Status.blocked))) = true := by
    simp [ho]; exact hs
  unfold Tasks.release
  simp only [hr, hA, h2, ↓reduceIte]

/-- H2, enabled (model: `releaseOther_enabled`): the communicator's or the user's `task release i` of a task another
agent holds, claimed or blocked, succeeds and names that agent. -/
theorem release_other_enabled {c : Ctx} {i : Int} {db : Db} {r : Task} {f : String} (hr : db.find i = some r)
    (ho : r.owner = some f) (hne : f ≠ "") (hme : f ≠ c.me) (hc : Agents.inCharge db c.comms c.me = true)
    (hs : r.state = .claimed ∨ r.state = .blocked) : (Tasks.release c i none db).2 = .ok (some f) := by
  rw [release_other_eq hr ho hne hme hc hs]

/-- H2, what it does (model: `releaseOther_spec`): a `task release i` that took the task from `f` found it held by
`f` (claimed or blocked) and run by the communicator or the user; afterwards the task is open with no owner, lease or
question, records the stop (`stop_to`, `stop_msg`), and `f` is sent that stop, urgent, as the one new message; no
other task, no agent row and no cursor changes. -/
theorem release_other_spec {c : Ctx} {i : Int} {db : Db} {f : String}
    (h : (Tasks.release c i none db).2 = .ok (some f)) :
    ∃ r, db.find i = some r ∧ r.owner = some f ∧ (r.state = .claimed ∨ r.state = .blocked) ∧ f ≠ c.me ∧
      Agents.inCharge db c.comms c.me = true ∧
      ∃ r' m, (Tasks.release c i none db).1.find i = some r' ∧ r'.state = .open ∧ r'.owner = none ∧
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
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, by subst hP; rfl, rfl, rfl, by subst hP; rfl, fun j hj => ?_, by subst hP; rfl, by subst hP; rfl⟩
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

/-- `task claim` is enabled for a task that is open, not held (or claimed with the communicator's --force, board #128),
waits on no task not done, has no stop pending, and is not behind the context fence (model: `claim_enabled`,
`claimable`, `fenced`; N1's retake: an agent reap took the task from may claim it back), with a lease text it reads. -/
theorem claim_enabled {c : Ctx} {i : Int} {l : String} {db : Db} {r : Task} {u : Int} (hr : db.find i = some r)
    (hh : (r.hold.isSome && !(c.force && Agents.inCharge db c.comms c.me)) = false) (ho : r.state = .open) (hu : undone db r = []) (hb : blockedByDeps db r = false) (hs : stopPending db r = false)
    (hk : ctxOf db c.me < CTX_WARN ∨ reapedFrom db c.me i = true) (hl : dur l = some u) :
    ∃ x, (Tasks.claim c i l db).2 = .ok x := by
  obtain ⟨tt, -⟩ := touch_frame db c.me none c.here c.now
  have hb' : blockedByDeps (Agents.touch db c.me none c.here c.now) r = false := by
    unfold blockedByDeps at hb ⊢; rw [tt]; exact hb
  have hk' : (decide (ctxOf (Agents.touch db c.me none c.here c.now) c.me ≥ CTX_WARN) &&
      !reapedFrom (Agents.touch db c.me none c.here c.now) c.me i) = false := by
    rw [ctxOf_touch, reapedFrom_events (touch_events ..)]
    rcases hk with hk | hk <;> simp [hk]
    omega
  unfold Tasks.claim
  simp only [hr, hh, hu, hk', Bool.false_eq_true, ↓reduceIte, hl, find_congr tt, stopPending_touch, hs, ho, hb',
    Bool.not_false, Bool.and_true, decide_true]
  exact ⟨_, rfl⟩

end SwarmLean.Board
