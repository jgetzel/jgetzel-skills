import SwarmLean.Db.Tasks
import SwarmLean.Assumptions

/-! The slice's theorems (board #96) about the real steps: `Cmd.step` runs Db/Tasks.lean's `add`, `claim` and
`release`, the functions the CLI runs in `Store.txn`. -/

namespace SwarmLean
open Tasks

/-- A command the theorems cover, with everything it reads of the world. -/
inductive Cmd
  | add (c : Tasks.Ctx) (a : AddArgs)
  | claim (c : Tasks.Ctx) (i : Int) (lease : String)
  | release (c : Tasks.Ctx) (i : Int) (after : Option (List Int))
  | board

/-- What a command answers. -/
inductive Result
  | added (r : Except String Nat)
  | claimed (r : Except String Claimed)
  | released (r : Except String (Option String))
  | board (tasks : List Task)

/-- A command's whole effect on the db, and its answer: the CLI's own step functions. -/
def Cmd.step : Cmd → Db → Db × Result
  | .add c a, db => ((Tasks.add c a db).1, .added (Tasks.add c a db).2)
  | .claim c i l, db => ((Tasks.claim c i l db).1, .claimed (Tasks.claim c i l db).2)
  | .release c i af, db => ((Tasks.release c i af db).1, .released (Tasks.release c i af db).2)
  | .board, db => (db, .board db.tasks)

/-- A task's owner fits its state: a claimed task has an owner, an open one has none. -/
def Task.Owned (t : Task) : Prop :=
  (t.state = .claimed → t.owner.isSome) ∧ (t.state = .open → t.owner = none)

/-- The store's invariant: task ids are unique and below the next id, and every task's owner fits its state. -/
def Inv (db : Db) : Prop :=
  (db.tasks.map (·.id)).Nodup ∧ (∀ t ∈ db.tasks, t.id < db.taskNext) ∧ ∀ t ∈ db.tasks, t.Owned

/-- The db after `cs` from the empty db. -/
def run (cs : List Cmd) : Db := (replay Cmd.step {} cs).1

/-- Each command of `cs`, from `db`, with its answer. -/
def trace (db : Db) (cs : List Cmd) : List (Cmd × Result) := (replay Cmd.step db cs).2

/-- Agent `a` owns task `i` in `db`. -/
def Owns (db : Db) (i : Int) (a : String) : Prop := ∃ t ∈ db.tasks, (t.id : Int) = i ∧ t.owner = some a

/-- A successful claim of task `i`. -/
def ClaimedOf (i : Int) : Cmd × Result → Bool
  | (.claim _ j _, .claimed (.ok _)) => j == i
  | _ => false

/-- A successful release of task `i`. -/
def ReleasedOf (i : Int) : Cmd × Result → Bool
  | (.release _ j _, .released (.ok _)) => j == i
  | _ => false

/-! Frame lemmas: what each part of a step leaves of the task table. -/

@[simp] theorem log_tasks (db : Db) ts a k p x : (db.log ts a k p x).tasks = db.tasks := rfl
@[simp] theorem log_next (db : Db) ts a k p x : (db.log ts a k p x).taskNext = db.taskNext := rfl
@[simp] theorem set_next (db : Db) i f : (db.set i f).taskNext = db.taskNext := rfl
@[simp] theorem post_tasks (db : Db) n f d b u k : (Msgs.post db n f d b u k).1.tasks = db.tasks := rfl
@[simp] theorem post_next (db : Db) n f d b u k : (Msgs.post db n f d b u k).1.taskNext = db.taskNext := rfl

theorem touch_frame (db : Db) n cwd here now :
    (Agents.touch db n cwd here now).tasks = db.tasks ∧ (Agents.touch db n cwd here now).taskNext = db.taskNext := by
  unfold Agents.touch Agents.newInbox
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

theorem find_congr {db db' : Db} (h : db'.tasks = db.tasks) (i : Int) : db'.find i = db.find i := by
  simp [Db.find, h]

theorem set_congr {db db' : Db} (h : db'.tasks = db.tasks) (i : Int) f : (db'.set i f).tasks = (db.set i f).tasks := by
  simp [Db.set, h]

theorem set_set (db : Db) (i : Int) (f g : Task → Task) (hf : ∀ t, (f t).id = t.id) :
    ((db.set i f).set i g).tasks = (db.set i (g ∘ f)).tasks := by
  simp only [Db.set, List.map_map]
  exact List.map_congr_left fun t _ => by by_cases h : (t.id : Int) = i <;> simp [h, hf]

theorem setDeps_ok {db db' : Db} {i : Int} {l : List Int} {ds : List String} (h : setDeps db i l = .ok (db', ds)) :
    ∃ f : Task → Task, (∀ t, (f t).id = t.id ∧ (f t).state = t.state ∧ (f t).owner = t.owner) ∧
      db'.tasks = (db.set i f).tasks ∧ db'.taskNext = db.taskNext := by
  unfold setDeps at h
  split at h
  · cases h
  · cases h; exact ⟨depsF _, fun _ => ⟨rfl, rfl, rfl⟩, rfl, rfl⟩

/-! What each step does to the task table. -/

theorem add_spec (c : Tasks.Ctx) (a : AddArgs) (db : Db) :
    ((Tasks.add c a db).1.tasks = db.tasks ∧ (Tasks.add c a db).1.taskNext = db.taskNext ∧
      ∀ x, (Tasks.add c a db).2 ≠ .ok x) ∨
    (∃ t : Task, (Tasks.add c a db).1.tasks = db.tasks ++ [t] ∧ t.id = db.taskNext ∧ t.state = .open ∧
      t.owner = none ∧ (Tasks.add c a db).1.taskNext = db.taskNext + 1) := by
  unfold Tasks.add
  split
  · exact .inl ⟨rfl, rfl, fun _ => nofun⟩
  · split
    · exact .inl ⟨rfl, rfl, fun _ => nofun⟩
    · split
      · exact .inl ⟨rfl, rfl, fun _ => nofun⟩
      · split
        · exact .inl ⟨rfl, rfl, fun _ => nofun⟩
        · exact .inr ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem claim_spec (c : Tasks.Ctx) (i : Int) (l : String) (db : Db) :
    (Tasks.claim c i l db).1.taskNext = db.taskNext ∧
    (((Tasks.claim c i l db).1.tasks = db.tasks ∧ ∀ x, (Tasks.claim c i l db).2 ≠ .ok x) ∨
     (∃ t g, db.find i = some t ∧ t.state = .open ∧
        (∀ u, (g u).id = u.id ∧ (g u).state = .claimed ∧ (g u).owner = some c.me) ∧
        (Tasks.claim c i l db).1.tasks = (db.set i g).tasks ∧ ∃ x, (Tasks.claim c i l db).2 = .ok x)) := by
  have ⟨tt, tn⟩ := touch_frame db c.me none c.here c.now
  unfold Tasks.claim
  split
  · exact ⟨rfl, .inl ⟨rfl, fun _ => nofun⟩⟩
  · split
    · exact ⟨rfl, .inl ⟨rfl, fun _ => nofun⟩⟩
    · dsimp only
      split
      · exact ⟨tn, .inl ⟨tt, fun _ => nofun⟩⟩
      · split
        · exact ⟨tn, .inl ⟨tt, fun _ => nofun⟩⟩
        · split
          · exact ⟨tn, .inl ⟨tt, fun _ => nofun⟩⟩
          · rename_i r1 h1
            split
            · exact ⟨tn, .inl ⟨tt, fun _ => nofun⟩⟩
            · split
              · rename_i hs
                refine ⟨by simp [tn], .inr ⟨r1, claimF c.me _ _ c.now, by rw [← find_congr tt]; exact h1, ?_,
                  fun _ => ⟨rfl, rfl, rfl⟩, set_congr tt i _, _, rfl⟩⟩
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hs; exact hs.1
              · split <;> exact ⟨tn, .inl ⟨tt, fun _ => nofun⟩⟩

theorem release_spec (c : Tasks.Ctx) (i : Int) (af : Option (List Int)) (db : Db) :
    (Tasks.release c i af db).1.taskNext = db.taskNext ∧
    (((Tasks.release c i af db).1.tasks = db.tasks ∧ ∀ x, (Tasks.release c i af db).2 ≠ .ok x) ∨
     (∃ g, (∀ u, (g u).id = u.id ∧ (g u).state = .open ∧ (g u).owner = none) ∧
        (Tasks.release c i af db).1.tasks = (db.set i g).tasks ∧ ∃ x, (Tasks.release c i af db).2 = .ok x)) := by
  unfold Tasks.release
  split
  · exact ⟨rfl, .inl ⟨rfl, fun _ => nofun⟩⟩
  · dsimp only
    split
    · exact ⟨rfl, .inl ⟨rfl, fun _ => nofun⟩⟩
    · rename_i db1 h1
      -- db1 is db with task i reopened by some g1
      have ⟨g1, hg1, e1⟩ : ∃ g1 : Task → Task, (∀ u, (g1 u).id = u.id ∧ (g1 u).state = .open ∧ (g1 u).owner = none) ∧
          db1 = db.set i g1 := by
        split at h1
        · split at h1
          · cases h1; exact ⟨reopenFromF, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩
          · cases h1
        · split at h1
          · cases h1; exact ⟨reopenF, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩
          · cases h1
      subst e1
      split
      · exact ⟨rfl, .inl ⟨rfl, fun _ => nofun⟩⟩
      · rename_i db2 h2
        -- db2 is db1 with task i's deps set, or db1
        have ⟨g2, hg2, e2, n2⟩ : ∃ g2 : Task → Task, (∀ u, (g2 u).id = u.id ∧ (g2 u).state = u.state ∧ (g2 u).owner = u.owner) ∧
            db2.tasks = ((db.set i g1).set i g2).tasks ∧ db2.taskNext = db.taskNext := by
          split at h2
          · cases h' : setDeps (db.set i g1) i _ with
            | error e => rw [h'] at h2; cases h2
            | ok p =>
              rw [h'] at h2; cases h2
              obtain ⟨f, hf, e, n⟩ := setDeps_ok h'
              exact ⟨f, hf, e, n⟩
          · cases h2; exact ⟨id, fun _ => ⟨rfl, rfl, rfl⟩, by simp [Db.set], rfl⟩
        have e12 : db2.tasks = (db.set i (g2 ∘ g1)).tasks := by rw [e2, set_set _ _ _ _ fun u => (hg1 u).1]
        split
        · refine ⟨by simp [n2], .inr ⟨_ ∘ (g2 ∘ g1), fun u => ?_,
            (set_congr (db := db.set i (g2 ∘ g1)) (by simp [e12]) i _).trans
              (set_set db i (g2 ∘ g1) _ fun u => by simp [Function.comp, (hg2 _).1, (hg1 u).1]), _, rfl⟩⟩
          simp [(hg2 _).1, (hg2 _).2.1, (hg2 _).2.2, (hg1 u).1, (hg1 u).2.1, (hg1 u).2.2]
        · refine ⟨by simp [n2], .inr ⟨g2 ∘ g1, fun u => ?_, by simp [e12], _, rfl⟩⟩
          simp [(hg2 _).1, (hg2 _).2.1, (hg2 _).2.2, (hg1 u).1, (hg1 u).2.1, (hg1 u).2.2]

/-! The invariant. -/

theorem inv_empty : Inv {} := by simp [Inv]

theorem inv_congr {db db' : Db} (ht : db'.tasks = db.tasks) (hn : db'.taskNext = db.taskNext) (h : Inv db) :
    Inv db' := by
  unfold Inv; rw [ht, hn]; exact h

theorem set_tasks_ids (db : Db) (i : Int) (f : Task → Task) (hf : ∀ t, (f t).id = t.id) :
    (db.set i f).tasks.map (·.id) = db.tasks.map (·.id) := by
  simp only [Db.set, List.map_map]
  exact List.map_congr_left fun t _ => by by_cases h : (t.id : Int) = i <;> simp [h, hf]

theorem set_inv (db : Db) (i : Int) (f : Task → Task) (hf : ∀ t, (f t).id = t.id) (ho : ∀ t, (f t).Owned)
    (h : Inv db) : Inv (db.set i f) := by
  obtain ⟨hn, hb, hw⟩ := h
  refine ⟨set_tasks_ids db i f hf ▸ hn, ?_, ?_⟩ <;> intro t' ht' <;>
    simp only [Db.set, List.mem_map] at ht' <;> obtain ⟨t, ht, rfl⟩ := ht' <;>
    by_cases e : (t.id : Int) = i <;> simp [e, hf, ho, hw t ht] <;> simpa [Db.set, e] using hb t ht

/-- A set of task `i` to `g`, where `g` keeps ids and gives an owner that fits, keeps the invariant. -/
theorem set_spec_inv {db db' : Db} {i : Int} {g : Task → Task} (hg : ∀ u, (g u).id = u.id ∧ (g u).Owned)
    (ht : db'.tasks = (db.set i g).tasks) (hn : db'.taskNext = db.taskNext) (h : Inv db) : Inv db' :=
  inv_congr ht hn (set_inv db i g (fun u => (hg u).1) (fun u => (hg u).2) h)

theorem step_inv (c : Cmd) (db : Db) (h : Inv db) : Inv (c.step db).1 := by
  cases c with
  | add c a =>
    rcases add_spec c a db with ⟨ht, hn, -⟩ | ⟨t, ht, hid, hs, ho, hn⟩
    · exact inv_congr ht hn h
    · obtain ⟨hnd, hb, hw⟩ := h
      show Inv (Tasks.add c a db).1
      unfold Inv; rw [ht, hn]
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        exact List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩,
          fun x hx y hy => by
            simp at hy; subst hy; obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx; rw [hid]; exact Nat.ne_of_lt (hb u hu)⟩
      · intro u hu; simp at hu; rcases hu with hu | rfl
        · exact Nat.lt_succ_of_lt (hb u hu)
        · rw [hid]; exact Nat.lt_succ_self _
      · intro u hu; simp at hu; rcases hu with hu | rfl
        · exact hw u hu
        · exact ⟨fun e => (by rw [hs] at e; cases e), fun _ => ho⟩
  | claim c i l =>
    obtain ⟨hn, hs⟩ := claim_spec c i l db
    rcases hs with ⟨ht, -⟩ | ⟨-, g, -, -, hg, ht, -⟩
    · exact inv_congr ht hn h
    · refine set_spec_inv (fun u => ⟨(hg u).1, ?_⟩) ht hn h
      unfold Task.Owned; rw [(hg u).2.1, (hg u).2.2]; exact ⟨fun _ => rfl, fun e => by cases e⟩
  | release c i af =>
    obtain ⟨hn, hs⟩ := release_spec c i af db
    rcases hs with ⟨ht, -⟩ | ⟨g, hg, ht, -⟩
    · exact inv_congr ht hn h
    · refine set_spec_inv (fun u => ⟨(hg u).1, ?_⟩) ht hn h
      unfold Task.Owned; rw [(hg u).2.1, (hg u).2.2]; exact ⟨fun e => (by cases e), fun _ => rfl⟩
  | board => exact h

theorem replay_inv (db : Db) (cs : List Cmd) (h : Inv db) : Inv (replay Cmd.step db cs).1 := by
  induction cs generalizing db with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_inv c db h)

/-- The invariant holds after any commands by any agents from the empty db. -/
theorem run_inv (cs : List Cmd) : Inv (run cs) := replay_inv _ cs inv_empty

theorem nodup_inj {l : List Task} (h : (l.map (·.id)).Nodup) {x y : Task} (hx : x ∈ l) (hy : y ∈ l)
    (e : x.id = y.id) : x = y := by
  induction l with
  | nil => cases hx
  | cons t l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd ⟨y, hy', e.symm⟩ h.1
    · exact absurd ⟨x, hx', e⟩ h.1
    · exact ih h.2 hx' hy'

/-- No task has two owners, after any commands by any agents in any order from the empty db. -/
theorem one_owner (cs : List Cmd) (i : Int) (a b : String) (ha : Owns (run cs) i a) (hb : Owns (run cs) i b) :
    a = b := by
  obtain ⟨t, ht, e1, hta⟩ := ha
  obtain ⟨t', ht', e2, htb⟩ := hb
  have := nodup_inj (run_inv cs).1 ht ht' (by omega)
  subst this; simpa [hta] using htb

/-! One claim wins. -/

/-- Task `i` is claimed in `db`. -/
def Held (db : Db) (i : Int) : Prop := ∃ t, db.find i = some t ∧ t.state = .claimed

theorem find_set (db : Db) (i j : Int) (f : Task → Task) (hf : ∀ t, (f t).id = t.id) :
    (db.set j f).find i = (db.find i).map fun t => if (t.id : Int) = j then f t else t := by
  simp only [Db.find, Db.set, List.find?_map]
  congr 2; funext t; by_cases h : (t.id : Int) = j <;> simp [h, hf]

theorem find_id {db : Db} {i : Int} {t : Task} (h : db.find i = some t) : (t.id : Int) = i := by
  simpa using List.find?_some h

theorem held_set {db db' : Db} {i j : Int} {g : Task → Task} (hg : ∀ u, (g u).id = u.id) (hij : j ≠ i)
    (ht : db'.tasks = (db.set j g).tasks) (h : Held db i) : Held db' i := by
  obtain ⟨t, hf, hs⟩ := h
  refine ⟨t, ?_, hs⟩
  rw [find_congr ht, find_set _ _ _ _ hg, hf]
  simp [find_id hf, Ne.symm hij]

/-- A claim answered with success leaves its task claimed. -/
theorem claimed_held (c : Tasks.Ctx) (i : Int) (l : String) (db : Db) (x : Claimed)
    (h : (Tasks.claim c i l db).2 = .ok x) : Held (Tasks.claim c i l db).1 i := by
  obtain ⟨-, ⟨-, hne⟩ | ⟨t, g, hf, -, hg, ht, -⟩⟩ := claim_spec c i l db
  · exact absurd h (hne x)
  · refine ⟨g t, ?_, (hg t).2.1⟩
    rw [find_congr ht, find_set _ _ _ _ fun u => (hg u).1, hf]
    simp [find_id hf]

/-- From a db where task `i` is claimed, a command other than its successful release keeps it claimed and is not a
successful claim of it. -/
theorem held_step (db : Db) (i : Int) (c : Cmd) (h : Held db i) (hr : ReleasedOf i (c, (c.step db).2) = false) :
    Held (c.step db).1 i ∧ ClaimedOf i (c, (c.step db).2) = false := by
  cases c with
  | add c a =>
    refine ⟨?_, rfl⟩
    show Held (Tasks.add c a db).1 i
    rcases add_spec c a db with ⟨ht, -, -⟩ | ⟨t, ht, -⟩
    · obtain ⟨u, hf, hs⟩ := h; exact ⟨u, by rw [find_congr ht]; exact hf, hs⟩
    · obtain ⟨u, hf, hs⟩ := h
      refine ⟨u, ?_, hs⟩
      simp only [Db.find] at hf ⊢; rw [ht, List.find?_append, hf]; rfl
  | claim c j l =>
    obtain ⟨-, hs⟩ := claim_spec c j l db
    rcases hs with ⟨ht, hne⟩ | ⟨t, g, hf, ho, hg, ht, x, hx⟩
    · refine ⟨?_, ?_⟩
      · show Held (Tasks.claim c j l db).1 i
        obtain ⟨u, hu, hs⟩ := h; exact ⟨u, by rw [find_congr ht]; exact hu, hs⟩
      · show ClaimedOf i (.claim c j l, .claimed (Tasks.claim c j l db).2) = false
        cases e : (Tasks.claim c j l db).2 with
        | error _ => rfl
        | ok x => exact absurd e (hne x)
    · have hij : j ≠ i := fun e => by
        subst e; obtain ⟨u, hu, hs⟩ := h; rw [hf] at hu; cases hu; rw [hs] at ho; cases ho
      refine ⟨(held_set (fun u => (hg u).1) hij ht h : Held (Tasks.claim c j l db).1 i), ?_⟩
      show ClaimedOf i (.claim c j l, .claimed (Tasks.claim c j l db).2) = false
      rw [hx]; simp [ClaimedOf, hij]
  | release c j af =>
    refine ⟨?_, rfl⟩
    show Held (Tasks.release c j af db).1 i
    obtain ⟨-, hs⟩ := release_spec c j af db
    rcases hs with ⟨ht, -⟩ | ⟨g, hg, ht, x, hx⟩
    · obtain ⟨u, hu, hs⟩ := h; exact ⟨u, by rw [find_congr ht]; exact hu, hs⟩
    · have hij : j ≠ i := fun e => by
        subst e
        have hs : ((Cmd.release c j af).step db).2 = .released (.ok x) := by simp only [Cmd.step, hx]
        rw [hs] at hr; simp [ReleasedOf] at hr
      exact held_set (fun u => (hg u).1) hij ht h
  | board => exact ⟨h, rfl⟩

theorem trace_cons (db : Db) (c : Cmd) (cs : List Cmd) :
    trace db (c :: cs) = (c, (c.step db).2) :: trace (c.step db).1 cs := rfl

theorem claimedOf_true {i : Int} {c : Cmd} {r : Result} (h : ClaimedOf i (c, r) = true) :
    ∃ cc l x, c = .claim cc i l ∧ r = .claimed (.ok x) := by
  cases c with
  | claim cc j l =>
    cases r with
    | claimed e =>
      cases e with
      | ok x => simp only [ClaimedOf, beq_iff_eq] at h; subst h; exact ⟨cc, l, x, rfl, rfl⟩
      | error _ => simp [ClaimedOf] at h
    | _ => simp [ClaimedOf] at h
  | _ => simp [ClaimedOf] at h

/-- A successful claim's step is a successful `Tasks.claim`. -/
theorem claimed_step {db : Db} {cc : Tasks.Ctx} {i : Int} {l : String} {x : Claimed}
    (h : ((Cmd.claim cc i l).step db).2 = .claimed (.ok x)) : (Tasks.claim cc i l db).2 = .ok x := by
  simp only [Cmd.step, Result.claimed.injEq] at h; exact h

/-- From a db where task `i` is claimed, a later successful claim of it comes after a successful release of it. -/
theorem held_claimed (db : Db) (i : Int) (cs : List Cmd) (h : Held db i) (t2 t3 : List (Cmd × Result)) (b : Cmd × Result)
    (hb : ClaimedOf i b = true) (e : trace db cs = t2 ++ b :: t3) : ∃ x ∈ t2, ReleasedOf i x := by
  induction cs generalizing db t2 with
  | nil => cases t2 <;> simp [trace, replay] at e
  | cons c cs ih =>
    rw [trace_cons] at e
    cases t2 with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at e
      obtain ⟨rfl, -⟩ := e
      obtain ⟨cc, l, x, rfl, hx⟩ := claimedOf_true hb
      have := (held_step db i (.claim cc i l) h (by simp [ReleasedOf, Cmd.step])).2
      rw [hb] at this; cases this
    | cons x t2 =>
      simp only [List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      by_cases hr : ReleasedOf i (c, (c.step db).2)
      · exact ⟨_, List.mem_cons_self .., hr⟩
      · obtain ⟨y, hy, hy'⟩ := ih _ (held_step db i c h (by simpa using hr)).1 t2 e
        exact ⟨y, List.mem_cons_of_mem _ hy, hy'⟩

/-- Of any commands by any agents from any db, two successful claims of one task have a successful release of it
between them: a claim succeeds for at most one agent until the task is released. -/
theorem claimed_once (db : Db) (cs : List Cmd) (i : Int) (a b : Cmd × Result) (ha : ClaimedOf i a = true)
    (hb : ClaimedOf i b = true) (t1 t2 t3 : List (Cmd × Result)) (e : trace db cs = t1 ++ a :: t2 ++ b :: t3) :
    ∃ x ∈ t2, ReleasedOf i x := by
  induction cs generalizing db t1 with
  | nil => cases t1 <;> simp [trace, replay] at e
  | cons c cs ih =>
    rw [trace_cons] at e
    cases t1 with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
      obtain ⟨rfl, e⟩ := e
      obtain ⟨cc, l, x, rfl, hx⟩ := claimedOf_true ha
      exact held_claimed _ i cs (claimed_held cc i l db x (claimed_step hx)) t2 t3 b hb e
    | cons y t1 =>
      simp only [List.cons_append, List.append_assoc, List.cons.injEq] at e
      exact ih _ t1 (by simpa using e.2)

/-- From a db where task `i` is claimed, with no successful release of it, no command successfully claims it. -/
theorem claims_held (db : Db) (i : Int) (cs : List Cmd) (h : Held db i)
    (hr : ∀ x ∈ trace db cs, ReleasedOf i x = false) : (trace db cs).filter (ClaimedOf i) = [] := by
  induction cs generalizing db with
  | nil => rfl
  | cons c cs ih =>
    rw [trace_cons] at hr ⊢
    have ⟨h', hc⟩ := held_step db i c h (hr _ (List.mem_cons_self ..))
    simp only [List.filter_cons, hc, Bool.false_eq_true, ↓reduceIte]
    exact ih _ h' fun x hx => hr x (List.mem_cons_of_mem _ hx)

/-- With no successful release of task `i` among them, at most one of the commands from `db` successfully claims it. -/
theorem claims_le (db : Db) (i : Int) (cs : List Cmd) (hr : ∀ x ∈ trace db cs, ReleasedOf i x = false) :
    ((trace db cs).filter (ClaimedOf i)).length ≤ 1 := by
  induction cs generalizing db with
  | nil => simp [trace, replay]
  | cons c cs ih =>
    rw [trace_cons] at hr ⊢
    have hr' := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    cases hcl : ClaimedOf i (c, (c.step db).2)
    · simp only [List.filter_cons, hcl, Bool.false_eq_true, ↓reduceIte]; exact ih _ hr'
    · obtain ⟨cc, l, x, rfl, hx⟩ := claimedOf_true hcl
      have e := claims_held _ i cs (claimed_held cc i l db x (claimed_step hx)) hr'
      rw [List.filter_cons_of_pos hcl]
      show (_ :: List.filter (ClaimedOf i) (trace (Tasks.claim cc i l db).1 cs)).length ≤ 1
      rw [e]; simp

/-- Under the store's assumption (`Atomic`), when processes ran commands at once with no successful release of task
`i` among them, at most one of them successfully claimed it. -/
theorem one_winner (before after : Db) (ran : List (Cmd × Result)) (i : Int) (h : Atomic Cmd.step before after ran)
    (hr : ∀ x ∈ ran, ReleasedOf i x = false) : (ran.filter (ClaimedOf i)).length ≤ 1 := by
  obtain ⟨order, hp, e⟩ := h
  have ht : trace before (order.map (·.1)) = order := congrArg Prod.snd e
  rw [← (hp.filter _).length_eq, ← ht]
  exact claims_le before i _ (by rw [ht]; exact fun x hx => hr x (hp.mem_iff.1 hx))

/-- Under the store's assumption, when every process ran `task claim i` (as any agent, any lease) and each claim
would have succeeded alone on the store as it was, exactly one succeeded: what `test-claim.sh` checks of the real
store. -/
theorem exactly_one_winner (before after : Db) (ran : List (Cmd × Result)) (i : Int)
    (h : Atomic Cmd.step before after ran)
    (hc : ∀ x ∈ ran, ∃ cc l, x.1 = .claim cc i l ∧ ∃ y, (Tasks.claim cc i l before).2 = .ok y)
    (hn : ran ≠ []) : (ran.filter (ClaimedOf i)).length = 1 := by
  refine Nat.le_antisymm (one_winner before after ran i h fun x hx => ?_) ?_
  · obtain ⟨cc, l, hx1, -⟩ := hc x hx; obtain ⟨c, r⟩ := x; simp only at hx1; subst hx1; rfl
  · obtain ⟨order, hp, e⟩ := h
    have ht : trace before (order.map (·.1)) = order := congrArg Prod.snd e
    obtain ⟨x, xs, rfl⟩ : ∃ x xs, order = x :: xs := by
      cases order with
      | nil => exact absurd (List.Perm.nil_eq hp).symm hn
      | cons x xs => exact ⟨x, xs, rfl⟩
    obtain ⟨cc, l, ha, y, hy⟩ := hc x (hp.mem_iff.1 (List.mem_cons_self ..))
    rw [← (hp.filter _).length_eq, ← ht, List.map_cons, ha, trace_cons]
    simp [Cmd.step, hy, ClaimedOf]

end SwarmLean
