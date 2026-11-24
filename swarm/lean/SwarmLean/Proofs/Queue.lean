import SwarmLean.Proofs.Tasks
import SwarmLean.Db.Queue

/-! Board #128 with Linear's states: the places, Ready and Backlog, and staffing, proved of the real steps
(Db/Queue.lean's `setQueue`, `toEnd`, `add`, `rm`, `backlog`, `ready`, `assign`, `tidy`, `done`, `drop`,
`staffing`, `staffHead`), the functions Cmd/Tasks.lean runs in `Store.txn`. Every place move keeps the tasks' places
distinct and changes nothing but the places (and the events it logs); `task assign` changes no place; only a Ready task
no one is assigned is staffed; with no task reserved, the staffing order is the pool's. The staffing theorem itself,
about auto-spawn's reservation, is `WatchdProofs.reserveTask_top`. -/

namespace SwarmLean.QueueProofs
open Tasks Queue

/-! The places. -/

/-- `db` with no task placed: everything a place move must leave as it was (but the events it logs). -/
def unplaced (db : Db) : Db := { db with tasks := db.tasks.map fun t => { t with pos := none } }

theorem mem_dedup {a : Int} : ∀ {l : List Int}, a ∈ dedup l ↔ a ∈ l
  | [] => by simp [dedup]
  | x :: xs => by
    simp only [dedup, List.mem_cons, List.mem_filter, mem_dedup, bne_iff_ne, ne_eq]
    by_cases h : a = x <;> simp [h]

theorem nodup_dedup : ∀ l : List Int, (dedup l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    simp only [dedup]
    refine List.nodup_cons.2 ⟨by simp, ?_⟩
    exact (List.pairwise_filter.2 ((nodup_dedup xs).imp fun h _ _ => h))

/-- The first places in `l` of distinct ids, `l` of distinct ids among them, are `0..|l|-1`. -/
theorem idxOf_perm {ids l : List Int} (hi : ids.Nodup) (hl : l.Nodup) (hs : ∀ x ∈ l, x ∈ ids) :
    (ids.filterMap (l.idxOf? ·)).Perm (List.range l.length) := by
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun n => ?_
  · refine List.pairwise_filterMap.2 (hi.imp fun hab x hx y hy hxy => ?_)
    subst hxy
    obtain ⟨_, e1, -⟩ := List.idxOf?_eq_some_iff.1 hx
    obtain ⟨_, e2, -⟩ := List.idxOf?_eq_some_iff.1 hy
    exact hab (e1.symm.trans e2)
  · simp only [List.mem_filterMap, List.mem_range]
    constructor
    · rintro ⟨a, -, ha⟩
      obtain ⟨h, -, -⟩ := List.idxOf?_eq_some_iff.1 ha
      exact h
    · intro hn
      refine ⟨l[n], hs _ (List.getElem_mem hn), List.idxOf?_eq_some_iff.2 ⟨hn, rfl, fun j hj e => ?_⟩⟩
      have := (List.Nodup.getElem_inj hl).mp e
      omega

theorem places_setQueue (db : Db) (l : List Int) :
    places (setQueue db l) = ((db.tasks.map fun t => (t.id : Int)).filterMap
      ((dedup (l.filter fun i => (db.find i).isSome)).idxOf? ·)).map fun (i : Nat) => (i : Int) + 1 := by
  simp only [places, setQueue, List.filterMap_map, List.map_filterMap]
  rfl

/-- `setQueue` gives the tasks it places the places 1..n, each once. -/
theorem setQueue_perm (db : Db) (l : List Int) (hi : (db.tasks.map (·.id)).Nodup) :
    ∃ n, (places (setQueue db l)).Perm ((List.range n).map fun (i : Nat) => (i : Int) + 1) := by
  refine ⟨(dedup (l.filter fun i => (db.find i).isSome)).length, ?_⟩
  rw [places_setQueue]
  refine (idxOf_perm ?_ (nodup_dedup _) fun x hx => ?_).map _
  · rw [List.Nodup, List.pairwise_map]
    have := List.pairwise_map.1 hi
    exact this.imp fun h e => h (by omega)
  · obtain ⟨-, hx⟩ := List.mem_filter.1 (mem_dedup.1 hx)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hx
    exact List.mem_map.2 ⟨t, Board.find_mem ht, find_id ht⟩

/-- So its places are distinct and positive. -/
theorem setQueue_qinv (db : Db) (l : List Int) (hi : (db.tasks.map (·.id)).Nodup) : QInv (setQueue db l) := by
  obtain ⟨n, hp⟩ := setQueue_perm db l hi
  refine ⟨hp.nodup_iff.2 ?_, fun p h => ?_⟩
  · rw [List.Nodup, List.pairwise_map]
    exact List.Pairwise.imp (fun h e => h (by omega)) (List.nodup_range ..)
  · obtain ⟨k, -, rfl⟩ := List.mem_map.1 (hp.mem_iff.1 h)
    omega

/-- `setQueue` changes the places only. -/
theorem setQueue_frame (db : Db) (l : List Int) : unplaced (setQueue db l) = unplaced db := by
  simp only [unplaced, setQueue, List.map_map]
  rfl

theorem setQueue_ids (db : Db) (l : List Int) : (setQueue db l).tasks.map (·.id) = db.tasks.map (·.id) := by
  simp only [setQueue, List.map_map]; rfl

/-- The tasks' places after a map that only takes places or keeps them are distinct if they were. -/
theorem nodup_places_map (ts : List Task) (g : Task → Task) (hg : ∀ t x, (g t).pos = some x → t.pos = some x)
    (hq : (ts.filterMap (·.pos)).Nodup) : ((ts.map g).filterMap (·.pos)).Nodup := by
  rw [List.filterMap_map]
  unfold List.Nodup at *
  rw [List.pairwise_filterMap] at hq ⊢
  exact hq.imp fun h x hx y hy => h x (hg _ _ hx) y (hg _ _ hy)

/-- Setting task `i`'s place to `e`, a place no task holds, keeps the places distinct (ids unique). -/
theorem places_setPos (ts : List Task) (i e : Int) (hi : (ts.map (·.id)).Nodup) (hq : (ts.filterMap (·.pos)).Nodup)
    (he : ∀ t ∈ ts, t.pos ≠ some e) :
    ((ts.map fun t => if (t.id : Int) = i then { t with pos := some e } else t).filterMap (·.pos)).Nodup := by
  rw [List.filterMap_map]
  unfold List.Nodup at *
  rw [List.pairwise_filterMap] at hq ⊢
  rw [List.pairwise_map] at hi
  refine (hi.and hq).imp_of_mem fun {a b} _ hb hab x hx y hy hxy => ?_
  obtain ⟨hid, hp⟩ := hab
  subst hxy
  simp only [Function.comp_apply, Option.mem_def] at hx hy
  by_cases hai : (a.id : Int) = i <;> by_cases hbi : (b.id : Int) = i <;>
    simp only [hai, hbi, ↓reduceIte] at hx hy
  · exact hid (by omega)
  · exact he b hb (by rw [hy]; exact hx.symm)
  · exact he _ ‹a ∈ ts› (by rw [hx]; exact hy.symm)
  · exact hp x hx x hy rfl

/-- A map that only takes places or keeps them keeps them positive. -/
theorem pos_places_map (ts : List Task) (g : Task → Task) (hg : ∀ t x, (g t).pos = some x → t.pos = some x)
    (hq : ∀ p ∈ ts.filterMap (·.pos), 0 < p) : ∀ p ∈ (ts.map g).filterMap (·.pos), 0 < p := by
  intro p hp
  rw [List.filterMap_map, List.mem_filterMap] at hp
  obtain ⟨t, ht, e⟩ := hp
  exact hq p (List.mem_filterMap.2 ⟨t, ht, hg t p e⟩)

/-- Setting task `i`'s place to a positive `e` keeps the places positive. -/
theorem pos_setPos (ts : List Task) (i e : Int) (he : 0 < e) (hq : ∀ p ∈ ts.filterMap (·.pos), 0 < p) :
    ∀ p ∈ (ts.map fun t => if (t.id : Int) = i then { t with pos := some e } else t).filterMap (·.pos), 0 < p := by
  intro p hp
  rw [List.filterMap_map, List.mem_filterMap] at hp
  obtain ⟨t, ht, h⟩ := hp
  simp only [Function.comp_apply] at h
  split at h
  · cases h; exact he
  · exact hq p (List.mem_filterMap.2 ⟨t, ht, h⟩)

theorem le_foldl_max : ∀ (l : List Int) (a : Int), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => ⟨Int.le_refl a, by simp⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max a y)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨Int.le_trans (Int.le_max_left a y) h1, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact Int.le_trans (Int.le_max_right a x) h1
    · exact h2 x hx

/-- `endPos` is a place no task holds: past every place. -/
theorem endPos_fresh (db : Db) : ∀ t ∈ db.tasks, t.pos ≠ some (endPos db) := by
  intro t ht hp
  have hm : endPos db ∈ db.tasks.filterMap (·.pos) := List.mem_filterMap.2 ⟨t, ht, hp⟩
  have := (le_foldl_max (db.tasks.filterMap (·.pos)) 0).2 _ hm
  unfold endPos at this
  omega

/-- `endPos` is positive. -/
theorem endPos_pos (db : Db) : 0 < endPos db := by
  have := (le_foldl_max (db.tasks.filterMap (·.pos)) 0).1
  unfold endPos; omega

theorem toEnd_ids (i : Int) (db : Db) : (toEnd i db).tasks.map (·.id) = db.tasks.map (·.id) :=
  set_tasks_ids _ _ _ fun _ => rfl

/-- `toEnd` keeps the places distinct and positive. -/
theorem toEnd_qinv (i : Int) (db : Db) (hi : (db.tasks.map (·.id)).Nodup) (hq : QInv db) : QInv (toEnd i db) :=
  ⟨places_setPos db.tasks i (endPos db) hi hq.1 (endPos_fresh db), pos_setPos db.tasks i (endPos db) (endPos_pos db) hq.2⟩

/-- A step that changes tasks only by `db.set` of fields other than the place keeps the places. -/
theorem places_set (db : Db) (i : Int) (f : Task → Task) (hf : ∀ t, (f t).pos = t.pos) :
    places (db.set i f) = places db := by
  simp only [places, Db.set, List.filterMap_map]
  congr 1; funext t; simp only [Function.comp]; split <;> simp [hf]

/-! Ids unique and places distinct, kept by each step of a place move. -/

/-- Ids unique and places distinct. -/
def P (db : Db) : Prop := (db.tasks.map (·.id)).Nodup ∧ QInv db

theorem p_foldl {β : Type} (f : Db → β → Db) (hf : ∀ db b, P db → P (f db b)) :
    ∀ (l : List β) (db : Db), P db → P (l.foldl f db)
  | [], _, h => h
  | b :: bs, db, h => p_foldl f hf bs _ (hf db b h)

theorem p_log (db : Db) ts a k p x (h : P db) : P (db.log ts a k p x) := h

theorem p_toEnd (i : Int) (db : Db) (h : P db) : P (toEnd i db) :=
  ⟨by rw [toEnd_ids]; exact h.1, toEnd_qinv i db h.1 h.2⟩

theorem p_set (db : Db) (i : Int) (f : Task → Task) (hid : ∀ t, (f t).id = t.id) (hf : ∀ t, (f t).pos = t.pos)
    (h : P db) : P (db.set i f) :=
  ⟨by rw [set_tasks_ids _ _ _ hid]; exact h.1, by unfold QInv; rw [places_set _ _ _ hf]; exact h.2⟩

theorem p_inChargeStep (c : Ctx) (what kind data : String) (f : Db → Db) (db : Db) (hf : P (f db)) (h : P db) :
    P (inChargeStep c what kind data f db).1 := by
  unfold inChargeStep; dsimp only; split
  · exact p_log _ _ _ _ _ _ hf
  · exact p_log _ _ _ _ _ _ h

/-! Frames: a place move changes nothing but the places and the events it logs. -/

/-- `db'` is `db` with other places and some events appended. -/
def Moved (db db' : Db) : Prop := { unplaced db' with events := db.events, eventNext := db.eventNext } = unplaced db

theorem moved_refl (db : Db) : Moved db db := rfl

theorem moved_trans {a b c : Db} (h1 : Moved a b) (h2 : Moved b c) : Moved a c := by
  unfold Moved at *; rw [← h2] at h1; exact h1

theorem moved_log (db : Db) ts a k p x : Moved db (db.log ts a k p x) := rfl

theorem moved_foldl {β : Type} (f : Db → β → Db) (hf : ∀ db b, Moved db (f db b)) :
    ∀ (l : List β) (db : Db), Moved db (l.foldl f db)
  | [], db => moved_refl db
  | b :: bs, db => moved_trans (hf db b) (moved_foldl f hf bs _)

theorem unplaced_set (db : Db) (i : Int) (f : Task → Task) (hf : ∀ t, { f t with pos := none } = { t with pos := none }) :
    unplaced (db.set i f) = unplaced db := by
  simp only [unplaced, Db.set, List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => by simp only [Function.comp]; split; exact hf t; rfl

theorem moved_toEnd (i : Int) (db : Db) : Moved db (toEnd i db) := by
  unfold Moved toEnd; dsimp only; rw [unplaced_set db i (fun x => { x with pos := some (endPos db) }) fun _ => rfl]; rfl

theorem moved_setQueue (db : Db) (l : List Int) : Moved db (setQueue db l) := by
  unfold Moved; rw [setQueue_frame]; rfl

/-! `queue add` and `queue rm`. -/

theorem add_p (c : Ctx) (ids : List Int) (w : Place) (db : Db) (h : P db) : P (Queue.add c ids w db).1 := by
  unfold Queue.add
  split
  · exact h
  · dsimp only
    refine p_foldl _ (fun db _ h => p_log db _ _ _ _ _ h) _ _ ?_
    split
    · exact p_foldl _ (fun db i h => p_toEnd i db h) _ _ h
    · exact ⟨by rw [setQueue_ids]; exact h.1, setQueue_qinv _ _ h.1⟩

theorem add_moved (c : Ctx) (ids : List Int) (w : Place) (db : Db) : Moved db (Queue.add c ids w db).1 := by
  unfold Queue.add
  split
  · exact moved_refl _
  · dsimp only
    refine moved_trans ?_ (moved_foldl _ (fun db _ => moved_log db _ _ _ _ _) _ _)
    split
    · exact moved_foldl _ (fun db i => moved_toEnd i db) _ _
    · exact moved_setQueue _ _

/-- Place moves (`queue add`, `queue rm`, `task backlog`, `task ready`, and `tidy`, which `task done`/`task drop`
end with) keep the tasks' places distinct. -/
theorem add_qinv (c : Ctx) (ids : List Int) (w : Place) (db : Db) (hi : Inv db) (hq : QInv db) :
    QInv (Queue.add c ids w db).1 := (add_p c ids w db ⟨hi.1, hq⟩).2

theorem rm_qinv (c : Ctx) (ids : List Int) (db : Db) (hi : Inv db) (hq : QInv db) : QInv (Queue.rm c ids db).1 :=
  add_qinv c ids .back db hi hq

/-- `queue add` and `queue rm` change nothing but the places and the events they log. -/
theorem add_frame (c : Ctx) (ids : List Int) (w : Place) (db : Db) :
    { unplaced (Queue.add c ids w db).1 with events := db.events, eventNext := db.eventNext } = unplaced db :=
  add_moved c ids w db

theorem rm_frame (c : Ctx) (ids : List Int) (db : Db) :
    { unplaced (Queue.rm c ids db).1 with events := db.events, eventNext := db.eventNext } = unplaced db :=
  add_moved c ids .back db

/-! `task backlog`, `task ready`, `task assign`. -/

theorem backlog_qinv (c : Ctx) (i : Int) (note : String) (db : Db) (hi : Inv db) (hq : QInv db) :
    QInv (Queue.backlog c i note db).1 := by
  have h : P db := ⟨hi.1, hq⟩
  unfold Queue.backlog
  split
  · exact hq
  · dsimp only
    split
    · exact hq
    · split
      · exact hq
      · refine (p_log _ _ _ _ _ _ ?_).2
        split
        · exact p_toEnd _ _ (p_set _ _ _ (fun _ => rfl) (fun _ => rfl) h)
        · exact p_set _ _ _ (fun _ => rfl) (fun _ => rfl) h

theorem ready_qinv (c : Ctx) (i : Int) (db : Db) (hi : Inv db) (hq : QInv db) : QInv (Queue.ready c i db).1 := by
  have h : P db := ⟨hi.1, hq⟩
  unfold Queue.ready
  split
  · exact hq
  · try dsimp only
    split
    · exact hq
    · exact (p_inChargeStep _ _ _ _ _ _ (by exact p_toEnd _ _ (p_set _ _ _ (fun _ => rfl) (fun _ => rfl) h)) h).2

/-- `task assign` changes the task's assignee and nothing of the places. -/
theorem assign_places (c : Ctx) (i : Int) (who : Option String) (db : Db) :
    places (Queue.assign c i who db).1 = places db := by
  unfold Queue.assign
  split
  · rfl
  · dsimp only
    split
    · rfl
    · unfold inChargeStep; dsimp only; split
      · exact places_set _ _ _ fun _ => rfl
      · rfl

/-! `tidy`, `task done`, `task drop`. -/

/-- `tidy` keeps the places distinct and positive. It takes places without renumbering, so it needs them distinct
before: two open tasks on one place stay so. -/
theorem tidy_qinv (db : Db) (hq : QInv db) : QInv (tidy db) :=
  ⟨nodup_places_map db.tasks _ (fun t x h => by split at h <;> simp_all) hq.1,
    pos_places_map db.tasks _ (fun t x h => by split at h <;> simp_all) hq.2⟩

/-- `task add` gives the new task the end place, so the places stay distinct and positive. -/
theorem tasks_add_qinv (c : Ctx) (a : AddArgs) (db : Db) (hq : QInv db) : QInv (Tasks.add c a db).1 := by
  have hpl : ∀ t : Task, t.pos = some (endPos db) →
      places { db with tasks := db.tasks ++ [t], taskNext := db.taskNext + 1 } = places db ++ [endPos db] := by
    intro t ht; simp [places, List.filterMap_append, ht]
  unfold Tasks.add
  repeat' split
  all_goals first
    | exact hq
    | (show QInv ({ db with tasks := db.tasks ++ [_], taskNext := db.taskNext + 1 }.log _ _ _ _ _)
       unfold QInv; rw [show ∀ d : Db, places (d.log _ _ _ _ _) = places d from fun _ => rfl, hpl _ rfl]
       refine ⟨List.nodup_append.2 ⟨hq.1, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun x hx y hy e => ?_⟩, fun p hp => ?_⟩
       · simp only [List.mem_singleton] at hy; subst hy; subst e
         obtain ⟨t, ht, htp⟩ := List.mem_filterMap.1 hx
         exact endPos_fresh db t ht htp
       · rcases List.mem_append.1 hp with hp | hp
         · exact hq.2 p hp
         · simp only [List.mem_singleton] at hp; subst hp; exact endPos_pos db)

theorem tidy_frame (db : Db) : unplaced (tidy db) = unplaced db := by
  simp only [unplaced, tidy, List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => by simp only [Function.comp]; split <;> rfl

/-- `task done` and `task drop` end with `tidy`: their db is `Tasks.done`'s (`Tasks.drop`'s) with the closed tasks'
places taken. -/
theorem done_tidy (c : Ctx) (i : Int) (e : String) (db : Db) :
    (Queue.done c i e db).1 = (Tasks.done c i e db).1 ∨ (Queue.done c i e db).1 = tidy (Tasks.done c i e db).1 := by
  unfold Queue.done
  split <;> simp_all

theorem drop_tidy (c : Ctx) (i : Int) (dup : Option Int) (note : Option String) (db : Db) :
    (Queue.drop c i dup note db).1 = (Tasks.drop c i dup note db).1 ∨
      (Queue.drop c i dup note db).1 = tidy (Tasks.drop c i dup note db).1 := by
  unfold Queue.drop
  split <;> simp_all

theorem tasksDone_places (c : Ctx) (i : Int) (e : String) (db : Db) : places (Tasks.done c i e db).1 = places db := by
  unfold Tasks.done
  repeat' split
  all_goals first | rfl | exact places_set _ _ _ fun _ => rfl

theorem tasksDrop_places (c : Ctx) (i : Int) (dup : Option Int) (note : Option String) (db : Db) :
    places (Tasks.drop c i dup note db).1 = places db := by
  unfold Tasks.drop
  repeat' split
  all_goals first | rfl | exact places_set _ _ _ fun _ => rfl

theorem done_qinv (c : Ctx) (i : Int) (e : String) (db : Db) (_hi : Inv db) (hq : QInv db) :
    QInv (Queue.done c i e db).1 := by
  have h0 : QInv (Tasks.done c i e db).1 := by unfold QInv; rw [tasksDone_places]; exact hq
  rcases done_tidy c i e db with h | h
  · rw [h]; exact h0
  · rw [h]; exact tidy_qinv _ h0

theorem drop_qinv (c : Ctx) (i : Int) (dup : Option Int) (note : Option String) (db : Db) (_hi : Inv db)
    (hq : QInv db) : QInv (Queue.drop c i dup note db).1 := by
  have h0 : QInv (Tasks.drop c i dup note db).1 := by unfold QInv; rw [tasksDrop_places]; exact hq
  rcases drop_tidy c i dup note db with h | h
  · rw [h]; exact h0
  · rw [h]; exact tidy_qinv _ h0

/-! Staffing. -/

theorem mem_staffing {db : Db} {t : Task} (h : t ∈ staffing db) : t ∈ pool db ∧ free t = true := by
  simp only [staffing, staffRed, staffReady, List.mem_append, List.mem_filter, Bool.and_eq_true] at h
  rcases h with ⟨hp, hf, -⟩ | ⟨hp, hf, -⟩ <;> exact ⟨hp, hf⟩

/-- Only a Ready task no one is assigned is staffed: never a Backlog task, never a reserved one, not by auto-spawn,
not told to an idle agent. -/
theorem staffing_free {db : Db} {t : Task} (h : t ∈ staffing db) : t.status = .ready ∧ t.assignee = none := by
  obtain ⟨hp, hf⟩ := mem_staffing h
  exact ⟨((Board.mem_pool db t).1 hp).2.1, by simpa [free] using hf⟩

/-- Auto-spawn's choice is a startable task no one is assigned. -/
theorem staffHead_free {db : Db} {skip : Task → Bool} {i : Int} (h : staffHead skip db = some i) :
    ∃ t ∈ pool db, (t.id : Int) = i ∧ t.assignee = none ∧ skip t = false := by
  unfold staffHead at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some ht
  have hs := List.find?_some ht
  exact ⟨t, (mem_staffing hm).1, rfl, (staffing_free hm).2, by simpa using hs⟩

/-- With no startable red task left to staff, auto-spawn's next is the first startable Ready task no one is assigned,
in place order. -/
theorem staffHead_ready {db : Db} {skip : Task → Bool} {q : Task} (hr : ∀ t ∈ staffRed db, skip t = true)
    (hq : (staffReady db).find? (!skip ·) = some q) : staffHead skip db = some (q.id : Int) := by
  have : (staffRed db).find? (!skip ·) = none := List.find?_eq_none.2 fun t ht => by simp [hr t ht]
  simp only [staffHead, staffing, List.find?_append, this, hq, Option.none_or, Option.some_or, Option.map_some]

/-- The startable Ready tasks no one is assigned, no red one. -/
theorem mem_staffReady (db : Db) (t : Task) :
    t ∈ staffReady db ↔ t ∈ pool db ∧ t.assignee = none ∧ redKey t = 0 := by
  simp only [staffReady, free, List.mem_filter, Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq]

/-- ... in place order (then id), as `queued` orders them: the pool's order, which is the place order when every place
is positive. -/
theorem staffReady_sorted (db : Db) (hq : QInv db) : (staffReady db).Pairwise (qLe · · = true) := by
  have hs : (staffReady db).Pairwise (boardLe redKey · · = true) := (Board.pool_sorted db).filter _
  refine hs.imp_of_mem fun {a b} ha hb h => ?_
  have hpos : ∀ t ∈ staffReady db, ∀ p, t.pos = some p → 0 < p := fun t ht p e =>
    hq.2 p (List.mem_filterMap.2 ⟨t, ((Board.mem_pool db t).1 ((mem_staffReady db t).1 ht).1).1, e⟩)
  have ra := ((mem_staffReady db a).1 ha).2.2
  have rb := ((mem_staffReady db b).1 hb).2.2
  unfold boardLe at h
  unfold qLe
  simp only [ra, rb, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  cases e1 : a.pos <;> cases e2 : b.pos <;> simp only [e1, e2, Option.map_none, Option.map_some, Option.getD_none,
    Option.getD_some, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
  all_goals split at h <;> simp only [decide_eq_true_eq, true_and] at h ⊢
  all_goals first
    | omega
    | (have := hpos _ hb _ e2; omega)

/-- In a list sorted as the pool is, the red tasks come first. -/
theorem red_first : ∀ {l : List Task}, l.Pairwise (boardLe redKey · · = true) →
    l.filter (redKey · == 1) ++ l.filter (redKey · == 0) = l
  | [], _ => rfl
  | a :: l, h => by
    have hr : ∀ t, redKey t = 0 ∨ redKey t = 1 := fun t => by unfold redKey; split <;> simp
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 h
    have ih := red_first hl
    rcases hr a with e | e
    · have hall : ∀ b ∈ l, redKey b = 0 := fun b hb => by
        have := ha b hb
        unfold boardLe at this
        rcases hr b with e' | e'
        · exact e'
        · simp [e, e'] at this
      have h1 : l.filter (redKey · == 1) = [] := List.filter_eq_nil_iff.2 fun b hb => by simp [hall b hb]
      have h0 : l.filter (redKey · == 0) = l := List.filter_eq_self.2 fun b hb => by simp [hall b hb]
      simp [e, h1, h0]
    · simp only [List.filter_cons, e, beq_self_eq_true, ↓reduceIte, List.cons_append]
      simp only [show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
      rw [ih]

/-- With no task reserved for an assignee, the staffing order is exactly the pool: red first, then Ready by place. -/
theorem staffing_today (db : Db) (ha : ∀ t ∈ db.tasks, t.assignee = none) : staffing db = pool db := by
  have hf : ∀ t ∈ pool db, free t = true := fun t ht => by
    simp [free, ha t ((Board.mem_pool db t).1 ht).1]
  have e1 : staffRed db = (pool db).filter (redKey · == 1) := by
    unfold staffRed; exact List.filter_congr fun t ht => by simp [hf t ht]
  have e2 : staffReady db = (pool db).filter (redKey · == 0) := by
    unfold staffReady; exact List.filter_congr fun t ht => by simp [hf t ht]
  rw [staffing, e1, e2]
  exact red_first (Board.pool_sorted db)

/-! Claims. -/

/-- `task claim` refuses a Backlog task, unless the communicator (or the user) gives --force. -/
theorem claim_not_backlog {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) :
    r.status ≠ .backlog ∨ (c.force = true ∧ Agents.inCharge db c.comms c.me = true) := by
  unfold Tasks.claim at h
  rw [hr] at h
  dsimp only at h
  split at h
  · cases h
  · by_cases e : r.status = .backlog
    · right; simp_all
    · exact .inl e

/-- `task claim` of a Ready or Backlog task reserved for an assignee succeeds only for that assignee, unless the
communicator (or the user) gives --force. -/
theorem claim_reserved {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) (hs : r.status = .ready ∨ r.status = .backlog) :
    (py r.assignee).all (· == c.me) = true ∨ (c.force = true ∧ Agents.inCharge db c.comms c.me = true) := by
  unfold Tasks.claim at h
  rw [hr] at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h2
      by_cases hf : (c.force && Agents.inCharge db c.comms c.me) = true
      · right; simpa using hf
      · left
        cases e : py r.assignee with
        | none => rfl
        | some a => rcases hs with hs | hs <;> simp_all

/-! Ready's and Backlog's places are 1..n: the k-th task of each list, in place order, is at place k + 1. -/

theorem findIdx_id {l : List Task} (h : (l.map (·.id)).Nodup) {k : Nat} (hk : k < l.length) :
    l.findIdx? (·.id == l[k].id) = some k := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hk, by simp, fun j hj e => ?_⟩
  have hjk : j < l.length := by omega
  simp only [beq_iff_eq] at e
  have := List.pairwise_iff_getElem.1 h j k (by simpa using hjk) (by simpa using hk) hj
  simp only [List.getElem_map] at this
  exact this e

theorem queued_ids {db : Db} (hi : (db.tasks.map (·.id)).Nodup) : ((queued db).map (·.id)).Nodup :=
  ((List.mergeSort_perm _ _).map _).nodup_iff.2 (List.Nodup.sublist ((List.filter_sublist ..).map _) hi)

theorem filter_ids {l : List Task} {p : Task → Bool} (h : (l.map (·.id)).Nodup) : ((l.filter p).map (·.id)).Nodup :=
  List.Nodup.sublist ((List.filter_sublist ..).map _) h

/-- Ready's places are 1..n in its order. -/
theorem readyList_place (db : Db) (hi : (db.tasks.map (·.id)).Nodup) (k : Nat) (hk : k < (readyList db).length) :
    place db (readyList db)[k] = some (k + 1) := by
  have hs : (readyList db)[k].status = .ready := by
    have := List.getElem_mem hk
    simp only [readyList, List.mem_filter, decide_eq_true_eq] at this
    exact this.2
  have := findIdx_id (filter_ids (p := fun t => decide (t.status = .ready)) (queued_ids hi)) hk
  simp only [place, hs, ↓reduceIte]
  exact congrArg (Option.map (· + 1)) this

/-- Backlog's places are 1..n in its order. -/
theorem backlogList_place (db : Db) (hi : (db.tasks.map (·.id)).Nodup) (k : Nat) (hk : k < (backlogList db).length) :
    place db (backlogList db)[k] = some (k + 1) := by
  have hs : (backlogList db)[k].status = .backlog := by
    have := List.getElem_mem hk
    simp only [backlogList, List.mem_filter, decide_eq_true_eq] at this
    exact this.2
  have := findIdx_id (filter_ids (p := fun t => decide (t.status = .backlog)) (queued_ids hi)) hk
  simp only [place, hs, reduceCtorEq, ↓reduceIte]
  exact congrArg (Option.map (· + 1)) this

end SwarmLean.QueueProofs
