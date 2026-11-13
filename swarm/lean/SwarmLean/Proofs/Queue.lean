import SwarmLean.Proofs.Tasks
import SwarmLean.Db.Queue

/-! Board #128: the staffing queue and holds, proved of the real steps (Db/Queue.lean's `setQueue`, `add`, `rm`,
`tidy`, `hold`, `unhold`, `done`, `drop`, `staffing`, `staffHead`), the functions Cmd/Tasks.lean runs in `Store.txn`.
Every queue op keeps the queued tasks' places a permutation of 1..n and changes nothing but the places (and the events
it logs); a held task is never staffed; with an empty queue and queue-only off, the staffing order is the pool's.
The staffing theorem itself, about auto-spawn's reservation, is `WatchdProofs.reserveTask_top`. -/

namespace SwarmLean.QueueProofs
open Tasks Queue

/-! The places. -/

/-- The places the queued tasks hold. -/
def places (db : Db) : List Int := db.tasks.filterMap (·.qpos)

/-- The queue's invariant: the queued tasks hold the places 1..n, each once. -/
def QInv (db : Db) : Prop := ∃ n, (places db).Perm ((List.range n).map fun (i : Nat) => (i : Int) + 1)

/-- `db` with no task queued: everything a queue op must leave as it was (but the events it logs). -/
def unplaced (db : Db) : Db := { db with tasks := db.tasks.map fun t => { t with qpos := none } }

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

/-- `setQueue` gives the tasks it queues the places 1..n, each once. -/
theorem setQueue_qinv (db : Db) (l : List Int) (hi : (db.tasks.map (·.id)).Nodup) : QInv (setQueue db l) := by
  refine ⟨(dedup (l.filter fun i => (db.find i).isSome)).length, ?_⟩
  rw [places_setQueue]
  refine (idxOf_perm ?_ (nodup_dedup _) fun x hx => ?_).map _
  · rw [List.Nodup, List.pairwise_map]
    have := List.pairwise_map.1 hi
    exact this.imp fun h e => h (by omega)
  · obtain ⟨-, hx⟩ := List.mem_filter.1 (mem_dedup.1 hx)
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hx
    exact List.mem_map.2 ⟨t, Board.find_mem ht, find_id ht⟩

/-- `setQueue` changes the places only. -/
theorem setQueue_frame (db : Db) (l : List Int) : unplaced (setQueue db l) = unplaced db := by
  simp only [unplaced, setQueue, List.map_map]
  rfl

theorem setQueue_ids (db : Db) (l : List Int) : (setQueue db l).tasks.map (·.id) = db.tasks.map (·.id) := by
  simp only [setQueue, List.map_map]; rfl

/-- `db'` is `db` with some events appended. -/
def Logged (db db' : Db) : Prop := ∃ evs n, db' = { db with events := evs, eventNext := n }

theorem logged_foldl {β : Type} (f : Db → β → Db) (hf : ∀ db b, Logged db (f db b)) :
    ∀ (l : List β) (db : Db), Logged db (l.foldl f db)
  | [], db => ⟨db.events, db.eventNext, rfl⟩
  | b :: bs, db => by
    obtain ⟨e1, n1, h1⟩ := hf db b
    obtain ⟨e2, n2, h2⟩ := logged_foldl f hf bs (f db b)
    simp only [List.foldl_cons]
    exact ⟨e2, n2, h2.trans (by rw [h1])⟩

theorem logged_log (db : Db) ts a k p x : Logged db (db.log ts a k p x) := ⟨_, _, rfl⟩

theorem logged_places {db db' : Db} (h : Logged db db') : places db' = places db := by
  obtain ⟨_, _, rfl⟩ := h; rfl

/-- What a queue op does: nothing (a refusal), or set the queue and log. -/
def QStep (db db' : Db) : Prop := db' = db ∨ ∃ l, Logged (setQueue db l) db'

theorem qstep_qinv {db db' : Db} (h : QStep db db') (hi : (db.tasks.map (·.id)).Nodup) (hq : QInv db) : QInv db' := by
  rcases h with rfl | ⟨l, hl⟩
  · exact hq
  · unfold QInv; rw [logged_places hl]; exact setQueue_qinv db l hi

theorem qstep_frame {db db' : Db} (h : QStep db db') :
    { unplaced db' with events := db.events, eventNext := db.eventNext } = unplaced db := by
  rcases h with rfl | ⟨l, _, _, rfl⟩
  · rfl
  · show { unplaced (setQueue db l) with events := db.events, eventNext := db.eventNext } = unplaced db
    rw [setQueue_frame]
    rfl

theorem add_step (c : Ctx) (ids : List Int) (w : Place) (db : Db) : QStep db (Queue.add c ids w db).1 := by
  unfold Queue.add
  split
  · exact .inl rfl
  · exact .inr ⟨_, logged_foldl _ (fun _ _ => logged_log ..) _ _⟩

theorem rm_step (c : Ctx) (ids : List Int) (db : Db) : QStep db (Queue.rm c ids db).1 := by
  unfold Queue.rm
  dsimp only
  repeat' split
  all_goals first | exact .inl rfl | exact .inr ⟨_, logged_foldl _ (fun _ _ => logged_log ..) _ _⟩

theorem tidy_step (db : Db) : QStep db (tidy db) := .inr ⟨_, _, _, rfl⟩

/-- Queue ops (`queue add`, `queue rm`, and `tidy`, which `task done`/`task drop` and watchd's done marks end with)
keep the places a permutation of 1..n. -/
theorem add_qinv (c : Ctx) (ids : List Int) (w : Place) (db : Db) (hi : Inv db) (hq : QInv db) :
    QInv (Queue.add c ids w db).1 := qstep_qinv (add_step ..) hi.1 hq

theorem rm_qinv (c : Ctx) (ids : List Int) (db : Db) (hi : Inv db) (hq : QInv db) : QInv (Queue.rm c ids db).1 :=
  qstep_qinv (rm_step ..) hi.1 hq

theorem tidy_qinv (db : Db) (hi : (db.tasks.map (·.id)).Nodup) : QInv (tidy db) := setQueue_qinv _ _ hi

/-- Queue ops change nothing but the places and the events they log. -/
theorem add_frame (c : Ctx) (ids : List Int) (w : Place) (db : Db) :
    { unplaced (Queue.add c ids w db).1 with events := db.events, eventNext := db.eventNext } = unplaced db :=
  qstep_frame (add_step ..)

theorem rm_frame (c : Ctx) (ids : List Int) (db : Db) :
    { unplaced (Queue.rm c ids db).1 with events := db.events, eventNext := db.eventNext } = unplaced db :=
  qstep_frame (rm_step ..)

theorem tidy_frame (db : Db) : unplaced (tidy db) = unplaced db := setQueue_frame _ _

/-- `task done` and `task drop` end with `tidy`: their db is `Tasks.done`'s (`Tasks.drop`'s) with the places
renumbered, a permutation of 1..n again. -/
theorem done_tidy (c : Ctx) (i : Int) (e : String) (db : Db) :
    (Queue.done c i e db).1 = (Tasks.done c i e db).1 ∨ (Queue.done c i e db).1 = tidy (Tasks.done c i e db).1 := by
  unfold Queue.done
  split <;> simp_all

theorem drop_tidy (c : Ctx) (i : Int) (db : Db) :
    (Queue.drop c i db).1 = (Tasks.drop c i db).1 ∨ (Queue.drop c i db).1 = tidy (Tasks.drop c i db).1 := by
  unfold Queue.drop
  split <;> simp_all

/-- A step that changes tasks only by `db.set` of fields other than the place keeps the places. -/
theorem places_set (db : Db) (i : Int) (f : Task → Task) (hf : ∀ t, (f t).qpos = t.qpos) :
    places (db.set i f) = places db := by
  simp only [places, Db.set, List.filterMap_map]
  congr 1; funext t; simp only [Function.comp]; split <;> simp [hf]

theorem tasksDone_places (c : Ctx) (i : Int) (e : String) (db : Db) : places (Tasks.done c i e db).1 = places db := by
  unfold Tasks.done
  repeat' split
  all_goals first | rfl | exact places_set _ _ _ fun _ => rfl

theorem tasksDrop_places (c : Ctx) (i : Int) (db : Db) : places (Tasks.drop c i db).1 = places db := by
  unfold Tasks.drop
  repeat' split
  all_goals first | rfl | exact places_set _ _ _ fun _ => rfl

theorem done_qinv (c : Ctx) (i : Int) (e : String) (db : Db) (hi : Inv db) (hq : QInv db) :
    QInv (Queue.done c i e db).1 := by
  rcases done_tidy c i e db with h | h
  · unfold QInv; rw [h, tasksDone_places]; exact hq
  · rw [h]; apply tidy_qinv
    rcases Board.done_spec c i e db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · rw [ht]; exact hi.1
    · rw [ht, set_tasks_ids _ _ _ fun u => (hf u).1]; exact hi.1

theorem drop_qinv (c : Ctx) (i : Int) (db : Db) (hi : Inv db) (hq : QInv db) : QInv (Queue.drop c i db).1 := by
  rcases drop_tidy c i db with h | h
  · unfold QInv; rw [h, tasksDrop_places]; exact hq
  · rw [h]; apply tidy_qinv
    rcases Board.drop_spec c i db with ⟨ht, -⟩ | ⟨f, hf, ht, -⟩
    · rw [ht]; exact hi.1
    · rw [ht, set_tasks_ids _ _ _ fun u => (hf u).1]; exact hi.1

/-! Holds and staffing. -/

/-- `task hold` and `task unhold` change the task's hold and nothing of the queue. -/
theorem hold_places (c : Ctx) (i : Int) (why : String) (db : Db) : places (Queue.hold c i why db).1 = places db := by
  unfold Queue.hold
  repeat' split
  all_goals first | rfl | exact places_set _ _ _ fun _ => rfl

theorem unhold_places (c : Ctx) (i : Int) (db : Db) : places (Queue.unhold c i db).1 = places db := by
  unfold Queue.unhold
  repeat' split
  all_goals first | rfl | exact places_set _ _ _ fun _ => rfl

theorem mem_staffing {db : Db} {t : Task} (h : t ∈ staffing db) : t ∈ pool db ∧ t.hold = none := by
  simp only [staffing, staffRed, staffQueue, staffRest, List.mem_append, List.mem_mergeSort, held] at h
  have key : ∀ {p : Task → Bool}, t ∈ (pool db).filter (fun t => !t.hold.isSome && p t) → t ∈ pool db ∧ t.hold = none :=
    fun hm => by
      obtain ⟨hp, hh⟩ := List.mem_filter.1 hm
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hh
      exact ⟨hp, hh.1⟩
  rcases h with (h | h) | h
  · exact key h
  · exact key (p := fun t => redKey t == 0 && t.qpos.isSome) (by simpa [Bool.and_assoc] using h)
  · split at h
    · cases h
    · exact key (p := fun t => redKey t == 0 && t.qpos.isNone) (by simpa [Bool.and_assoc] using h)

/-- A held task is never staffed: not by auto-spawn, not told to an idle agent. -/
theorem staffing_not_held {db : Db} {t : Task} (h : t ∈ staffing db) : t.hold = none := (mem_staffing h).2

/-- Auto-spawn's choice is a startable task not held. -/
theorem staffHead_not_held {db : Db} {skip : Task → Bool} {i : Int} (h : staffHead skip db = some i) :
    ∃ t ∈ pool db, (t.id : Int) = i ∧ t.hold = none ∧ skip t = false := by
  unfold staffHead at h
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_find?_eq_some ht
  have hs := List.find?_some ht
  exact ⟨t, (mem_staffing hm).1, rfl, (mem_staffing hm).2, by simpa using hs⟩

/-- The queue part of the staffing order is exactly the startable queued tasks not held (no red one)... -/
theorem mem_staffQueue (db : Db) (t : Task) :
    t ∈ staffQueue db ↔ t ∈ pool db ∧ t.hold = none ∧ redKey t = 0 ∧ t.qpos.isSome := by
  simp only [staffQueue, held, List.mem_mergeSort, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, beq_iff_eq, and_assoc]

/-- ... in queue order. -/
theorem staffQueue_sorted (db : Db) : (staffQueue db).Pairwise (qLe · · = true) :=
  List.pairwise_mergeSort (fun a b c h1 h2 => by unfold qLe at *; simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by unfold qLe; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _

/-- With no startable red task left to staff, auto-spawn's next is the first startable queued task not held. -/
theorem staffHead_queue {db : Db} {skip : Task → Bool} {q : Task} (hr : ∀ t ∈ staffRed db, skip t = true)
    (hq : (staffQueue db).find? (!skip ·) = some q) : staffHead skip db = some (q.id : Int) := by
  have : (staffRed db).find? (!skip ·) = none := List.find?_eq_none.2 fun t ht => by simp [hr t ht]
  simp only [staffHead, staffing, List.find?_append, this, hq, Option.none_or, Option.some_or, Option.map_some]

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

/-- With an empty queue and queue-only off, the staffing order is the pool's without the held tasks. -/
theorem staffing_unqueued (db : Db) (hq : ∀ t ∈ db.tasks, t.qpos = none) (ho : queueOnly db = false) :
    staffing db = (pool db).filter (!held ·) := by
  have hp : ∀ t ∈ pool db, t.qpos = none := fun t ht => hq t ((Board.mem_pool db t).1 ht).1
  have hs := (Board.pool_sorted db).filter (!held ·)
  have e1 : staffRed db = ((pool db).filter (!held ·)).filter (redKey · == 1) := by
    simp only [staffRed, List.filter_filter]
    exact List.filter_congr fun t _ => by cases held t <;> simp
  have e2 : staffQueue db = [] := by
    simp only [staffQueue]
    rw [List.filter_eq_nil_iff.2 fun t ht => by simp [hp t ht]]
    exact List.mergeSort_nil
  have e3 : staffRest db = ((pool db).filter (!held ·)).filter (redKey · == 0) := by
    simp only [staffRest, ho, Bool.false_eq_true, ↓reduceIte, List.filter_filter]
    exact List.filter_congr fun t ht => by simp [hp t ht]; cases held t <;> simp
  rw [staffing, e1, e2, e3, List.append_nil]
  exact red_first hs

/-- With an empty queue, queue-only off and no task held, the staffing order is exactly today's: the pool. -/
theorem staffing_today (db : Db) (hq : ∀ t ∈ db.tasks, t.qpos = none) (hh : ∀ t ∈ db.tasks, t.hold = none)
    (ho : queueOnly db = false) : staffing db = pool db := by
  rw [staffing_unqueued db hq ho]
  exact List.filter_eq_self.2 fun t ht => by simp [held, hh t ((Board.mem_pool db t).1 ht).1]

/-- `task claim` refuses a held task, unless the communicator (or the user) gives --force. -/
theorem claim_not_held {c : Ctx} {i : Int} {l : String} {db : Db} {x : Claimed} {r : Task}
    (h : (Tasks.claim c i l db).2 = .ok x) (hr : db.find i = some r) :
    r.hold = none ∨ (c.force = true ∧ Agents.inCharge db c.comms c.me = true) := by
  unfold Tasks.claim at h
  rw [hr] at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hh
    cases e : r.hold
    · exact .inl rfl
    · right; simp_all

end SwarmLean.QueueProofs
