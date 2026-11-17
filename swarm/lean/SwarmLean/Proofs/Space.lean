import SwarmLean.Db.Agents

/-! The swarm's Herdr space (meta space), recorded whichever comes first of the communicator's `swarm join` and the
watchd start that names it (`SWARM_COMMS`). swarm/model's Comms.lean takes each swarm's space as given (`CCfg.home`);
this is the code establishing it: join records its terminal's space when the joiner is the communicator (`joinSpace`,
after its `bind`), and watchd's start records the space of the terminal the communicator's row is bound to
(`startSpace`). Before this fix the start named the communicator and nothing more (`nameComms`), so SKILL.md's order,
join then watchd, left the swarm with no space (`nameComms_after_join`). What hc answers of a terminal is any function
`spOf` (a terminal another swarm's communicator holds answers none). -/

namespace SwarmLean.Proofs.Space
open SwarmLean Agents

theorem find_map_k (l : List Meta) (k : String) (f : Meta → Meta) (hf : ∀ m, (f m).k = m.k) :
    (l.map f).find? (·.k == k) = (l.find? (·.k == k)).map f := by
  rw [List.find?_map]
  have : ((fun x : Meta => x.k == k) ∘ f) = (fun x => x.k == k) := by funext m; simp [hf]
  rw [this]

/-- Setting meta `k` makes it read back. -/
theorem getMeta_setMeta (db : Db) (k : String) (v : Option String) : (db.setMeta k v).getMeta k = some { k, v } := by
  unfold Db.setMeta Db.getMeta
  split
  · rename_i h
    rw [find_map_k _ _ _ (by intro m; split <;> rfl)]
    cases hm : db.metas.find? (·.k == k) with
    | none =>
      obtain ⟨x, hx, hpx⟩ := List.any_eq_true.mp h
      exact absurd hpx (List.find?_eq_none.mp hm x hx)
    | some m =>
      have hk : m.k = k := by simpa using List.find?_some hm
      simp [hk]
  · rename_i h
    have hn : db.metas.find? (·.k == k) = none := by simpa using h
    simp [List.find?_append, hn]

/-- Setting meta `k` leaves every other key's. -/
theorem getMeta_setMeta_ne (db : Db) {k k' : String} (v : Option String) (hne : k' ≠ k) :
    (db.setMeta k v).getMeta k' = db.getMeta k' := by
  unfold Db.setMeta Db.getMeta
  split
  · rw [find_map_k _ _ _ (by intro m; split <;> rfl)]
    cases hm : db.metas.find? (·.k == k') with
    | none => rfl
    | some m =>
      have hk : m.k = k' := by simpa using List.find?_some hm
      simp [hk, hne]
  · simp [List.find?_append, hne.symm]

theorem getMeta_metas {a b : Db} (h : a.metas = b.metas) (k : String) : a.getMeta k = b.getMeta k := by
  unfold Db.getMeta; rw [h]

/-- The row named `n` after `setAgent n f`, for an `f` that keeps the name. -/
theorem agent_setAgent (db : Db) (n : String) (f : Agent → Agent) (hf : ∀ a, (f a).name = a.name) :
    (db.setAgent n f).agent n = (db.agent n).map f := by
  unfold Db.setAgent Db.agent
  rw [List.find?_map]
  have : ((fun a : Agent => a.name == n) ∘ fun a => if a.name = n then f a else a) = (·.name == n) := by
    funext a; by_cases h : a.name = n <;> simp [h, hf]
  rw [this]
  cases hm : db.agents.find? (·.name == n) with
  | none => rfl
  | some a => have : a.name = n := by simpa using List.find?_some hm
              simp [this]

/-- `nameComms` keeps the communicator's terminal. -/
theorem commsTerm_nameComms (db : Db) (c : String) (now : Int) : commsTerm (nameComms db c now) c = commsTerm db c := by
  have hm : (db.setMeta "comms" (some c)).agent c = db.agent c := by unfold Db.setMeta Db.agent; split <;> rfl
  unfold nameComms; dsimp only
  split
  · have h2 : (((db.setMeta "comms" (some c)).setAgent c ({ · with stay := some "the user's channel" })).log now (some c)
        "stay" none (some "the user's channel")).agent c = (db.agent c).map ({ · with stay := some "the user's channel" }) := by
      show ((db.setMeta "comms" (some c)).setAgent c ({ · with stay := some "the user's channel" })).agent c = _
      rw [agent_setAgent _ c (fun x => { x with stay := some "the user's channel" }) (fun _ => rfl), hm]
    unfold commsTerm; rw [h2]; cases db.agent c <;> rfl
  · unfold commsTerm; rw [hm]

/-- `nameComms` names the communicator and leaves the space. -/
theorem nameComms_meta (db : Db) (c : String) (now : Int) :
    (nameComms db c now).getMeta "comms" = some { k := "comms", v := some c } ∧
    (nameComms db c now).getMeta "space" = db.getMeta "space" := by
  have hc := getMeta_setMeta db "comms" (some c)
  have hs := getMeta_setMeta_ne db (k := "comms") (k' := "space") (some c) (by decide)
  unfold nameComms; dsimp only
  split
  · exact ⟨(getMeta_metas rfl _).trans hc, (getMeta_metas rfl _).trans hs⟩
  · exact ⟨hc, hs⟩

/-- A recorded space is never replaced. -/
theorem recordSpace_keeps (db : Db) (sp : Option String) (h : (db.getMeta "space").isSome) : recordSpace db sp = db := by
  unfold recordSpace; split <;> simp [h]

/-- With none recorded, `recordSpace` records `sp`. -/
theorem recordSpace_sets (db : Db) (sp : String) (h : db.getMeta "space" = none) :
    (recordSpace db (some sp)).getMeta "space" = some { k := "space", v := some sp } := by
  unfold recordSpace; simp [h, getMeta_setMeta]

/-- `bind`, join's transaction, changes no meta. -/
theorem bind_metas (db : Db) (name : String) (cwd hc model : Option String) (r : Binding) (now : Int) :
    (Agents.bind db name cwd hc model r now).1.metas = db.metas := by
  unfold Agents.bind
  split
  · rfl
  · simp only []
    split <;> (split <;> (split <;> (try split) <;> simp [Db.setAgent, Db.log, newInbox] <;> (try split) <;> rfl))

/-- SKILL.md's order: the communicator `c` joins (its row bound to terminal `h`) before anything names it, then watchd
starts naming it; the swarm's space is `h`'s. -/
theorem join_then_start (db : Db) (envComms : Option String) (c h sp : String) (now : Int) (spOf : String → Option String)
    (hs : db.getMeta "space" = none) (hnc : isComms db envComms (some c) = false) (ht : commsTerm db c = some h)
    (hsp : spOf h = some sp) :
    (startSpace (joinSpace db envComms c (spOf h)) c now spOf).getMeta "space" = some { k := "space", v := some sp } := by
  have hj : joinSpace db envComms c (spOf h) = db := by unfold joinSpace; simp [hnc]
  rw [hj]
  unfold startSpace; dsimp only
  rw [commsTerm_nameComms, ht]
  simp only [Option.bind_some, hsp]
  exact recordSpace_sets _ _ ((nameComms_meta db c now).2.trans hs)

/-- The other order: watchd's start names `c` while no live row of it is bound (it has not joined), then `c` joins
from a terminal in space `sp` (`bind`, then `joinSpace`); the swarm's space is `sp`. (`isComms` takes no empty name.) -/
theorem start_then_join (db : Db) (envComms : Option String) (c sp : String) (now t : Int) (spOf : String → Option String)
    (cwd hc model : Option String) (r : Binding)
    (hc0 : c ≠ "") (hs : db.getMeta "space" = none) (hno : commsTerm db c = none) :
    (joinSpace (Agents.bind (startSpace db c now spOf) c cwd hc model r t).1 envComms c (some sp)).getMeta "space"
      = some { k := "space", v := some sp } := by
  have hm := nameComms_meta db c now
  have hs1 : startSpace db c now spOf = nameComms db c now := by
    unfold startSpace; dsimp only; rw [commsTerm_nameComms, hno]; rfl
  rw [hs1]
  have hb := getMeta_metas (bind_metas (nameComms db c now) c cwd hc model r t)
  have hcm : isComms (Agents.bind (nameComms db c now) c cwd hc model r t).1 envComms (some c) = true := by
    unfold isComms commsOf; rw [hb, hm.1]; split <;> simp_all
  unfold joinSpace; simp only [hcm, ↓reduceIte]
  exact recordSpace_sets _ _ (by rw [hb, hm.2, hs])

/-- The start before this fix named the communicator and nothing more (`nameComms`): after a join that came first, no
space. -/
theorem nameComms_after_join (db : Db) (envComms : Option String) (c : String) (now : Int) (sp : Option String)
    (hs : db.getMeta "space" = none) (hnc : isComms db envComms (some c) = false) :
    (nameComms (joinSpace db envComms c sp) c now).getMeta "space" = none := by
  have hj : joinSpace db envComms c sp = db := by unfold joinSpace; simp [hnc]
  rw [hj, (nameComms_meta db c now).2, hs]

end SwarmLean.Proofs.Space
