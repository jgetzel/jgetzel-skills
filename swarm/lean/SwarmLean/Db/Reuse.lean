import SwarmLean.Db.Queue

/-! Reuse (board #186): an agent that finished a task with context under `swarm limits --reuse-below` is offered the
startable tasks related to it (its lineage, a shared label) for its model, instead of being ended. Lifecycle's
"context" check is this offer: the agent claims what it has context for or declines, and watchd ends it then, or once
the offer is `OFFER_TTL` old. -/

namespace SwarmLean.Reuse
open Agents Tasks

/-- The reuse threshold in tokens: meta reuse_below; 0 (the default) is off. -/
def reuseBelow (db : Db) : Nat := ((metaNum db "reuse_below").getD 0).toNat

/-- `swarm limits --reuse-below`, by `me`. -/
def setBelow (db : Db) (me : String) (n : Int) (now : Int) : Db :=
  (db.setMeta "reuse_below" (some (toString n))).log now (some me) "limits" none (some s!"reuse below {n}")

/-- `reuse: …`, the third line of `swarm limits`. -/
def limitsLine (db : Db) : String :=
  let n := reuseBelow db
  if n > 0 then s!"reuse: an agent done under {n / 1000}k context is offered related tasks" else "reuse: off"

/-- The most tasks one offer names. -/
def MAX_OFFER : Nat := 5
/-- How long an offer keeps its agent and its tasks from auto-spawn, in seconds. -/
def OFFER_TTL : Int := 300

/-- The task agent `n` finished last: its done task with the latest done time. -/
def lastDone (db : Db) (n : String) : Option Task :=
  (db.tasks.filter fun t => t.owner == some n && t.status = .completed).foldl
    (fun b t => match b with | some x => if t.done_at.getD 0 ≥ x.done_at.getD 0 then some t else b | none => some t) none

/-- Task `t` is related to `f`, finished by `n`: `n` filed it while holding `f`, it waits on `f`, or they share a label. -/
def related (n : String) (f t : Task) : Bool :=
  (t.created_by == some n && (parentsOf t).contains (f.id : Int)) || (depsOf t).contains (f.id : Int) ||
    (labelsOf t).any (labelsOf f).contains

/-- The model a task is staffed with: its own, else `dflt` (auto-spawn's). -/
def modelOf (dflt : String) (t : Task) : String := (py t.model).getD dflt

/-- The offer to agent `n` of model `model`: the tasks of `staffing` (startable, unassigned, not in Backlog) related to its last done task and staffed with its model, in staffing order, at most MAX_OFFER. -/
def candidates (db : Db) (n : String) (model : Option String) (dflt : String) (staffing : List Task) : List Task :=
  match lastDone db n with
  | none => []
  | some f => (staffing.filter fun t => related n f t && some (modelOf dflt t) == py model).take MAX_OFFER

/-- `n`'s offers (digest events) since it finished its last task: their times and the task ids named. -/
def offers (db : Db) (n : String) : List (Int × List Int) :=
  let since := ((lastDone db n).bind (·.done_at)).getD 0
  (db.events.filter fun e => e.kind == some "digest" && e.agent == some n && e.ts.getD 0 ≥ since).map fun e =>
    (e.ts.getD 0, ((e.data.getD "").splitOn ",").filterMap parseInt)

/-- The offer to `n` has run out at `t`: it was told of every candidate in `ids`, the last time `OFFER_TTL` ago. -/
def expired (db : Db) (n : String) (ids : List Int) (t : Int) : Bool :=
  let os := offers db n
  !os.isEmpty && ids.all (fun i => os.any (·.2.contains i)) && os.all (fun o => t - o.1 ≥ OFFER_TTL)

/-- The task ids under an outstanding offer at `t`: named to a live agent in the last `OFFER_TTL`. Auto-spawn skips them. -/
def offered (db : Db) (t : Int) : List Int :=
  (live db).flatMap fun a => ((offers db a.name).filter fun o => t - o.1 < OFFER_TTL).flatMap (·.2)

/-- The offer's message. -/
def text (ts : List Task) : String :=
  s!"Your task is done and your context is small. Related tasks are startable: " ++
  "; ".intercalate (ts.map fun t => s!"#{t.id} {t.title.getD ""}") ++
  ". Claim one you have real context for (`swarm task claim <id>`); if none fits, decline by stopping: " ++
  s!"watchd ends you and staffs them fresh (in {OFFER_TTL / 60} min at the latest)."

/-! The offer's guarantees. -/

/-- An offered task is one of the staffing order's, related to the agent's last done task, and staffed with its model. -/
theorem candidates_spec {db n model dflt staffing t} (h : t ∈ candidates db n model dflt staffing) :
    t ∈ staffing ∧ some (modelOf dflt t) = py model ∧ ∃ f, lastDone db n = some f ∧ related n f t = true := by
  unfold candidates at h
  split at h
  · simp at h
  · rename_i f hf
    have := List.mem_of_mem_take h
    simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1, this.2.2, f, hf, this.2.1⟩

/-- An offer names at most MAX_OFFER tasks. -/
theorem candidates_length {db n model dflt staffing} : (candidates db n model dflt staffing).length ≤ MAX_OFFER := by
  unfold candidates; split
  · simp
  · exact List.length_take_le _ _

/-- Off by default: with no reuse_below set, the threshold is 0 and no context is under it. -/
theorem off_default {db : Db} (h : db.getMeta "reuse_below" = none) : reuseBelow db = 0 := by
  simp [reuseBelow, metaNum, h]

/-- An agent that finished nothing is offered nothing. -/
theorem candidates_none {db n model dflt staffing} (h : lastDone db n = none) : candidates db n model dflt staffing = [] := by
  simp [candidates, h]

end SwarmLean.Reuse
