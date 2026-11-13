import SwarmLean.Db.Agents

/-! Context compaction (board #136): the thresholds (`swarm limits` settings), watchd's pure decision per agent and the
`/compact` line it and `swarm compact` type into the agent's terminal. -/

namespace SwarmLean.Compact
open Agents

/-- The default nudge threshold in tokens: from here an agent takes no new task and is told to compact. -/
def NUDGE_AT : Int := 325000
/-- The default compaction threshold in tokens: watchd compacts an idle agent from here. -/
def COMPACT_AT : Int := 400000

/-- The nudge threshold: meta ctx_nudge (0: off), else NUDGE_AT. -/
def nudgeAt (db : Db) : Int := (metaNum db "ctx_nudge").getD NUDGE_AT
/-- The compaction threshold: meta ctx_compact (0: off), else COMPACT_AT. -/
def compactAt (db : Db) : Int := (metaNum db "ctx_compact").getD COMPACT_AT
/-- `swarm limits --compact-stayers on`: the communicator and agents with a stay are compacted too, not only nudged. -/
def stayersToo (db : Db) : Bool := ((db.getMeta "compact_stayers").bind (·.v)) == some "on"

/-- `swarm limits` with --ctx-nudge, --ctx-compact or --compact-stayers, by `me`. -/
def setLimits (db : Db) (me : String) (nudge compact : Option Int) (stayers : Option Bool) (now : Int) : Db :=
  let db := match nudge with | some n => db.setMeta "ctx_nudge" (some (toString n)) | none => db
  let db := match compact with | some n => db.setMeta "ctx_compact" (some (toString n)) | none => db
  let db := match stayers with | some b => db.setMeta "compact_stayers" (some (if b then "on" else "off")) | none => db
  db.log now (some me) "limits" none (some s!"ctx nudge {nudgeAt db} compact {compactAt db} stayers {stayersToo db}")

/-- `compaction: …`, the second line of `swarm limits`. -/
def limitsLine (db : Db) : String :=
  let t (n : Int) := if n > 0 then s!"{n / 1000}k" else "off"
  s!"compaction: nudge at {t (nudgeAt db)}, compact at {t (compactAt db)}" ++
  (if stayersToo db then ", the communicator and stayers too" else ", the communicator and stayers only nudged")

/-- Context `k` is at or over threshold `n`, which 0 turns off. -/
def over (k n : Int) : Bool := n > 0 && k ≥ n

/-- What an agent's terminal shows: idle between turns, mid-turn, a dialog or prompt, or no Claude session. -/
inductive Term | idle | working | prompt | none
  deriving DecidableEq, Repr

/-- hc's status of a terminal. -/
def Term.ofHc : Option String → Term
  | some "idle" | some "done" => .idle
  | some "working" => .working
  | some "blocked" => .prompt
  | _ => .none

/-- What watchd does: nothing, nudge the agent, compact it, or tell the communicator a compaction did not shrink it. -/
inductive Act | nothing | nudge | compact | failed
  deriving DecidableEq, Repr

/-- What watchd did since the context was last seen below each threshold. -/
structure St where
  nudged : Bool := false
  compacted : Bool := false
  told : Bool := false
  deriving DecidableEq, Repr

/-- The decision at context `k`, thresholds `nAt`/`cAt`, terminal `t`, state `s`; `force`: watchd may compact this agent.
A reading below a threshold clears what was done at it; an idle agent over `cAt` is compacted once, and if it is still
over at its next idle the communicator is told once; else one nudge per crossing of `nAt`. -/
def step (k nAt cAt : Int) (force : Bool) (t : Term) (s : St) : Act × St :=
  let s := if over k nAt then s else { s with nudged := false }
  let s := if over k cAt then s else { s with compacted := false, told := false }
  if force && over k cAt && t == .idle then
    if !s.compacted then (.compact, { s with compacted := true, nudged := true })
    else if !s.told then (.failed, { s with told := true })
    else (.nothing, s)
  else if over k nAt && !s.nudged then (.nudge, { s with nudged := true })
  else (.nothing, s)

/-- The state's meta key for agent `n`. -/
def key (n : String) : String := "ctx:" ++ n

/-- Agent `n`'s state from meta. -/
def load (db : Db) (n : String) : St :=
  let v := ((db.getMeta (key n)).bind (·.v)).getD ""
  { nudged := v.contains 'n', compacted := v.contains 'c', told := v.contains 't' }

/-- `db` with agent `n`'s state stored (none when all clear). -/
def save (db : Db) (n : String) (s : St) : Db :=
  let v := (if s.nudged then "n" else "") ++ (if s.compacted then "c" else "") ++ (if s.told then "t" else "")
  if v == "" then delMeta db (key n) else db.setMeta (key n) (some v)

/-- One line: newlines to spaces. -/
def oneLine (s : String) : String := s.map fun c => if c == '\n' || c == '\r' then ' ' else c

/-- Longest `--keep` text sent inline; Claude Code pastes anything over ~800 chars as an attachment, not a command. -/
def maxKeep : Nat := 300

/-- The `/compact` line for agent `name`: what to keep, from its task, worktree and branch, plus `extra`. -/
def line (name : String) (task : Option (Int × String)) (cwd branch : Option String) (extra : Option String) : String :=
  let t := match task with | some (i, ti) => s!" on task #{i} ({ti})" | none => ""
  let w := match cwd with | some c => s!"; worktree {c}" | none => ""
  let b := match branch with | some b => if b != "" then s!", branch {b}" else "" | none => ""
  let x := match extra with | some e => if e != "" then " " ++ e else "" | none => ""
  oneLine s!"/compact Keep what swarm agent {name} needs to go on{t}: what is done, what is next, decisions made and why, open questions and promises to peers{w}{b}.{x}"

/-- The nudge at the first threshold; `force`: say watchd compacts at the second. -/
def nudgeText (k cAt : Int) (task : Option Int) (force : Bool) : String :=
  let id := match task with | some i => toString i | none => "<id>"
  s!"Context is ~{k / 1000}k tokens: commit WIP, note on the task what is done and what is next " ++
  s!"(`swarm task edit {id} --append \"…\"`), then `swarm compact --keep \"<what else to keep>\"`; it runs when this turn ends." ++
  (if force && cAt > 0 then s!" From {cAt / 1000}k watchd compacts you when you are idle." else "")

/-- The communicator's notice when a compaction left agent `n` over `cAt`. -/
def failedText (n : String) (k cAt : Int) (hc : String) : String :=
  s!"{n}'s context is still ~{k / 1000}k after a compaction (limit {cAt / 1000}k); watchd won't compact it again until it drops below. `hc read {hc}`."

/-! The decision's guarantees. -/

/-- watchd compacts only an idle agent: never mid-turn, into a dialog or prompt, or a terminal with no Claude session. -/
theorem step_compact_idle {k nAt cAt force t s} (h : (step k nAt cAt force t s).1 = .compact) : t = .idle := by
  unfold step at *
  generalize over k nAt = a at *; generalize over k cAt = b at *
  rcases s with ⟨_ | _, _ | _, _ | _⟩ <;> cases force <;> cases t <;> cases a <;> cases b <;> simp_all

/-- watchd compacts only an agent it may (not the communicator or a stayer unless the limit says so). -/
theorem step_compact_force {k nAt cAt force t s} (h : (step k nAt cAt force t s).1 = .compact) : force = true := by
  unfold step at *
  generalize over k nAt = a at *; generalize over k cAt = b at *
  rcases s with ⟨_ | _, _ | _, _ | _⟩ <;> cases force <;> cases t <;> cases a <;> cases b <;> simp_all

/-- A compaction marks the state compacted. -/
theorem step_compact_marks {k nAt cAt force t s} (h : (step k nAt cAt force t s).1 = .compact) :
    (step k nAt cAt force t s).2.compacted = true := by
  unfold step at *
  generalize over k nAt = a at *; generalize over k cAt = b at *
  rcases s with ⟨_ | _, _ | _, _ | _⟩ <;> cases force <;> cases t <;> cases a <;> cases b <;> simp_all

/-- While the context stays over the threshold a compacted state stays compacted and is not compacted again: between
two compactions a reading below the threshold. -/
theorem step_no_recompact {k nAt cAt force t s} (hs : s.compacted = true) (ho : over k cAt = true) :
    (step k nAt cAt force t s).1 ≠ .compact ∧ (step k nAt cAt force t s).2.compacted = true := by
  unfold step at *
  generalize over k nAt = a at *; generalize over k cAt = b at *
  rcases s with ⟨_ | _, _ | _, _ | _⟩ <;> cases force <;> cases t <;> cases a <;> cases b <;> simp_all

end SwarmLean.Compact
