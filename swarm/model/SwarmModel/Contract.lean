import SwarmModel.Workers
import SwarmModel.Basic
import SwarmModel.Locks
import SwarmModel.Inbox
import SwarmModel.Workspaces
import SwarmModel.NoWorkLost
import SwarmModel.Fair
import SwarmModel.Gone
import SwarmModel.Real
import SwarmModel.Release
import SwarmModel.End
import SwarmModel.Away
import SwarmModel.Nudge
import SwarmModel.Stay

/-! The contract (board #25): the theorems a proof about a program that uses the swarm should build on, each restated
here over the model's types (`Cfg`, `State`, `Reachable`, `Run`; `Env.Tools`, `Env.Db`), so a change to one that
breaks this statement breaks the build. Import this module alone (`example/Client.lean` does).

Each says what it guarantees and what it rests on. "Switches" are the `Cfg` fields it takes as hypotheses: the fixes,
all on in `Cfg`'s defaults but `splitGC`, `perTaskBase`, `recordedWorkspaces`, `bgLives` and `ownAdded` (main has
them; `replay` sets them).
"Env" is which of `Env.lean`'s assumptions it takes, as hypotheses on any `Tools` or `Db`: the model theorems take
none. For the machine the swarm runs on, `Env.real` and `Env.realDb`, `Real.lean` supplies them from the axioms
(`Env.landedRef_reach`, `Env.realDb_sound`, …); for another, supply proofs (`Env.consistent` for `Env.ideal`). -/

namespace Swarm.Contract
open Env

/-! ## Safety: every reachable state, any number of agents, tasks, locks and messages -/

/-- S1: no two agents, each working or at an hc prompt, both believe they hold one task.
Switches: `release = .idle`, and `humanRelease` off or `stopFirst` on: without board #53's fix the user's release of a
working agent's task breaks it (`not_S1_humanRelease`). Env: none. -/
theorem s1_oneWorker {c : Cfg} (hfix : c.release = .idle) (hhr : c.humanRelease = false ∨ c.stopFirst = true) {s : State} (h : Reachable c s) :
    oneWorker s = true :=
  oneWorker_of_reachable hfix hhr h

/-- S1 at the board: a task an agent at work believes it holds is held by it on the board (claimed or blocked, it the
owner), or was dropped, or (board #80) watchd's poll marked it done when its PR merged (`merged`: the merge recorded),
which the agent hasn't read yet. Switches: `release = .idle`, `humanRelease` off. Env: none. -/
theorem s1_believes_held {c : Cfg} (hfix : c.release = .idle) (hhr : c.humanRelease = false) {s : State} (h : Reachable c s) {a t : Nat}
    (ha : active (s.agt a) = true) (ht : t ∈ (s.agt a).believes) :
    held (s.tk t) a = true ∨ (s.tk t).st = .dropped ∨ ((s.tk t).st = .done ∧ (s.tk t).merged = true) := by
  rcases (J_of_reachable hfix (Or.inl hhr) h).1 a t ht with hi | hd | hs
  · exact absurd hi.1 (by simp [ha])
  · exact hd
  · have := hs.1.1; rw [stopTo_none hhr h] at this; cases this

/-- S1 at the board, with H2 and its fix (board #53): a task an agent at work believes it holds is held by it, or was
dropped, or done by watchd's poll (board #80), or the user released it from that agent, which hasn't read the stop yet:
the task is open, its stop names the agent, and no one may take it (`stopped`). Switches: `release = .idle`,
`stopFirst`. Env: none. -/
theorem s1_believes_held_stop {c : Cfg} (hfix : c.release = .idle) (hsf : c.stopFirst = true) {s : State} (h : Reachable c s)
    {a t : Nat} (ha : active (s.agt a) = true) (ht : t ∈ (s.agt a).believes) :
    held (s.tk t) a = true ∨ (s.tk t).st = .dropped ∨ ((s.tk t).st = .done ∧ (s.tk t).merged = true) ∨
      ((s.tk t).st = .opn ∧ stopped s t = true) := by
  rcases (J_of_reachable hfix (Or.inr hsf) h).1 a t ht with hi | hd | hs
  · exact absurd hi.1 (by simp [ha])
  · rcases hd with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
  · refine Or.inr (Or.inr (Or.inr ⟨hs.2, ?_⟩))
    unfold stopped; rw [hs.1.1]; simp [ha, hs.1.2.1]

/-- S2: no task was ever claimed while a task it is after wasn't done. Switches: `claimChecksDeps`. Env: none. -/
theorem s2_noEarlyStart {c : Cfg} (hfix : c.claimChecksDeps = true) {s : State} (h : Reachable c s) :
    noEarlyStart s = true :=
  noEarlyStart_of_reachable hfix h

/-- S3, as files: two live locks of different agents never both cover one path. Switches: `lockOverlap`, `lockForms`.
Env: none. -/
theorem s3_noSharedFile {c : Cfg} (hfix : c.lockOverlap = true) (hforms : c.lockForms = true) {s : State}
    (h : Reachable c s) {p q : Nat} {l m : Lock} {a b : Nat} (hp : s.lock[p]? = some l) (hq : s.lock[q]? = some m)
    (hpq : p ≠ q) (ha : l.holder = some a) (hb : m.holder = some b) (hab : a ≠ b) (he1 : l.exp = false)
    (he2 : m.exp = false) (x : String) (hx : Glob.Bytes x.toList) :
    ¬ (covers c x (c.pat p) = true ∧ covers c x (c.pat q) = true) :=
  noSharedFile_of_reachable hfix hforms h hp hq hpq ha hb hab he1 he2 x hx

/-- S4: no message is shown twice, and no cursor passes a message it didn't show. Switches: `deliverCas`. Env: none. -/
theorem s4_inboxExact {c : Cfg} (hfix : c.deliverCas = true) {s : State} (h : Reachable c s) : inboxExact s = true :=
  inboxExact_of_reachable hfix h

/-- S5: every done task has evidence. Switches: `evidenceRequired`. Env: none. -/
theorem s5_doneHasEvidence {c : Cfg} (hfix : c.evidenceRequired = true) {s : State} (h : Reachable c s) :
    doneHasEvidence s = true :=
  doneHasEvidence_of_reachable hfix h

/-- W1: a step removes a worktree only if it was clean, unattached, had no process inside and its HEAD on a protected
ref, and deletes a branch only if it is no protected ref and its tip was on one. Switches: `splitGC`. Env: none
(`env_sweepGate` is the same gate on the tools' answers). -/
theorem w1_gcOk (c : Cfg) (hc : c.splitGC = true) {s s' : State} (act : Action) (h : Reachable c s)
    (hs : step c s act = some s') : gcOk c s s'.git = true :=
  W1_of c hc s act s' h hs

/-- N1: watchd never discards work that isn't landed (`N1`'s four parts). Switches: `release = .idle`, `bgKeeps`,
`retake`, `allWts`, `bgLives`, `ownAdded`, `perTaskBase`, `splitGC`. Env: none. -/
theorem n1_noWorkLost (c : Cfg) (hrel : c.release = .idle) (hbk : c.bgKeeps = true) (hret : c.retake = true)
    (haw : c.allWts = true) (hbl : c.bgLives = true) (hoa : c.ownAdded = true) (hp : c.perTaskBase = true)
    (hs : c.splitGC = true) : N1 c :=
  N1_of c hrel hbk hret haw hbl hoa hp hs

/-! ## Liveness: over fair runs (`Run.Fair`: every action enabled infinitely often in `fair` is taken) -/

/-- L2: a claimed task whose owner is idle is eventually done or open again, or its owner back at work, while no agent
starts a background job or dies. Switches: `racy = false`, `release ≠ .ended`, `watchd`. Env: none. -/
theorem l2_idleClaim {c : Cfg} (hr : c.racy = false) (hfix : c.release ≠ .ended) (hw : c.watchd = true) {a t : Nat}
    (ha : a ∈ c.agents) (ht : t ∈ c.tasks) (r : Run c) (hf : r.Fair) {n : Nat}
    (hq : ∀ k, n ≤ k → ∀ b, r.act k ≠ .bgStart b ∧ r.act k ≠ .die b)
    (hbg0 : ((r.st n).agt a).bg = false) (hdd0 : ((r.st n).agt a).dead = false)
    (h : idleClaim (r.st n) a t = true) : ∃ m, n ≤ m ∧ idleClaim (r.st m) a t = false :=
  idleClaim_leads_to hr hfix hw ha ht r hf hq hbg0 hdd0 h

/-- L4: a row whose terminal is gone is eventually ended (its claims and locks released). Switches: `racy = false`,
`watchd`, `hcSees`, the row bound (`unbound`). Env: none (`env_reapGone` is `hc ls` telling it). -/
theorem l4_deadLive {c : Cfg} (hr : c.racy = false) (hw : c.watchd = true) (hh : c.hcSees = true) {a : Nat}
    (ha : a ∈ c.agents) (hb : c.unbound.contains a = false) (r : Run c) (hf : r.Fair) {n : Nat}
    (hR : Reachable c (r.st n)) (h : deadLive (r.st n) a = true) : ∃ m, n ≤ m ∧ deadLive (r.st m) a = false :=
  deadLive_leads_to hr hw hh ha hb r hf hR h

/-- H2: after the user's or the communicator's release of a task another holds, its ex-owner is sent a stop and does
not keep at work unaware of it forever: it reads it, stops being at work, or its terminal is gone (which `l4_deadLive`
ends). Switches: none. Env: none. -/
theorem h2_released_reads {c : Cfg} (r : Run c) (hf : r.Fair) {n t : Nat} (hR : Reachable c (r.st n))
    (hact : r.act n = .releaseOther t) :
    ∃ o i, held ((r.st n).tk t) o = true ∧ ((r.st (n + 1)).msg i).kind = .released ∧ ((r.st (n + 1)).msg i).task = t ∧
      ∃ m, n + 1 ≤ m ∧ (active ((r.st m).agt o) = false ∨ ((r.st m).agt o).dead = true ∨ i ≤ (r.st m).cur o) :=
  released_reads r hf hR hact

/-- H1: `swarm end A` by the user or the communicator without --force never ends an agent that holds work (a background
job running, or work off its tasks' bases in a worktree it works in or owns): its check is lifecycle's but the 2 min.
`--force` does (`not_N1end_force`). Switches: `allWts`, `ownAdded`, `perTaskBase`. Env: none. -/
theorem h1_end_keeps_work {c : Cfg} (haw : c.allWts = true) (hoa : c.ownAdded = true) (hp : c.perTaskBase = true)
    {s s' : State} {a : Nat} (h : Reachable c s) (hs : step c s (.endOther a false) = some s') : holdsWork c s a = false :=
  N1end_of haw hoa hp s s' a h hs

/-- H1: `swarm end A` without --force changes nothing but A's row: A ended, no task, lock, message, cursor, git ref or
other agent changed. Switches: none. Env: none. -/
theorem h1_end_spec {c : Cfg} {s s' : State} {a : Nat} (hs : step c s (.endOther a false) = some s') :
    endable c s a = true ∧ s'.task = s.task ∧ s'.lock = s.lock ∧ s'.log = s.log ∧ s'.cursor = s.cursor ∧ s'.git = s.git ∧
      (a < s.ag.length → (s'.agt a).st = .ended) ∧ ∀ b, b ≠ a → s'.agt b = s.agt b :=
  endOther_spec hs

/-- Q1 (board #47): after a tick every blocked task's latest question was told. Switches: `renotify`. Env: none. -/
theorem q1_told {c : Cfg} (hr : c.renotify = true) : Q1 c := Q1_of hr
/-- A2 (board #47): a block notice is urgent exactly when the user is not away. Switches: `awayQuiet`. Env: none. -/
theorem a2_quiet {c : Cfg} (h : c.awayQuiet = true) : A2quiet c := A2quiet_of h
/-- A2 (board #47): on a run fair to the communicator's waiter, all it was sent before `--back` is read. Switches:
`backTells`. Env: none. -/
theorem a2_reaches {c : Cfg} (h : c.backTells = true) : A2live c := A2live_of h
/-- A3 (board #47): the away flag changes nothing the tick does but the notices' urgency. Switches: none. Env: none. -/
theorem a3_blind (c : Cfg) (s : State) (v : Option Nat) : blind (tickOf c (withAway s v)) = blind (tickOf c s) := A3 c s v

/-- N1' (board #50): `swarm nudge` changes no task, claim, lock, lease, message or cursor; it types its line into the
nudged agent's terminal only, starts or ends no terminal, and leaves the repo's durable state. Switches: none.
Env: `HcSendTargets`. -/
theorem n1'_nudge {t : Tools} (hs : HcSendTargets t) {c : Cfg} {s s' : State} {a : Nat}
    (h : step c s (.hnudge a) = some s') {w : t.World} {hT : Nat} (hl : t.termLive w hT = true) (l : String) :
    s' = s ∧ t.typed (t.hcSend w hT l) hT = t.typed w hT ++ [l] ∧
      (∀ h', h' ≠ hT → t.typed (t.hcSend w hT l) h' = t.typed w h') ∧
      (∀ h', t.termLive (t.hcSend w hT l) h' = t.termLive w h') ∧
      Git.durable (t.git (t.hcSend w hT l)) = Git.durable (t.git w) :=
  Tools.N1' hs h hl l

/-- Stays (board #79): the tick keeps a live stayer's row (but for the pool ids a digest told it of), and `swarm end`
without --force refuses it. Switches: none. Env: none. -/
theorem stay_kept {c : Cfg} {s : State} {a : Nat} (hs : (s.agt a).stay = true) (hl : (s.agt a).live = true) :
    { (tickOf c s).agt a with told := [] } = { s.agt a with told := [] } ∧ step c s (.endOther a false) = none :=
  ⟨tick_keeps_stayer hs hl, endOther_stay hs⟩
/-- Stays (board #79): `--back`'s digest lists a slot as hung exactly when its agent hung since away and did not end
since. Switches: none. Env: none. -/
theorem digest_hung' (c : Cfg) (s : State) (since a : Nat) :
    a ∈ (digestOf c s since).hung ↔
      a < c.nagents ∧ ∃ l1 l2, s.evs.drop since = l1 ++ .hung a :: l2 ∧ Ev.ended a ∉ l2 :=
  digest_hung c s since a

/-! ## The tools: what the Lua decides on their answers is what the model decides on its view -/

/-- watchd.landed_ref saying "landed" means the commit is reachable from the branch, or `gh` said so.
Env: `AncestorReach`, `SameContentReach`. -/
theorem env_landedRef {t : Tools} (ha : AncestorReach t) (hsc : SameContentReach t) {w : t.World} {k b : Nat}
    {gh : Bool} (h : landedRef t w k b gh = true) : (t.git w).reachFrom k b = true ∨ gh = true :=
  Tools.landedRef_reach ha hsc h

/-- The sweep's gate on the tools' answers (no `gh`) is W1's premise on the model's view.
Env: `AncestorReach`, `SameContentReach`, `StatusClean`, `ListedOn`, `CwdsProc`, `TouchedRecent`. -/
theorem env_sweepGate {t : Tools} (ha : AncestorReach t) (hsc : SameContentReach t) (hsl : StatusClean t)
    (hlo : ListedOn t) (hcp : CwdsProc t) (htr : TouchedRecent t) {w : t.World} {c : Cfg} {used : Bool} {x : Nat}
    (h : sweepGate t w c used x (fun _ => false) = true) :
    let y := (t.git w).wt x
    y.on = true ∧ used = false ∧ y.proc = false ∧ y.recent = false ∧ y.dirty = false ∧ (t.git w).safe c y.head = true :=
  Tools.sweepGate_W1 ha hsc hsl hlo hcp htr h

/-- reap reads a bound row as gone exactly when its terminal is. Env: `HcLsLive`. -/
theorem env_reapGone {t : Tools} (hl : HcLsLive t) {w : t.World} {h : Nat} :
    t.hcLs w h = false ↔ t.termLive w h = false :=
  Tools.reap_gone hl

/-- The db is serializable: every committed version is its transaction's statements run on the one before, and a
transaction holding the write lock runs on the latest. Env: `SqliteSound` (all five sqlite assumptions). -/
theorem db_serializable {db : Db} (hdb : SqliteSound db) {w0 w : db.World} {d0 : Sql.DB}
    (h0 : db.view w0 = Iso.Eng.init d0) (h : db.Run w0 w) : Iso.Inv Iso.sqlLang (db.view w) :=
  Db.serializable hdb h0 h

end Swarm.Contract
