import SwarmLean.Lib.Bases
import SwarmLean.Lib.Agents
import SwarmLean.Lib.Machine
import SwarmLean.Lib.Workspaces
import SwarmLean.Db.Msgs
import SwarmLean.Db.Tasks
import SwarmLean.Sys

/-! watchd's verdict on a live agent (watchd.fate, model Decide.lean's fateL) and the reads it is made of
(watchd.reads, unlanded, landed, landed_ref, unclean_list): lifecycle's verdict each tick, and state --json's. -/

namespace SwarmLean.Fate
open Lean (Json)

variable {m : Type → Type} [Monad m]

/-- Python truthiness of a text. -/
def nz (s : Option String) : Option String := py s

section
variable [Git m] [Proc m] [Fs m] [Sys m]

/-- `git -C cwd …`'s exit 0. -/
def gx (cwd : String) (args : List String) : m Bool := return (← Git.git (["-C", cwd] ++ args) none).isSome

/-- Whether `ref` (in `cwd`) is on base `b`: an ancestor, the same content under other commits (squash or rebase), or
the head of a merged PR from its branch (watchd.landed_ref). -/
def landedRef1 (cwd ref b : String) : m Bool := do
  if ← gx cwd ["merge-base", "--is-ancestor", ref, b] then return true
  let mb := nz ((← Git.git ["-C", cwd, "merge-base", b, ref] none).map strip)
  let files := match mb with
    | some mb => fun (o : Option String) => ((o.getD "").splitOn "\x00").filter (· ≠ "")
    | none => fun _ => []
  let files := files (← match mb with
    | some mb => Git.git ["-C", cwd, "diff", "--name-only", "-z", mb, ref] none
    | none => pure none)
  if !files.isEmpty then
    if ← gx cwd (["diff", "--quiet", ref, b, "--"] ++ files) then return true
  let br := nz ((← Git.git ["-C", cwd, "rev-parse", "--abbrev-ref", ref] none).map strip)
  let head := nz ((← Git.git ["-C", cwd, "rev-parse", ref] none).map strip)
  let (some br, some head) := (br, head) | return false
  let prs ← Proc.output ["gh", "pr", "list", "--head", br, "--state", "merged", "--json", "number,headRefOid"] (some cwd) []
  let j := prs.bind fun o => if o.code == 0 then Json.decode o.stdout else none
  return (Json.items (j.getD .null)).any fun pr => Json.fstr pr "headRefOid" == some head

/-- landed_ref on any of the bases `bs`. -/
def landedRef (cwd ref : String) (bs : List String) : m Bool := bs.anyM (landedRef1 cwd ref)

/-- Nothing in worktree `wt` is unlanded relative to any of `bs` (watchd.landed). -/
def landed (wt : String) (bs : List String) (main : String) : m Bool := do
  if (← Sys.kind wt true) == .none then
    -- nothing uncommitted can be lost; judge by its branch if git still knows it
    let mut br : Option String := none
    let mut inwt := false
    for line in splitlines ((← Git.git ["-C", main, "worktree", "list", "--porcelain"] none).getD "") do
      if line.startsWith "worktree " then inwt := (line.drop 9).toString == wt
      else if inwt && line.startsWith "branch refs/heads/" then br := some (line.drop 18).toString; break
    match br with
    | none => return true
    | some b => landedRef main b bs
  let some st ← Git.git ["-C", wt, "status", "--porcelain"] none | return false
  if strip st != "" then return false
  return wt == main || (← landedRef wt "HEAD" bs)

/-- What keeps worktree `wt` from landing: git status lines and commits not on `b` (watchd.unclean_list). -/
def uncleanList (wt b : String) : m String := do
  if (← Sys.kind wt true) == .none then return s!"{wt} is gone; its branch holds commits not on {b}"
  let st := (splitlines ((← Git.git ["-C", wt, "status", "--porcelain"] none).getD "")).filter (· ≠ "")
  let lg := (splitlines ((← Git.git ["-C", wt, "log", "--oneline", b ++ "..HEAD"] none).getD "")).filter (· ≠ "")
  return "\n".intercalate (st ++ lg.map ("commit " ++ ·))

/-- The first of agent `n`'s worktrees with work not on its bases, and those bases' refs (watchd.unlanded). -/
def unlanded (db : Db) (n main : String) (wts : List (String × String)) (allWts : List (String × String)) :
    m (Option (String × List String)) := do
  let names ← Bases.ofAgent ((db.tasks.filter (·.owner == some n)).map (·.base)) (some main)
  let own := (wts.lookup n).toList ++ Workspaces.ownedWts n allWts (some db) ++ Workspaces.ownedWts n allWts none
  let mut seen : List String := []
  for w in own do
    if seen.contains w then continue
    seen := w :: seen
    let mut bs ← Bases.refs names (some main)
    if let some b := (db.workspaces.find? fun x => x.path == w && x.agent == n && x.ro == some 0).bind (·.base) then
      bs := bs ++ [← Bases.ref b (some main)]
    if !(← landed w bs main) then return some (w, bs)
  return none

end

/-- The reads fate makes of one agent, each only when the verdict needs it (watchd.reads' f). -/
structure F (m : Type → Type) where
  ours : String → m Bool
  pool : Nat
  alive : Int → m Bool
  claims : m Bool
  locks : m Bool
  /-- the worktree with unlanded work and its bases' refs -/
  unlanded : m (Option (String × List String))
  /-- a background job runs: its process -/
  job : m (Option (Option Machine.ProcInfo))
  passedOver : m Bool

/-- What a fate run heard: each check made (label, holds), the unlanded worktree and its refs, the job's process. -/
structure Heard where
  checks : List (String × Bool) := []
  held : Option (String × List String) := none
  proc : Option Machine.ProcInfo := none

/-- Lifecycle's verdict on live agent row `a` (watchd.fate): none (kept), "unclean", "reuse" or "end". `x`: its hc
terminal; `hasTerms`: hc answered. With `all` no check holds, so every one is made (the verdict is then meaningless). -/
def fate (a : Agent) (t : Int) (x : Option Agents.Term) (hasTerms : Bool) (f : F m) (all : Bool := false) :
    m (Option String × Heard) := do
  let mut h : Heard := {}
  -- one check: recorded, and with `all` it never holds
  let k (h : Heard) (label : String) (v : Bool) : Heard × Bool := ({ h with checks := h.checks ++ [(label, v)] }, v && !all)
  let (h1, b) := k h "stay" (nz a.stay).isSome
  h := h1; if b then return (none, h)
  let (h1, b) := k h "idle" (a.status != some "idle" || t - a.last_active.getD 0 < 120)
  h := h1; if b then return (none, h)
  let other ← match x.bind (·.cwd) |>.bind (nz ·) with
    | some c => pure !(← f.ours c)
    | none => pure false
  let busy := (nz a.hc).isSome && hasTerms && match x with
    | none => true
    | some x => x.status != some "idle" && x.status != some "done"
  let (h1, b) := k h "terminal" (other || busy)
  h := h1; if b then return (none, h)
  let (h1, b) := k h "task" (← f.claims)
  h := h1; if b then return (none, h)
  let (h1, b) := k h "lock" (← f.locks)
  h := h1; if b then return (none, h)
  let u ← f.unlanded
  h := { h with held := u }
  let (h1, b) := k h "unlanded" u.isSome
  h := h1; if b then return (some "unclean", h)
  let j ← f.job
  h := { h with proc := j.join }
  let (h1, b) := k h "job" j.isSome
  h := h1; if b then return (none, h)
  let smallV ← if a.ctx_tokens.getD 0 < Agents.SMALL_CTX && f.pool > 0 then pure !(← f.passedOver) else pure false
  let (h1, small) := k h "context" smallV
  h := h1
  let w ← match a.waiter with
    | some p => f.alive p
    | none => pure false
  let (h1, b) := k h "waiter" w
  h := h1
  if b && small then return (some "reuse", h)
  return (some "end", h)

end SwarmLean.Fate
