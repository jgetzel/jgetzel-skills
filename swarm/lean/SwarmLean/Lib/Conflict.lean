import SwarmLean.Lib.Re
import SwarmLean.Lib.Difflib
import SwarmLean.Lib.Json
import SwarmLean.Db.Locks
import SwarmLean.Db.Msgs
import SwarmLean.World

/-! conflict.lua: diff3 hunks, the edits each side made and whether two edits clash; snapshots of worktrees, trial
merges, and the conflict tick (watchd's), which turns clashing uncommitted work into notices and releases landed
locks. Which agent works in which worktree (wt_map) and a task's base are given by the caller. -/

namespace SwarmLean.Conflict

/-- A token: a word, one other non-space character, or a newline (conflict.TOK). -/
def TOK : String := "\\w+|[^\\w\\s]|\\n"

/-- diff3 conflict hunks as (ours, base, theirs), each keeping its trailing newline, by scanning lines for the
markers (conflict.hunks). -/
def hunks (text : String) : List (String × String × String) := Id.run do
  let ls := ((text.splitOn "\n").map (· ++ "\n")).toArray
  -- the last piece has no newline after it
  let ls := if text.endsWith "\n" then ls.pop else ls.modify (ls.size - 1) fun l => String.ofList l.toList.dropLast
  let n := ls.size
  let next (start : Nat) (mark : String) : Option Nat := Id.run do
    for k in [start:n] do
      if ls[k]!.startsWith mark then return some k
    return none
  let cat (a b : Nat) : String := String.join (ls.extract a b).toList
  let mut res : Array (String × String × String) := #[]
  let mut pos := 0
  for _ in [0:n + 1] do
    let some a := next pos "<<<<<<< " | break
    let b := next (a + 1) "||||||| "
    let c := b.bind fun b => next (b + 1) "=======\n"
    let some dd := c.bind fun c => next (c + 1) ">>>>>>> " | break
    let (b, c) := (b.get!, c.get!)
    res := res.push (cat (a + 1) b, cat (b + 1) c, cat (c + 1) dd)
    pos := dd + 1
  return res.toList

/-- The base-token spans one side changed, half-open; an empty span is an insertion there (conflict.edits). -/
def edits (base side : Array String) : List (Nat × Nat) :=
  (Difflib.opcodes base side).toList.filterMap fun (t, i1, i2, _) => if t == "equal" then none else some (i1, i2)

/-- Two spans clash if both change a common base token, or one inserts strictly inside the other's change. -/
def clash (a b : Nat × Nat) : Bool :=
  let (a1, a2) := a
  let (b1, b2) := b
  if a1 == a2 && b1 == b2 then false
  else if a1 == a2 then b1 < a1 && a1 < b2
  else if b1 == b2 then a1 < b1 && b1 < a2
  else a1 < b2 && b1 < a2

/-- A text's tokens. -/
def toks (s : String) : Array String :=
  match Re.findall TOK s with
  | .ok l => (l.map (·.headD "")).toArray
  | .error _ => #[]

/-- Whether a hunk is a real conflict: some edit of ours clashes with one of theirs (conflict.real_hunk). -/
def realHunk (base ours theirs : String) : Bool :=
  let b := toks base
  let eb := edits b (toks theirs)
  (edits b (toks ours)).any fun x => eb.any (clash x)


variable {m : Type → Type} [Monad m] [Proc m] [Git m] [Env m]

/-- `argv`'s stdout when it exits 0 (proc.run). -/
def run (argv : List String) (cwd : Option String := none) (env : List (String × String) := []) : m (Option String) := do
  match ← Proc.output argv cwd env with
  | some o => return if o.code == 0 then some o.stdout else none
  | none => return none

/-- `git <args>`'s stdout, stripped, when it exits 0 (proc.git). -/
def git (args : List String) (cwd : Option String := none) : m (Option String) := return (← Git.git args cwd).map strip

/-- A worktree's working state as an unreferenced commit, and the files it changed since its merge-base with the
base (conflict.snapshot). -/
structure Snap where
  head : String
  tree : String
  commit : String
  files : List String
  deriving Inhabited

/-- The snapshot as agent.snap stores it. -/
def Snap.json (s : Snap) : String :=
  Json.encode (Lean.Json.mkObj [("head", s.head), ("tree", s.tree), ("commit", s.commit),
    ("files", Lean.Json.arr (s.files.map Lean.Json.str).toArray)])

/-- Commits `wt`'s working state (tracked and untracked, not ignored) through a copy of its index; reads `wt` only
(conflict.snapshot). The copy keeps the index's mtime, or git would trust stale stat data. -/
def snapshot (wt : String) (base : Option String) : m (Option Snap) := do
  let some head ← git ["-C", wt, "rev-parse", "HEAD"] | return none
  let some idx ← git ["-C", wt, "rev-parse", "--path-format=absolute", "--git-path", "index"] | return none
  if head == "" || idx == "" then return none
  let tmpRoot := (← Env.var "TMPDIR").getD "/tmp"
  let some d ← run ["mktemp", "-d", tmpRoot ++ "/swarm-snap-XXXXXX"] | return none
  let d := strip d
  let tmp := d ++ "/index"
  -- cp -p keeps the mtime to the nanosecond where the Lua keeps whole seconds: git rehashes no more, the same tree
  discard <| Proc.output ["cp", "-p", idx, tmp] none []
  let env := [("GIT_INDEX_FILE", tmp), ("GIT_OPTIONAL_LOCKS", "0"), ("GIT_AUTHOR_NAME", "swarm"),
    ("GIT_AUTHOR_EMAIL", "swarm@swarm"), ("GIT_COMMITTER_NAME", "swarm"), ("GIT_COMMITTER_EMAIL", "swarm@swarm")]
  let g (args : List String) : m String := return strip ((← run (["git", "-C", wt] ++ args) none env).getD "")
  discard <| g ["add", "-A"]
  let tree ← g ["write-tree"]
  let commit ← if tree != "" then g ["commit-tree", tree, "-p", head, "-m", "swarm snapshot"] else pure ""
  discard <| Proc.output ["rm", "-rf", d] none []
  if commit == "" then return none
  let mb ← match base with
    | some b => git ["-C", wt, "merge-base", b, commit]
    | none => pure none
  let files ← match mb with
    | some mb => if mb == "" then pure [] else
        pure ((((← run ["git", "-C", wt, "diff", "--name-only", "-z", mb, commit]).getD "").splitOn "\x00").filter (· != ""))
    | none => pure []
  return some { head, tree, commit, files }

/-- The tree of `commit`'s own changes (since its merge-base with `base`) replayed onto `base`; none if they conflict
with base (conflict.onto). -/
def onto (wt base commit : String) : m (Option String) := do
  let some mb ← git ["-C", wt, "merge-base", base, commit] | return none
  if mb == "" then return none
  let some o ← Proc.output ["git", "-C", wt, "merge-tree", "--write-tree", "--no-messages", s!"--merge-base={mb}", base,
    commit] none [] | return none
  if o.code != 0 then return none
  return (o.stdout.split Char.isWhitespace).find? (· != "") |>.map (·.toString)

/-- util.splitlines: on `\n` only, no empty last line. -/
def lines (s : String) : List String :=
  let l := s.splitOn "\n"
  if s.endsWith "\n" then l.dropLast else if s == "" then [] else l

/-- Merges two trees that are each one agent's own changes on `base`: none if git failed; else each conflicted path
with its real hunks' (ours, theirs) texts, and whether some conflict was line-only (conflict.trial_merge). -/
def trialMerge (cwd base ca cb : String) : m (Option (List (String × List (String × String)) × Bool)) := do
  let some o ← Proc.output ["git", "-c", "merge.conflictStyle=diff3", s!"--attr-source={base}", "merge-tree",
    "--write-tree", "--name-only", "--no-messages", s!"--merge-base={base}", ca, cb] (some cwd) [] | return none
  if o.code != 1 then return if o.code == 0 then some ([], false) else none
  let ls := lines o.stdout
  let tree := ls.headD ""
  let files := ((ls.drop 1).filter (· != "")).eraseDups.toArray.qsort (· < ·)
  let mut real : Array (String × List (String × String)) := #[]
  let mut compat := false
  for f in files do
    -- not UTF-8 (binary): no hunks, so it counts as real
    let text := (← git ["show", s!"{tree}:{f}"] (some cwd)).getD ""
    let hs := hunks text
    let bad := hs.filterMap fun (ours, base, theirs) => if realHunk base ours theirs then some (ours, theirs) else none
    -- no diff3 hunks: a rename or file/directory conflict, which counts as real
    if !bad.isEmpty || hs.isEmpty then real := real.push (f, if bad.isEmpty then [("", "")] else bad)
    else compat := true
  return some (real.toList, compat)

/-- The lines `text` spans in `commit:path`, as `a–b`, or `?` (conflict.line_range). -/
def lineRange (cwd commit path text : String) : m String := do
  let text := String.ofList ((text.toList.dropWhile (· == '\n')).reverse.dropWhile (· == '\n')).reverse
  let f := (← git ["show", s!"{commit}:{path}"] (some cwd)).getD ""
  if text == "" then return "?"
  match f.splitOn text with
  | pre :: _ :: _ =>
    let n := (pre.toList.filter (· == '\n')).length
    let k := (text.toList.filter (· == '\n')).length
    return s!"{n + 1}–{n + 1 + k}"
  | _ => return "?"

/-- The commit work for base `b` is measured against: origin/<b>, unless local <b> is ahead; main also falls back to
master (conflict.base_sha). -/
def baseSha (b : String) : m (Option String) := do
  let mut got : List String := []
  for r in if b == "main" then ["origin/main", "main", "master"] else ["origin/" ++ b, b] do
    if (← git ["rev-parse", "--verify", "-q", r]).isSome then got := got ++ [r]
  if let a :: b' :: rest := got then
    if a == "origin/" ++ b && b' == b && (← git ["merge-base", "--is-ancestor", a, b]).isSome then got := b' :: rest
  match got with
  | r :: _ => git ["rev-parse", r]
  | [] => return none

/-- `xs` without repeats, sorted. -/
def uniqSorted (xs : List String) : List String := (xs.eraseDups.toArray.qsort (· < ·)).toList

/-- The conflict tick's write (`conflictTick`): each candidate pair's key and conflicts from its git work (`work`,
`ranges`), the notices, lock violations, and locks whose holder's work landed. -/
def tickApply (wts : List (String × String)) (snaps : List (String × Snap))
    (work : List (String × String × String × Option (Option (List (String × List (String × String)) × Bool))))
    (ranges : List ((String × String × String) × String × String)) (t : Int) (db : Db) : Db :=
  let wtOf (n : String) : String := (wts.lookup n).getD ""
  let names := snaps.map (·.1)
  let snapOf (n : String) : Snap := (snaps.lookup n).getD default
  let tally (w : String) : Nat := (wts.filter (·.2 == w)).length
  let setKey (db : Db) (a b key : String) : Db :=
    { db with pairkeys := db.pairkeys.filter (fun r => !(r.a == a && r.b == b)) ++ [{ a, b, key := some key }] }
  let (db, notes) := work.foldl (init := (db, ([] : List (String × List String)))) fun (db, notes) (a, b, key, r) =>
    match r with
    | none => ((setKey db a b key).log t (some a) "conflict-stale" (some b) none, notes)
    | some none => (db.log t (some a) "conflict-error" (some b) none, notes)
    | some (some (real, compat)) =>
      let db := setKey db a b key
      let had := (db.conflicts.filter fun c => c.a == a && c.b == b).map (·.path)
      let db := { db with conflicts := db.conflicts.filter fun c => !(c.a == a && c.b == b && !real.any (·.1 == c.path)) }
      let db := if compat then db.log t (some a) "conflict-compat" (some b) none else db
      real.foldl (init := (db, notes)) fun (db, notes) (p, _) =>
        if had.contains p then (db, notes) else
        let db := { db with conflicts := db.conflicts ++ [({ a, b, path := p, since := some t } : Conflict)] }
        let db := db.log t (some a) "conflict" (some p) (some b)
        let (ha, hb) := ((ranges.lookup (a, b, p)).getD ("", ""))
        let note (o mine theirs : String) : String :=
          s!"Your uncommitted work conflicts with {o}'s ({Locks.taskOf db o}) in {p} (your lines {mine}, theirs {theirs}). Whoever lands first wins; the other rebases onto it. Message {o} only if the two changes can't both stand."
        let add (notes : List (String × List String)) (n x : String) :=
          if notes.any (·.1 == n) then notes.map fun (k, l) => if k == n then (k, l ++ [x]) else (k, l)
          else notes ++ [(n, [x])]
        (db, add (add notes a (note b ha hb)) b (note a hb ha))
  let db := notes.foldl (init := db) fun db (n, l) => (Msgs.post db t "swarm" n ("\n".intercalate l) false (some "notice")).1
  -- edits to another agent's lock, from the snapshot; only in trees one agent owns
  let db := names.foldl (init := db) fun db n =>
    if tally (wtOf n) > 1 then db else
    (snapOf n).files.foldl (init := db) fun db p =>
      match Locks.lockHolder db n p t with
      | none => db
      | some lk =>
        if db.events.any fun e => e.kind == some "lock-violation" && e.agent == some n && e.path == some p then db else
        let who := lk.agent.getD ""
        let db := db.log t (some n) "lock-violation" (some p) (some who)
        let db := (Msgs.post db t "swarm" n s!"{n} edited {p}, locked by {who}: violation. Revert it or ask {who}." false (some "system")).1
        (Msgs.post db t "swarm" who s!"{n} edited your locked path {p}." false (some "system")).1
  -- a lock is released once the holder's work on it lands (it matched, and no longer does)
  let db := db.locks.foldl (init := db) fun db lk =>
    match lk.agent.bind (fun n => snaps.lookup n) with
    | none => db
    | some s =>
      let hit := s.files.any (Locks.covers · lk.path)
      let seen := lk.seen.any (· != 0)
      if hit && !seen then { db with locks := db.locks.map fun (l : Lock) => if l.path == lk.path then { l with seen := some 1 } else l }
      else if !hit && seen then
        ({ db with locks := db.locks.filter fun (l : Lock) => l.path != lk.path }).log t lk.agent "unlock" (some lk.path) (some "landed")
      else db
  db

/-- The conflict tick (conflict.conflict_tick): snapshots each live agent's worktree (`wts`: agent and worktree,
by name), trial-merges every pair working for one base whose changed files meet, notices both of a new real conflict,
flags edits to a peer's lock, and releases a lock once its holder's work on it has landed. `baseFor` is
bases.base_for of the base column of the task an agent holds (none: it holds none, or the column is NULL). -/
def conflictTick [Store m] (wts : List (String × String)) (baseFor : Option String → m String) (t : Int) : m Unit := do
  let wtOf (n : String) : String := (wts.lookup n).getD ""
  let db0 ← Store.txn [.task] fun db => (db, db)
  let mut snaps : List (String × Snap) := []
  let mut bywt : List (String × Option Snap) := []
  let mut shas : List (String × Option String) := []
  let mut basesOf : List (String × Option String) := []
  let mut bnames : List (String × String) := []
  for (n, w) in wts do
    let held := (db0.tasks.filter fun x => x.owner == some n && (x.state = .claimed || x.state = .blocked)).mergeSort
      (·.id ≤ ·.id) |>.head? |>.bind (·.base)
    let bn ← baseFor held
    let base ← match shas.lookup bn with
      | some b => pure b
      | none => do let b ← baseSha bn; shas := (bn, b) :: shas; pure b
    basesOf := (n, base) :: basesOf
    bnames := (n, bn) :: bnames
    let s ← match bywt.lookup w with
      | some s => pure s
      | none => do let s ← snapshot w base; bywt := (w, s) :: bywt; pure s
    if let some s := s then
      snaps := snaps ++ [(n, s)]
      Store.txn [.agent] fun db => (db.setAgent n ({ · with snap := some s.json }), ())
  let names := snaps.map (·.1)
  let snapOf (n : String) : Snap := (snaps.lookup n).getD default
  let mut cand : List (String × String) := []
  for (a, i) in names.zipIdx do
    for b in names.drop (i + 1) do
      if wtOf a != wtOf b && bnames.lookup a == bnames.lookup b && (snapOf b).files.any (snapOf a).files.contains then
        cand := cand ++ [(a, b)]
  let db ← Store.txn [.conflict, .pairkey] fun db =>
    let db := { db with conflicts := db.conflicts.filter fun r => cand.contains (r.a, r.b) }
    (db, db)
  -- the git work for each candidate pair whose key changed: none (stale), some none (git failed), some (some merge)
  let mut ontos : List (String × Option String) := []
  let mut work : List (String × String × String × Option (Option (List (String × List (String × String)) × Bool))) := []
  for (a, b) in cand do
    let base := (basesOf.lookup a).join.getD ""
    let key := (snapOf a).tree ++ (snapOf b).tree ++ base
    if (db.pairkeys.find? fun r => r.a == a && r.b == b).bind (·.key) == some key then continue
    for n in [a, b] do
      if (ontos.lookup n).isNone then ontos := (n, ← onto (wtOf n) base (snapOf n).commit) :: ontos
    match (ontos.lookup a).join, (ontos.lookup b).join with
    | some oa, some ob => work := work ++ [(a, b, key, some (← trialMerge (wtOf a) base oa ob))]
    | _, _ => work := work ++ [(a, b, key, none)]
  -- the line ranges of each new real conflict, from each side's snapshot
  let mut ranges : List ((String × String × String) × String × String) := []
  for (a, b, _, r) in work do
    let some (some (real, _)) := r | continue
    for (p, hs) in real do
      if db.conflicts.any fun c => c.a == a && c.b == b && c.path == p then continue
      let rng (n : String) (side : (String × String) → String) : m String := do
        let mut l := []
        for h in hs do l := l ++ [← lineRange (wtOf n) (snapOf n).commit p (side h)]
        return ", ".intercalate (uniqSorted l)
      ranges := ranges ++ [((a, b, p), ← rng a (·.1), ← rng b (·.2))]
  Store.txn [.conflict, .pairkey, .task, .lock, .agent, .event] fun db => (tickApply wts snaps work ranges t db, ())

end SwarmLean.Conflict
