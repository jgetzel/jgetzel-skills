import SwarmLean.Proofs.Watchd
import Std.Tactic.Do
import Lean

set_option linter.deprecated.syntax false
-- the code's string functions on literals: vcgen must not evaluate them
attribute [local irreducible] String.startsWith String.drop SwarmLean.splitlines SwarmLean.strip String.splitOn String.intercalate SwarmLean.joinPath

namespace SwarmLean.SweepProofs
open Std.Do

variable {M : Tools}

@[simp] theorem withEnv_nil (argv : List String) : withEnv [] argv = argv := rfl

abbrev PS (M : Tools) := PostShape.except Exit (.arg (Rec M) .pure)

theorem go_spec (x : RecM M α) (Q : PostCond α (PS M)) :
    ⦃fun s => match Rec.go x s with | (.ok a, s') => Q.1 a s' | (.error e, s') => Q.2.1 e s'⦄ x ⦃Q⦄ := by
  intro s
  simp only [Rec.go, WP.wp, PredTrans.pushExcept, PredTrans.pushArg, PredTrans.apply, ExceptT.run, StateT.run]
  split <;> rename_i h <;> simp [h] <;> exact id

end SwarmLean.SweepProofs

namespace SwarmLean.SweepProofs
open Std.Do
variable {M : Tools}

@[spec] theorem cmd_spec {argv : List String} {cwd : Option String} {ans : M.World → α} {Q : PostCond α (PS M)} :
    ⦃fun s => Q.1 (ans s.w) { s with w := M.after s.w argv cwd, log := s.log ++ [(s.w, .cmd argv cwd)] }⦄
      (Rec.cmd argv cwd ans : RecM M α) ⦃Q⦄ := by mvcgen [Rec.cmd]
@[spec] theorem eff_spec {e : Eff} {ans : M.World → α} {Q : PostCond α (PS M)} :
    ⦃fun s => Q.1 (ans s.w) { s with w := M.effect s.w e, log := s.log ++ [(s.w, .eff e)] }⦄
      (Rec.eff e ans : RecM M α) ⦃Q⦄ := by mvcgen [Rec.eff]
@[spec] theorem ask_spec {f : M.World → α} {Q : PostCond α (PS M)} :
    ⦃fun s => Q.1 (f s.w) s⦄ (Rec.ask f : RecM M α) ⦃Q⦄ := by mvcgen [Rec.ask]

/-- What `x` answers from state `s` when it does not throw (`default` when it does). -/
@[irreducible] def Rec.val [Inhabited α] (x : RecM M α) (s : Rec M) : α := match (Rec.go x s).1 with | .ok a => a | .error _ => default

/-- `x` never ends early, from any state. -/
def NoThrow (x : RecM M α) : Prop := ∀ s, ∃ a, (Rec.go x s).1 = .ok a

theorem noThrow_of (h : ⦃fun _ => ⌜True⌝⦄ x ⦃⇓ _ => ⌜True⌝⦄) : NoThrow (M := M) x := by
  intro s
  have := h s trivial
  simp only [WP.wp, PredTrans.pushExcept, PredTrans.pushArg, PredTrans.apply, ExceptT.run, StateT.run] at this
  unfold Rec.go ExceptT.run StateT.run
  revert this
  rcases e : x s with ⟨r, s'⟩
  cases r <;> simp [Id.run, ExceptConds.false]
  exact id

theorem go_val [Inhabited α] {x : RecM M α} (h : NoThrow x) (s : Rec M) : (Rec.go x s).1 = .ok (Rec.val x s) := by
  obtain ⟨a, ha⟩ := h s; simp [Rec.val, ha]

theorem val_spec [Inhabited α] {x : RecM M α} (h : NoThrow x) (Q : PostCond α (PS M)) :
    ⦃fun s => Q.1 (Rec.val x s) (Rec.go x s).2⦄ x ⦃Q⦄ := by
  intro s
  have hv := go_val h s
  simp only [Rec.go, ExceptT.run, StateT.run] at hv
  simp only [WP.wp, PredTrans.pushExcept, PredTrans.pushArg, PredTrans.apply, ExceptT.run, StateT.run, Rec.go]
  rcases e : x s with ⟨r, s'⟩
  rw [e] at hv; simp only at hv; subst hv
  simp [Id.run]
  exact id

end SwarmLean.SweepProofs

namespace SwarmLean.SweepProofs
open Std.Do
variable {M : Tools}

/-- What the code unfolds to on the recording world. -/
macro "rec_unfold" : tactic => `(tactic| mvcgen [Lifecycle.landed, Lifecycle.landedRef, Lifecycle.landedRef1,
  Lifecycle.run, Lifecycle.code, Proc.output, Sys.kind, Git.git, Sys.realpath, Watchd.real, Workspaces.real])



/-- A call that removes a worktree or deletes a branch. -/
def Bad : Call → Prop
  | .cmd ["git", "-C", _, "worktree", "remove", _] none => True
  | .cmd ["git", "-C", _, "branch", "-d", _] none => True
  | .cmd ["git", "-C", _, "update-ref", "-d", _, _] none => True
  | _ => False

/-- Log `l'` is `L` and then calls none of which removes a worktree or deletes a branch. -/
def Grows (L l' : List (M.World × Call)) : Prop := ∃ l, l' = L ++ l ∧ ∀ e ∈ l, ¬ Bad e.2

theorem Grows.refl (L : List (M.World × Call)) : Grows L L := ⟨[], by simp, by simp⟩
theorem Grows.trans {L l1 l2 : List (M.World × Call)} (h1 : Grows L l1) (h2 : Grows l1 l2) : Grows L l2 := by
  obtain ⟨a, rfl, ha⟩ := h1; obtain ⟨b, rfl, hb⟩ := h2
  refine ⟨a ++ b, by simp, ?_⟩
  simp only [List.mem_append]
  rintro x (h | h)
  · exact ha x h
  · exact hb x h
theorem Grows.snoc {L l : List (M.World × Call)} {e : M.World × Call} (h : Grows L l) (he : ¬ Bad e.2) :
    Grows L (l ++ [e]) := h.trans ⟨[e], rfl, by simpa⟩
theorem Grows.prefix {L l : List (M.World × Call)} (h : Grows L l) : L <+: l := by
  obtain ⟨a, rfl, _⟩ := h; exact List.prefix_append _ _

/-- `x`'s answer from state `s`, and the log it left grows `s`'s: what a sub-call's specification says. -/
def Ext [Inhabited α] (x : RecM M α) : Prop := ∀ s, (Rec.go x s).1 = .ok (Rec.val x s) ∧ Grows s.log (Rec.go x s).2.log

theorem ext_of [Inhabited α] {x : RecM M α}
    (h : ∀ L, ⦃fun s => ⌜Grows L s.log⌝⦄ x ⦃⇓ _ s => ⌜Grows L s.log⌝⦄) : Ext x := by
  intro s0
  have := h s0.log s0 (Grows.refl _)
  simp only [WP.wp, PredTrans.pushExcept, PredTrans.pushArg, PredTrans.apply, ExceptT.run, StateT.run] at this
  unfold Rec.val Rec.go ExceptT.run StateT.run
  revert this
  rcases e : x s0 with ⟨r, s'⟩
  cases r <;> simp [Id.run, ExceptConds.false] <;> exact id

theorem Ext.nt [Inhabited α] {x : RecM M α} (h : Ext x) : NoThrow x := fun s => ⟨_, (h s).1⟩

theorem Grows.go [Inhabited α] {x : RecM M α} {L : List (M.World × Call)} {s : Rec M} (hx : Ext x) (h : Grows L s.log) :
    Grows L (Rec.go x s).2.log := h.trans (hx s).2

set_option maxHeartbeats 1000000 in
theorem landedRef1_nt : NoThrow (Lifecycle.landedRef1 cwd ref b : RecM M Bool) := noThrow_of (by
  mvcgen [Lifecycle.landedRef1, Lifecycle.run, Lifecycle.code, Proc.output])

/-- What `git` answered, mapped: a read logged. -/
theorem git_map_ext [Inhabited β] {g : Option String → β} {args : List String} {cwd : Option String} :
    Ext (g <$> (Git.git args cwd : RecM M (Option String))) := ext_of fun L => by
  mvcgen -trivial [Git.git]
  all_goals (try mleave)
  exact Grows.snoc ‹_› (by simp [Bad])

/-- Closes `Grows L (L ++ [c₁] ++ … )` for calls none of which is `Bad`. -/
macro "grow0" : tactic => `(tactic| (
  subst_vars
  try simp only [List.map_nil, withEnv_nil] at *
  repeat (any_goals (first | exact Grows.refl _ | assumption | apply Grows.snoc | apply Grows.go))
  all_goals (try simp [Bad])))

/-- Closes `Ext` of a lambda the sweep maps over a list. -/
macro "ext_lam" : tactic => `(tactic| (
  apply ext_of
  intro L
  mvcgen -trivial [Watchd.real, Workspaces.real, Sys.realpath, Watchd.git, Git.git]
  all_goals first | exact ⇓ _ s => ⌜Grows L s.log⌝ | skip
  all_goals (try mleave)
  all_goals grow0))

/-- `grow0`, and the `Ext` of a `mapM` over a lambda. -/
macro "grow" : tactic => `(tactic| (
  grow0
  all_goals (try (apply mapM_ext; intro; first | exact git_map_ext | ext_lam))))

/-- Closes a vcgen's goals for `ext_of`: each loop keeps the log growing, each call is not `Bad`. -/
macro "ext_close" L:term : tactic => `(tactic| (
  all_goals first | exact ⇓ _ s => ⌜Grows $L s.log⌝ | skip
  all_goals (try mleave)
  all_goals grow0))

@[simp] theorem landedRef1_ext : Ext (Lifecycle.landedRef1 cwd ref b : RecM M Bool) := ext_of fun L => by
  mvcgen -trivial [Lifecycle.landedRef1, Lifecycle.run, Lifecycle.code, Proc.output]
  ext_close L

@[spec] theorem landedRef1_spec {Q : PostCond Bool (PS M)} :
    ⦃fun s => Q.1 (Rec.val (Lifecycle.landedRef1 cwd ref b) s) (Rec.go (Lifecycle.landedRef1 cwd ref b) s).2⦄
      (Lifecycle.landedRef1 cwd ref b : RecM M Bool) ⦃Q⦄ := val_spec landedRef1_ext.nt Q

@[simp] theorem landed_ext : Ext (Lifecycle.landed wt bs main : RecM M Bool) := ext_of fun L => by
  mvcgen -trivial [Lifecycle.landed, Lifecycle.landedRef, Lifecycle.run, Proc.output, Sys.kind]
  ext_close L

theorem mapM_ext [Inhabited β] {f : α → RecM M β} {xs : List α} (h : ∀ a, Ext (f a)) : Ext (xs.mapM f) := ext_of fun L => by
  induction xs with
  | nil => simp only [List.mapM_nil]; mvcgen
  | cons a as ih =>
    simp only [List.mapM_cons]
    have hs : ∀ Q, ⦃fun s => Q.1 (Rec.val (f a) s) (Rec.go (f a) s).2⦄ f a ⦃Q⦄ := fun Q => val_spec (h a).nt Q
    mvcgen [hs, ih]
    exact Grows.go (h a) ‹_›

@[spec] theorem mapM_val_spec [Inhabited β] {f : α → RecM M β} {xs : List α} (h : ∀ a, Ext (f a)) {Q : PostCond (List β) (PS M)} :
    ⦃fun s => Q.1 (Rec.val (xs.mapM f) s) (Rec.go (xs.mapM f) s).2⦄ xs.mapM f ⦃Q⦄ := val_spec (mapM_ext h).nt Q

@[simp] theorem baseFor_ext : Ext (Bases.baseFor b cwd : RecM M _) := ext_of fun L => by
  mvcgen -trivial [Bases.baseFor, Bases.default, Git.git, Fs.read]
  ext_close L

theorem go_bind (x : RecM M α) (f : α → RecM M β) (s : Rec M) :
    Rec.go (x >>= f) s = match Rec.go x s with | (.ok a, s') => Rec.go (f a) s' | (.error e, s') => (.error e, s') := by
  unfold Rec.go
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.bindCont, ExceptT.run, StateT.run, StateT.bind]
  rcases x s with ⟨r, s'⟩; cases r <;> rfl

theorem go_pure (a : α) (s : Rec M) : Rec.go (pure a : RecM M α) s = (.ok a, s) := by unfold Rec.go; rfl

theorem git_go (args : List String) (cwd : Option String) (s : Rec M) : Rec.go (Git.git args cwd : RecM M _) s =
    (.ok (M.git s.w args cwd), { s with log := s.log ++ [(s.w, .git args cwd)] }) := by unfold Rec.go; rfl
theorem ask_go (f : M.World → α) (s : Rec M) : Rec.go (Rec.ask f : RecM M _) s = (.ok (f s.w), s) := by unfold Rec.go; rfl

@[simp] theorem default_ext : Ext (Bases.default cwd : RecM M _) := ext_of fun L => by
  mvcgen -trivial [Bases.default, Git.git, Fs.read]
  ext_close L

@[spec] theorem default_spec {Q : PostCond _ (PS M)} :
    ⦃fun s => Q.1 (Rec.val (Bases.default cwd) s) (Rec.go (Bases.default cwd) s).2⦄ (Bases.default cwd : RecM M _) ⦃Q⦄ :=
  val_spec default_ext.nt Q

@[simp] theorem ref_ext : Ext (Bases.ref b cwd : RecM M _) := ext_of fun L => by
  mvcgen -trivial [Bases.ref, Bases.remoteRef, Git.git]
  ext_close L

@[simp] theorem cwds_ext : Ext (Machine.cwds : RecM M _) := ext_of fun L => by
  mvcgen -trivial [Machine.cwds, Machine.osName, Machine.procRoot, Proc.output, Env.var, Fs.list, Sys.readlink]
  ext_close L

@[simp] theorem worktrees_ext : Ext (Workspaces.worktrees : RecM M _) := ext_of fun L => by
  mvcgen -trivial [Workspaces.worktrees, Workspaces.real, Git.git, Sys.realpath]
  ext_close L

@[simp] theorem protectedOf_ext : Ext (Workspaces.protectedOf db cwd : RecM M _) := ext_of fun L => by
  mvcgen -trivial [Workspaces.protectedOf, Bases.protectedBases]
  ext_close L
  all_goals exact mapM_ext fun _ => by simp

@[simp] theorem refs_ext : Ext (Bases.refs ns cwd : RecM M _) := ext_of fun L => by
  mvcgen -trivial [Bases.refs]
  ext_close L
  all_goals exact mapM_ext fun _ => by simp

@[simp] theorem cleanRemote_ext : Ext (Run.cleanRemote wt : RecM M _) := ext_of fun L => by
  mvcgen -trivial [Run.cleanRemote, Proc.output, Store.txn, Clock.now]
  ext_close L

@[spec] theorem landed_spec {Q : PostCond Bool (PS M)} :
    ⦃fun s => Q.1 (Rec.val (Lifecycle.landed wt bs main) s) (Rec.go (Lifecycle.landed wt bs main) s).2⦄
      (Lifecycle.landed wt bs main : RecM M Bool) ⦃Q⦄ := val_spec landed_ext.nt Q
@[spec] theorem cwds_spec {Q : PostCond _ (PS M)} :
    ⦃fun s => Q.1 (Rec.val Machine.cwds s) (Rec.go Machine.cwds s).2⦄ (Machine.cwds : RecM M _) ⦃Q⦄ :=
  val_spec cwds_ext.nt Q
@[spec] theorem worktrees_spec {Q : PostCond _ (PS M)} :
    ⦃fun s => Q.1 (Rec.val Workspaces.worktrees s) (Rec.go Workspaces.worktrees s).2⦄
      (Workspaces.worktrees : RecM M _) ⦃Q⦄ := val_spec worktrees_ext.nt Q
@[spec] theorem protectedOf_spec {Q : PostCond _ (PS M)} :
    ⦃fun s => Q.1 (Rec.val (Workspaces.protectedOf db cwd) s) (Rec.go (Workspaces.protectedOf db cwd) s).2⦄
      (Workspaces.protectedOf db cwd : RecM M _) ⦃Q⦄ := val_spec protectedOf_ext.nt Q
@[spec] theorem refs_spec {Q : PostCond _ (PS M)} :
    ⦃fun s => Q.1 (Rec.val (Bases.refs ns cwd) s) (Rec.go (Bases.refs ns cwd) s).2⦄ (Bases.refs ns cwd : RecM M _) ⦃Q⦄ :=
  val_spec refs_ext.nt Q
@[spec] theorem cleanRemote_spec {Q : PostCond _ (PS M)} :
    ⦃fun s => Q.1 (Rec.val (Run.cleanRemote wt) s) (Rec.go (Run.cleanRemote wt) s).2⦄ (Run.cleanRemote wt : RecM M _) ⦃Q⦄ :=
  val_spec cleanRemote_ext.nt Q

/-! ## Reads -/

/-- `x` only reads: from any state it answers `g` of the machine and leaves the state as it was. -/
def Reads (x : RecM M α) (g : M.World → α) : Prop := ∀ s, Rec.go x s = (.ok (g s.w), s)

theorem Reads.ext [Inhabited α] {x : RecM M α} {g : M.World → α} (h : Reads x g) : Ext x := fun s => by
  have := h s; refine ⟨?_, ?_⟩
  · unfold Rec.val; rw [this]
  · rw [this]; exact Grows.refl _

theorem Reads.val [Inhabited α] {x : RecM M α} {g : M.World → α} (h : Reads x g) (s : Rec M) : Rec.val x s = g s.w := by
  unfold Rec.val; rw [h s]

theorem Reads.go {x : RecM M α} {g : M.World → α} (h : Reads x g) (s : Rec M) : (Rec.go x s).2 = s := by rw [h s]

theorem real_reads (p : String) : Reads (Watchd.real p : RecM M String) fun w => (M.realpath w p).getD p := fun s => by
  simp only [Watchd.real, Workspaces.real, Sys.realpath, Rec.ask, go_bind]
  unfold Rec.go; rfl

theorem mapM_reads {f : α → RecM M β} {g : M.World → α → β} (hf : ∀ a, Reads (f a) (g · a)) (xs : List α) :
    Reads (xs.mapM f) fun w => xs.map (g w) := by
  induction xs with
  | nil => intro s; simp only [List.mapM_nil, go_pure, List.map_nil]
  | cons a as ih => intro s; simp only [List.mapM_cons, go_bind, hf a s, ih s, go_pure, List.map_cons]

/-! ## Branches: `deleteBranch` -/

/-- `git -C main worktree remove wt`. -/
def rmArgv (main wt : String) : List String := ["git", "-C", main, "worktree", "remove", wt]

/-- A call that removes a worktree. -/
def IsRm (c : Call) : Prop := ∃ m x, c = .cmd (rmArgv m x) none

theorem not_rm_of_not_bad {c : Call} (h : ¬ Bad c) : ¬ IsRm c := by
  rintro ⟨m, x, rfl⟩; exact h trivial

/-- What deleteBranch may run: `branch -d b` or `update-ref -d refs/heads/b k`, `b` none of `prot` nor master. -/
def BranchCall (main : String) (prot : List String) (b k : String) (c : Call) : Prop :=
  b ∉ prot ∧ b ≠ "master" ∧
    (c = .cmd ["git", "-C", main, "branch", "-d", b] none ∨
      c = .cmd ["git", "-C", main, "update-ref", "-d", "refs/heads/" ++ b, k] none)

/-- The log grew by calls none of which removes a worktree, each `Bad` one a `BranchCall`. -/
def DelGrows (main : String) (prot : List String) (br tip : Option String) (L l' : List (M.World × Call)) : Prop :=
  ∃ l, l' = L ++ l ∧ ∀ e ∈ l, ¬ IsRm e.2 ∧ (Bad e.2 → ∃ b k, br = some b ∧ tip = some k ∧ BranchCall main prot b k e.2)

theorem DelGrows.refl (L : List (M.World × Call)) : DelGrows main prot br tip L L := ⟨[], by simp, by simp⟩
theorem DelGrows.snoc {L l : List (M.World × Call)} {e : M.World × Call} (h : DelGrows main prot br tip L l)
    (he : ¬ IsRm e.2 ∧ (Bad e.2 → ∃ b k, br = some b ∧ tip = some k ∧ BranchCall main prot b k e.2)) :
    DelGrows main prot br tip L (l ++ [e]) := by
  obtain ⟨a, rfl, ha⟩ := h
  refine ⟨a ++ [e], by simp, fun x hx => ?_⟩
  rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · simp at h; subst h; exact he

theorem deleteBranch_ext (s : Rec M) :
    (Rec.go (Watchd.deleteBranch main br tip prot) s).1 = .ok () ∧
      DelGrows main prot br tip s.log (Rec.go (Watchd.deleteBranch main br tip prot) s).2.log := by
  have h : ⦃fun s' => ⌜s' = s⌝⦄ (Watchd.deleteBranch main br tip prot : RecM M Unit)
      ⦃⇓ _ s' => ⌜DelGrows main prot br tip s.log s'.log⌝⦄ := by
    mvcgen -trivial [Watchd.deleteBranch, Lifecycle.code, Proc.output, discard, Functor.mapConst]
    all_goals (try mleave)
    all_goals ((try simp only [withEnv_nil, List.map_nil, Prod.mk.injEq] at *); subst_vars; (try obtain ⟨rfl, rfl⟩ := ‹br = _ ∧ tip = _›))
    all_goals (repeat (any_goals (first | exact DelGrows.refl _ | apply DelGrows.snoc)))
    all_goals simp_all [IsRm, rmArgv, BranchCall, Bad]
  have := h s rfl
  simp only [WP.wp, PredTrans.pushExcept, PredTrans.pushArg, PredTrans.apply, ExceptT.run, StateT.run] at this
  unfold Rec.go ExceptT.run StateT.run
  revert this
  rcases e : (Watchd.deleteBranch main br tip prot : RecM M Unit) s with ⟨r, s'⟩
  cases r <;> simp [Id.run, ExceptConds.false] <;> exact id

@[spec] theorem deleteBranch_spec {Q : PostCond Unit (PS M)} :
    ⦃fun s => Q.1 () (Rec.go (Watchd.deleteBranch main br tip prot) s).2⦄ (Watchd.deleteBranch main br tip prot : RecM M Unit) ⦃Q⦄ := by
  have := go_spec (Watchd.deleteBranch main br tip prot : RecM M Unit) Q
  intro s h; apply this
  have e := (deleteBranch_ext (main := main) (br := br) (tip := tip) (prot := prot) s).1
  revert h; rcases hg : Rec.go (Watchd.deleteBranch main br tip prot : RecM M Unit) s with ⟨r, s'⟩
  rw [hg] at e; simp only at e; subst e; simp only [hg]; exact id

/-! ## The sweep -/

theorem mem_go [Inhabited α] {x : RecM M α} (hx : Ext x) {s : Rec M} {e : M.World × Call} (h : e ∈ s.log) :
    e ∈ (Rec.go x s).2.log := (hx s).2.prefix.subset h
theorem prefix_go [Inhabited α] {x : RecM M α} (hx : Ext x) (s : Rec M) : s.log <+: (Rec.go x s).2.log := (hx s).2.prefix

/-- `p` as `Watchd.real` reads it on machine `w`. -/
def realW (w : M.World) (p : String) : String := (M.realpath w p).getD p

/-- `git worktree list --porcelain`, the sweep's first command. -/
def lsArgv : List String := ["git", "worktree", "list", "--porcelain"]

/-- The lines of what the sweep's `git worktree list` printed, run on machine `w`. -/
def lsLines (w : M.World) : List String :=
  splitlines (((M.out w lsArgv none).bind fun o => if o.code == 0 then some o.stdout else none).getD "")

/-- The later mtime of `wt` and of its git dir's logs/HEAD, `gd` what `rev-parse --absolute-git-dir` printed: the
sweep's "last touched", read on machine `w`. -/
def lastAt (w : M.World) (wt : String) (gd : Option String) : Int :=
  max (max 0 ((M.mtime w wt).getD 0)) ((M.mtime w (joinPath (joinPath ((py (gd.map strip)).getD wt) "logs") "HEAD")).getD 0)

/-- What the sweep, run from state `s0`, checked of worktree `x` of the main checkout `m` before removing it, `L` the
calls it made before: `x` is listed (the realpath of a `worktree` line of the `git worktree list` it ran first, `m`
the first such line's), not the main checkout, used by no live agent of the db (realpaths read on one machine `w`), no process sat in it when
`Machine.cwds` read, untouched for `SWEEP_IDLE` and `status` clean (both read on one machine `wk`), and `landed` found
it landed on the refs of the protected bases. -/
structure Gate (s0 : Rec M) (m x : String) (L : List (M.World × Call)) : Prop where
  main : ∃ first, (lsLines s0.w).head? = some first ∧ m = realW (M.after s0.w lsArgv none) (first.drop 9).toString
  notMain : x ≠ m
  listed : ∃ e ∈ Watchd.wtLines (lsLines s0.w).tail, ∃ w : M.World, x = realW w e.1
  unused : ∃ w : M.World, ∀ p ∈ ((Agents.live s0.db).flatMap fun a => [a.wt.getD "", a.cwd.getD ""]).filter (· != ""),
    Watchd.inside (realW w p) x = false
  noProc : ∃ (s : Rec M) (cs : List (Int × String)), s.log <+: L ∧ (Rec.go (Machine.cwds : RecM M _) s).1 = .ok (some cs) ∧
    ∀ c ∈ cs, Watchd.inside (realW (Rec.go (Machine.cwds : RecM M _) s).2.w c.2) x = false
  idle : ∃ wk t, (wk, .git ["-C", x, "rev-parse", "--absolute-git-dir"] none) ∈ L ∧
    (wk, .cmd ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none) ∈ L ∧
    (∃ st, (M.out wk ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none).bind
      (fun o => if o.code == 0 then some o.stdout else none) = some st ∧ strip st = "") ∧
    (∃ st : Rec M, st.log <+: L ∧ t = M.now st.w) ∧
    Watchd.SWEEP_IDLE ≤ t - lastAt wk x (M.git wk ["-C", x, "rev-parse", "--absolute-git-dir"] none)
  landed : ∃ s sp sb : Rec M,
    (Rec.go (Lifecycle.landed x (Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf s0.db (some m) : RecM M _) sp)
      (some m) : RecM M _) sb) (some m) : RecM M Bool) s).2.log <+: L ∧
    (Rec.go (Lifecycle.landed x (Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf s0.db (some m) : RecM M _) sp)
      (some m) : RecM M _) sb) (some m) : RecM M Bool) s).1 = .ok true

/-- Every worktree removal at or after index `n` of log `l` passed `G` on the calls before it. -/
def GoodFrom (n : Nat) (G : String → String → List (M.World × Call) → Prop) (l : List (M.World × Call)) : Prop :=
  ∀ i w m x, n ≤ i → l[i]? = some (w, .cmd (rmArgv m x) none) → G m x (l.take i)

theorem GoodFrom.base (G : String → String → List (M.World × Call) → Prop) (l : List (M.World × Call)) :
    GoodFrom l.length G l := fun i _ _ _ hi h => by simp [List.getElem?_eq_none hi] at h

theorem GoodFrom.append {n : Nat} {G : String → String → List (M.World × Call) → Prop} {l l' : List (M.World × Call)}
    (h : GoodFrom n G l) (hl : ∀ e ∈ l', ¬ IsRm e.2) : GoodFrom n G (l ++ l') := by
  intro i w m x hi he
  by_cases hil : i < l.length
  · rw [List.getElem?_append_left hil] at he
    rw [List.take_append_of_le_length (Nat.le_of_lt hil)]
    exact h i w m x hi he
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hil)] at he
    exact absurd ⟨m, x, rfl⟩ (hl _ (List.mem_of_getElem? he))

theorem GoodFrom.snoc {n : Nat} {G : String → String → List (M.World × Call) → Prop} {l : List (M.World × Call)}
    {e : M.World × Call} (h : GoodFrom n G l) (he : ¬ IsRm e.2) : GoodFrom n G (l ++ [e]) :=
  h.append (by simpa using he)

theorem GoodFrom.rm {n : Nat} {G : String → String → List (M.World × Call) → Prop} {l : List (M.World × Call)}
    {w : M.World} {m x : String} (h : GoodFrom n G l) (hg : G m x l) :
    GoodFrom n G (l ++ [(w, .cmd (rmArgv m x) none)]) := by
  intro i w' m' x' hi he
  by_cases hil : i < l.length
  · rw [List.getElem?_append_left hil] at he
    rw [List.take_append_of_le_length (Nat.le_of_lt hil)]
    exact h i w' m' x' hi he
  · have hle := Nat.le_of_not_lt hil
    rw [List.getElem?_append_right hle] at he
    have : i - l.length = 0 := by
      cases e : i - l.length with
      | zero => rfl
      | succ k => rw [e] at he; simp at he
    rw [this] at he
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, Call.cmd.injEq, rmArgv] at he
    obtain ⟨-, he, -⟩ := he
    simp only [List.cons.injEq, and_true, true_and] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [show i = l.length by omega, List.take_left]
    exact hg

theorem GoodFrom.go [Inhabited α] {n : Nat} {G : String → String → List (M.World × Call) → Prop} {x : RecM M α}
    {s : Rec M} (hx : Ext x) (h : GoodFrom n G s.log) : GoodFrom n G (Rec.go x s).2.log := by
  obtain ⟨l, e, hl⟩ := (hx s).2
  rw [e]; exact h.append fun e he => not_rm_of_not_bad (hl e he)

theorem GoodFrom.del {n : Nat} {G : String → String → List (M.World × Call) → Prop} {s : Rec M}
    (h : GoodFrom n G s.log) : GoodFrom n G (Rec.go (Watchd.deleteBranch main br tip prot) s).2.log := by
  obtain ⟨l, e, hl⟩ := (deleteBranch_ext s).2
  rw [e]; exact h.append fun e he => (hl e he).1

/-- Closes `GoodFrom n G l` for an `l` that grows a `GoodFrom` log by calls removing no worktree. -/
macro "good" : tactic => `(tactic| (
  simp only [List.map_nil, withEnv_nil] at *
  repeat (any_goals (first | assumption | exact GoodFrom.base _ _ | apply GoodFrom.snoc | apply GoodFrom.del | apply GoodFrom.go))
  all_goals (try simp [IsRm, rmArgv])
  all_goals (try (apply mapM_ext; intro; first | exact git_map_ext | ext_lam))))

theorem not_or4 {a b c d : Bool} (h : ¬((a || b || c) || d) = true) : a = false ∧ c = false ∧ d = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all
theorem not_or3 {a b c : Bool} (h : ¬((a || b) || c) = true) : a = false ∧ b = false ∧ c = false := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- `Gate` from what the sweep's loop body knows when it reaches `worktree remove`: the first line `c`, the listed
entry `cur`, the continue tests, the cwds read from `Sc`, the loop's entry log a prefix of the body's state `s`, the
calls logged since, and `landed`'s answer from `Sl` and the log it left. -/
theorem gate_intro {s0 : Rec M} {c : String} {cur : String × Option String} {L : List (M.World × Call)}
    {f : String × Option String → RecM M (String × Option String)} {S1 : Rec M} {pref suff : List (String × Option String)}
    {g : String → RecM M String} {S2 : Rec M} {rest : List String} {k : Bool}
    {Sc : Rec M} {cw : List (Int × String)} {h : Int × String → RecM M String}
    {s Sl Sp Sb : Rec M} {Lst : List (M.World × Call)}
    (hc : (lsLines s0.w).head? = some c)
    (hl : Rec.val ((Watchd.wtLines (lsLines s0.w).tail).mapM f) S1 = pref ++ cur :: suff)
    (hcw : Rec.val Machine.cwds Sc = some cw)
    (hcont : ¬((cur.1 == realW (M.after s0.w lsArgv none) (c.drop 9).toString || k ||
      (Rec.val ((((Agents.live s0.db).flatMap fun a => [a.wt.getD "", a.cwd.getD ""]).filter (· != "")).mapM g) S2 ++
        rest).any fun y => Watchd.inside y cur.1) ||
      (Rec.val (cw.mapM h) (Rec.go Machine.cwds Sc).2).any fun y => Watchd.inside y cur.1) = true)
    (hpre : (Rec.go (cw.mapM h) (Rec.go Machine.cwds Sc).2).2.log <+: s.log)
    (hidle : ¬((decide (M.now (Rec.go (cw.mapM h) (Rec.go Machine.cwds Sc).2).2.w -
          lastAt s.w cur.1 (M.git s.w ["-C", cur.1, "rev-parse", "--absolute-git-dir"] none) < Watchd.SWEEP_IDLE) ||
        ((M.out s.w ["git", "--no-optional-locks", "-C", cur.1, "status", "--porcelain"] none).bind
          fun o => if o.code == 0 then some o.stdout else none).isNone) ||
      strip (((M.out s.w ["git", "--no-optional-locks", "-C", cur.1, "status", "--porcelain"] none).bind
          fun o => if o.code == 0 then some o.stdout else none).getD "") != "") = true)
    (hland : ¬(!Rec.val (Lifecycle.landed cur.1 (Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf s0.db
      (some (realW (M.after s0.w lsArgv none) (c.drop 9).toString))) Sp)
      (some (realW (M.after s0.w lsArgv none) (c.drop 9).toString))) Sb)
      (some (realW (M.after s0.w lsArgv none) (c.drop 9).toString))) Sl) = true)
    (hf : ∀ a, Reads (f a) fun w => (realW w a.1, a.2))
    (hg : ∀ p, Reads (g p) fun w => realW w p)
    (hh : ∀ c, Reads (h c) fun w => realW w c.2)
    (hgit : Grows (s.log ++ [(s.w, .git ["-C", cur.1, "rev-parse", "--absolute-git-dir"] none)]) L)
    (hst : Grows (Lst ++ [(s.w, .cmd ["git", "--no-optional-locks", "-C", cur.1, "status", "--porcelain"] none)]) L)
    (hsl : Grows (Rec.go (Lifecycle.landed cur.1 (Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf s0.db
      (some (realW (M.after s0.w lsArgv none) (c.drop 9).toString))) Sp)
      (some (realW (M.after s0.w lsArgv none) (c.drop 9).toString))) Sb)
      (some (realW (M.after s0.w lsArgv none) (c.drop 9).toString))) Sl).2.log L) :
    Gate s0 (realW (M.after s0.w lsArgv none) (c.drop 9).toString) cur.1 L := by
  obtain ⟨hm, hu, hp⟩ := not_or4 hcont
  obtain ⟨ht, hn, hs⟩ := not_or3 hidle
  have hsL : s.log <+: L := (List.prefix_append _ _).trans hgit.prefix
  have hE : (Rec.go (cw.mapM h) (Rec.go Machine.cwds Sc).2).2 = (Rec.go Machine.cwds Sc).2 := (mapM_reads hh cw).go _
  refine ⟨⟨c, hc, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hm
  · rw [(mapM_reads hf _).val] at hl
    have : cur ∈ (Watchd.wtLines (lsLines s0.w).tail).map fun a => (realW S1.w a.1, a.2) := by rw [hl]; simp
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 this
    exact ⟨e, he, S1.w, rfl⟩
  · refine ⟨S2.w, fun p hp' => ?_⟩
    rw [(mapM_reads hg _).val] at hu
    have := List.any_eq_false.1 hu (realW S2.w p) (List.mem_append_left _ (List.mem_map_of_mem hp'))
    simpa using this
  · refine ⟨Sc, cw, ?_, by rw [(cwds_ext Sc).1, hcw], fun c' hc' => ?_⟩
    · rw [hE] at hpre; exact (prefix_go cwds_ext Sc).trans (hpre.trans hsL)
    · rw [(mapM_reads hh _).val] at hp
      have := List.any_eq_false.1 hp _ (List.mem_map_of_mem hc')
      simpa using this
  · generalize hO : ((M.out s.w ["git", "--no-optional-locks", "-C", cur.1, "status", "--porcelain"] none).bind
        fun o => if o.code == 0 then some o.stdout else none) = O at hn hs
    cases O with
    | none => simp at hn
    | some st =>
      refine ⟨s.w, _, hgit.prefix.subset (by simp), hst.prefix.subset (by simp), ⟨st, hO, by simpa using hs⟩,
        ⟨_, hpre.trans hsL, rfl⟩, ?_⟩
      simpa using ht
  · exact ⟨Sl, Sp, Sb, hsl.prefix, by rw [(landed_ext Sl).1]; simpa using hland⟩

/-- `exact List.prefix_refl _`, allowed to assign the invariant's `?pre` hole (a goal, so synthetic opaque). -/
elab "pre_refl" : tactic => Lean.Meta.withAssignableSyntheticOpaque do
  Lean.Elab.Tactic.evalTactic (← `(tactic| exact List.prefix_refl _))

theorem pre_snoc {A B : List (M.World × Call)} (l : List (M.World × Call)) (h : A <+: B) : A <+: B ++ l :=
  h.trans (List.prefix_append _ _)
theorem pre_go [Inhabited α] {x : RecM M α} {A : List (M.World × Call)} {s : Rec M} (hx : Ext x) (h : A <+: s.log) :
    A <+: (Rec.go x s).2.log := h.trans (prefix_go hx s)
theorem pre_del {A : List (M.World × Call)} {s : Rec M} (h : A <+: s.log) :
    A <+: (Rec.go (Watchd.deleteBranch main br tip prot) s).2.log := by
  obtain ⟨l, e, -⟩ := (deleteBranch_ext (main := main) (br := br) (tip := tip) (prot := prot) s).2
  rw [e]; exact pre_snoc _ h

/-- Closes `A <+: l` for an `l` that grows, by any calls, a log `A` is a prefix of. -/
macro "pfx" : tactic => `(tactic| (
  try simp only [List.map_nil, withEnv_nil] at *
  repeat (any_goals (first | exact List.prefix_refl _ | assumption | apply pre_snoc | apply pre_del | apply pre_go))
  all_goals (try simp)
  all_goals (try (apply mapM_ext; intro; first | exact git_map_ext | ext_lam))))

/-- From a `worktree remove` VC's `GoodFrom` goal: peel the calls after the removal, then `GoodFrom.rm`. -/
macro "peel" : tactic => `(tactic| (
  repeat (first | apply GoodFrom.del | (refine GoodFrom.go (by simp) ?_) | (apply GoodFrom.snoc; simp [IsRm, rmArgv]; done))
  apply GoodFrom.rm))

set_option hygiene false in
/-- Closes `Gate s0 m x L` in a `worktree remove` VC through `gate_intro`. -/
macro "gate" : tactic => `(tactic| (
  apply gate_intro
  case hc => assumption
  case hl => assumption
  case hcw => assumption
  case hcont => assumption
  case hpre => assumption
  case hidle => assumption
  case hland => assumption
  case hf | hg | hh => intro a s; simp only [go_bind, ask_go, go_pure, realW]
  case hgit | hst | hsl => grow0; all_goals (apply mapM_ext; intro; exact git_map_ext)))

/-- Splits the first hypothesis that unfolds to a conjunction (the loop invariant). -/
elab "split_inv" : tactic => Lean.Elab.Tactic.liftMetaTactic fun g => g.withContext do
  for d in ← Lean.getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    let ty ← Lean.Meta.whnfD d.type
    if ty.isAppOfArity ``And 2 then
      let g ← g.replaceLocalDeclDefEq d.fvarId ty
      return (← g.cases d.fvarId).toList.map (·.mvarId)
  throwError "split_inv: no conjunction"

/-- A step VC of the sweep's loop: the invariant (`GoodFrom`, the entry log a prefix) carries over. -/
macro "step" : tactic => `(tactic| (
  subst_vars
  try simp only [id, PostCond.noThrow] at *
  try split_inv
  first | (good; done) | (refine ⟨?_, ?_⟩ <;> first | (good; done) | (pfx; done))))

set_option hygiene false in
/-- The sweep's VCs on the recording world, the invariant `GoodFrom` and the loop's entry log a prefix. -/
macro "sweep_vcs" : tactic => `(tactic| (
  mvcgen -trivial [Watchd.sweep, Lifecycle.run, Lifecycle.code, Watchd.real, Workspaces.real, Watchd.git, Proc.output,
    Sys.realpath, Sys.kind, Sys.mtime, Store.txn, Clock.now, Git.git]
  case' inv1 => refine (fun (pre : List (M.World × Call)) => ⇓ _ s => ⌜GoodFrom s0.log.length (Gate s0) s.log ∧ pre <+: s.log⌝) ?pre
  all_goals (try mleave)
  case vc1 | vc2 | vc3 | vc6 => intro; ext_lam
  case vc15 =>
    refine ⟨?_, ?p⟩
    case p => pre_refl
    subst_vars; (try simp only [id, PostCond.noThrow] at *); good
  case vc9 | vc10 | vc11 | vc12 =>
    subst_vars
    split_inv
    refine ⟨?_, by pfx⟩
    peel
    · good
    · gate
  all_goals step))

set_option maxHeartbeats 1000000 in
/-- W1 on the code: every `git worktree remove` the sweep runs passed `Gate` on the calls before it. -/
theorem sweep_W1 (s0 : Rec M) (comms : Option String) (dry : Bool) (nl : List String) :
    ⦃fun s => ⌜s = s0⌝⦄ (Watchd.sweep comms dry nl : RecM M _) ⦃⇓ _ s => ⌜GoodFrom s0.log.length (Gate s0) s.log⌝⦄ := by
  cases comms <;> sweep_vcs

/-! ## On the machines the checks read -/

theorem mem_modify {l : List α} {i : Nat} {f : α → α} {e : α} (h : e ∈ l.modify i f) : e ∈ l ∨ ∃ y ∈ l, e = f y := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_modify] at hj
  cases hy : l[j]? with
  | none => simp [hy] at hj
  | some y =>
    have hm : y ∈ l := List.mem_iff_getElem?.2 ⟨j, hy⟩
    simp only [hy, Option.map_eq_map, Option.map_some, Option.some.injEq] at hj
    split at hj
    · exact .inr ⟨y, hm, hj.symm⟩
    · exact .inl (hj ▸ hm)

/-- A path `Watchd.wtLines` reads is on a `worktree <path>` line. -/
theorem wtLines_mem {ls : List String} {e : String × Option String} (h : e ∈ Watchd.wtLines ls) :
    ∃ l ∈ ls, l.startsWith "worktree " = true ∧ e.1 = (l.drop 9).toString := by
  unfold Watchd.wtLines at h
  have key : ∀ (xs : List String) (acc : Array (String × Option String)), (∀ l ∈ xs, l ∈ ls) →
      (∀ e ∈ acc.toList, ∃ l ∈ ls, l.startsWith "worktree " = true ∧ e.1 = (l.drop 9).toString) →
      ∀ e ∈ (xs.foldl (fun (wts : Array (String × Option String)) l =>
        if l.startsWith "worktree " then wts.push ((l.drop 9).toString, none)
        else if l.startsWith "branch refs/heads/" && !wts.isEmpty then
          wts.modify (wts.size - 1) fun (p, _) => (p, some (l.drop 18).toString)
        else wts) acc).toList, ∃ l ∈ ls, l.startsWith "worktree " = true ∧ e.1 = (l.drop 9).toString := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; simpa using hacc
    | cons l xs ih =>
      intro acc hxs hacc
      simp only [List.foldl_cons]
      apply ih _ (fun l' hl' => hxs l' (List.mem_cons_of_mem _ hl'))
      split
      · simp only [Array.toList_push, List.mem_append, List.mem_singleton]
        rintro e (he | rfl)
        · exact hacc e he
        · exact ⟨l, hxs l List.mem_cons_self, ‹_›, rfl⟩
      · split
        · rw [Array.toList_modify]
          intro e he
          rcases mem_modify he with he | ⟨y, hy, rfl⟩
          · exact hacc e he
          · obtain ⟨l', hl', hw, hy1⟩ := hacc y hy
            exact ⟨l', hl', hw, by rw [← hy1]⟩
        · exact hacc
  exact key ls #[] (fun _ h => h) (by simp) e h

/-- `gh pr list --head br --state merged …`, landedRef1's last check. -/
def ghArgv (br : String) : List String :=
  ["gh", "pr", "list", "--head", br, "--state", "merged", "--json", "number,headRefOid"]

/-- landedRef1 answering true: a machine it ran a command on has `b` holding `ref`'s changes, or it asked `gh`. -/
def Reached (cwd ref b : String) (l : List (M.World × Call)) : Prop :=
  (∃ e ∈ l, M.Holds e.1 cwd ref b) ∨ ∃ w br, (w, .cmd (ghArgv br) (some cwd)) ∈ l

/-- What `Lifecycle.run` answers of a command's result. -/
def okOut (o : ProcOut) : Option String := if o.code == 0 then some o.stdout else none

theorem ok0_of {o : Option ProcOut} (h : ((Option.map (fun x => x.code) o).getD 127 == 0) = true) : Ok0 o := by
  cases o with
  | none => simp at h
  | some x => exact ⟨x, rfl, by simpa using h⟩

theorem run_some {o : Option ProcOut} {v : String} (h : o.bind okOut = some v) : ∃ x, o = some x ∧ x.code = 0 ∧ v = x.stdout := by
  cases o with
  | none => simp at h
  | some x =>
    simp only [Option.bind_some, okOut] at h
    split at h
    · exact ⟨x, rfl, beq_iff_eq.1 ‹_›, (Option.some.inj h).symm⟩
    · cases h

/-- landedRef1's squash check returning true: `b` holds `ref`'s changes on the machine `diff --quiet` ran on. -/
theorem sc_of (hsc : SameContentReach M) {w : M.World} {cwd ref b mb : String}
    (hmb : py (Option.map strip ((M.out w ["git", "-C", cwd, "merge-base", b, ref] none).bind okOut)) = some mb)
    (hf : (!(List.filter (fun x => decide (x ≠ "")) ((((M.out (M.after w ["git", "-C", cwd, "merge-base", b, ref] none)
      ["git", "-C", cwd, "diff", "--name-only", "-z", mb, ref] none).bind okOut).getD "").splitOn "\x00")).isEmpty) = true)
    (hq : ((Option.map (fun x => x.code) (M.out (M.after (M.after w ["git", "-C", cwd, "merge-base", b, ref] none)
      ["git", "-C", cwd, "diff", "--name-only", "-z", mb, ref] none) (["git", "-C", cwd, "diff", "--quiet", ref, b, "--"] ++
      List.filter (fun x => decide (x ≠ "")) ((((M.out (M.after w ["git", "-C", cwd, "merge-base", b, ref] none)
      ["git", "-C", cwd, "diff", "--name-only", "-z", mb, ref] none).bind okOut).getD "").splitOn "\x00")) none)).getD 127
      == 0) = true) :
    M.Holds (M.after (M.after w ["git", "-C", cwd, "merge-base", b, ref] none)
      ["git", "-C", cwd, "diff", "--name-only", "-z", mb, ref] none) cwd ref b := by
  cases e1 : (M.out w ["git", "-C", cwd, "merge-base", b, ref] none).bind okOut with
  | none => simp [e1, py] at hmb
  | some v =>
    obtain ⟨o, ho, hc, rfl⟩ := run_some e1
    simp only [e1, Option.map_some, py, Option.filter_some, decide_eq_true_eq] at hmb
    split at hmb
    · obtain rfl := Option.some.inj hmb
      cases e2 : (M.out (M.after w ["git", "-C", cwd, "merge-base", b, ref] none)
          ["git", "-C", cwd, "diff", "--name-only", "-z", strip o.stdout, ref] none).bind okOut with
      | none =>
        rw [e2, Option.getD_none, show ("".splitOn "\x00") = [""] from by
          unfold String.splitOn String.splitOnAux; simp [String.Pos.Raw.atEnd, String.Pos.Raw.extract]] at hf
        simp at hf
      | some u =>
        obtain ⟨d, hd, hdc, rfl⟩ := run_some e2
        rw [e2] at hf hq
        simp only [Option.getD_some] at hf hq
        exact hsc w cwd ref b o d ho hc ‹_› hd hdc (by simpa using hf) (ok0_of hq)
    · cases hmb

theorem landedRef1_reach_spec (ha : AncestorReach M) (hsc : SameContentReach M) :
    ⦃fun _ => ⌜True⌝⦄ (Lifecycle.landedRef1 cwd ref b : RecM M Bool) ⦃⇓ r s => ⌜r = true → Reached cwd ref b s.log⌝⦄ := by
  unfold Lifecycle.landedRef1
  mvcgen -trivial [Lifecycle.run, Lifecycle.code, Proc.output]
  all_goals (try mleave)
  all_goals simp only [withEnv_nil, List.map_nil] at *
  all_goals (try intro hr)
  all_goals first
    | cases hr
    | exact .inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ha _ _ _ _ (ok0_of ‹_›)⟩
    | exact .inl ⟨_, List.mem_append_right _ (List.mem_singleton_self _), sc_of hsc ‹_› ‹_› ‹_›⟩
    | exact .inr ⟨_, _, List.mem_append_right _ (List.mem_singleton_self _)⟩
    | (simp at *; done)

/-- A specification's postcondition holds where the code ends, run from any state (it never ends early). -/
theorem post_of {x : RecM M α} {P : α → Rec M → Prop}
    (h : ⦃fun _ => ⌜True⌝⦄ x ⦃⇓ r s => ⌜P r s⌝⦄) (s : Rec M) : ∃ a, (Rec.go x s).1 = .ok a ∧ P a (Rec.go x s).2 := by
  have := h s trivial
  simp only [WP.wp, PredTrans.pushExcept, PredTrans.pushArg, PredTrans.apply, ExceptT.run, StateT.run] at this
  unfold Rec.go ExceptT.run StateT.run
  revert this
  rcases e : x s with ⟨r, s'⟩
  cases r <;> simp [Id.run, ExceptConds.false] <;> exact id

theorem val_of_go [Inhabited α] {x : RecM M α} {s : Rec M} {a : α} (h : (Rec.go x s).1 = .ok a) : Rec.val x s = a := by
  unfold Rec.val; rw [h]

/-- `post_of` for a specification from one state. -/
theorem post_of' {x : RecM M α} {P : α → Rec M → Prop} {s0 : Rec M}
    (h : ⦃fun s => ⌜s = s0⌝⦄ x ⦃⇓ r s => ⌜P r s⌝⦄) : ∃ a, (Rec.go x s0).1 = .ok a ∧ P a (Rec.go x s0).2 := by
  have := h s0 rfl
  simp only [WP.wp, PredTrans.pushExcept, PredTrans.pushArg, PredTrans.apply, ExceptT.run, StateT.run] at this
  unfold Rec.go ExceptT.run StateT.run
  revert this
  rcases e : x s0 with ⟨r, s'⟩
  cases r <;> simp [Id.run, ExceptConds.false] <;> exact id

theorem Reached.mono {l l' : List (M.World × Call)} (h : Reached cwd ref b l) (hl : l <+: l') : Reached cwd ref b l' := by
  rcases h with ⟨e, he, hh⟩ | ⟨w, br, hm⟩
  · exact .inl ⟨e, hl.subset he, hh⟩
  · exact .inr ⟨w, br, hl.subset hm⟩

/-- landedRef1 answering true from `s`: `Reached` on the log it left. -/
theorem landedRef1_reach (ha : AncestorReach M) (hsc : SameContentReach M) (s : Rec M)
    (h : Rec.val (Lifecycle.landedRef1 cwd ref b : RecM M Bool) s = true) :
    Reached cwd ref b (Rec.go (Lifecycle.landedRef1 cwd ref b : RecM M Bool) s).2.log := by
  obtain ⟨a, ha', hp⟩ := post_of (landedRef1_reach_spec ha hsc) s
  rw [val_of_go ha'] at h
  exact hp h

theorem landedRef_reach_spec (ha : AncestorReach M) (hsc : SameContentReach M) :
    ⦃fun _ => ⌜True⌝⦄ (Lifecycle.landedRef cwd ref bs : RecM M Bool)
      ⦃⇓ r s => ⌜r = true → ∃ b ∈ bs, Reached cwd ref b s.log⌝⦄ := by
  unfold Lifecycle.landedRef
  mvcgen -trivial
  case inv1 => exact ⇓ p s => ⌜p.2.1 = some true → ∃ b ∈ bs, Reached cwd ref b s.log⌝
  all_goals (try mleave)
  case vc1 => exact ⟨_, by simp [‹bs = _›], landedRef1_reach ha hsc _ ‹_›⟩
  case vc4 => rintro rfl; exact ‹_ → _› (by simpa using ‹_›)
  all_goals simp

/-- `landed wt bs main` answering true from `s0`: the worktree's directory was gone when it looked (it then judges
only the branch), or it is the main checkout, or `b` holds its HEAD's changes for some `b` of `bs` (`Reached`). -/
theorem landed_reach_spec (ha : AncestorReach M) (hsc : SameContentReach M) (s0 : Rec M) :
    ⦃fun s => ⌜s = s0⌝⦄ (Lifecycle.landed wt bs main : RecM M Bool)
      ⦃⇓ r s => ⌜r = true → M.kind s0.w wt true = .none ∨ some wt = main ∨ ∃ b ∈ bs, Reached wt "HEAD" b s.log⌝⦄ := by
  have hs : ∀ cwd ref, ⦃fun _ => ⌜True⌝⦄ (Lifecycle.landedRef cwd ref bs : RecM M Bool)
      ⦃⇓ r s => ⌜r = true → ∃ b ∈ bs, Reached cwd ref b s.log⌝⦄ := fun _ _ => landedRef_reach_spec ha hsc
  unfold Lifecycle.landed
  mvcgen -trivial [hs, Lifecycle.run, Proc.output, Sys.kind]
  case inv1 => exact ⇓ _ _ => ⌜True⌝
  all_goals (try mleave)
  all_goals subst_vars
  case vc5 => exact .inl (by simpa using ‹(M.kind _ wt true == Kind.none) = true›)
  case vc6 => intro _ _; exact .inl (by simpa using ‹(M.kind _ wt true == Kind.none) = true›)
  case vc9 =>
    intro h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact .inr (.inl (by simpa using h))
    · exact .inr (.inr (‹_ → _› h))
  all_goals simp

/-- W1 on the machines the sweep's checks read, from `Gate`: the worktree it removes is the realpath of one that was
there when `worktree list` ran; no process was inside it when `Machine.cwds` read; it had nothing uncommitted when
`status` ran, if it was there; and it was not used in the `SWEEP_IDLE` before `status` ran, if git printed its git dir
then and the clock had not gone back since the sweep read it; and `landed` found its directory gone, or its HEAD
reached from one of the protected bases' refs (`Reached`). -/
theorem sweepGate_W1 (ha : AncestorReach M) (hsc : SameContentReach M) (hlo : ListedOn M) (hsl : StatusClean M)
    (hcp : CwdsProc M) (htr : TouchedRecent M) {s0 : Rec M} {m x : String} {L : List (M.World × Call)} (h : Gate s0 m x L) :
    (∃ (p : String) (w : M.World), M.There s0.w p ∧ x = realW w p) ∧
    (∃ s : Rec M, s.log <+: L ∧ ¬ M.Inside s.w x) ∧
    (∃ wk, (wk, .cmd ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none) ∈ L ∧ (M.There wk x → ¬ M.Dirty wk x) ∧
      ∃ t, (∃ st : Rec M, st.log <+: L ∧ t = M.now st.w) ∧
        ∀ gd, M.git wk ["-C", x, "rev-parse", "--absolute-git-dir"] none = some gd → t ≤ M.now wk → ¬ M.Recent wk x) ∧
    ∃ s sp sb : Rec M, s.log <+: L ∧ (M.kind s.w x true = .none ∨ ∃ b ∈ Rec.val (Bases.refs (Rec.val
      (Workspaces.protectedOf s0.db (some m) : RecM M _) sp) (some m) : RecM M _) sb, Reached x "HEAD" b L) := by
  obtain ⟨⟨first, hfirst, -⟩, hne, ⟨e, he, w, hx⟩, -, ⟨s, cs, hs, hcs, hin⟩, ⟨wk, t, -, hst, ⟨st, hst', hcl⟩, hclk, hidle⟩,
    ⟨sl, sp, sb, hlL, hlv⟩⟩ := h
  refine ⟨?_, ⟨s, hs, fun hI => ?_⟩, ⟨wk, hst, fun hT => ?_, t, hclk, fun gd hgd ht hR => ?_⟩, sl, sp, sb,
    (prefix_go landed_ext sl).trans hlL, ?_⟩
  · obtain ⟨l, hl, hw, he1⟩ := wtLines_mem he
    unfold lsLines at hfirst hl
    cases ho : M.out s0.w lsArgv none with
    | none => simp [ho, splitlines] at hfirst
    | some o =>
      by_cases hc : o.code = 0
      · simp only [ho, Option.bind_some, hc, beq_self_eq_true, ite_true, Option.getD_some] at hl
        exact ⟨e.1, w, he1 ▸ hlo s0.w none o l ho hc (List.mem_of_mem_tail hl) hw, hx⟩
      · simp [ho, hc, splitlines] at hfirst
  · obtain ⟨c, hc, hc'⟩ := hcp s cs x hcs hI
    have := hin c hc; unfold realW at this; rw [this] at hc'; cases hc'
  · obtain ⟨o, ho, hst'⟩ := Option.bind_eq_some_iff.1 hst'
    by_cases hc : o.code = 0
    · simp only [hc, beq_self_eq_true, ite_true, Option.some.injEq] at hst'
      exact hsl wk x o hT ho hc (hst' ▸ hcl)
    · simp [hc] at hst'
  · have := htr wk x gd hR hgd
    simp only [lastAt, hgd, Option.map_some] at hidle
    omega
  · obtain ⟨a, hgo, hp⟩ := post_of' (landed_reach_spec ha hsc sl)
    rw [hlv] at hgo; cases hgo
    rcases hp rfl with hk | hm | ⟨b, hb, hr⟩
    · exact .inl hk
    · exact absurd (Option.some.inj hm) hne
    · exact .inr ⟨b, hb, hr.mono hlL⟩

/-- `git -C main worktree remove wt` (the sweep's `rmArgv`) moves no branch tip, changes no other worktree, and changes
nothing when `wt` is dirty. -/
theorem wtRemove_only (hwr : WtRemove M) (w : M.World) (main wt : String) :
    let w' := M.after w (rmArgv main wt) none
    (∀ b, M.tip w' b = M.tip w b) ∧ (∀ x, x ≠ wt → (M.There w' x ↔ M.There w x) ∧ (M.Dirty w' x ↔ M.Dirty w x)) ∧
      (M.Dirty w wt → M.SameRepo w w') :=
  ⟨(hwr w main wt).2.2.1, (hwr w main wt).2.2.2.1, (hwr w main wt).2.1⟩

/-- deleteBranch's guarded path, `update-ref -d refs/heads/b k` (`BranchCall`, with `k` the HEAD the sweep read before
`landed`): if branch `b`'s tip changed, it was `k`; no other branch changed. -/
theorem delRef_guarded (hdr : DelRef M) (w : M.World) (main b k : String) :
    let w' := M.after w ["git", "-C", main, "update-ref", "-d", "refs/heads/" ++ b, k] none
    (M.tip w' b ≠ M.tip w b → M.tip w b = some k) ∧ ∀ b', b' ≠ b → M.tip w' b' = M.tip w b' := by
  refine ⟨fun hne => ?_, (hdr w main b k).2.1⟩
  have := (hdr w main b k).1
  by_cases hk : M.tip w b = some k
  · exact hk
  · exact absurd (by rw [this, if_neg hk]) hne


/-! ## W2: ending an agent -/

theorem discard_eq (x : RecM M α) : discard x = (x >>= fun _ => pure ()) := by
  simp only [discard, LawfulFunctor.map_const, Function.comp, map_eq_pure_bind]

theorem sameRepo_refl (w : M.World) : M.SameRepo w w :=
  ⟨fun _ => rfl, fun _ => ⟨Iff.rfl, Iff.rfl⟩, fun _ _ _ => Iff.rfl, fun _ => rfl, fun _ => Iff.rfl⟩

theorem sameRepo_trans {a b c : M.World} (h1 : M.SameRepo a b) (h2 : M.SameRepo b c) : M.SameRepo a c :=
  ⟨fun x => (h2.1 x).trans (h1.1 x), fun x => ⟨(h2.2.1 x).1.trans (h1.2.1 x).1, (h2.2.1 x).2.trans (h1.2.1 x).2⟩,
    fun cwd x b => (h2.2.2.1 cwd x b).trans (h1.2.2.1 cwd x b), fun x => (h2.2.2.2.1 x).trans (h1.2.2.2.1 x),
    fun x => (h2.2.2.2.2 x).trans (h1.2.2.2.2 x)⟩

/-- W2 on a machine: ending an agent (its row, its terminal, its cgroup scope) changes no worktree, branch or commit. -/
theorem endAgent_keepsGit (hk : HcKillEnds M) (hr : HcRmKeeps M) (hc : CgroupKillKeeps M) (w0 : M.World) (a : Agent)
    (force : Bool) (by_ : Option String) :
    ⦃fun s => ⌜M.SameRepo w0 s.w⌝⦄ (Lifecycle.endAgent a force by_ : RecM M Bool) ⦃⇓ _ s => ⌜M.SameRepo w0 s.w⌝⦄ := by
  mvcgen -trivial [Lifecycle.endAgent, Machine.cgroup, Machine.procRoot, Machine.cgroupRoot, Proc.output, Store.txn,
    Clock.now, Fs.write, Fs.read, Env.var, discard_eq]
  all_goals (try mleave)
  all_goals (try simp only [withEnv_nil, List.map_nil] at *)
  all_goals (repeat (first | assumption | refine sameRepo_trans ?_ (hc _ _) | refine sameRepo_trans ?_ (hr _ _) |
    refine sameRepo_trans ?_ (hk _ _).2))

end SwarmLean.SweepProofs
