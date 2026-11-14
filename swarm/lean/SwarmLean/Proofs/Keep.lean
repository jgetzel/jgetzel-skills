import SwarmLean.Proofs.Trust

/-! The sweep loses no work, end to end (board #132): after any run of sweeps and ends, every commit reachable before
is reachable after unless it was below the HEAD of a worktree the sweep removed after `Gate` (which found it landed),
and every worktree there before is there after unless the sweep removed it clean. -/

set_option linter.deprecated.syntax false
attribute [local irreducible] String.startsWith String.drop SwarmLean.splitlines SwarmLean.strip String.splitOn String.intercalate SwarmLean.joinPath

namespace SwarmLean.SweepProofs
open Std.Do
variable {M : Tools}

/-! ## Reads: calls that leave the repo -/

/-- The machine after call `c` ran on `w`: a command or an effect moves it on, a git read does not. -/
def nxt (w : M.World) : Call → M.World
  | .cmd argv cwd => M.after w argv cwd
  | .git _ _ => w
  | .eff e => M.effect w e

/-- The calls `l` ran from machine `w`, each on the machine the one before left, and left `w'`. -/
def Steps : M.World → List (M.World × Call) → M.World → Prop
  | w, [], w' => w' = w
  | w, e :: l, w' => e.1 = w ∧ Steps (nxt w e.2) l w'

theorem Steps.append {w w1 w2 : M.World} {l1 l2 : List (M.World × Call)} (h1 : Steps w l1 w1) (h2 : Steps w1 l2 w2) :
    Steps w (l1 ++ l2) w2 := by
  induction l1 generalizing w with
  | nil => cases h1; exact h2
  | cons e l ih => exact ⟨h1.1, ih h1.2⟩

/-- A call the sweep makes to read: a git read, or a command `GitRead` or `ToolRead` names. -/
def KeepCall : Call → Prop
  | .git _ _ => True
  | .cmd argv _ => GitRead argv ∨ ToolRead argv
  | .eff _ => False

/-- From `s` to `s'` the code made only reads, each on the machine the one before left. -/
def Chain (s s' : Rec M) : Prop := ∃ l, s'.log = s.log ++ l ∧ Steps s.w l s'.w ∧ ∀ e ∈ l, KeepCall e.2

theorem Chain.refl (s : Rec M) : Chain s s := ⟨[], by simp, rfl, by simp⟩

theorem Chain.trans {a b c : Rec M} (h1 : Chain a b) (h2 : Chain b c) : Chain a c := by
  obtain ⟨l1, e1, s1, k1⟩ := h1; obtain ⟨l2, e2, s2, k2⟩ := h2
  refine ⟨l1 ++ l2, by rw [e2, e1, List.append_assoc], s1.append s2, fun e he => ?_⟩
  rcases List.mem_append.1 he with h | h
  · exact k1 e h
  · exact k2 e h

theorem Chain.snoc {s0 s : Rec M} {c : Call} (h : Chain s0 s) (hc : KeepCall c) :
    Chain s0 { s with w := nxt s.w c, log := s.log ++ [(s.w, c)] } :=
  h.trans ⟨[(s.w, c)], rfl, ⟨rfl, rfl⟩, by simpa using hc⟩

theorem Chain.cmd {s0 s : Rec M} {argv : List String} {cwd : Option String} (h : Chain s0 s)
    (hc : GitRead argv ∨ ToolRead argv) :
    Chain s0 { s with w := M.after s.w argv cwd, log := s.log ++ [(s.w, .cmd argv cwd)] } := h.snoc (c := .cmd argv cwd) hc

theorem Chain.git {s0 s : Rec M} {args : List String} {cwd : Option String} (h : Chain s0 s) :
    Chain s0 { s with log := s.log ++ [(s.w, .git args cwd)] } := h.snoc (c := .git args cwd) trivial

theorem Chain.db {s0 s : Rec M} {d : Db} (h : Chain s0 s) : Chain s0 { s with db := d } := h

theorem Chain.mk_self {s0 s : Rec M} {d : Db} {cs : List Db} (h : Chain s0 s) : Chain s0 ⟨s.w, d, s.log, cs⟩ := h

/-- A state vcgen spells out: a command read after `⟨w, _, L⟩`. -/
theorem Chain.mkCmd {s0 : Rec M} {w : M.World} {d : Db} {cs : List Db} {L : List (M.World × Call)} {argv : List String}
    {cwd : Option String} (h : Chain s0 ⟨w, d, L, cs⟩) (hc : GitRead argv ∨ ToolRead argv) :
    Chain s0 ⟨M.after w argv cwd, d, L ++ [(w, .cmd argv cwd)], cs⟩ := Chain.cmd (s := ⟨w, d, L, cs⟩) h hc

/-- A state vcgen spells out: a git read after `⟨w, _, L⟩`. -/
theorem Chain.mkGit {s0 : Rec M} {w : M.World} {d : Db} {cs : List Db} {L : List (M.World × Call)} {args : List String}
    {cwd : Option String} (h : Chain s0 ⟨w, d, L, cs⟩) : Chain s0 ⟨w, d, L ++ [(w, .git args cwd)], cs⟩ :=
  Chain.git (s := ⟨w, d, L, cs⟩) h

/-- `s'` is `s` and then reads `l` (the shape vcgen leaves a state in). -/
theorem Chain.ext {s0 s s' : Rec M} {l : List (M.World × Call)} (h : Chain s0 s) (hl : s'.log = s.log ++ l)
    (hs : Steps s.w l s'.w) (hk : ∀ e ∈ l, KeepCall e.2) : Chain s0 s' := h.trans ⟨l, hl, hs, hk⟩

/-- `x` only reads, from any state. -/
def KExt (x : RecM M α) : Prop := ∀ s, Chain s (Rec.go x s).2

theorem Chain.go {x : RecM M α} {s0 s : Rec M} (hx : KExt x) (h : Chain s0 s) : Chain s0 (Rec.go x s).2 := h.trans (hx s)

theorem kext_of {x : RecM M α} (h : ∀ s0, ⦃fun s => ⌜Chain s0 s⌝⦄ x ⦃⇓ _ s => ⌜Chain s0 s⌝⦄) : KExt x := by
  intro s0
  have h' : ⦃fun s => ⌜s = s0⌝⦄ x ⦃⇓ _ s => ⌜Chain s0 s⌝⦄ := fun s hs => h s0 s (hs ▸ Chain.refl s0)
  obtain ⟨_, _, hp⟩ := post_of' h'
  exact hp

theorem Reads.kext {x : RecM M α} {g : M.World → α} (h : Reads x g) : KExt x := fun s => by
  rw [h.go]; exact Chain.refl _

theorem git_map_kext {g : Option String → β} {args : List String} {cwd : Option String} :
    KExt (g <$> (Git.git args cwd : RecM M (Option String))) := kext_of fun s0 => by
  mvcgen -trivial [Git.git]
  all_goals (try mleave)
  exact Chain.git ‹_›

theorem mapM_kext [Inhabited β] {f : α → RecM M β} {xs : List α} (h : ∀ a, KExt (f a)) (he : ∀ a, Ext (f a)) :
    KExt (xs.mapM f) := by
  induction xs with
  | nil => intro s; rw [List.mapM_nil, go_pure]; exact Chain.refl _
  | cons a as ih =>
    intro s
    rw [List.mapM_cons, go_bind]
    have h1 := h a s
    have hr1 := (he a s).1
    rcases e1 : Rec.go (f a) s with ⟨r1, s1⟩
    rw [e1] at hr1 h1; subst hr1
    simp only []
    rw [go_bind]
    have h2 := ih s1
    have hr2 := (mapM_ext (xs := as) he s1).1
    rcases e2 : Rec.go (as.mapM f) s1 with ⟨r2, s2⟩
    rw [e2] at hr2 h2; subst hr2
    simp only [go_pure]
    exact h1.trans h2

set_option hygiene false in
/-- Closes `KExt` of a lambda the sweep maps over a list. -/
macro "kext_lam" : tactic => `(tactic| (
  apply kext_of
  intro s0
  mvcgen -trivial [Watchd.real, Workspaces.real, Sys.realpath, Watchd.git, Git.git]
  all_goals first | exact ⇓ _ s => ⌜Chain s0 s⌝ | skip
  all_goals (try mleave)
  all_goals (subst_vars; repeat (any_goals (first | exact Chain.refl _ | assumption | apply Chain.git)))))

set_option hygiene false in
/-- Closes a `KExt` or `Ext` goal of a sub-call of the sweep (no `mapM`). -/
macro "kext1" : tactic => `(tactic| first
  | exact landedRef1_kext | exact landed_kext | exact default_kext | exact baseFor_kext | exact ref_kext
  | exact cwds_kext | exact worktrees_kext | exact protectedOf_kext | exact refs_kext | exact cleanRemote_kext
  | exact git_map_kext | exact git_map_ext | exact landedRef1_ext | exact landed_ext | exact default_ext
  | exact baseFor_ext | exact ref_ext | exact cwds_ext | exact worktrees_ext | exact protectedOf_ext | exact refs_ext
  | exact cleanRemote_ext)

set_option hygiene false in
/-- Closes a `KExt` goal of a sub-call of the sweep. -/
macro "kexts" : tactic => `(tactic| first
  | kext1
  | (with_reducible apply mapM_kext <;> intro <;> first | kext1 | kext_lam | ext_lam))

set_option hygiene false in
/-- Closes `KeepCall` of each call of a list. -/
macro "keepcalls" : tactic => `(tactic| (
  simp (config := {zetaDelta := true}) [KeepCall, GitRead, ToolRead]
  all_goals assumption))

set_option hygiene false in
/-- Closes `Chain s0 s'` for an `s'` that the reads of a vcgen goal reach from a state `Chain` holds of. -/
macro "chain0" : tactic => `(tactic| (
  subst_vars
  try simp only [List.map_nil, withEnv_nil] at *
  repeat (any_goals (first | exact Chain.refl _ | assumption | (apply Chain.go; kexts) | (intro; kext1) |
    (refine Chain.mkCmd ?_ ?keepcall; case keepcall => keepcalls) | apply Chain.mkGit |
    (apply Chain.mk_self; first | exact Chain.refl _ | assumption | (apply Chain.go; kexts)) |
    (refine Chain.ext ?_ rfl (by simp (config := {zetaDelta := true}) [Steps, nxt]) (by keepcalls))))))

set_option hygiene false in
/-- Closes a vcgen's goals for `kext_of`. -/
macro "kext_close" s0:term : tactic => `(tactic| (
  all_goals first | exact ⇓ _ s => ⌜Chain $s0 s⌝ | skip
  all_goals (try mleave)
  all_goals chain0))

theorem landedRef1_kext : KExt (Lifecycle.landedRef1 cwd ref b : RecM M Bool) := kext_of fun s0 => by
  unfold Lifecycle.landedRef1
  mvcgen -trivial [Lifecycle.landedRef1, Lifecycle.run, Lifecycle.code, Proc.output]
  kext_close s0

theorem landed_kext : KExt (Lifecycle.landed wt bs main : RecM M Bool) := kext_of fun s0 => by
  unfold Lifecycle.landed
  have hs : ∀ cwd ref b Q, ⦃fun s => Q.1 (Rec.val (Lifecycle.landedRef1 cwd ref b) s)
      (Rec.go (Lifecycle.landedRef1 cwd ref b) s).2⦄ (Lifecycle.landedRef1 cwd ref b : RecM M Bool) ⦃Q⦄ :=
    fun _ _ _ Q => val_spec landedRef1_ext.nt Q
  mvcgen -trivial [Lifecycle.landed, Lifecycle.landedRef, Lifecycle.run, Proc.output, Sys.kind, hs]
  kext_close s0

theorem default_kext : KExt (Bases.default cwd : RecM M _) := kext_of fun s0 => by
  unfold Bases.default
  mvcgen -trivial [Bases.default, Git.git, Fs.read]
  kext_close s0

theorem baseFor_kext : KExt (Bases.baseFor b cwd : RecM M _) := kext_of fun s0 => by
  unfold Bases.baseFor
  mvcgen -trivial [Bases.baseFor, Bases.default, Git.git, Fs.read]
  kext_close s0

theorem ref_kext : KExt (Bases.ref b cwd : RecM M _) := kext_of fun s0 => by
  unfold Bases.ref
  mvcgen -trivial [Bases.ref, Bases.remoteRef, Git.git]
  kext_close s0

theorem cwds_kext : KExt (Machine.cwds : RecM M _) := kext_of fun s0 => by
  unfold Machine.cwds
  mvcgen -trivial [Machine.cwds, Machine.osName, Machine.procRoot, Proc.output, Env.var, Fs.list, Sys.readlink]
  kext_close s0

theorem worktrees_kext : KExt (Workspaces.worktrees : RecM M _) := kext_of fun s0 => by
  unfold Workspaces.worktrees
  mvcgen -trivial [Workspaces.worktrees, Workspaces.real, Git.git, Sys.realpath]
  kext_close s0

theorem protectedOf_kext : KExt (Workspaces.protectedOf db cwd : RecM M _) := kext_of fun s0 => by
  unfold Workspaces.protectedOf
  mvcgen -trivial [Workspaces.protectedOf, Bases.protectedBases]
  kext_close s0

theorem refs_kext : KExt (Bases.refs ns cwd : RecM M _) := kext_of fun s0 => by
  unfold Bases.refs
  mvcgen -trivial [Bases.refs]
  kext_close s0

theorem cleanRemote_kext : KExt (Run.cleanRemote wt : RecM M _) := kext_of fun s0 => by
  unfold Run.cleanRemote
  mvcgen -trivial [Run.cleanRemote, Proc.output, Store.txn, Clock.now]
  kext_close s0

/-! ## What a sweep keeps -/

/-- Reads leave the repo as it was. -/
theorem Chain.same (hg : GitReadsKeep M) (ht : ToolsKeep M) {s s' : Rec M} (h : Chain s s') : M.SameRepo s.w s'.w := by
  obtain ⟨l, -, hs, hk⟩ := h
  induction l generalizing s with
  | nil => simp only [Steps] at hs; rw [hs]; exact sameRepo_refl _
  | cons e l ih =>
    obtain ⟨he, hs⟩ := hs
    have h1 : M.SameRepo s.w (nxt s.w e.2) := by
      have := hk e List.mem_cons_self
      rcases e with ⟨w, c⟩
      cases c with
      | git => exact sameRepo_refl _
      | cmd argv cwd => exact this.elim (hg _ _ _) (ht _ _ _)
      | eff => cases this
    exact sameRepo_trans h1 (ih (s := ⟨nxt s.w e.2, s.db, s.log, s.commits⟩) hs fun e he => hk e (List.mem_cons_of_mem _ he))

theorem getElem?_prefix {l l' : List α} {i : Nat} {e : α} (h : l[i]? = some e) (hl : l <+: l') : l'[i]? = some e := by
  obtain ⟨t, rfl⟩ := hl
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 h
  rw [List.getElem?_append_left hi]; exact h

/-- Commit `c` is `k` or below it, `k` the HEAD of a worktree `x` that a `worktree remove` at index `n` or later of `l`
removed, on the machine it ran on. -/
def Lost (n : Nat) (c : String) (l : List (M.World × Call)) : Prop :=
  ∃ i w m x k, n ≤ i ∧ l[i]? = some (w, .cmd (rmArgv m x) none) ∧ M.head w x = some k ∧ M.Anc c k

/-- A `worktree remove` of `x` at index `n` or later of `l` ran on a machine where `x` had nothing uncommitted. -/
def Gone (n : Nat) (x : String) (l : List (M.World × Call)) : Prop :=
  ∃ i w m, n ≤ i ∧ l[i]? = some (w, .cmd (rmArgv m x) none) ∧ ¬ M.Dirty w x

theorem Lost.mono {l l' : List (M.World × Call)} (h : Lost n c l) (hl : l <+: l') : Lost n c l' := by
  obtain ⟨i, w, m, x, k, hn, hi, hh, ha⟩ := h; exact ⟨i, w, m, x, k, hn, getElem?_prefix hi hl, hh, ha⟩
theorem Gone.mono {l l' : List (M.World × Call)} (h : Gone n x l) (hl : l <+: l') : Gone n x l' := by
  obtain ⟨i, w, m, hn, hi, hd⟩ := h; exact ⟨i, w, m, hn, getElem?_prefix hi hl, hd⟩

/-- From `s0` to `s`: the log grew; every commit reachable on `s0`'s machine is on `s`'s, or `Lost`; every worktree
there on `s0`'s machine is on `s`'s, or `Gone`. -/
def Kept (s0 s : Rec M) : Prop :=
  s0.log <+: s.log ∧ (∀ c, M.Reach s0.w c → M.Reach s.w c ∨ Lost s0.log.length c s.log) ∧
    ∀ x, M.There s0.w x → M.There s.w x ∨ Gone s0.log.length x s.log

theorem Kept.refl (s : Rec M) : Kept s s := ⟨List.prefix_refl _, fun _ h => .inl h, fun _ h => .inl h⟩

/-- Kept, and then calls that keep reachability and worktrees (`hr`, `ht`) and grow the log. -/
theorem Kept.mono {s0 s s' : Rec M} (h : Kept s0 s) (hl : s.log <+: s'.log) (hr : ∀ c, M.Reach s.w c → M.Reach s'.w c)
    (ht : ∀ x, M.There s.w x → M.There s'.w x) : Kept s0 s' := by
  obtain ⟨hp, hR, hT⟩ := h
  refine ⟨hp.trans hl, fun c hc => ?_, fun x hx => ?_⟩
  · rcases hR c hc with h | h
    · exact .inl (hr c h)
    · exact .inr (h.mono hl)
  · rcases hT x hx with h | h
    · exact .inl (ht x h)
    · exact .inr (h.mono hl)

theorem Kept.chain (hg : GitReadsKeep M) (ht : ToolsKeep M) {s0 s s' : Rec M} (h : Kept s0 s) (hc : Chain s s') :
    Kept s0 s' := by
  have hs := hc.same hg ht
  obtain ⟨l, e, -⟩ := hc
  exact h.mono (by rw [e]; exact List.prefix_append _ _) (fun c => (hs.2.2.2.2 c).2) (fun x => ((hs.2.1 x).1).2)

theorem Kept.mk_self {s0 s : Rec M} {d : Db} {cs : List Db} (h : Kept s0 s) : Kept s0 ⟨s.w, d, s.log, cs⟩ := h

theorem Kept.go (hg : GitReadsKeep M) (ht : ToolsKeep M) {x : RecM M α} {s0 s : Rec M} (hx : KExt x) (h : Kept s0 s) :
    Kept s0 (Rec.go x s).2 := h.chain hg ht (hx s)

theorem Kept.mkCmd (hg : GitReadsKeep M) (ht : ToolsKeep M) {s0 : Rec M} {w : M.World} {d : Db} {cs : List Db}
    {L : List (M.World × Call)} {argv : List String} {cwd : Option String} (h : Kept s0 ⟨w, d, L, cs⟩)
    (hc : GitRead argv ∨ ToolRead argv) : Kept s0 ⟨M.after w argv cwd, d, L ++ [(w, .cmd argv cwd)], cs⟩ :=
  h.chain hg ht (Chain.mkCmd (Chain.refl _) hc)

theorem Kept.mkGit (hg : GitReadsKeep M) (ht : ToolsKeep M) {s0 : Rec M} {w : M.World} {d : Db} {cs : List Db}
    {L : List (M.World × Call)} {args : List String} {cwd : Option String} (h : Kept s0 ⟨w, d, L, cs⟩) :
    Kept s0 ⟨w, d, L ++ [(w, .git args cwd)], cs⟩ :=
  h.chain hg ht (Chain.mkGit (Chain.refl _))

/-- `worktree remove`: what it leaves unreachable is `Lost`, the worktree it takes away `Gone`. -/
theorem Kept.mkRm (hwr : WtRemove M) {s0 : Rec M} {w : M.World} {d : Db} {cs : List Db} {L : List (M.World × Call)} {m x : String}
    (h : Kept s0 ⟨w, d, L, cs⟩) :
    Kept s0 ⟨M.after w ["git", "-C", m, "worktree", "remove", x] none, d,
      L ++ [(w, .cmd ["git", "-C", m, "worktree", "remove", x] none)], cs⟩ := by
  obtain ⟨hp, hR, hT⟩ := h
  have hw := hwr w m x
  have hpre : L <+: L ++ [(w, .cmd ["git", "-C", m, "worktree", "remove", x] none)] := List.prefix_append _ _
  have hn : s0.log.length ≤ L.length := hp.length_le
  have hi : (L ++ [(w, Call.cmd (rmArgv m x) none)])[L.length]? = some (w, .cmd (rmArgv m x) none) := by simp
  refine ⟨hp.trans hpre, fun c hc => ?_, fun y hy => ?_⟩
  · rcases hR c hc with h | h
    · rcases hw.2.2.2.2.2 c h with h | ⟨k, hk, ha⟩
      · exact .inl h
      · exact .inr ⟨L.length, w, m, x, k, hn, hi, hk, ha⟩
    · exact .inr (h.mono hpre)
  · rcases hT y hy with h | h
    · by_cases hyx : y = x
      · subst hyx
        by_cases hd : M.Dirty w y
        · exact .inl (((hw.2.1 hd).2.1 y).1.2 h)
        · exact .inr ⟨L.length, w, m, hn, hi, hd⟩
      · exact .inl (((hw.2.2.2.1 y hyx).1).2 h)
    · exact .inr (h.mono hpre)

/-- `branch -d` keeps every commit and worktree. -/
theorem Kept.mkBranchD (hbd : BranchD M) {s0 : Rec M} {w : M.World} {d : Db} {cs : List Db} {L : List (M.World × Call)} {m b : String}
    (h : Kept s0 ⟨w, d, L, cs⟩) :
    Kept s0 ⟨M.after w ["git", "-C", m, "branch", "-d", b] none, d, L ++ [(w, .cmd ["git", "-C", m, "branch", "-d", b] none)], cs⟩ :=
  h.mono (List.prefix_append _ _) (hbd w m b).1 (fun x => ((hbd w m b).2 x).2)

/-- `update-ref -d refs/heads/b k`: what it leaves unreachable is below `k`, `Lost` when `k` is (`hk`). -/
theorem Kept.mkDelRef (hdr : DelRef M) {s0 : Rec M} {w : M.World} {d : Db} {cs : List Db} {L : List (M.World × Call)} {m b k : String}
    (h : Kept s0 ⟨w, d, L, cs⟩) (hk : ∀ c, M.Anc c k → Lost s0.log.length c L) :
    Kept s0 ⟨M.after w ["git", "-C", m, "update-ref", "-d", "refs/heads/" ++ b, k] none, d,
      L ++ [(w, .cmd ["git", "-C", m, "update-ref", "-d", "refs/heads/" ++ b, k] none)], cs⟩ := by
  obtain ⟨hp, hR, hT⟩ := h
  have hw := hdr w m b k
  have hpre := List.prefix_append L [(w, Call.cmd ["git", "-C", m, "update-ref", "-d", "refs/heads/" ++ b, k] none)]
  refine ⟨hp.trans hpre, fun c hc => ?_, fun y hy => ?_⟩
  · rcases hR c hc with h | h
    · rcases hw.2.2.2.2 c h with h | h
      · exact .inl h
      · exact .inr ((hk c h).mono hpre)
    · exact .inr (h.mono hpre)
  · rcases hT y hy with h | h
    · exact .inl (((hw.2.2.1 y).1).2 h)
    · exact .inr (h.mono hpre)

/-- The branch delete keeps what `Kept` says when what it may delete, the tip `tip` it was handed, is `Lost`. -/
theorem deleteBranch_kept (hbd : BranchD M) (hdr : DelRef M) {s0 s : Rec M} (h : Kept s0 s)
    (hk : ∀ k, tip = some k → ∀ c, M.Anc c k → Lost s0.log.length c s.log) :
    Kept s0 (Rec.go (Watchd.deleteBranch main br tip prot) s).2 := by
  have : ⦃fun s' => ⌜s' = s⌝⦄ (Watchd.deleteBranch main br tip prot : RecM M Unit) ⦃⇓ _ s' => ⌜Kept s0 s'⌝⦄ := by
    unfold Watchd.deleteBranch
    mvcgen -trivial [Watchd.deleteBranch, Lifecycle.code, Proc.output, discard_eq]
    all_goals (try mleave)
    all_goals (try simp only [withEnv_nil, List.map_nil, Prod.mk.injEq] at *)
    all_goals subst_vars
    all_goals (try obtain ⟨rfl, rfl⟩ := ‹br = _ ∧ tip = _›)
    all_goals first
      | exact h
      | exact Kept.mkBranchD hbd (Kept.mk_self h)
      | exact Kept.mkDelRef hdr (Kept.mkBranchD hbd (Kept.mk_self h))
          fun c hc => (hk _ rfl c hc).mono (List.prefix_append _ _)
  obtain ⟨_, _, hp⟩ := post_of' this
  exact hp

/-- The branch delete's guard: the HEAD the sweep read of `x` (on `w`), before reads only and then `worktree remove x`
(and the remote clean), is what that remove left unreachable: anything below it is `Lost`. -/
theorem tie_lost (hg : GitReadsKeep M) (ht : ToolsKeep M) (hrp : RevParseHead M) {s0 : Rec M} {w wT : M.World}
    {d dT : Db} {cs csT : List Db} {L LT : List (M.World × Call)} {m x k : String}
    (hk : py ((M.git w ["-C", x, "rev-parse", "HEAD"] none).map strip) = some k)
    (hch : Chain ⟨w, d, L, cs⟩ ⟨wT, dT, LT, csT⟩) (hT : Kept s0 ⟨wT, dT, LT, csT⟩) : ∀ c, M.Anc c k → Lost s0.log.length c
      (Rec.go (Run.cleanRemote x) ⟨M.after wT ["git", "-C", m, "worktree", "remove", x] none, dT,
        LT ++ [(wT, .cmd ["git", "-C", m, "worktree", "remove", x] none)], csT⟩).2.log := by
  intro c hc'
  have hh : M.head w x = some k := by
    cases ho : M.git w ["-C", x, "rev-parse", "HEAD"] none with
    | none => simp [ho, py] at hk
    | some o =>
      by_cases hne : strip o = ""
      · simp [ho, py, hne] at hk
      · simp [ho, py] at hk; rw [← hk.1]; exact hrp _ _ _ ho hne
  have he : M.head wT x = M.head w x := (hch.same hg ht).2.2.2.1 x
  exact ⟨LT.length, wT, m, x, k, hT.1.length_le, getElem?_prefix (by simp [rmArgv]) (prefix_go cleanRemote_ext _),
    he.trans hh, hc'⟩

set_option hygiene false in
/-- Closes `Kept s0 s'` for an `s'` that a vcgen goal reaches by the sweep's reads and removes from a state `Kept`
holds of. -/
macro "kept1" : tactic => `(tactic| (
  repeat (any_goals (first | with_reducible assumption | with_reducible exact Kept.refl _ |
    (with_reducible apply Kept.mk_self; with_reducible exact Kept.refl _) |
    with_reducible apply Kept.mkRm hwr | (with_reducible refine Kept.mkCmd hg ht ?_ ?keepcall; case keepcall => keepcalls) |
    with_reducible apply Kept.mkGit hg ht |
    (with_reducible apply Kept.mk_self; first | with_reducible assumption | (with_reducible apply Kept.go hg ht; kexts)) |
    (with_reducible apply Kept.go hg ht; kexts) | (intro; kext1)))))

set_option hygiene false in
/-- A sweep VC: the invariant spelled out, the branch delete's guard tied to the remove before it, the rest `kept1`. -/
macro "kept0" : tactic => `(tactic| (
  try simp (config := {zetaDelta := true}) only [id, PostCond.noThrow, List.map_nil, withEnv_nil, SPred.down_pure]
  try simp only [id, PostCond.noThrow, SPred.down_pure] at *
  subst_vars
  try exact ExceptConds.entails.refl _
  try (refine Kept.mk_self ?_; refine deleteBranch_kept hbd hdr ?_ ?tie
       case tie =>
         intro k hk
         apply tie_lost hg ht hrp hk
         · chain0
         · kept1)
  kept1))

set_option hygiene false in
/-- `sweep_kept`'s VCs: the loop invariant `Kept s0`, the mapped lambdas' `Ext`, each VC by `kept0`. -/
macro "sweep_kept_vcs" : tactic => `(tactic| (
  mvcgen -trivial [Watchd.sweep, Lifecycle.run, Lifecycle.code, Watchd.real, Workspaces.real, Watchd.git, Proc.output,
    Sys.realpath, Sys.kind, Sys.mtime, Store.txn, Clock.now, Git.git]
  case' inv1 => exact ⇓ _ s => ⌜Kept s0 s⌝
  all_goals (try mleave)
  all_goals first | (intro; ext_lam; done) | skip
  all_goals kept0))

set_option maxHeartbeats 1000000 in
/-- The sweep keeps every commit and worktree but what it removed: from where it starts to where it ends, `Kept`. -/
theorem sweep_kept (hg : GitReadsKeep M) (ht : ToolsKeep M) (hwr : WtRemove M) (hbd : BranchD M) (hdr : DelRef M)
    (hrp : RevParseHead M) (s0 : Rec M) (comms : Option String) (dry : Bool) (nl : List String) :
    ⦃fun s => ⌜s = s0⌝⦄ (Watchd.sweep comms dry nl : RecM M _) ⦃⇓ _ s => ⌜Kept s0 s⌝⦄ := by
  cases comms <;> sweep_kept_vcs

/-! ## Any run of sweeps and ends -/

theorem Lost.weaken {n n' : Nat} {l : List (M.World × Call)} (h : Lost n' c l) (hn : n ≤ n') : Lost n c l := by
  obtain ⟨i, w, m, x, k, hi, he, hh, ha⟩ := h; exact ⟨i, w, m, x, k, Nat.le_trans hn hi, he, hh, ha⟩
theorem Gone.weaken {n n' : Nat} {l : List (M.World × Call)} (h : Gone n' x l) (hn : n ≤ n') : Gone n x l := by
  obtain ⟨i, w, m, hi, he, hd⟩ := h; exact ⟨i, w, m, Nat.le_trans hn hi, he, hd⟩

theorem Kept.trans {s0 s1 s2 : Rec M} (h1 : Kept s0 s1) (h2 : Kept s1 s2) : Kept s0 s2 := by
  obtain ⟨p1, r1, t1⟩ := h1; obtain ⟨p2, r2, t2⟩ := h2
  have hn := p1.length_le
  refine ⟨p1.trans p2, fun c hc => ?_, fun x hx => ?_⟩
  · rcases r1 c hc with h | h
    · rcases r2 c h with h | h
      · exact .inl h
      · exact .inr (h.weaken hn)
    · exact .inr (h.mono p2)
  · rcases t1 x hx with h | h
    · rcases t2 x h with h | h
      · exact .inl h
      · exact .inr (h.weaken hn)
    · exact .inr (h.mono p2)

/-- The worktree `x` of main checkout `m` passed `Gate` on the calls `L` before its removal, in the sweep that started
from some state. -/
def GateAny (m x : String) (L : List (M.World × Call)) : Prop := ∃ sk : Rec M, Gate sk m x L

theorem GoodFrom.join {n : Nat} {s1 : Rec M} {l : List (M.World × Call)}
    (h1 : GoodFrom n GateAny s1.log) (hp : s1.log <+: l) (h2 : GoodFrom s1.log.length (Gate s1) l) :
    GoodFrom n GateAny l := by
  intro i w m x hi he
  by_cases hl : i < s1.log.length
  · obtain ⟨t, rfl⟩ := hp
    rw [List.getElem?_append_left hl] at he
    rw [List.take_append_of_le_length (Nat.le_of_lt hl)]
    exact h1 i w m x hi he
  · exact ⟨s1, h2 i w m x (Nat.le_of_not_lt hl) he⟩

theorem endAgent_ext : Ext (Lifecycle.endAgent a force by_ : RecM M Bool) := ext_of fun L => by
  mvcgen -trivial [Lifecycle.endAgent, Machine.cgroup, Machine.procRoot, Machine.cgroupRoot, Proc.output, Store.txn,
    Clock.now, Fs.write, Fs.read, Env.var, discard_eq]
  ext_close L

/-- One step of watchd or the CLI that touches worktrees or branches: a sweep (watchd's, or `--dry-run`), or ending an
agent (`swarm end`, lifecycle's end, hung's). -/
inductive Step
  | sweep (comms : Option String) (dry : Bool) (notLanded : List String)
  | stop (a : Agent) (force : Bool) (by_ : Option String)

/-- What a step runs. -/
def Step.run : Step → RecM M Unit
  | .sweep comms dry nl => discard (Watchd.sweep comms dry nl)
  | .stop a force by_ => discard (Lifecycle.endAgent a force by_)

/-- From `s0` to `s`: `Kept`, and every `worktree remove` since passed `Gate`. -/
def RunInv (s0 s : Rec M) : Prop := Kept s0 s ∧ GoodFrom s0.log.length GateAny s.log

/-- The tool assumptions the end-to-end theorem rests on. -/
structure NoLossTools (M : Tools) : Prop where
  gitReads : GitReadsKeep M
  tools : ToolsKeep M
  wtRemove : WtRemove M
  branchD : BranchD M
  delRef : DelRef M
  revParse : RevParseHead M
  hcKill : HcKillEnds M
  hcRm : HcRmKeeps M
  cgroupKill : CgroupKillKeeps M

theorem go_discard {x : RecM M α} {s : Rec M} {a : α} (h : (Rec.go x s).1 = .ok a) :
    Rec.go (discard x) s = (.ok (), (Rec.go x s).2) := by
  rw [discard_eq, go_bind]
  rcases e : Rec.go x s with ⟨r, s'⟩
  rw [e] at h; cases h; simp [go_pure]

theorem step_inv (H : NoLossTools M) (st : Step) {s0 s1 : Rec M} (h : RunInv s0 s1) :
    (∃ u, (Rec.go (st.run (M := M)) s1).1 = .ok u) ∧ RunInv s0 (Rec.go (st.run (M := M)) s1).2 := by
  cases st with
  | sweep comms dry nl =>
    obtain ⟨a, ha, hk⟩ := post_of' (sweep_kept H.gitReads H.tools H.wtRemove H.branchD H.delRef H.revParse s1 comms dry nl)
    obtain ⟨a', ha', hw⟩ := post_of' (sweep_W1 (M := M) s1 comms dry nl)
    simp only [Step.run, go_discard ha]
    exact ⟨⟨(), by simp⟩, h.1.trans hk, h.2.join hk.1 hw⟩
  | stop a force by_ =>
    have he := endAgent_ext (M := M) (a := a) (force := force) (by_ := by_) s1
    obtain ⟨_, -, hs⟩ := post_of' (P := fun _ s => M.SameRepo s1.w s.w) (s0 := s1)
      (fun s hs => endAgent_keepsGit H.hcKill H.hcRm H.cgroupKill s1.w a force by_ s (hs ▸ sameRepo_refl _))
    simp only [Step.run, go_discard he.1]
    refine ⟨⟨(), by simp⟩, h.1.mono he.2.prefix (fun c => (hs.2.2.2.2 c).2) (fun x => ((hs.2.1 x).1).2), ?_⟩
    obtain ⟨l, e, hl⟩ := he.2
    rw [e]; exact h.2.append fun e he => not_rm_of_not_bad (hl e he)

theorem run_inv (H : NoLossTools M) (steps : List Step) {s0 s : Rec M} (h : RunInv s0 s) :
    (∃ u, (Rec.go (steps.forM (Step.run (M := M))) s).1 = .ok u) ∧
      RunInv s0 (Rec.go (steps.forM (Step.run (M := M))) s).2 := by
  induction steps generalizing s with
  | nil => simp only [List.forM, go_pure]; exact ⟨⟨(), by simp⟩, h⟩
  | cons st rest ih =>
    obtain ⟨⟨u, hu⟩, h1⟩ := step_inv H st h
    simp only [List.forM, go_bind]
    rcases e : Rec.go (st.run (M := M)) s with ⟨r, s'⟩
    rw [e] at hu h1; cases hu
    exact ih h1

/-- **No work lost**, end to end: on a machine with these git, hc and cgroup assumptions, after any run of sweeps and ends from any state `s0`,
every commit reachable before (from a branch, a tag, a remote ref or a worktree's HEAD) is reachable after, unless it
is the HEAD, or below the HEAD, of a worktree `x` that a `worktree remove` in the run took away, on the machine it ran
on, after `x` passed the sweep's `Gate` (which found it landed: `sweepGate_W1`); and every worktree there before is
there after, unless a `worktree remove` in the run took it away when it had nothing uncommitted, after it passed
`Gate`. -/
theorem no_work_lost (hg : GitReadsKeep M) (ht : ToolsKeep M) (hwr : WtRemove M) (hbd : BranchD M) (hdr : DelRef M)
    (hrp : RevParseHead M) (hk : HcKillEnds M) (hr : HcRmKeeps M) (hc : CgroupKillKeeps M) (s0 : Rec M) (steps : List Step) :
    let s := (Rec.go (steps.forM (Step.run (M := M))) s0).2
    (∀ c, M.Reach s0.w c → M.Reach s.w c ∨ ∃ i w m x k, s.log[i]? = some (w, .cmd (rmArgv m x) none) ∧
      GateAny m x (s.log.take i) ∧ M.head w x = some k ∧ M.Anc c k) ∧
    ∀ x, M.There s0.w x → M.There s.w x ∨ ∃ i w m, s.log[i]? = some (w, .cmd (rmArgv m x) none) ∧
      GateAny m x (s.log.take i) ∧ ¬ M.Dirty w x := by
  intro s
  obtain ⟨-, ⟨-, hR, hT⟩, hG⟩ := run_inv ⟨hg, ht, hwr, hbd, hdr, hrp, hk, hr, hc⟩ steps (s := s0) ⟨Kept.refl _, GoodFrom.base _ _⟩
  refine ⟨fun c hc => ?_, fun x hx => ?_⟩
  · rcases hR c hc with h | ⟨i, w, m, x, k, hi, he, hh, ha⟩
    · exact .inl h
    · exact .inr ⟨i, w, m, x, k, he, hG i w m x hi he, hh, ha⟩
  · rcases hT x hx with h | ⟨i, w, m, hi, he, hd⟩
    · exact .inl h
    · exact .inr ⟨i, w, m, he, hG i w m x hi he, hd⟩

end SwarmLean.SweepProofs
