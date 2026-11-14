import SwarmLean.Proofs.Sweep

/-! Each hypothesis `sweepGate_W1` takes is needed (the model's Trust.need_sweep_*): for each, a machine with the other
five on which a worktree passes the sweep's gate and the guarantee fails. The machines (`Tr`) list main `/m` and a
worktree `/x`, call `/x` clean and its HEAD landed on main (by ancestry, or by the same content when `anc` is false),
and make one tool fact false. -/

namespace SwarmLean.SweepProofs
open SwarmLean

/-- `sweepGate_W1`'s statement, of machine `M` -/
def GateW1 (M : Tools) : Prop := ∀ (s0 : Rec M) m x L, Gate s0 m x L →
    (∃ (p : String) (w : M.World), M.There s0.w p ∧ x = realW w p) ∧
    (∃ s : Rec M, s.log <+: L ∧ ¬ M.Inside s.w x) ∧
    (∃ wk, (wk, .cmd ["git", "--no-optional-locks", "-C", x, "status", "--porcelain"] none) ∈ L ∧ (M.There wk x → ¬ M.Dirty wk x) ∧
      ∃ t, (∃ st : Rec M, st.log <+: L ∧ t = M.now st.w) ∧
        ∀ gd, M.git wk ["-C", x, "rev-parse", "--absolute-git-dir"] none = some gd → t ≤ M.now wk → ¬ M.Recent wk x) ∧
    ∃ s sp sb : Rec M, s.log <+: L ∧ (M.kind s.w x true = .none ∨ ∃ b ∈ Rec.val (Bases.refs (Rec.val
      (Workspaces.protectedOf s0.db (some m) : RecM M _) sp) (some m) : RecM M _) sb, Reached x "HEAD" b L)

theorem gateW1 (ha : AncestorReach M) (hsc : SameContentReach M) (hlo : ListedOn M) (hsl : StatusClean M)
    (hcp : CwdsProc M) (htr : TouchedRecent M) : GateW1 M :=
  fun _ _ _ _ h => sweepGate_W1 ha hsc hlo hsl hcp htr h

/-- A machine with one worktree list, one clean `/x` landed on main, and the given tool facts; the commands the sweep
runs on `/x` told apart by length (`merge-base --is-ancestor` 7, `diff --name-only` 8, `diff --quiet` 9; of length 6,
`merge-base` has `-C` second and status `--no-optional-locks`). -/
def Tr (anc : Bool) (there dirty inside recent holds : Prop) : Tools :=
  { Tools.idle with
    World := Unit
    out := fun _ a _ =>
      if a = lsArgv then some ⟨0, "worktree /m\nworktree /x\n", ""⟩ else
      match a.length with
      | 7 => if anc then some ⟨0, "", ""⟩ else some ⟨1, "", ""⟩
      | 6 => if a[1]? = some "-C" then (if anc then none else some ⟨0, "mb\n", ""⟩) else some ⟨0, "", ""⟩
      | 8 => some ⟨0, "f\x00", ""⟩
      | 9 => some ⟨0, "", ""⟩
      | _ => none
    git := fun _ a _ => if a.getLast? = some "--absolute-git-dir" then some "/g" else none
    var := fun _ k => if k = "SWARM_OS" then some "Linux" else none
    list := fun _ _ => some []
    kind := fun _ _ _ => .dir
    now := fun _ => 2000
    Holds := fun _ _ _ _ => holds
    There := fun _ _ => there
    Dirty := fun _ _ => dirty
    Inside := fun _ _ => inside
    Recent := fun _ _ => recent }

section
variable {anc : Bool} {P Q R S T : Prop}

/-- The sweep's start: no agents, nothing run. -/
def tr0 : Rec (Tr anc P Q R S T) := ⟨(), {}, [], []⟩

/-- what `Lifecycle.landed /x [main] /m` runs on `Tr` -/
def trLog (anc : Bool) : List ((Tr anc P Q R S T).World × Call) :=
  ((), .cmd ["git", "--no-optional-locks", "-C", "/x", "status", "--porcelain"] none) ::
    ((), .cmd ["git", "-C", "/x", "merge-base", "--is-ancestor", "HEAD", "main"] none) ::
    if anc then [] else
      [((), .cmd ["git", "-C", "/x", "merge-base", "main", "HEAD"] none),
        ((), .cmd ["git", "-C", "/x", "diff", "--name-only", "-z", "mb", "HEAD"] none),
        ((), .cmd ["git", "-C", "/x", "diff", "--quiet", "HEAD", "main", "--", "f"] none)]

/-- the calls the gate needs: landed's, then the git dir read -/
def trL (anc : Bool) : List ((Tr anc P Q R S T).World × Call) :=
  trLog anc ++ [(show (Tr anc P Q R S T).World from (), .git ["-C", "/x", "rev-parse", "--absolute-git-dir"] none)]

theorem tr_refs : Rec.val (Bases.refs (Rec.val (Workspaces.protectedOf (tr0 : Rec (Tr anc P Q R S T)).db (some "/m") : RecM (Tr anc P Q R S T) _) tr0)
    (some "/m") : RecM (Tr anc P Q R S T) _) tr0 = ["main"] := by
  unfold Rec.val Rec.go; rfl

theorem tr_files : ("f\x00".splitOn "\x00").filter (fun x => decide (x ≠ "")) = ["f"] := by
  simp (config := {decide := true}) [String.splitOn, String.splitOnAux]

theorem tr_lines : lsLines (M := Tr anc P Q R S T) () = ["worktree /m", "worktree /x"] := by
  have h1 : "worktree /m\nworktree /x\n".splitOn "\n" = ["worktree /m", "worktree /x", ""] := by
    simp (config := {decide := true}) [String.splitOn, String.splitOnAux]
  have h2 : "worktree /m\nworktree /x\n".endsWith "\n" = true := by decide +kernel
  simp (config := {decide := true}) [lsLines, Tr, splitlines, h1, h2]

theorem strip_mb : strip "mb\n" = "mb" := by decide

theorem out_go {M : Tools} (argv : List String) (cwd : Option String) (s : Rec M) :
    Rec.go (Proc.output argv cwd [] : RecM M _) s = (.ok (M.out s.w argv cwd),
      { s with w := M.after s.w argv cwd, log := s.log ++ [(s.w, .cmd argv cwd)] }) := by unfold Rec.go; rfl
theorem kind_go {M : Tools} (p : String) (f : Bool) (s : Rec M) :
    Rec.go (Sys.kind p f : RecM M _) s = (.ok (M.kind s.w p f), s) := by unfold Rec.go; rfl

theorem tr_landed : Rec.go (Lifecycle.landed "/x" ["main"] (some "/m") : RecM (Tr anc P Q R S T) Bool) tr0 =
    (.ok true, { (tr0 : Rec (Tr anc P Q R S T)) with log := trLog anc }) := by
  cases anc
  · have af : ∀ a c, (Tr false P Q R S T).after () a c = () := fun _ _ => rfl
    have k : (Tr false P Q R S T).kind () "/x" true = .dir := rfl
    have o1 : (Tr false P Q R S T).out () ["git", "--no-optional-locks", "-C", "/x", "status", "--porcelain"] none = some ⟨0, "", ""⟩ := rfl
    have o2 : (Tr false P Q R S T).out () ["git", "-C", "/x", "merge-base", "--is-ancestor", "HEAD", "main"] none =
      some ⟨1, "", ""⟩ := rfl
    have o3 : (Tr false P Q R S T).out () ["git", "-C", "/x", "merge-base", "main", "HEAD"] none =
      some ⟨0, "mb\n", ""⟩ := rfl
    have o4 : (Tr false P Q R S T).out () ["git", "-C", "/x", "diff", "--name-only", "-z", "mb", "HEAD"] none =
      some ⟨0, "f\x00", ""⟩ := rfl
    have o5 : (Tr false P Q R S T).out () ["git", "-C", "/x", "diff", "--quiet", "HEAD", "main", "--", "f"] none =
      some ⟨0, "", ""⟩ := rfl
    simp (config := {decide := true}) only [Lifecycle.landed, Lifecycle.landedRef, Lifecycle.landedRef1,
      Lifecycle.code, Lifecycle.run, go_bind, go_pure, kind_go, out_go, List.forIn_cons, List.forIn_nil, af, k, o1, o2, o3,
      o4, o5, tr_files, strip_mb, py, Option.map, Option.bind, Option.getD, Option.filter, tr0, trLog, List.nil_append,
      List.cons_append, beq_iff_eq, Bool.or_true, ite_false, ite_true]
    all_goals rfl
  · unfold Rec.go; rfl

theorem tr_gate : Gate (M := Tr anc P Q R S T) tr0 "/m" "/x" (trL anc) where
  main := ⟨"worktree /m", by simp [tr0, tr_lines], by show "/m" = ("worktree /m".drop 9).toString; decide⟩
  notMain := by decide
  listed := ⟨("/x", none), by simp (config := {decide := true}) [tr0, tr_lines, Watchd.wtLines], (), rfl⟩
  unused := ⟨(), by simp [tr0, Agents.live]⟩
  noProc := ⟨tr0, [], List.nil_prefix, by unfold Rec.go; rfl, by simp⟩
  idle := ⟨(), 2000, List.mem_append_right _ (List.mem_singleton_self _),
    List.mem_append_left _ (List.mem_cons_self ..), ⟨"", by simp [Tr, lsArgv], by decide⟩,
    ⟨tr0, List.nil_prefix, rfl⟩, by simp [lastAt, Tr, Tools.idle, Watchd.SWEEP_IDLE]⟩
  landed := ⟨tr0, tr0, tr0, by rw [tr_refs, tr_landed]; exact List.prefix_append (trLog anc) _, by rw [tr_refs, tr_landed]⟩

theorem tr_ha (h : anc = false ∨ T) : AncestorReach (Tr anc P Q R S T) := by
  rintro w cwd ref b ⟨o, ho, hc⟩
  rcases h with rfl | h
  · simp [Tr, lsArgv] at ho; subst ho; simp at hc
  · exact h
theorem tr_hsc (h : anc = true ∨ T) : SameContentReach (Tr anc P Q R S T) := by
  intro w cwd ref b o d
  rcases h with rfl | h
  · simp [Tr, lsArgv]
  · intros; exact h
theorem tr_hlo (h : P) : ListedOn (Tr anc P Q R S T) := fun _ _ _ _ _ _ _ _ => h
theorem tr_hsl (h : ¬ Q) : StatusClean (Tr anc P Q R S T) := fun _ _ _ _ _ _ _ => h
theorem tr_hcp (h : ¬ R) : CwdsProc (Tr anc P Q R S T) := fun _ _ _ _ hr => absurd hr h
theorem tr_htr (h : ¬ S) : TouchedRecent (Tr anc P Q R S T) := fun _ _ _ hr => absurd hr h

end

theorem need_sweep_ancestor : ∃ M, SameContentReach M ∧ ListedOn M ∧ StatusClean M ∧ CwdsProc M ∧ TouchedRecent M ∧
    ¬ GateW1 M := by
  refine ⟨Tr true True False False False False, tr_hsc (.inl rfl), tr_hlo trivial, tr_hsl id, tr_hcp id, tr_htr id,
    fun h => ?_⟩
  obtain ⟨-, -, -, s, sp, sb, -, hr⟩ := h _ _ _ _ tr_gate
  simp only [Tr, Tools.idle, reduceCtorEq, false_or, Reached, exists_and_right] at hr
  obtain ⟨-, ⟨-, hf⟩ | ⟨w, br, hm⟩⟩ := hr
  · exact hf
  · have := List.mem_map_of_mem (f := Prod.snd) hm
    simp [trL, trLog, ghArgv] at this

theorem need_sweep_sameContent : ∃ M, AncestorReach M ∧ ListedOn M ∧ StatusClean M ∧ CwdsProc M ∧ TouchedRecent M ∧
    ¬ GateW1 M := by
  refine ⟨Tr false True False False False False, tr_ha (.inl rfl), tr_hlo trivial, tr_hsl id, tr_hcp id, tr_htr id,
    fun h => ?_⟩
  obtain ⟨-, -, -, s, sp, sb, -, hr⟩ := h _ _ _ _ tr_gate
  simp only [Tr, Tools.idle, reduceCtorEq, false_or, Reached, exists_and_right] at hr
  obtain ⟨-, ⟨-, hf⟩ | ⟨w, br, hm⟩⟩ := hr
  · exact hf
  · have := List.mem_map_of_mem (f := Prod.snd) hm
    simp [trL, trLog, ghArgv] at this

/-- `worktree list` lists a worktree that isn't there -/
theorem need_sweep_listedOn : ∃ M, AncestorReach M ∧ SameContentReach M ∧ StatusClean M ∧ CwdsProc M ∧
    TouchedRecent M ∧ ¬ GateW1 M := by
  refine ⟨Tr true False False False False True, tr_ha (.inr trivial), tr_hsc (.inr trivial), tr_hsl id, tr_hcp id,
    tr_htr id, fun h => ?_⟩
  obtain ⟨⟨_, _, hp, -⟩, -⟩ := h _ _ _ _ tr_gate
  exact hp

/-- `status` says clean of a dirty worktree -/
theorem need_sweep_statusClean : ∃ M, AncestorReach M ∧ SameContentReach M ∧ ListedOn M ∧ CwdsProc M ∧
    TouchedRecent M ∧ ¬ GateW1 M := by
  refine ⟨Tr true True True False False True, tr_ha (.inr trivial), tr_hsc (.inr trivial), tr_hlo trivial, tr_hcp id,
    tr_htr id, fun h => ?_⟩
  obtain ⟨-, -, ⟨_, -, hd, -⟩, -⟩ := h _ _ _ _ tr_gate
  exact hd trivial trivial

/-- `machine.cwds()` misses a process inside -/
theorem need_sweep_cwdsProc : ∃ M, AncestorReach M ∧ SameContentReach M ∧ ListedOn M ∧ StatusClean M ∧
    TouchedRecent M ∧ ¬ GateW1 M := by
  refine ⟨Tr true True False True False True, tr_ha (.inr trivial), tr_hsc (.inr trivial), tr_hlo trivial, tr_hsl id,
    tr_htr id, fun h => ?_⟩
  obtain ⟨-, ⟨_, -, hi⟩, -⟩ := h _ _ _ _ tr_gate
  exact hi trivial

/-- the mtimes read old of a worktree used just now -/
theorem need_sweep_touchedRecent : ∃ M, AncestorReach M ∧ SameContentReach M ∧ ListedOn M ∧ StatusClean M ∧
    CwdsProc M ∧ ¬ GateW1 M := by
  refine ⟨Tr true True False False True True, tr_ha (.inr trivial), tr_hsc (.inr trivial), tr_hlo trivial, tr_hsl id,
    tr_hcp id, fun h => ?_⟩
  obtain ⟨-, -, ⟨_, -, -, t, ⟨st, -, ht⟩, hr⟩, -⟩ := h _ _ _ _ tr_gate
  exact hr "/g" rfl (by subst ht; exact Int.le_refl _) trivial

end SwarmLean.SweepProofs
