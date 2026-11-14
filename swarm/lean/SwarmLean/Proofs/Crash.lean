import SwarmLean.Proofs.Cross
import SwarmLean.Dispatch
import Lean
import Init.Internal.Order.While

namespace SwarmLean.Crash
open Cross Board

variable {M : Tools}

/-- From state `s` to `s'`: `P` holds of the db, and of every db a transaction committed since (`Rec.commits`). -/
def Kept (P : Db → Prop) (s s' : Rec M) : Prop := P s'.db ∧ ∀ d ∈ s'.commits, d ∈ s.commits ∨ P d

theorem kept_trans {P : Db → Prop} {s s' s'' : Rec M} (h : Kept P s s') (h' : Kept P s' s'') : Kept P s s'' :=
  ⟨h'.1, fun d hd => (h'.2 d hd).elim (fun e => h.2 d e) .inr⟩

/-- `x` run from a state whose db has `P` leaves a db with `P`, and every transaction it commits on the way leaves
one: wherever the run stops, the db it committed last has `P`. -/
@[irreducible] def Keeps (P : Db → Prop) (x : RecM M α) : Prop := ∀ s, P s.db → Kept P s (Rec.go x s).2

theorem go_bind (x : RecM M α) (f : α → RecM M β) (s : Rec M) :
    Rec.go (x >>= f) s = match Rec.go x s with | (.ok a, s') => Rec.go (f a) s' | (.error e, s') => (.error e, s') := by
  simp only [Rec.go]
  change StateT.bind x (ExceptT.bindCont f) s = match x s with | (.ok a, s') => (f a) s' | (.error e, s') => (.error e, s')
  simp only [StateT.bind]
  rcases h : x s with ⟨r, s'⟩
  cases r <;> simp [ExceptT.bindCont] <;> rfl

variable {P : Db → Prop}

theorem keeps_bind {x : RecM M α} {f : α → RecM M β} (hx : Keeps P x) (hf : ∀ a, Keeps P (f a)) :
    Keeps P (x >>= f) := by
  unfold Keeps at *
  intro s hs
  rw [go_bind]
  have := hx s hs
  revert this
  rcases Rec.go x s with ⟨r, s'⟩
  cases r with
  | ok a => exact fun h => kept_trans h (hf a s' h.1)
  | error e => exact id

/-- A call that leaves the db. -/
theorem keeps_of {x : RecM M α} (h : ∀ s, (Rec.go x s).2.db = s.db ∧ (Rec.go x s).2.commits = s.commits) :
    Keeps P x := by
  unfold Keeps; exact fun s hs => ⟨(h s).1.symm ▸ hs, fun d hd => .inl ((h s).2 ▸ hd)⟩

theorem keeps_pure (a : α) : Keeps P (pure a : RecM M α) := keeps_of fun s => by simp only [Rec.go]; exact ⟨rfl, rfl⟩

theorem keeps_throw (e : Exit) : Keeps P (throw e : RecM M α) := keeps_of fun s => by simp only [Rec.go]; exact ⟨rfl, rfl⟩
theorem keeps_throwThe (e : Exit) : Keeps P (throwThe Exit e : RecM M α) := keeps_of fun s => by simp only [Rec.go]; exact ⟨rfl, rfl⟩

theorem keeps_map {f : α → β} {x : RecM M α} (hx : Keeps P x) : Keeps P (f <$> x) := by
  have : f <$> x = x >>= fun a => pure (f a) := by
    simp only [Functor.map, ExceptT.map, bind, ExceptT.bind, ExceptT.mk]
    funext s; simp only [StateT.bind]; rcases x s with ⟨r, s'⟩; cases r <;> rfl
  rw [this]; exact keeps_bind hx fun a => keeps_pure _

theorem go_eq (x : RecM M α) (s : Rec M) : Rec.go x s = x s := by simp only [Rec.go]; rfl

theorem keeps_tryCatch {x : RecM M α} {h : Exit → RecM M α} (hx : Keeps P x) (hh : ∀ e, Keeps P (h e)) :
    Keeps P (tryCatchThe Exit x h) := by
  unfold Keeps at *
  intro s hs
  have hx' : Kept P s (x s).2 := go_eq x s ▸ hx s hs
  rw [go_eq]
  change Kept P s (ExceptT.tryCatch x h s).2
  simp only [ExceptT.tryCatch, ExceptT.mk, bind, StateT.bind]
  revert hx'
  rcases e : x s with ⟨r, s'⟩
  cases r with
  | ok a => exact id
  | error er => intro h'; have := hh er s' h'.1; rw [go_eq] at this; exact kept_trans h' this

theorem keeps_forIn {xs : List β} {b : γ} {f : β → γ → RecM M (ForInStep γ)} (hf : ∀ a c, Keeps P (f a c)) :
    Keeps P (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact keeps_pure _
  | cons a as ih =>
    rw [List.forIn_cons]
    refine keeps_bind (hf a b) fun r => ?_
    split
    · exact keeps_pure _
    · exact ih

theorem keeps_ite {c : Prop} {_ : Decidable c} {x y : RecM M α} (hx : Keeps P x) (hy : Keeps P y) :
    Keeps P (if c then x else y) := by split <;> assumption

theorem keeps_dite {c : Prop} {_ : Decidable c} {x : c → RecM M α} {y : ¬ c → RecM M α} (hx : ∀ h, Keeps P (x h))
    (hy : ∀ h, Keeps P (y h)) : Keeps P (if h : c then x h else y h) := by split <;> simp_all

theorem keeps_mapConst {x : RecM M α} {b : β} (hx : Keeps P x) : Keeps P (Functor.mapConst b x) := by
  have : Functor.mapConst b x = Function.const _ b <$> x := rfl
  rw [this]; exact keeps_map hx

theorem keeps_mapM_loop {f : α → RecM M β} (hf : ∀ a, Keeps P (f a)) :
    ∀ (xs : List α) (acc : List β), Keeps P (List.mapM.loop f xs acc)
  | [], acc => keeps_pure _
  | a :: as, acc => by
    rw [List.mapM.loop]; exact keeps_bind (hf a) fun b => keeps_mapM_loop hf as _

theorem keeps_forIn_array {xs : Array β} {b : γ} {f : β → γ → RecM M (ForInStep γ)} (hf : ∀ a c, Keeps P (f a c)) :
    Keeps P (forIn xs b f) := by
  rw [← Array.forIn_toList]; exact keeps_forIn hf

theorem keeps_forIn_range {r : Std.Legacy.Range} {b : γ} {f : Nat → γ → RecM M (ForInStep γ)} (hf : ∀ a c, Keeps P (f a c)) :
    Keeps P (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact keeps_forIn hf

/-- A `repeat`/`while` loop whose every turn keeps `P` keeps it. Lean's `repeat` is a fixpoint that has a defined
result only for a run that ends (`Loop.forIn_eq_of_monadTail`); for those it holds (`loop_ends`). -/
def LoopsKeep (M : Tools) (P : Db → Prop) : Prop :=
  ∀ (β : Type) (l : Lean.Loop) (b : β) (f : Unit → β → RecM M (ForInStep β)), (∀ c, Keeps P (f () c)) →
    Keeps P (forIn l b f)

theorem keeps_loop {l : Lean.Loop} {b : β} {f : Unit → β → RecM M (ForInStep β)} (hL : LoopsKeep M P)
    (hf : ∀ c, Keeps P (f () c)) : Keeps P (forIn l b f) := hL β l b f hf

theorem keeps_txn {ts : List Table} {f : Db → Db × α} (h : ∀ db, P db → P (f db).1) :
    Keeps P (Store.txn ts f : RecM M α) := by
  unfold Keeps; intro s hs; simp only [Rec.go]
  refine ⟨h _ hs, fun d hd => ?_⟩
  have hd : d ∈ s.commits ++ [(f s.db).1] := hd
  rcases List.mem_append.1 hd with hd | hd
  · exact .inl hd
  · exact .inr (List.mem_singleton.1 hd ▸ h _ hs)

theorem keeps_ask (f : M.World → α) : Keeps P (Rec.ask f : RecM M α) := keeps_of fun s => by rw [go_eq]; exact ⟨rfl, rfl⟩
theorem keeps_cmd (argv : List String) (cwd : Option String) (f : M.World → α) :
    Keeps P (Rec.cmd argv cwd f : RecM M α) := keeps_of fun s => by rw [go_eq]; exact ⟨rfl, rfl⟩
theorem keeps_eff (e : Eff) (f : M.World → α) : Keeps P (Rec.eff e f : RecM M α) := keeps_of fun s => by rw [go_eq]; exact ⟨rfl, rfl⟩

theorem keeps_modifyGet {f : Rec M → α × Rec M} (h : ∀ s, (f s).2.db = s.db ∧ (f s).2.commits = s.commits) :
    Keeps P (modifyGet f : RecM M α) := keeps_of fun s => by rw [go_eq]; exact h s

theorem keeps_throw_bind (e : Exit) (f : α → RecM M β) : Keeps P (throwThe Exit e >>= f) := by
  unfold Keeps; intro s hs; rw [go_bind]
  have : Rec.go (throwThe Exit e : RecM M α) s = (.error e, s) := by simp only [Rec.go]; rfl
  rw [this]; exact ⟨hs, fun d hd => .inl hd⟩

theorem keeps_die_bind (x : String) (f : α → RecM M β) : Keeps P ((die x : RecM M α) >>= f) := by
  unfold die; rw [bind_assoc]
  refine keeps_bind (keeps_of fun s => by rw [go_eq]; exact ⟨rfl, rfl⟩) fun _ => keeps_throw_bind _ f

/-- `orDie e` then `f`: `f` runs only on `e = .ok a`, which its walk keeps in context. -/
theorem keeps_orDie_bind {e : Except String α} {f : α → RecM M β} (hf : ∀ a, e = .ok a → Keeps P (f a)) :
    Keeps P ((orDie e : RecM M α) >>= f) := by
  cases e with
  | ok a => simp only [orDie, pure_bind]; exact hf a rfl
  | error x => exact keeps_die_bind x f

open Lean Meta in
/-- `replaceTargetDefEq` without its `id <old goal>` hint: the walk changes the goal at every step, and the hints,
each holding the rest of the code, made the proof term grow with the square of the code. -/
def replaceBare (g : MVarId) (t : Expr) : MetaM MVarId := g.withContext do
  let n ← mkFreshExprSyntheticOpaqueMVar t (← g.getTag)
  g.assign n
  return n.mvarId!

open Lean Elab Tactic Meta in
/-- Fails unless the goal is `Keeps P x`. -/
elab "is_keeps" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isAppOf ``Keeps do throwError "not Keeps"

open Lean Elab Tactic Meta in
/-- Unfolds the call `x` of a goal `Keeps P x` one step. -/
elab "unfold_head" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOf ``Keeps do throwError "not Keeps"
  let x := t.appArg!
  if [``ForIn.forIn, ``ForIn'.forIn', ``Bind.bind, ``Functor.map, ``Pure.pure, ``Seq.seq, ``SeqLeft.seqLeft, ``SeqRight.seqRight].any x.isAppOf then
    throwError "unfold_head: no lemma for {x}"
  match ← unfoldDefinition? x with
  | some x' => replaceMainGoal [← replaceBare g (mkApp t.appFn! x')]
  | none =>
    let x' ← match x.getAppFn with
      | .proj n i st => do
        let st' ← whnf st
        whnfCore (mkAppN (.proj n i st') x.getAppArgs)
      | _ => withTransparency .instances <| whnfCore (← withTransparency .instances <| whnf x)
    if x' == x then throwError "unfold_head: can't unfold {x}"
    replaceMainGoal [← replaceBare g (mkApp t.appFn! x')]

/-- A clock read on a machine whose clock reads no later than `t`: the value is at most `t`. -/
theorem keeps_now_bind {t : Int} {f : Int → RecM M β} (hM : ∀ w, M.now w ≤ t) (hf : ∀ a, a ≤ t → Keeps P (f a)) :
    Keeps P ((Clock.now : RecM M Int) >>= f) := by
  unfold Keeps at *
  intro s hs
  rw [go_bind]
  have e : Rec.go (Clock.now : RecM M Int) s = (.ok (M.now s.w), s) := by rw [go_eq]; rfl
  rw [e]; exact hf _ (hM _) s hs

open Lean Meta in
/-- `∀ ys, (∀ vs, K (y₁ vs)) → … → K (matcher … ys)`: `keeps_match`'s goal with the alternatives abstracted. -/
def matchGen (K f : Expr) (args : Array Expr) (a0 : Nat) : List Expr → Array Expr → MetaM Expr
    | [], ys => do
      let mut as := args
      for i in [0:ys.size] do as := as.set! (a0 + i) ys[i]!
      let body := mkApp K (mkAppN f as)
      let hs ← ys.mapM fun y => do
        forallTelescope (← inferType y) fun vs _ => mkForallFVars vs (mkApp K (mkAppN y vs))
      let body := hs.foldr (fun h acc => .forallE `h h acc .default) body
      mkForallFVars ys body
    | a :: rest, ys => do
      withLocalDeclD `y (← inferType a) fun y => matchGen K f args a0 rest (ys.push y)

open Lean Meta in
/-- `matchGen`'s goal with the discriminants abstracted first. -/
def discrGen (K f : Expr) (args : Array Expr) (d0 a0 : Nat) (alts : List Expr) : List Expr → Array Expr → MetaM Expr
  | [], dvs => do
    let mut as := args
    for i in [0:dvs.size] do as := as.set! (d0 + i) dvs[i]!
    mkForallFVars dvs (← matchGen K f as a0 alts #[])
  | d :: rest, dvs => do withLocalDeclD `d (← inferType d) fun y => discrGen K f args d0 a0 alts rest (dvs.push y)

open Lean Elab Tactic Meta in
/-- `Keeps P (match d with alts)`: the alternatives abstracted (`split` on the small goal), each left as a goal
`∀ vars, Keeps P (alt vars)`. `split` on the goal itself costs ~0.1 s at the size of a command's code. -/
elab "keeps_match" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOf ``Keeps do throwError "keeps_match: not Keeps"
  let x := t.appArg!.consumeMData
  let some c := x.getAppFn.constName? | throwError "keeps_match: no head"
  let some info ← getMatcherInfo? c | throwError "keeps_match: not a matcher"
  let args := x.getAppArgs
  unless args.size == info.arity do
    throwError "keeps_match: extra arguments"
  let a0 := info.getFirstAltPos
  let alts := args.extract a0 (a0 + info.numAlts)
  let K := t.appFn!
  -- the discriminants abstracted too: `split` reduces a big one (a `timing …` field) and times out
  let d0 := info.getFirstDiscrPos
  let ds := args.extract d0 (d0 + info.numDiscrs)
  let T ← discrGen K x.getAppFn args d0 a0 alts.toList ds.toList #[]
  let m ← mkFreshExprMVar T
  let stx ← `(tactic| (intros; split <;> (apply_assumption)))
  let r ← Tactic.run m.mvarId! (Term.withoutErrToSorry <| withoutRecover <| evalTactic stx)
  unless r.isEmpty do throwError "keeps_match: split left goals"
  -- the hypotheses for the real alternatives
  let mut ty ← instantiateForall T (ds ++ alts)
  let mut hs : Array Expr := #[]
  for _ in alts do
    let .forallE _ d b _ := ty | throwError "keeps_match: shape"
    let h ← mkFreshExprSyntheticOpaqueMVar d
    hs := hs.push h
    ty := b.instantiate1 h
  g.assign (mkAppN m (ds ++ alts ++ hs))
  replaceMainGoal (hs.toList.map (·.mvarId!))

open Lean Elab Tactic Meta in
/-- One step of `keeps_walk`, chosen by the head of the code. -/
elab "keeps_step" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    if t.isForall then evalTactic (← `(tactic| intro)); return
    unless t.isAppOf ``Keeps do throwError "keeps_step: not Keeps"
    let x := t.appArg!.consumeMData
    -- a `have`/`let`: a join point (a function into the monad) stays abstract, any other value is substituted
    let letParts : Option (Expr × Expr) := match x with
      | .letE _ _ v b _ => some (v, b)
      | _ => if x.isAppOfArity ``letFun 4 then
          match x.appArg! with | .lam _ _ b _ => some (x.appFn!.appArg!, b) | _ => none
        else none
    if let some (v, b) := letParts then
      let ty ← whnfD (← inferType v)
      let n ← forallTelescope ty fun xs r => return (if r.isAppOf ``RecM || r.isAppOf ``ExceptT then xs.size else 0)
      if n == 0 then
        replaceMainGoal [← replaceBare g (mkApp t.appFn! (b.instantiate1 v))]
      else
        -- a join point: `∀ xs, Keeps P (v xs)`, and the body for an abstract `y` with that
        let P := t.appFn!.appArg!
        let K (e : Expr) : MetaM Expr := mkAppM ``Keeps #[P, e]
        let vty ← inferType v
        let hv ← forallTelescope vty fun xs _ => do mkForallFVars xs (← K (mkAppN v xs))
        let g1 ← mkFreshExprSyntheticOpaqueMVar hv
        let g2ty ← withLocalDeclD `jp vty fun y => do
          let hy ← forallTelescope vty fun xs _ => do mkForallFVars xs (← K (mkAppN y xs))
          withLocalDeclD `hjp hy fun h => do mkForallFVars #[y, h] (mkApp t.appFn! (b.instantiate1 y))
        let g2 ← mkFreshExprSyntheticOpaqueMVar g2ty
        g.assign (mkApp2 g2 v g1)
        replaceMainGoal [g1.mvarId!, g2.mvarId!]
      return
    if x.isHeadBetaTarget then
      replaceMainGoal [← replaceBare g (mkApp t.appFn! x.headBeta)]; return
    let run (s : TSyntax `tactic) := evalTactic s
    if x.getAppFn.isFVar then run (← `(tactic| apply_assumption)); return
    let some c := x.getAppFn.constName? | run (← `(tactic| unfold_head))
    if c == ``Bind.bind then
      if (x.getArg! 4).isAppOf ``orDie then run (← `(tactic| apply keeps_orDie_bind))
      else if (x.getArg! 4).isAppOf ``Lifecycle.readsNow then
        run (← `(tactic| simp only [Lifecycle.readsNow, bind_assoc, pure_bind]))
      else if (x.getArg! 4).isAppOf ``Clock.now then run (← `(tactic| (apply keeps_now_bind; assumption)))
      else run (← `(tactic| apply keeps_bind))
    else if c == ``Store.txn then run (← `(tactic| apply keeps_txn))
    else if c == ``Pure.pure then run (← `(tactic| apply keeps_pure))
    else if c == ``Functor.map then run (← `(tactic| apply keeps_map))
    else if c == ``MonadExcept.throw || c == ``MonadExceptOf.throw || c == ``throwThe then
      run (← `(tactic| first | apply keeps_throw | apply keeps_throwThe))
    else if c == ``tryCatchThe || c == ``MonadExceptOf.tryCatch || c == ``MonadExcept.tryCatch then
      run (← `(tactic| apply keeps_tryCatch))
    else if c == ``ForIn.forIn then
      run (← `(tactic| first | apply keeps_forIn | apply keeps_forIn_range | apply keeps_forIn_array | (apply keeps_loop; assumption)))
    else if c == ``Rec.ask then run (← `(tactic| apply keeps_ask))
    else if c == ``Rec.cmd then run (← `(tactic| apply keeps_cmd))
    else if c == ``Rec.eff then run (← `(tactic| apply keeps_eff))
    else if c == ``modifyGet || c == ``MonadStateOf.modifyGet then run (← `(tactic| (apply keeps_modifyGet; intro; exact ⟨rfl, rfl⟩)))
    else if c == ``ite then run (← `(tactic| apply keeps_ite))
    else if c == ``dite then run (← `(tactic| apply keeps_dite))
    else if c == ``Functor.mapConst then run (← `(tactic| apply keeps_mapConst))
    else if c == ``List.mapM.loop then run (← `(tactic| apply keeps_mapM_loop))
    else if (← isMatcher c) then run (← `(tactic| first | keeps_match | split))
    else if (← getEnv).contains (`SwarmLean.Crash.K ++ c) then
      -- a function with its own lemma (`K.<its name>`): applied, its hypotheses from the context
      run (← `(tactic| (apply $(mkIdent (`SwarmLean.Crash.K ++ c))) <;> assumption))
    else run (← `(tactic| unfold_head))

/-- Walks the code of a goal `Keeps P x`, leaving each transaction's step as a goal. -/
elab "keeps_walk" : tactic => do
  let gs ← Lean.Elab.Tactic.getGoals
  let stx ← `(tactic| keeps_step)
  let step (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM (List Lean.MVarId) := Lean.Elab.Tactic.evalTacticAt stx g
  -- `repeat'`'s own cap (100000 steps) is too small for the biggest commands
  let gs' ← Lean.Meta.repeat' step gs (maxIters := 100000000)
  Lean.Elab.Tactic.setGoals gs'

/-! ## The cross-area invariant -/

/-- From `a` to `b` the tasks and locks are as they were, no agent stops being live (and the user does not start),
and the message log and cursors only grow: what a step that is not a task, lock or end step does. -/
def XGrow (a b : Db) : Prop :=
  b.tasks = a.tasks ∧ b.taskNext = a.taskNext ∧ b.locks = a.locks ∧ Locks.Grows a b ∧ Inbox.Grows a b

theorem xinv_of_xgrow {a b : Db} {t : Int} (g : XGrow a b) (h : XInv a t) : XInv b t :=
  ⟨binv_same g.1 g.2.1 h.1, Inbox.grows_inv g.2.2.2.2 h.2.1, Locks.good_grow g.2.2.1 g.2.2.2.1 h.2.2⟩

theorem xgrow_refl (a : Db) : XGrow a a := ⟨rfl, rfl, rfl, Locks.grows_refl rfl, Inbox.grows_refl a⟩

/-- A step that changes none of the tables the invariant reads. -/
theorem xgrow_same {a b c : Db} (g : XGrow a b) (ht : c.tasks = b.tasks) (hn : c.taskNext = b.taskNext)
    (hl : c.locks = b.locks) (ha : c.agents = b.agents) (hm : c.msgs = b.msgs) (hc : c.cursors = b.cursors)
    (hmn : c.msgNext = b.msgNext) : XGrow a c :=
  ⟨ht.trans g.1, hn.trans g.2.1, hl.trans g.2.2.1, Locks.grows_of_agents ha g.2.2.2.1,
   Inbox.grows_trans g.2.2.2.2 (Inbox.grows_of_eq hm hc hmn)⟩

theorem xgrow_log {a b : Db} (g : XGrow a b) ts ag k p d : XGrow a (b.log ts ag k p d) :=
  xgrow_same g rfl rfl rfl rfl rfl rfl rfl

theorem xgrow_setMeta {a b : Db} (g : XGrow a b) k v : XGrow a (b.setMeta k v) := by
  unfold Db.setMeta; split <;> exact xgrow_same g rfl rfl rfl rfl rfl rfl rfl

theorem xgrow_delMeta {a b : Db} (g : XGrow a b) k : XGrow a (Agents.delMeta b k) := xgrow_same g rfl rfl rfl rfl rfl rfl rfl

theorem xgrow_post {a b : Db} (g : XGrow a b) now frm dest body u k : XGrow a (Msgs.post b now frm dest body u k).1 :=
  ⟨g.1, g.2.1, g.2.2.1, Locks.grows_of_agents rfl g.2.2.2.1, Inbox.grows_trans g.2.2.2.2 (Inbox.grows_post _ _ _ _ _ _ _)⟩

theorem xgrow_say {a b : Db} (g : XGrow a b) now dest body u k : XGrow a (Watchd.say b now dest body u k) :=
  xgrow_post g _ _ _ _ _ _

theorem xgrow_workspaces {a b : Db} (g : XGrow a b) w : XGrow a { b with workspaces := w } :=
  xgrow_same g rfl rfl rfl rfl rfl rfl rfl
theorem xgrow_cis {a b : Db} (g : XGrow a b) w : XGrow a { b with cis := w } := xgrow_same g rfl rfl rfl rfl rfl rfl rfl
theorem xgrow_metas {a b : Db} (g : XGrow a b) w : XGrow a { b with metas := w } := xgrow_same g rfl rfl rfl rfl rfl rfl rfl
theorem xgrow_conflicts {a b : Db} (g : XGrow a b) w : XGrow a { b with conflicts := w } :=
  xgrow_same g rfl rfl rfl rfl rfl rfl rfl
theorem xgrow_pairkeys {a b : Db} (g : XGrow a b) w : XGrow a { b with pairkeys := w } :=
  xgrow_same g rfl rfl rfl rfl rfl rfl rfl
theorem xgrow_events {a b : Db} (g : XGrow a b) w : XGrow a { b with events := w } := xgrow_same g rfl rfl rfl rfl rfl rfl rfl

/-- An agent row changed but for its name and whether it ended. -/
theorem xgrow_setAgent {a b : Db} (g : XGrow a b) n (f : Agent → Agent) (hn : ∀ x, (f x).name = x.name)
    (he : ∀ x, (f x).ended = x.ended) : XGrow a (b.setAgent n f) := by
  refine ⟨g.1, g.2.1, g.2.2.1, Locks.grows_trans g.2.2.2.1 ?_, Inbox.grows_trans g.2.2.2.2 (Inbox.grows_of_eq rfl rfl rfl)⟩
  have e : ∀ x, Locks.Live (b.setAgent n f) x = Locks.Live b x := fun x => by
    simp only [Locks.Live, Db.setAgent, List.any_map]
    congr 1; funext y; simp only [Function.comp]; split <;> simp [hn, he]
  exact ⟨fun x h => (e x) ▸ h, fun x h => .inl ((e x) ▸ h)⟩

open Lean Elab Tactic Meta in
/-- One step of `xgrow`, chosen by the head of `b` in a goal `XGrow a b`: never a unification that could unfold a step. -/
elab "xgrow1" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``XGrow 2 do throwError "xgrow1: not XGrow"
  let a := t.appFn!.appArg!
  let b := t.appArg!
  if a == b then g.assign (mkApp (mkConst ``xgrow_refl) a); return
  let b' := match b with
    | .proj _ _ p => p
    | _ => if b.isAppOfArity ``Prod.fst 3 then b.getArg! 2 else b
  let some c := b'.getAppFn.constName? | throwError "xgrow1: no head"
  if c == ``ite || c == ``dite || (← isMatcher c) then evalTactic (← `(tactic| split)); return
  let ls : List Name :=
    if c == ``Db.log then [``xgrow_log] else if c == ``Db.setMeta then [``xgrow_setMeta]
    else if c == ``Agents.delMeta then [``xgrow_delMeta] else if c == ``Watchd.say then [``xgrow_say]
    else if c == ``Msgs.post then [``xgrow_post] else if c == ``Db.setAgent then [``xgrow_setAgent]
    else if c == ``Db.mk then [``xgrow_workspaces, ``xgrow_cis, ``xgrow_metas, ``xgrow_events, ``xgrow_conflicts,
      ``xgrow_pairkeys] else []
  for l in ls do
    try evalTactic (← `(tactic| with_reducible apply $(mkIdent l))); return catch _ => pure ()
  throwError "xgrow1: no lemma for {c}"

/-- Closes `XGrow a b` for `b` a chain of steps on `a` that keep the invariant's tables (or only grow the inbox). -/
macro "xgrow" : tactic => `(tactic| (repeat' (first | xgrow1 | (intro; rfl) | (intro; (try dsimp only); split <;> rfl))))

theorem xinv_locks_filter {db : Db} {t : Int} {p : Lock → Bool} (h : XInv db t) :
    XInv { db with locks := db.locks.filter p } t :=
  ⟨binv_same rfl rfl h.1, Inbox.grows_inv (Inbox.grows_of_eq rfl rfl rfl) h.2.1,
   Locks.good_sub (fun _ hl => (List.mem_filter.1 hl).1) (fun _ h => h) (fun _ _ _ _ h => h) h.2.2⟩

/-- The locks mapped by a change that keeps each lock's path, agent and lease (watchd marking a lock seen). -/
theorem xinv_locks_map {db : Db} {t : Int} {f : Lock → Lock}
    (hf : ∀ l, (f l).agent = l.agent ∧ (f l).path = l.path ∧ (f l).lease_until = l.lease_until) (h : XInv db t) :
    XInv { db with locks := db.locks.map f } t := by
  refine ⟨binv_same rfl rfl h.1, Inbox.grows_inv (Inbox.grows_of_eq rfl rfl rfl) h.2.1, ?_, ?_⟩
  · intro l hl a e
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
    rw [(hf u).1] at e
    exact h.2.2.1 u hu a e
  · intro l hl m hm hl' hm' hne
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hm
    have held : ∀ w, Locks.HeldAt { db with locks := db.locks.map f } t (f w) → Locks.HeldAt db t w :=
      fun w ⟨a, h1, h2, h3⟩ => ⟨a, (hf w).1 ▸ h1, (hf w).2.2 ▸ h2, h3⟩
    rw [(hf u).2.1, (hf v).2.1]
    exact h.2.2.2 u hu v hv (held u hl') (held v hm') (by rw [(hf u).1, (hf v).1] at hne; exact hne)

theorem X.List.foldl {β : Type} {db : Db} {t : Int} {f : Db → β → Db} {l : List β}
    (hf : ∀ d b, XInv d t → XInv (f d b) t) (h : XInv db t) : XInv (l.foldl f db) t := by
  induction l generalizing db with
  | nil => exact h
  | cons a as ih => exact ih (hf _ _ h)

/-- A fold whose accumulator is the db and a note list. -/
theorem X.List.foldl' {β γ : Type} {p : Db × γ} {t : Int} {f : Db × γ → β → Db × γ} {l : List β}
    (hf : ∀ d c b, XInv d t → XInv (f (d, c) b).1 t) (h : XInv p.1 t) : XInv (l.foldl f p).1 t := by
  induction l generalizing p with
  | nil => exact h
  | cons a as ih => exact ih (by have := hf p.1 p.2 a h; exact this)

/-- Closes a step's goal `XInv (f db).1 t` from `XInv db t`. -/
syntax "xstep" : tactic

syntax "xside" : tactic

theorem dropWhile_nil_iff {p : α → Bool} : ∀ {l : List α}, l.dropWhile p = [] ↔ l.all p = true
  | [] => by simp
  | a :: as => by
    simp only [List.dropWhile_cons, List.all_cons, Bool.and_eq_true]
    split <;> simp_all [dropWhile_nil_iff]

/-- A text strips to nothing exactly when it is all white space. -/
theorem strip_eq_empty {s : String} : strip s = "" ↔ s.toList.all isSpace = true := by
  unfold strip
  rw [String.ofList_eq_empty_iff, List.reverse_eq_nil_iff, dropWhile_nil_iff, List.all_reverse]
  constructor
  · intro h
    have : ∀ l : List Char, (l.dropWhile isSpace).all isSpace = true → l.all isSpace = true := by
      intro l; induction l with
      | nil => simp
      | cons a as ih => simp only [List.dropWhile_cons, List.all_cons]; split <;> simp_all
    exact this _ h
  · intro h
    have : ∀ l : List Char, l.all isSpace = true → (l.dropWhile isSpace).all isSpace = true := by
      intro l; induction l with
      | nil => simp
      | cons a as ih => simp only [List.dropWhile_cons, List.all_cons]; split <;> simp_all
    exact this _ h

theorem evOk_append {a b : String} (ha : a.toList.all isSpace = false) : EvOk (some (a ++ b)) :=
  ⟨_, rfl, fun e => by rw [strip_eq_empty, String.toList_append, List.all_append] at e; simp [ha] at e⟩

theorem evOk_lit {a : String} (ha : a.toList.all isSpace = false) : EvOk (some a) :=
  ⟨_, rfl, fun e => by rw [strip_eq_empty] at e; simp [ha] at e⟩

theorem evOk_left {a b : String} (ha : EvOk (some a)) : EvOk (some (a ++ b)) := by
  obtain ⟨s, hs, hne⟩ := ha; cases hs
  refine ⟨_, rfl, fun e => hne ?_⟩
  rw [strip_eq_empty, String.toList_append, List.all_append, Bool.and_eq_true] at e
  exact strip_eq_empty.2 e.1

/-- A side goal `∀ u, TaskOk u → TaskOk (f u)`. -/
macro "xok" : tactic => `(tactic| (intro u hu; simp only [TaskOk, Task.Owned, DoneEv] at hu ⊢; first | exact hu | (simp_all [evOk_append]; done) | (refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp_all [evOk_append]; done) | (split <;> simp_all [evOk_append]; done) | (refine ⟨⟨?_, ?_⟩, fun _ => ?_⟩ <;> (try simp_all) <;> (repeat (with_reducible apply evOk_left)) <;> exact evOk_lit (by decide))))

open Lean Elab Tactic Meta in
/-- The step of a goal `XInv e t` in normal form: `(a, b).1` is `a`, a `have` substituted, a `match` on pairs whose
patterns are pairs reduced (each pair discriminant `d` read as `(d.1, d.2)`, which it is by eta). -/
partial def xnormE (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  match e with
  | .letE _ _ v b _ => return ← xnormE (b.instantiate1 v)
  | .mdata _ x => return ← xnormE x
  | .proj ``Prod 0 p =>
    let p' ← xnormE p
    if p'.isAppOfArity ``Prod.mk 4 then return ← xnormE (p'.getArg! 2)
    return .proj ``Prod 0 p'
  | _ => pure ()
  if e.isAppOfArity ``letFun 4 then
    if let .lam _ _ b _ := e.appArg! then return ← xnormE (b.instantiate1 e.appFn!.appArg!)
  if e.isAppOfArity ``Prod.fst 3 then
    let p' ← xnormE (e.getArg! 2)
    if p'.isAppOfArity ``Prod.mk 4 then return ← xnormE (p'.getArg! 2)
    return mkAppN e.getAppFn #[e.getArg! 0, e.getArg! 1, p']
  if let some c := e.getAppFn.constName? then
    if let some info ← getMatcherInfo? c then
      let args := e.getAppArgs
      let ds := (args.extract info.getFirstDiscrPos (info.getFirstDiscrPos + info.numDiscrs))
      let rec eta (d : Expr) : MetaM Expr := do
        let ty ← whnfR (← inferType d)
        if ty.isAppOfArity ``Prod 2 && !d.isAppOfArity ``Prod.mk 4 then
          let a ← eta (← mkAppM ``Prod.fst #[d]); let b ← eta (← mkAppM ``Prod.snd #[d])
          return mkApp4 (mkConst ``Prod.mk ty.getAppFn.constLevels!) ty.appFn!.appArg! ty.appArg! a b
        return d
      let ds' ← ds.mapM eta
      let mut args' := args
      for i in [0:ds'.size] do args' := args'.set! (info.getFirstDiscrPos + i) ds'[i]!
      let e' := mkAppN e.getAppFn args'
      if let ReduceMatcherResult.reduced r ← withReducible <| Lean.Meta.reduceMatcher? e' then return ← xnormE r
      return e'
  return e

open Lean Elab Tactic Meta in
/-- Puts the step of a goal `XInv e t` in `xnormE`'s normal form; fails when it is already. -/
elab "xnorm" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``XInv 2 do throwError "xnorm: not XInv"
  let e := t.appFn!.appArg!
  let e' ← xnormE e
  if e' == e then throwError "xnorm: normal"
  replaceMainGoal [← replaceBare g (mkApp2 t.appFn!.appFn! e' t.appArg!)]

open Lean Elab Tactic Meta in
/-- Rewrites a goal `XInv (a, b).1 t` to `XInv a t`; fails on any other goal. -/
elab "pair_fst" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``XInv 2 do throwError "pair_fst: not XInv"
  let e := t.appFn!.appArg!
  let a? : Option Expr := match e with
    | .proj ``Prod 0 p => if p.isAppOfArity ``Prod.mk 4 then some (p.getArg! 2) else none
    | _ => if e.isAppOfArity ``Prod.fst 3 && (e.getArg! 2).isAppOfArity ``Prod.mk 4 then some ((e.getArg! 2).getArg! 2)
      else none
  let some a := a? | throwError "pair_fst: no pair"
  replaceMainGoal [← replaceBare g (mkApp2 t.appFn!.appFn! a t.appArg!)]

open Lean Elab Tactic Meta in
/-- Splits a goal `XInv e t` (or `XInv e.1 t`) whose `e` is an `if` or a `match`; fails on any other. -/
elab "split_step" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isAppOfArity ``XInv 2 do throwError "split_step: not XInv"
  let e := t.appFn!.appArg!
  let e := match e with
    | .proj _ _ p => p
    | _ => if e.isAppOfArity ``Prod.fst 3 then e.getArg! 2 else e
  let some c := e.getAppFn.constName? | throwError "split_step: no head"
  unless c == ``ite || c == ``dite || (← isMatcher c) do throwError "split_step: not a split"
  evalTactic (← `(tactic| split))

open Lean Elab Tactic Meta in
/-- Closes the goal by a hypothesis whose type is the goal's, up to `dsimp only` (beta, projections of a
constructor): never `assumption`, whose unifier would unfold a step at any transparency and time out. -/
elab "xassume" : tactic => withMainContext do
  let g ← getMainGoal
  let close (g : MVarId) : MetaM Bool := g.withContext do
    let tgt ← instantiateMVars (← g.getType)
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if (← instantiateMVars d.type) == tgt then g.assign d.toExpr; return true
    return false
  if ← close g then return
  let tgt ← instantiateMVars (← g.getType)
  if tgt.hasMVar && tgt.isAppOf ``Eq then
    for d in ← getLCtx do
      if !d.isImplementationDetail && d.type.isAppOf ``Eq then
        if ← withReducible (isDefEq d.type tgt) then g.assign d.toExpr; return
  evalTactic (← `(tactic| dsimp only))
  unless ← close (← getMainGoal) do throwError "xassume: no hypothesis"

open Lean Elab Tactic Meta in
/-- On a goal `XInv e t` (or `XInv e.1 t`) whose `e` is a call of `c`, applies the step's own lemma `X.<c>`,
its hypotheses from the context at reducible transparency; fails when there is none. -/
elab "xlemma" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isAppOfArity ``XInv 2 do throwError "xlemma: not XInv"
  let e := t.appFn!.appArg!
  let e := match e with
    | .proj _ _ p => p
    | _ => if e.isAppOfArity ``Prod.fst 3 then e.getArg! 2 else e
  let some c := e.getAppFn.constName? | throwError "xlemma: no head"
  let n := `SwarmLean.Crash.X ++ c.replacePrefix `SwarmLean .anonymous
  let ns := [n, n.appendAfter "'"].filter (← getEnv).contains
  if ns.isEmpty then throwError "xlemma: no X.{c}"
  for n in ns do
    try evalTactic (← `(tactic| ((with_reducible apply $(mkIdent n)) <;> xside))); return
    catch _ => pure ()
  throwError "xlemma: X.{c} did not apply"

open Lean Elab Tactic Meta in
/-- On a goal `XInv b t`, with `h : XInv a t` in context: leaves `XGrow a b`. -/
elab "xfrom" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isAppOfArity ``XInv 2 do throwError "xfrom: not XInv"
  for d in ← getLCtx do
    let ty ← instantiateMVars d.type
    if !d.isImplementationDetail && ty.isAppOfArity ``XInv 2 && ty.appArg! == t.appArg! then
      evalTactic (← `(tactic| refine xinv_of_xgrow ?_ $(← Term.exprToSyntax d.toExpr)))
      return
  throwError "xfrom: no XInv hypothesis"

macro_rules | `(tactic| xstep) => `(tactic| (try xnorm); first
  | xassume
  | xlemma
  | (xfrom; xgrow; done)
  | ((with_reducible apply xinv_locks_filter) <;> xside)
  | ((with_reducible apply xinv_locks_map) <;> xside)
  | ((with_reducible apply xinv_addTask) <;> xside)
  | (split_step <;> xstep))

/-- A side goal of a step's lemma: a hypothesis, a field the change keeps, or another step's invariant. -/
macro_rules
  | `(tactic| xside) =>
    `(tactic| first | xassume | rfl | (intro; rfl) | (intro; (try dsimp only); (split <;> rfl)) | (intro; (try dsimp only); (split <;> exact ⟨rfl, rfl, rfl⟩)) | xstep | (intros; xstep) | xok)

/-! ## Each step keeps the invariant (`X.<step>`, used by `xlemma`) -/

theorem X.Locks.lock {c : Tasks.Ctx} {p r l : String} {db : Db} {t : Int} (hn : c.now ≤ t) (h : XInv db t) :
    XInv (Locks.lock c p r l db).1 t :=
  step_xinv (.lock (.lock c p r l)) (fun _ hx c' _ _ _ e => by
    rw [List.mem_singleton.1 hx] at e; cases e; exact hn) h
theorem X.Locks.unlock {me p : String} {now : Int} {db : Db} {t : Int} (h : XInv db t) :
    XInv (Locks.unlock me p now db) t := step_xinv (.lock (.unlock me p now)) (fun _ hx _ _ _ _ e => by
    rw [List.mem_singleton.1 hx] at e; cases e) h

/-- A step that keeps the tasks and the locks, lets no agent stop being live (nor the user start), and only grows the
message log and cursors keeps the invariant. -/
theorem xinv_frame {a b : Db} {t : Int} (ht : b.tasks = a.tasks) (hn : b.taskNext = a.taskNext) (hl : b.locks = a.locks)
    (hg : Locks.Grows a b) (hi : Inbox.Grows a b) (h : XInv a t) : XInv b t := xinv_of_xgrow ⟨ht, hn, hl, hg, hi⟩ h

/-- A step that changes only the tasks, keeping the board's invariant. -/
theorem xinv_tasks {a b : Db} {t : Int} (hb : BInv a → BInv b) (hl : b.locks = a.locks) (ha : b.agents = a.agents)
    (hm : b.msgs = a.msgs) (hc : b.cursors = a.cursors) (hmn : b.msgNext = a.msgNext) (h : XInv a t) : XInv b t :=
  ⟨hb h.1, Inbox.grows_inv (Inbox.grows_of_eq hm hc hmn) h.2.1, Locks.good_grow hl (Locks.grows_refl ha) h.2.2⟩

theorem nolock {x : XCmd} {t : Int} (hx : ∀ c p r l, x ≠ .lock (.lock c p r l)) : XBefore t [x] :=
  fun _ hy c p r l e => absurd (List.mem_singleton.1 hy ▸ e) (hx c p r l)

section
variable {db : Db} {t : Int}
theorem X.Tasks.add {c a} (h : XInv db t) : XInv (Tasks.add c a db).1 t := step_xinv (.task (.add c a)) (nolock nofun) h
theorem X.Tasks.claim {c i l} (h : XInv db t) : XInv (Tasks.claim c i l db).1 t := step_xinv (.task (.claim c i l)) (nolock nofun) h
theorem X.Tasks.after {c i l} (h : XInv db t) : XInv (Tasks.after c i l db).1 t := step_xinv (.task (.after c i l)) (nolock nofun) h
theorem X.Tasks.priority {c i p} (h : XInv db t) : XInv (Tasks.priority c i p db).1 t :=
  step_xinv (.task (.priority c i p)) (nolock nofun) h
theorem X.Tasks.renew {c i l} (h : XInv db t) : XInv (Tasks.renew c i l db).1 t := step_xinv (.task (.renew c i l)) (nolock nofun) h
theorem X.Tasks.done {c i e} (h : XInv db t) : XInv (Tasks.done c i e db).1 t := step_xinv (.task (.done c i e)) (nolock nofun) h
theorem X.Tasks.block {c i q} (h : XInv db t) : XInv (Tasks.block c i q db).1 t := step_xinv (.task (.block c i q)) (nolock nofun) h
theorem X.Tasks.unblock {c i a} (h : XInv db t) : XInv (Tasks.unblock c i a db).1 t :=
  step_xinv (.task (.unblock c i a)) (nolock nofun) h
theorem X.Tasks.release {c i a} (h : XInv db t) : XInv (Tasks.release c i a db).1 t :=
  step_xinv (.task (.release c i a)) (nolock nofun) h
theorem X.Tasks.edit {c i a} (h : XInv db t) : XInv (Tasks.edit c i a db).1 t := step_xinv (.task (.edit c i a)) (nolock nofun) h
theorem X.Tasks.drop {c i} (h : XInv db t) : XInv (Tasks.drop c i db).1 t := step_xinv (.task (.drop c i)) (nolock nofun) h
theorem X.Msgs.post {now f d b u k} (h : XInv db t) : XInv (Msgs.post db now f d b u k).1 t :=
  step_xinv (.post now f d b u k) (nolock nofun) h
theorem X.Watchd.say {now d b u k} (h : XInv db t) : XInv (Watchd.say db now d b u k) t := X.Msgs.post h
theorem X.Msgs.take {n} (h : XInv db t) : XInv (Msgs.take n id db).1 t := step_xinv (.read n) (nolock nofun) h
theorem X.Msgs.deliverStep {n b} (h : XInv db t) : XInv (Msgs.deliverStep n b db).1 t := step_xinv (.deliver n b) (nolock nofun) h
theorem X.Lifecycle.endStep {n hc f b now} (h : XInv db t) : XInv (Lifecycle.endStep n hc f b now db).1 t :=
  step_xinv (.end_ n hc f b now) (nolock nofun) h
theorem X.Watchd.reapTask {r t' now} (h : XInv db t) : XInv (Watchd.reapTask r t' now db).1 t :=
  step_xinv (.reapTask r t' now) (nolock nofun) h
theorem X.Watchd.reapLock {l t' now} (h : XInv db t) : XInv (Watchd.reapLock l t' now db).1 t :=
  step_xinv (.reapLock l t' now) (nolock nofun) h
theorem X.Watchd.reapGone {n hh t'} (h : XInv db t) : XInv (Watchd.reapGone n hh t' db).1 t :=
  step_xinv (.reapGone n hh t') (nolock nofun) h
theorem X.Agents.leave {n now} (h : XInv db t) : XInv (Agents.leave db n now) t :=
  step_xinv (.lock (.leave n now)) (nolock nofun) h

theorem X.Db.log {ts ag k p d} (h : XInv db t) : XInv (db.log ts ag k p d) t := xinv_of_xgrow (xgrow_log (xgrow_refl _) ..) h
theorem X.Db.setMeta {k v} (h : XInv db t) : XInv (db.setMeta k v) t := xinv_of_xgrow (xgrow_setMeta (xgrow_refl _) ..) h
theorem X.Agents.delMeta {k} (h : XInv db t) : XInv (Agents.delMeta db k) t := xinv_of_xgrow (xgrow_delMeta (xgrow_refl _) ..) h

theorem X.Agents.goAway {me comms note line now} (h : XInv db t) : XInv (Agents.goAway db me comms note line now).1 t :=
  have k := away_keeps db me comms note line now
  xinv_frame k.1 (by unfold SwarmLean.Agents.goAway SwarmLean.Agents.delMeta SwarmLean.Db.setMeta; (repeat' split) <;> rfl) k.2.1 (Locks.grows_refl k.2.2.1) k.2.2.2 h
theorem X.Agents.goBack {me comms now} (h : XInv db t) : XInv (Agents.goBack db me comms now).1 t :=
  have k := back_keeps db me comms now
  xinv_frame k.1 (by unfold SwarmLean.Agents.goBack SwarmLean.Agents.delMeta SwarmLean.Db.setMeta; (repeat' split) <;> rfl) k.2.1 (Locks.grows_refl k.2.2.1) k.2.2.2 h

theorem X.Agents.touch {n cwd here now} (h : XInv db t) : XInv (Agents.touch db n cwd here now) t :=
  xinv_frame (touch_tasks ..).1 (touch_tasks ..).2 (Locks.touch_locks ..) (Locks.touch_grows ..)
    (Inbox.grows_touch _ _ _ _ _ h.2.1.2.2.2) h

/-- `setAgent` by a function that keeps the name and whether the row ended. -/
theorem X.Db.setAgent {n} {f : Agent → Agent} (hn : ∀ x, (f x).name = x.name) (he : ∀ x, (f x).ended = x.ended)
    (h : XInv db t) : XInv (db.setAgent n f) t := xinv_of_xgrow (xgrow_setAgent (xgrow_refl _) n f hn he) h

theorem X.Agents.touchWith {n cwd here now b} {f : Agent → Agent} (hn : ∀ x, (f x).name = x.name)
    (he : ∀ x, (f x).ended = x.ended) (h : XInv db t) : XInv (Agents.touchWith db n cwd here now b f).1 t := by
  unfold SwarmLean.Agents.touchWith
  split
  · exact h
  · split
    · exact h
    · refine X.Db.setAgent (fun x => by (try dsimp only); split <;> simp [hn]) (fun x => by (try dsimp only); split <;> simp [he]) ?_
      split
      · exact X.Db.setAgent (fun x => by (try dsimp only); split <;> rfl) (fun x => by (try dsimp only); split <;> rfl)
          (X.Agents.touch h)
      · exact X.Agents.touch h

theorem X.Hook.setStatus {n here now st} {f : Agent → Agent} (hn : ∀ x, (f x).name = x.name)
    (he : ∀ x, (f x).ended = x.ended) (h : XInv db t) : XInv (Hook.setStatus db n here now st f) t := by
  have k := X.Agents.touchWith (db := db) (n := n) (cwd := none) (here := here) (now := now) (b := false)
    (f := fun a => f { a with last_active := some now, status := some st }) (fun x => hn _) (fun x => he _) h
  unfold SwarmLean.Hook.setStatus; dsimp only
  split <;> rename_i e <;> rw [e] at k
  · exact k
  · split
    · exact k
    · exact X.Db.log k

theorem X.Agents.setRole {n text now} (h : XInv db t) : XInv (Agents.setRole db n text now).1 t := by
  unfold SwarmLean.Agents.setRole; dsimp only
  split <;> exact X.Db.log (X.Db.setAgent (fun _ => rfl) (fun _ => rfl) h)

theorem X.Agents.fenced {n cwd here now} {f : Db → Db × α} (hf : ∀ d, XInv d t → XInv (f d).1 t) (h : XInv db t) :
    XInv (Agents.fenced db n cwd here now f).1 t := by
  unfold SwarmLean.Agents.fenced
  split
  · exact hf _ h
  · split
    · exact h
    · exact hf _ (X.Agents.touch h)

theorem X.Agents.role {n cwd here text now} (h : XInv db t) : XInv (Agents.role db n cwd here text now).1 t :=
  X.Agents.fenced (fun _ h => X.Agents.setRole h) h

theorem X.Agents.stay {n here v now} (h : XInv db t) : XInv (Agents.stay db n here v now).1 t :=
  X.Agents.fenced (fun _ h => X.Db.log (X.Db.setAgent (fun _ => rfl) (fun _ => rfl) h)) h

theorem X.Agents.endStay {me n now} (h : XInv db t) : XInv (Agents.endStay db me n now).1 t := by
  unfold SwarmLean.Agents.endStay
  split
  · exact h
  · split
    · exact h
    · exact X.Db.log (X.Db.setAgent (fun _ => rfl) (fun _ => rfl) h)

theorem X.Agents.setLimits {ec me mn mx now} (h : XInv db t) : XInv (Agents.setLimits db ec me mn mx now).1 t := by
  have hg : ∀ a b, XInv (Agents.setLimits.go db me mn mx now a b).1 t := fun a b => by
    unfold SwarmLean.Agents.setLimits.go; dsimp only
    refine X.Db.log ?_
    split <;> (try refine X.Db.setMeta ?_) <;> (split <;> (try refine X.Db.setMeta ?_) <;> exact h)
  unfold SwarmLean.Agents.setLimits; dsimp only
  split
  · split
    · exact h
    · exact hg _ _
  · exact hg _ _

theorem X.Workspaces.upsert {w} (h : XInv db t) : XInv (Workspaces.upsert db w) t :=
  xinv_of_xgrow (xgrow_workspaces (xgrow_refl _) _) h

theorem xinv_setQueue {l} (h : XInv db t) : XInv (Queue.setQueue db l) t :=
  xinv_tasks (binv_map rfl rfl (fun _ => rfl) fun u hu => by simpa [TaskOk, Task.Owned, DoneEv] using hu) rfl rfl rfl rfl rfl h

theorem xinv_logged {a b : Db} (hl : QueueProofs.Logged a b) (h : XInv a t) : XInv b t := by
  obtain ⟨_, _, rfl⟩ := hl; exact xinv_frame rfl rfl rfl (Locks.grows_refl rfl) (Inbox.grows_of_eq rfl rfl rfl) h

theorem xinv_qstep {a b : Db} (hq : QueueProofs.QStep a b) (h : XInv a t) : XInv b t := by
  rcases hq with rfl | ⟨l, hl⟩
  · exact h
  · exact xinv_logged hl (xinv_setQueue h)

theorem X.Queue.add {c ids w} (h : XInv db t) : XInv (Queue.add c ids w db).1 t := xinv_qstep (QueueProofs.add_step ..) h
theorem X.Queue.rm {c ids} (h : XInv db t) : XInv (Queue.rm c ids db).1 t := xinv_qstep (QueueProofs.rm_step ..) h
theorem X.Queue.done {c i e} (h : XInv db t) : XInv (Queue.done c i e db).1 t := by
  rcases QueueProofs.done_tidy c i e db with e | e <;> rw [e]
  · exact X.Tasks.done h
  · exact xinv_setQueue (X.Tasks.done h)
theorem X.Queue.drop {c i} (h : XInv db t) : XInv (Queue.drop c i db).1 t := by
  rcases QueueProofs.drop_tidy c i db with e | e <;> rw [e]
  · exact X.Tasks.drop h
  · exact xinv_setQueue (X.Tasks.drop h)

/-- The tasks mapped by a change that keeps each id and a well-owned task well-owned. -/
theorem xinv_tasks_map {f : Task → Task} (hid : ∀ u, (f u).id = u.id) (hok : ∀ u, TaskOk u → TaskOk (f u))
    (h : XInv db t) : XInv { db with tasks := db.tasks.map f } t := by
  refine xinv_tasks (a := db) ?_ rfl rfl rfl rfl rfl h
  rintro ⟨⟨hnd, hb, hw⟩, he⟩
  have ok : ∀ v ∈ db.tasks.map f, TaskOk v ∧ v.id < db.taskNext := fun v hv => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    exact ⟨hok u ⟨hw u hu, he u hu⟩, (hid u).symm ▸ hb u hu⟩
  have ids : (db.tasks.map f).map (·.id) = db.tasks.map (·.id) := by
    rw [List.map_map]; exact List.map_congr_left fun u _ => hid u
  exact ⟨⟨ids ▸ hnd, fun v hv => (ok v hv).2, fun v hv => (ok v hv).1.1⟩, fun v hv => (ok v hv).1.2⟩

macro_rules | `(tactic| xstep) => `(tactic| ((try xnorm); (with_reducible apply xinv_tasks_map) <;> xside))

theorem xinv_set {i} {f : Task → Task} (hid : ∀ u, (f u).id = u.id) (hok : ∀ u, TaskOk u → TaskOk (f u)) (h : XInv db t) :
    XInv (db.set i f) t :=
  xinv_tasks (binv_set hid (fun u _ _ => hok u) rfl rfl) rfl rfl rfl rfl rfl h

theorem X.Queue.hold {c i why} (h : XInv db t) : XInv (Queue.hold c i why db).1 t := by
  unfold SwarmLean.Queue.hold; dsimp only
  repeat' split
  all_goals first | exact h | exact X.Db.log (xinv_set (fun _ => rfl) (fun u hu => by simpa [TaskOk, Task.Owned, DoneEv] using hu) h)
theorem X.Queue.unhold {c i} (h : XInv db t) : XInv (Queue.unhold c i db).1 t := by
  unfold SwarmLean.Queue.unhold; dsimp only
  repeat' split
  all_goals first | exact h | exact X.Db.log (xinv_set (fun _ => rfl) (fun u hu => by simpa [TaskOk, Task.Owned, DoneEv] using hu) h)
end

section
variable {db : Db} {t : Int}
open Agents in
/-- A row brought to life (appended if absent, its inbox made, `setAgent` to not ended) for a name not the user's. -/
theorem xinv_revive {n : String} {row : Agent} {G : Agent → Agent} (hrn : row.name = n) (hn : n ≠ SwarmLean.Agents.HUMAN)
    (hGn : ∀ g, (G g).name = g.name) (hGe : ∀ g, (G g).ended = none) (h : XInv db t) :
    XInv ((newInbox (if db.agents.any (·.name == n) then db else { db with agents := db.agents ++ [row] }) n).setAgent n G) t := by
  generalize hD1 : (if db.agents.any (·.name == n) then db else { db with agents := db.agents ++ [row] }) = D1
  have g1 : D1.locks = db.locks ∧ D1.tasks = db.tasks ∧ D1.taskNext = db.taskNext ∧ D1.msgs = db.msgs ∧
      D1.cursors = db.cursors ∧ D1.msgNext = db.msgNext ∧ Locks.Grows db D1 ∧ D1.agents.any (·.name == n) = true := by
    subst hD1; split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Locks.grows_refl rfl, by assumption⟩
    · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨fun a h' => by simp only [Locks.Live] at h' ⊢; simp [List.any_append, h'],
        fun a h' => ?_⟩, by simp [hrn]⟩
      by_cases e : a = n
      · exact .inr (e ▸ hn)
      · left; simpa [Locks.Live, List.any_append, hrn, Ne.symm e] using h'
  obtain ⟨hl, ht, htn, hm, hc, hmn, hg, hrow⟩ := g1
  have e2 : (newInbox D1 n).locks = D1.locks ∧ (newInbox D1 n).agents = D1.agents ∧ (newInbox D1 n).tasks = D1.tasks ∧
      (newInbox D1 n).taskNext = D1.taskNext := by unfold newInbox; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  refine xinv_frame (e2.2.2.1.trans ht) (e2.2.2.2.trans htn) (e2.1.trans hl)
    (Locks.grows_trans hg (Locks.grows_of_agents rfl (Locks.grows_trans (Locks.grows_refl e2.2.1)
      (Locks.grows_setAgent hGn hGe (e2.2.1 ▸ hrow) hn)))) ?_ h
  exact Inbox.grows_trans (grows_ni db D1 n hm hc hmn h.2.1.2.2.2) (Inbox.grows_of_eq rfl rfl rfl)

theorem xinv_reserveAgent {ec n cwd model now} {d : Db} (hn : n ≠ SwarmLean.Agents.HUMAN) (h : XInv db t)
    (hr : Spawn.reserveAgent db ec n cwd model now = .ok d) : XInv d t := by
  have hg : Spawn.reserveAgent.go db n cwd model now = .ok d → XInv d t := fun e => by
    unfold Spawn.reserveAgent.go at e; cases e
    exact xinv_revive rfl hn (fun _ => rfl) (fun _ => rfl) h
  unfold Spawn.reserveAgent at hr
  split at hr
  · cases hr
  · dsimp only at hr; split at hr
    · split at hr
      · cases hr
      · exact hg hr
    · exact hg hr

theorem X.Spawn.reserve {ec n cwd model now} {u : Unit} (hn : SwarmLean.Agents.notHuman n = .ok u) (h : XInv db t) :
    XInv (Spawn.reserve db ec n cwd model now).1 t := by
  have hn : n ≠ SwarmLean.Agents.HUMAN := fun e => by simp [SwarmLean.Agents.notHuman, e] at hn
  unfold SwarmLean.Spawn.reserve
  split
  · exact xinv_reserveAgent hn h ‹_›
  · exact h

theorem X.Spawn.reserveTask {ec n cwd tid model now top} {u : Unit} (hn : SwarmLean.Agents.notHuman n = .ok u) (h : XInv db t) :
    XInv (Spawn.reserveTask db ec n cwd tid model now top).1 t := by
  have hn : n ≠ SwarmLean.Agents.HUMAN := fun e => by simp [SwarmLean.Agents.notHuman, e] at hn
  unfold SwarmLean.Spawn.reserveTask
  split
  · rename_i d r e
    unfold SwarmLean.Spawn.reserveTask.go at e
    simp only [bind, Except.bind, pure, Except.pure] at e
    repeat' (first | split at e | cases e | (simp [throw, throwThe, MonadExceptOf.throw] at e; done))
    all_goals exact X.Db.log (xinv_set (fun _ => rfl) (fun u hu => by simp [TaskOk, Task.Owned, DoneEv] at hu ⊢)
      (xinv_reserveAgent hn h ‹_›))
  · exact h

theorem X.Spawn.unreserve {n r now} (h : XInv db t) : XInv (Spawn.unreserve db n r now) t := by
  unfold SwarmLean.Spawn.unreserve; dsimp only
  generalize hD : db.setAgent n _ = D
  have hdown : ∀ a, Locks.Live D a = true → Locks.Live db a = true := fun a h' => by
    subst hD; exact Locks.live_setAgent_le (fun g => by (try dsimp only); split <;> rfl)
      (fun g => by (try dsimp only); split <;> simp_all) h'
  have hup : ∀ a, a ≠ n → Locks.Live db a = true → Locks.Live D a = true := fun a hne h' => by
    subst hD; rw [Locks.live_setAgent (fun g => by (try dsimp only); split <;> rfl) hne]; exact h'
  have hD' : D.tasks = db.tasks ∧ D.taskNext = db.taskNext ∧ D.locks = db.locks ∧ D.msgs = db.msgs ∧
      D.cursors = db.cursors ∧ D.msgNext = db.msgNext := by subst hD; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hE : XInv (if (SwarmLean.Agents.live D).any (·.name == n) then D else { D with locks := D.locks.filter (·.agent != some n) }) t := by
    refine ⟨binv_same ?_ ?_ h.1, Inbox.grows_inv (Inbox.grows_of_eq ?_ ?_ ?_) h.2.1, ?_⟩
    all_goals try (split <;> simp [hD'])
    refine Locks.good_sub (db := db) ?_ ?_ ?_ h.2.2
    · split
      · intro l hl; rw [hD'.2.2.1] at hl; exact hl
      · intro l hl; exact hD'.2.2.1 ▸ (List.mem_filter.1 hl).1
    · split <;> exact hdown
    · intro l hl a ha hlive
      by_cases e : a = n
      · subst e; split
        · rename_i hl'
          simp only [SwarmLean.Agents.live, List.any_eq_true, beq_iff_eq] at hl'
          obtain ⟨g, hg, rfl⟩ := hl'
          have := (List.mem_mergeSort.1 hg)
          simp only [List.mem_filter] at this
          simp only [Locks.Live, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
          exact ⟨g, this.1, rfl, this.2⟩
        · split at hl
          · contradiction
          · simp [List.mem_filter, ha] at hl
      · exact (by split <;> exact hup a e hlive)
  split
  · exact hE
  · rename_i r
    refine xinv_set (fun _ => by (try dsimp only); split <;> rfl) (fun u hu => ?_) hE
    split
    · simp [TaskOk, Task.Owned, DoneEv]
    · exact hu

theorem X.Agents.bind {n cwd hc model r now} {u : Unit} (hn : SwarmLean.Agents.notHuman n = .ok u) (h : XInv db t) :
    XInv (Agents.bind db n cwd hc model r now).1 t := by
  have hn : n ≠ SwarmLean.Agents.HUMAN := fun e => by simp [SwarmLean.Agents.notHuman, e] at hn
  exact ⟨binv_same (bind_tasks ..).1 (bind_tasks ..).2 h.1, Inbox.grows_inv (bind_grows _ _ _ _ _ _ _ h.2.1.2.2.2) h.2.1,
    Locks.bind_good n cwd hc model r now hn h.2.2⟩

theorem X.Agents.setQueueOnly {me on now} (h : XInv db t) : XInv (Agents.setQueueOnly db me on now) t :=
  X.Db.log (X.Db.setMeta h)

/-- `db.set` by a change that keeps the id and a well-owned task well-owned. -/
theorem X.Db.set {i} {f : Task → Task} (hid : ∀ u, (f u).id = u.id) (hok : ∀ u, TaskOk u → TaskOk (f u))
    (h : XInv db t) : XInv (db.set i f) t := xinv_set hid hok h

theorem X.Queue.setQueue {l} (h : XInv db t) : XInv (Queue.setQueue db l) t := xinv_setQueue h
theorem X.Queue.tidy (h : XInv db t) : XInv (Queue.tidy db) t := xinv_setQueue h

theorem X.Ci.due {now key every} (h : XInv db t) : XInv (Ci.due now key every db).1 t := by
  unfold SwarmLean.Ci.due; xstep

theorem X.Ci.ciPollGate {now noCi every} (h : XInv db t) : XInv (Ci.ciPollGate now noCi every db).1 t := by
  unfold SwarmLean.Ci.ciPollGate; xstep
theorem X.Ci.prCiGate {now} (h : XInv db t) : XInv (Ci.prCiGate now db).1 t := by
  unfold SwarmLean.Ci.prCiGate; xstep
theorem X.Ci.prWatchGate {now} (h : XInv db t) : XInv (Ci.prWatchGate now db).1 t := by
  unfold SwarmLean.Ci.prWatchGate; xstep

theorem X.Ci.ciPollApply {now runs wf} (h : XInv db t) : XInv (Ci.ciPollApply now runs wf db).1 t := by
  unfold SwarmLean.Ci.ciPollApply
  split
  · exact X.Db.setMeta h
  · refine X.List.foldl (fun d r hd => ?_) (xinv_frame rfl rfl rfl (Locks.grows_refl rfl) (Inbox.grows_of_eq rfl rfl rfl) h)
    dsimp only; repeat' split
    all_goals first | exact hd | exact xinv_frame rfl rfl rfl (Locks.grows_refl rfl) (Inbox.grows_of_eq rfl rfl rfl) hd

theorem X.Ci.prWatchApply {now gated tk pr} (h : XInv db t) : XInv (Ci.prWatchApply now gated tk pr db) t := by
  unfold SwarmLean.Ci.prWatchApply; dsimp only
  repeat' split
  · exact X.Msgs.post (X.Queue.tidy (X.Db.log (X.Db.set (fun _ => rfl) (by xok) h)))
  all_goals first | exact h | exact X.Msgs.post (X.Db.log h)

theorem X.Ci.prCiApply {now prs} (h : XInv db t) : XInv (Ci.prCiApply now prs db) t := by
  unfold SwarmLean.Ci.prCiApply; xstep

theorem X.Ci.ciCheckStep {now} (h : XInv db t) : XInv (Ci.ciCheckStep now db).1 t := by
  unfold SwarmLean.Ci.ciCheckStep; dsimp only
  split
  · exact h
  · split
    · refine X.Queue.tidy (X.List.foldl (fun d u hd => ?_) h)
      repeat' split
      all_goals first | exact hd | exact X.Msgs.post (X.Db.log (X.Db.set (fun _ => rfl) (by xok) hd)) | exact X.Db.log (X.Db.set (fun _ => rfl) (by xok) hd)
    · split
      · exact h
      · split
        · exact h
        · split
          · exact X.Db.set (fun _ => rfl) (by xok) (X.Db.log h)
          · exact X.Db.log h

/-- A new open task with no owner, at the next id. -/
theorem xinv_addTask {u : Task} (hid : u.id = db.taskNext) (hs : u.state = .open) (ho : u.owner = none)
    (h : XInv db t) : XInv { db with tasks := db.tasks ++ [u], taskNext := db.taskNext + 1 } t := by
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, Inbox.grows_inv (Inbox.grows_of_eq rfl rfl rfl) h.2.1,
    Locks.good_grow rfl (Locks.grows_refl rfl) h.2.2⟩
  · simp only [List.map_append, List.map_cons, List.map_nil]
    refine List.nodup_append.2 ⟨h.1.1.1, by simp, ?_⟩
    intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
    have := h.1.1.2.1 v hv; omega
  · intro v hv; show v.id < db.taskNext + 1; rcases List.mem_append.1 hv with hv | hv
    · have := h.1.1.2.1 v hv; omega
    · rw [List.mem_singleton.1 hv]; omega
  · intro v hv; rcases List.mem_append.1 hv with hv | hv
    · exact h.1.1.2.2 v hv
    · rw [List.mem_singleton.1 hv]; simp [Task.Owned, hs, ho]
  · intro v hv; rcases List.mem_append.1 hv with hv | hv
    · exact h.1.2 v hv
    · rw [List.mem_singleton.1 hv]; simp [DoneEv, hs]

theorem X.Ci.ciNewRedTask {now comms r rng names tail} (h : XInv db t) :
    XInv (Ci.ciNewRedTask now comms r rng names tail db) t := by
  unfold SwarmLean.Ci.ciNewRedTask
  dsimp only
  repeat' split
  all_goals first
    | exact X.Msgs.post (X.List.foldl (fun d n hd => X.Msgs.post hd) (X.Db.log (xinv_addTask (by rfl) (by rfl) (by rfl) h)))
    | exact X.List.foldl (fun d n hd => X.Msgs.post hd) (X.Db.log (xinv_addTask (by rfl) (by rfl) (by rfl) h))

theorem X.Ci.ciCheckFirst {now} (h : XInv db t) : XInv (Ci.ciCheckFirst now db).1 t := by
  have := X.Ci.ciCheckStep (now := now) h
  unfold SwarmLean.Ci.ciCheckFirst
  rcases e : SwarmLean.Ci.ciCheckStep now db with ⟨d, _ | r⟩
  · rw [e] at this; exact this
  · exact h

theorem X.Ci.ciCheckApply {now comms r rng names tail} (h : XInv db t) :
    XInv (Ci.ciCheckApply now comms r rng names tail db) t := by
  unfold SwarmLean.Ci.ciCheckApply
  have := X.Ci.ciCheckStep (now := now) h
  split
  · next db' r' heq =>
    rw [heq] at this
    split
    · exact X.Ci.ciNewRedTask this
    · exact h
  · exact h

/-- `swarm limits`' compaction thresholds: meta keys and an event. -/
theorem X.Compact.setLimits {me n c st now} (h : XInv db t) : XInv (Compact.setLimits db me n c st now) t := by
  unfold SwarmLean.Compact.setLimits
  apply X.Db.log
  cases st <;> cases c <;> cases n <;> dsimp only <;> (repeat apply X.Db.setMeta) <;> exact h

theorem xinv_ite {c : Prop} [Decidable c] {a b : Db} (ha : XInv a t) (hb : XInv b t) : XInv (if c then a else b) t := by
  split <;> assumption

/-- An agent's compaction state: a meta key set or deleted. -/
theorem X.Compact.save {n s} (h : XInv db t) : XInv (Compact.save db n s) t := by
  unfold SwarmLean.Compact.save
  dsimp only
  exact xinv_ite (X.Agents.delMeta h) (X.Db.setMeta h)

/-- The conflict tick's write: keys, conflicts, notices, violations and landed locks, none touching a task. -/
theorem X.Conflict.tickApply {wts snaps work ranges now} (h : XInv db t) :
    XInv (Conflict.tickApply wts snaps work ranges now db) t := by
  unfold SwarmLean.Conflict.tickApply
  xnorm
  with_reducible apply X.List.foldl
  · intro d lk hd; xstep
  · with_reducible apply X.List.foldl
    · intro d n hd; xstep
    · with_reducible apply X.List.foldl
      · intro d n hd; xstep
      · with_reducible apply X.List.foldl'
        · intro d c w hd
          xnorm; split_step
          · exact X.Db.log (xinv_frame rfl rfl rfl (Locks.grows_refl rfl) (Inbox.grows_of_eq rfl rfl rfl) hd)
          · exact X.Db.log hd
          · xnorm
            with_reducible apply X.List.foldl'
            · intro d' c' x hd'
              xnorm; split_step
              · exact hd'
              · xnorm
                exact X.Db.log (xinv_frame rfl rfl rfl (Locks.grows_refl rfl) (Inbox.grows_of_eq rfl rfl rfl) hd')
            · xnorm; split_step
              · exact X.Db.log (xinv_frame rfl rfl rfl (Locks.grows_refl rfl) (Inbox.grows_of_eq rfl rfl rfl) hd)
              · exact xinv_frame rfl rfl rfl (Locks.grows_refl rfl) (Inbox.grows_of_eq rfl rfl rfl) hd
        · exact h

theorem X.Tasks.rulesSet {x} (h : XInv db t) : XInv (Tasks.rulesSet x db) t := X.Db.setMeta h
end

instance : Guard (RecM M) where
  guard x := tryCatchThe Exit (do let a ← x; pure (.ok a)) fun e => pure (.error s!"exit {e.code}")

section
variable {t : Int}

/-! ## Every command and a watchd pass

Each theorem below runs a command group (or one watchd pass) on any machine whose clock reads no later than `t` (`hM`)
and says it `Keeps` the cross-area invariant `XInv · t`: the db it leaves, and the db after each transaction it
commits on the way, keep it. `hL` is `LoopsKeep`, for the groups with a `repeat` loop (see `loop_ends`). -/

set_option maxHeartbeats 20000000 in
/-- Every `Tasks` command keeps the cross-area invariant at every commit (`Cmd.Tasks.group`). -/
theorem tasks_keeps (hM : ∀ w, M.now w ≤ t) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Tasks.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Every `Msgs` command keeps the cross-area invariant at every commit (`Cmd.Msgs.group`). -/
theorem msgs_keeps (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Msgs.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Every `Locks` command keeps the cross-area invariant at every commit (`Cmd.Locks.group`). -/
theorem locks_keeps (hM : ∀ w, M.now w ≤ t) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Locks.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Every `Agents` command keeps the cross-area invariant at every commit (`Cmd.Agents.group`). -/
theorem agents_keeps (hM : ∀ w, M.now w ≤ t) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Agents.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Every `Cost` command keeps the cross-area invariant at every commit (`Cmd.Cost.group`). -/
theorem cost_keeps (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Cost.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Every `Ci` command keeps the cross-area invariant at every commit (`Cmd.Ci.group`). -/
theorem ci_keeps (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Ci.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Every `Run` command keeps the cross-area invariant at every commit (`Cmd.Run.group`). -/
theorem run_keeps (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Run.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Every `State` command keeps the cross-area invariant at every commit (`Cmd.State.group`). -/
theorem state_keeps (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.State.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Every `Hook` command keeps the cross-area invariant at every commit (`Cmd.Hook.group`). -/
theorem hook_keeps (hM : ∀ w, M.now w ≤ t) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Hook.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Reap keeps the cross-area invariant at every commit: its own theorem, which `pass_keeps` applies (`K.<function>`)
rather than walking it inline, so no one proof holds the whole pass. -/
theorem K.SwarmLean.Watchd.reap (hM : ∀ w, M.now w ≤ t) live t' comms :
    Keeps (M := M) (XInv · t) (Watchd.reap live t' comms) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- Lifecycle keeps the cross-area invariant at every commit (applied by `pass_keeps`, as `reap`). -/
theorem K.SwarmLean.Watchd.lifecycle (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) t' comms terms opts nl :
    Keeps (M := M) (XInv · t) (Watchd.lifecycle t' comms terms opts nl) := by
  keeps_walk
  all_goals xstep

set_option maxHeartbeats 20000000 in
/-- One watchd pass keeps the cross-area invariant at every commit. -/
theorem pass_keeps (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) mine comms repo opts up st :
    Keeps (M := M) (XInv · t) (Cmd.Watchd.watchdPass mine comms repo opts up st) := by
  keeps_walk
  all_goals xstep

/-- `pass_keeps` under the name `keeps_walk` looks for (`K.<function>`): `watchd_keeps` applies it at the loop's
pass instead of walking the pass a second time. -/
theorem K.SwarmLean.Cmd.Watchd.watchdPass (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) mine comms repo opts
    up st : Keeps (M := M) (XInv · t) (Cmd.Watchd.watchdPass mine comms repo opts up st) :=
  pass_keeps hM hL mine comms repo opts up st

set_option maxHeartbeats 20000000 in
/-- Every `Watchd` command keeps the cross-area invariant at every commit (`Cmd.Watchd.group`). -/
theorem watchd_keeps (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) (a : Args.Parsed) :
    Keeps (XInv · t) ((Cmd.Watchd.group (m := RecM M)).run a) := by
  keeps_walk
  all_goals xstep

/-- Every ported command group keeps the cross-area invariant at every commit. -/
theorem groups_keep (hM : ∀ w, M.now w ≤ t) (hL : LoopsKeep M (XInv · t)) :
    ∀ g ∈ Dispatch.groups (m := RecM M), ∀ a, Keeps (XInv · t) (g.run a) := by
  intro g hg a
  simp only [Dispatch.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tasks_keeps hM a
  · exact msgs_keeps hM hL a
  · exact locks_keeps hM a
  · exact agents_keeps hM a
  · exact cost_keeps a
  · exact ci_keeps hM hL a
  · exact run_keeps hM hL a
  · exact state_keeps hM hL a
  · exact hook_keeps hM a
  · exact watchd_keeps hM hL a

/-- Crash safety (board #133): a run of `x` that keeps `P`, from a store with `P` (and earlier commits with it),
stopped at any point, leaves a store with `P`: under SQLite's atomic commit (`AllOrNothing`) the store left is the one
it found or one its transactions committed, never a transaction in part. -/
theorem stopped_keeps {P : Db → Prop} {x : RecM M α} (hx : Keeps P x) {s : Rec M} (hs : P s.db)
    (hc : ∀ d ∈ s.commits, P d) {db : Db} (h : AllOrNothing s.db (Rec.go x s).2.commits db) : P db := by
  unfold Keeps at hx
  rcases h with rfl | h
  · exact hs
  · exact ((hx s hs).2 db h).elim (hc db) id

end

/-! ## Loops that end -/

/-- `f`'s loop from `b`, at most `n` turns: `none` when it has not ended by then. -/
def loopN (f : Unit → β → RecM M (ForInStep β)) : Nat → β → RecM M (Option β)
  | 0, _ => pure none
  | n + 1, b => do
    match ← f () b with
    | .done v => pure (some v)
    | .yield v => loopN f n v

/-- `LoopsKeep`'s claim for every run that ends: a `repeat`/`while` loop whose turns keep `P`, run from a state where
its first `n` turns end it (or throw), keeps `P`. Lean defines a loop only as a least fixed point
(`Loop.forIn_eq_of_monadTail`): one that never ends has an arbitrary value, of which nothing can be proved; that is
all `LoopsKeep` adds. -/
theorem loop_ends {P : Db → Prop} {l : Lean.Loop} {b : β} {f : Unit → β → RecM M (ForInStep β)}
    (hf : ∀ c, Keeps P (f () c)) {n : Nat} {s : Rec M} (hs : P s.db) (hn : (Rec.go (loopN f n b) s).1 ≠ .ok none) :
    Kept P s (Rec.go (forIn l b f) s).2 := by
  induction n generalizing b s with
  | zero => exact absurd (by simp only [loopN, Rec.go]; rfl) hn
  | succ n ih =>
    have e : (forIn l b f : RecM M β) = Lean.Loop.forIn l b f := rfl
    rw [e, Lean.Loop.forIn_eq_of_monadTail, go_bind]
    simp only [loopN] at hn; rw [go_bind] at hn
    have k := hf b; unfold Keeps at k; have k := k s hs
    revert hn k
    rcases Rec.go (f () b) s with ⟨r, s1⟩
    intro hn k
    cases r with
    | error e => exact k
    | ok r =>
      cases r with
      | done v => simp only; rw [go_eq]; exact k
      | yield v => exact kept_trans k (ih k.1 hn)

/-! ## Recovery (part 2) -/

/-- Lock `p` of `a` with lease `L` is held. -/
def LockHeld (db : Db) (p : String) (a : Option String) (L : Int) : Prop :=
  ∃ x ∈ db.locks, x.path = p ∧ x.agent = a ∧ x.lease_until = some L

/-- A dead agent's locks expire: on a run where reap, judging lock `l` of path `p` and agent `a`, runs at some point
from `n` on with a clock past the lease `L`, the lock does not last (claim_lapses's lock half). -/
theorem lock_lapses (db : Db) (r : Nat → XCmd) (n : Nat) {p : String} {a : Option String} {L : Int} {l : Lock}
    (hp : l.path = p) (ha : l.agent = a) (hfair : ∃ m ≥ n, ∃ t now, r m = .reapLock l t now ∧ L < t) :
    ∃ m ≥ n, ¬ LockHeld (at_ db r m) p a L := by
  obtain ⟨m, hm, t, now, hr, hL⟩ := hfair
  by_cases hc : LockHeld (at_ db r m) p a L
  · refine ⟨m + 1, by omega, ?_⟩
    obtain ⟨x, hx, hxp, hxa, hxl⟩ := hc
    have hfire : (at_ db r m).locks.any
        (fun x => x.path == l.path && x.agent == l.agent && x.lease_until.any (· < t)) = true :=
      List.any_eq_true.2 ⟨x, hx, by simp [hxp, hxa, hxl, hp, ha, hL]⟩
    rintro ⟨y, hy, hyp, hya, -⟩
    simp only [at_, hr, XCmd.step, Watchd.reapLock, hfire, ite_true, Db.log] at hy
    have := (List.mem_filter.1 hy).2
    simp [hyp, hya, hp, ha] at this
  · exact ⟨m, hm, hc⟩

open WatchdProofs in
/-- An idle row (as `reserveAgent` leaves one) never keeps a lapsed claim without a background job: reap reopens the
task a spawn reserved and never launched once its lease is past (`claim_lapses`). -/
theorem idle_unkept {a : Agent} (hs : a.status = some "idle") (live : Option (List String)) :
    Watchd.keeps (some a) false live = false := by
  cases h : Watchd.keeps (some a) false live
  · rfl
  · obtain ⟨b, hb, -, hb2, -⟩ := (keeps_iff _ _ _).1 h
    cases hb; simp_all

/-- A row with no terminal, staying for nothing and idle 2 min, holding no claim, lock, unlanded work or job, with no
waiter (a spawn that reserved it and died before the launch): lifecycle's verdict is to end it. -/
theorem unlaunched_ends {r : Swarm.Decide.ARow} {t : Int} {h : Bool} {F : Swarm.Decide.Facts} (hc : r.hc = none)
    (hs : Swarm.Decide.nz r.stay = false) (hi : r.status = "idle") (ht : 120 ≤ t - r.lastActive.getD 0)
    (hw : r.waiter = none) (hcl : F.claims = false) (hl : F.locks = false) (hu : F.unlanded = false)
    (hj : F.job = false) : Swarm.Decide.fateL r t none h F = .end_ := by
  have : ¬ (t - r.lastActive.getD 0 < 120) := by omega
  simp [Swarm.Decide.fateL, hc, hs, hi, this, hw, hcl, hl, hu, hj]; simp [Swarm.Decide.nz]

/-- The row `reserveAgent` leaves for `name` is idle, unbound and live. -/
theorem reserveAgent_row {db db' : Db} {e : Option String} {name cwd : String} {model : Option String} {now : Int}
    (h : Spawn.reserveAgent db e name cwd model now = .ok db') :
    ∀ a ∈ db'.agents, a.name = name → a.status = some "idle" ∧ a.hc = none ∧ a.ended = none := by
  have k : ∀ d : Db, ∀ a ∈ ((Agents.newInbox d name).setAgent name fun a =>
      { a with hc := none, ended := none, status := some "idle", model := model.orElse fun _ => a.model }).agents,
      a.name = name → a.status = some "idle" ∧ a.hc = none ∧ a.ended = none := by
    intro d a ha hn
    simp only [Db.setAgent, List.mem_map] at ha
    obtain ⟨b, -, rfl⟩ := ha
    split at hn <;> simp_all
  unfold Spawn.reserveAgent Spawn.reserveAgent.go at h
  repeat' split at h
  all_goals first | (cases h; exact k _) | cases h

end SwarmLean.Crash
