import LuaLean.Shallow

/-! The translator as a Lean function, `D.fn`, from a parsed function to `Shallow.lean`'s combinators, and one theorem,
`D.fn_ok`, that it is the interpreter's call for every program (research/translator-proof.md). A lifted function's
shallow form is `D.fn` of its body, unfolded: the kernel checks that by computation, so a function's `f_ok` is
`D.fn_ok` itself and no proof is written per function (`lua-lean lift`). -/

namespace Lua

/-- a scope `r` and one more name: `v` its cell, or none for a global -/
def res1 (x : String) (v : Option Nat) (r : String → Option Nat) : String → Option Nat :=
  fun y => match y == x with
    | true => v
    | false => r y

theorem res1_ok {env : Env} {x v r} (h : env.lookup x = v) (hr : ∀ y, env.lookup y = r y) :
    ∀ y, env.lookup y = res1 x v r y := by
  intro y; unfold res1; split
  · next e => rw [eq_of_beq e]; exact h
  · exact hr y

/-- where a function is being translated: the interpreter's context, and each name's cell as the translator knows
it (`res`: what `cx.env.lookup` is, but a term that computes on the function's free names too) -/
structure Sc where
  cx : Ctx
  res : String → Option Nat

namespace Sc
def ok (s : Sc) : Prop := ∀ x, s.cx.env.lookup x = s.res x
/-- a new local `x` in cell `c` -/
def bind (s : Sc) (x : String) (c : Nat) : Sc := ⟨{ s.cx with env := (x, c) :: s.cx.env }, res1 x (some c) s.res⟩
theorem bind_ok {s : Sc} (h : s.ok) (x : String) (c : Nat) : (s.bind x c).ok := by
  intro y; show List.lookup y ((x, c) :: s.cx.env) = res1 x (some c) s.res y
  rw [List.lookup_cons]; unfold res1; cases y == x
  · exact h y
  · rfl
end Sc

namespace D
open S

/-- an expression of one value, as one value and as several -/
def one (e : SE) : SE × SM := (e, mOne e)

/-- `names` bound to the values, then `k` in their scope (`let1` for each, then `letEnd`) -/
def lets {α} : List String → Sc → (Sc → M α) → List Val → M α
  | [], s, k => letEnd (k s)
  | x :: xs, s, k => let1 fun c => lets xs (s.bind x c) k

mutual
/-- an expression as one value (`eval`) and as several (`evalMulti`) -/
def exp (I : Sem) (s : Sc) : Exp → SE × SM
  | .nil => one eNil
  | .tru => one eTrue
  | .fls => one eFalse
  | .num x => one (eNum x)
  | .str x => one (eStr x)
  | .vararg => (eVa s.cx.va, mVa s.cx.va)
  | .func ps va b => one (eFunc ps va b s.cx.env)
  | .var x => one (match s.res x with
    | some c => eCell c
    | none => eGlob x)
  | .index t k => one (eIndex I (exp I s t).1 (exp I s k).1)
  | .call f as => let m := mCall I (exp I s f).1 (list I s as); (eFirst m, m)
  | .method o x as => let m := mMethod I (exp I s o).1 x (list I s as); (eFirst m, m)
  | .paren a => one (eParen (exp I s a).1)
  | .site st a => (eSite st (exp I s a).1, mSite st (exp I s a).2)
  | .and a b => one (eAnd (exp I s a).1 (exp I s b).1)
  | .or a b => one (eOr (exp I s a).1 (exp I s b).1)
  | .bin op a b => one (eBin I op (exp I s a).1 (exp I s b).1)
  | .un op a => one (eUn I op (exp I s a).1)
  | .table fs => one (eTable (fields I s fs))

def list (I : Sem) (s : Sc) : List Exp → SM
  | [] => lNil
  | [e] => lLast (exp I s e).2
  | e :: e' :: es => lCons (exp I s e).1 (list I s (e' :: es))

def fields (I : Sem) (s : Sc) : List Field → Nat → SM
  | [] => fNil
  | [.pos e] => fLast (exp I s e).2
  | .pos e :: f :: fs => fPos (exp I s e).1 (fields I s (f :: fs))
  | .named k e :: fs => fNamed k (exp I s e).1 (fields I s fs)
  | .keyed k e :: fs => fKeyed (exp I s k).1 (exp I s e).1 (fields I s fs)

def places (I : Sem) (s : Sc) : List Exp → SP
  | [] => pNil
  | .var x :: ts => pVar (match s.res x with
    | some c => wCell c
    | none => wGlob x) (places I s ts)
  | .site st (.index t k) :: ts => pIndex I (some st) (exp I s t).1 (exp I s k).1 (places I s ts)
  | .index t k :: ts => pIndex I none (exp I s t).1 (exp I s k).1 (places I s ts)
  -- no target: the parser makes none, and the interpreter's error is left to it
  | t :: ts => fun n => (fun ps => ps.map (writer I s.cx)) <$> Lua.places I.srcs I.oracle I.tgt n s.cx (t :: ts)

def stat (I : Sem) (s : Sc) : Stat → SB
  | .assign ts es => sAssign (places I s ts) (list I s es)
  | .call e => sCall (exp I s e).2
  | .block b => sBlock (block (seq I s b b fun _ => qEnd))
  | .while c b => sWhile (exp I s c).1 (block (seq I s b b fun _ => qEnd))
  | .rpt b c => sRepeat (seq I s b b fun s' => qEndRpt (exp I s' c).1)
  | .ite c t e => sIf (exp I s c).1 (block (seq I s t t fun _ => qEnd)) (block (seq I s e e fun _ => qEnd))
  | .fornum v a b st body =>
    sForNum (exp I s a).1 (exp I s b).1 (match st with
      | some e => some (exp I s e).1
      | none => none) fun c => block (seq I (s.bind v c) body body fun _ => qEnd)
  | .forin vs es body =>
    sForIn I (list I s es) fun n => lets vs s fun s' => block (seq I s' body body fun _ => qEnd) n
  | .ret es => sReturn (list I s es)
  | .brk => sBreak
  | .goto l => sGoto l
  | .site st a => sSite st (stat I s a)
  | .label _ | .loc .. | .locfn .. => sLabel

/-- the statements `rest` of block `full`, then `fin` in their scope: the end, or a repeat's condition -/
def seq (I : Sem) (s : Sc) (full : Block) : Block → (Sc → SB) → SB
  | [], fin => fin s
  | .loc ns es :: rest, fin => qLocal (list I s es) fun n => lets ns s fun s' => seq I s' full rest fin n
  | .locfn x ps va b :: rest, fin => qLocalFn x ps va b s.cx.env fun c => seq I (s.bind x c) full rest fin
  | st :: rest, fin => qStat (stat I s st) (gotos (trail full) (labels full)) (seq I s full rest fin)
end

/-- a closure as a function: `res` its free names' cells -/
def fn (I : Sem) (res : String → Option Nat) (c : Clo) : List Val → Nat → M (List Val) :=
  S.fn fun args n => lets c.params ⟨⟨c.env, []⟩, res⟩ fun s =>
    block (seq I { s with cx := { s.cx with va := if c.va then args.drop c.params.length else [] } }
      c.body c.body fun _ => qEnd) n

-- ---------- the one theorem ----------

section
variable {I : Sem}

theorem one_ok {cx e} {s : SE} (he : e.single = true) (h : CE I s cx e) : CE I (one s).1 cx e ∧ CM I (one s).2 cx e :=
  ⟨h, CM_one he h⟩

theorem var_ok {s : Sc} (hs : s.ok) (x : String) :
    CE I (match s.res x with | some c => eCell c | none => eGlob x) s.cx (.var x) := by
  have h := hs x; split
  · next e => exact CE_cell (h.trans e)
  · next e => exact CE_glob (h.trans e)

theorem wvar_ok {s : Sc} (hs : s.ok) (x : String) :
    (match s.res x with | some c => wCell c | none => wGlob x) = fun _ => setVar s.cx x := by
  have h := hs x; split
  · next e => exact wCell_ok (h.trans e)
  · next e => exact wGlob_ok (h.trans e)

theorem lets_ok {α} {K : Ctx → M α} : ∀ (xs : List String) (s : Sc) (k : Sc → M α), s.ok →
    (∀ s' : Sc, s'.ok → k s' = K s'.cx) → CBs (lets xs s k) s.cx xs K
  | [], s, _, hs, hk => CBs_end (hk s hs)
  | x :: xs, s, k, hs, hk => CBs_let fun c => lets_ok xs (s.bind x c) k (Sc.bind_ok hs x c) hk

mutual
theorem exp_ok : (e : Exp) → (s : Sc) → s.ok → CE I (exp I s e).1 s.cx e ∧ CM I (exp I s e).2 s.cx e
  | .nil, _, _ => one_ok rfl CE_nil
  | .tru, _, _ => one_ok rfl CE_true
  | .fls, _, _ => one_ok rfl CE_false
  | .num _, _, _ => one_ok rfl CE_num
  | .str _, _, _ => one_ok rfl CE_str
  | .vararg, _, _ => ⟨CE_va rfl, CM_va rfl⟩
  | .func .., _, _ => one_ok rfl (CE_func rfl)
  | .var x, _, hs => one_ok rfl (var_ok hs x)
  | .index t k, s, hs => one_ok rfl (CE_index (exp_ok t s hs).1 (exp_ok k s hs).1)
  | .call f as, s, hs => have h := CM_call (exp_ok f s hs).1 (list_ok as s hs); ⟨CE_call h, h⟩
  | .method o _ as, s, hs => have h := CM_method (exp_ok o s hs).1 (list_ok as s hs); ⟨CE_method h, h⟩
  | .paren a, s, hs => one_ok rfl (CE_paren (exp_ok a s hs).1)
  | .site _ a, s, hs => ⟨CE_site (exp_ok a s hs).1, CM_site (exp_ok a s hs).2⟩
  | .and a b, s, hs => one_ok rfl (CE_and (exp_ok a s hs).1 (exp_ok b s hs).1)
  | .or a b, s, hs => one_ok rfl (CE_or (exp_ok a s hs).1 (exp_ok b s hs).1)
  | .bin _ a b, s, hs => one_ok rfl (CE_bin (exp_ok a s hs).1 (exp_ok b s hs).1)
  | .un _ a, s, hs => one_ok rfl (CE_un (exp_ok a s hs).1)
  | .table fs, s, hs => one_ok rfl (CE_table (fields_ok fs s hs))

theorem list_ok : (es : List Exp) → (s : Sc) → s.ok → CL I (list I s es) s.cx es
  | [], _, _ => CL_nil
  | [e], s, hs => CL_last (exp_ok e s hs).2
  | e :: e' :: es, s, hs => CL_cons (exp_ok e s hs).1 (list_ok (e' :: es) s hs)

theorem fields_ok : (fs : List Field) → (s : Sc) → s.ok → CF I (fields I s fs) s.cx fs
  | [], _, _ => CF_nil
  | [.pos e], s, hs => CF_last (exp_ok e s hs).2
  | .pos e :: f :: fs, s, hs => CF_pos (exp_ok e s hs).1 (fields_ok (f :: fs) s hs)
  | .named _ e :: fs, s, hs => CF_named (exp_ok e s hs).1 (fields_ok fs s hs)
  | .keyed k e :: fs, s, hs => CF_keyed (exp_ok k s hs).1 (exp_ok e s hs).1 (fields_ok fs s hs)

theorem places_ok : (ts : List Exp) → (s : Sc) → s.ok → CP I (places I s ts) s.cx ts
  | [], _, _ => CP_nil
  | t :: ts, s, hs => by
    have hp := places_ok ts s hs
    cases t with
    | var x => exact CP_var (wvar_ok hs x) hp
    | index t k => exact CP_index (exp_ok t s hs).1 (exp_ok k s hs).1 hp
    | site st a =>
      cases a with
      | index t k => exact CP_site (exp_ok t s hs).1 (exp_ok k s hs).1 hp
      | _ => exact fun _ => rfl
    | _ => exact fun _ => rfl

theorem stat_ok : (st : Stat) → (s : Sc) → s.ok → CS I (stat I s st) s.cx st
  | .assign ts es, s, hs => CS_assign (places_ok ts s hs) (list_ok es s hs)
  | .call e, s, hs => CS_call (exp_ok e s hs).2
  | .block b, s, hs => CS_block (CK_block (seq_ok b s hs b none _ fun _ _ => CQ_end))
  | .while c b, s, hs => CS_while (exp_ok c s hs).1 (CK_block (seq_ok b s hs b none _ fun _ _ => CQ_end))
  | .rpt b c, s, hs => CS_repeat (seq_ok b s hs b (some c) _ fun s' hs' => CQ_endRpt (exp_ok c s' hs').1)
  | .ite c t e, s, hs => CS_if (exp_ok c s hs).1 (CK_block (seq_ok t s hs t none _ fun _ _ => CQ_end))
      (CK_block (seq_ok e s hs e none _ fun _ _ => CQ_end))
  | .fornum v a b (some e) body, s, hs => CS_fornum (st := some e) (sst := some _) (exp_ok a s hs).1 (exp_ok b s hs).1
      (exp_ok e s hs).1 fun c => CK_block (seq_ok body (s.bind v c) (Sc.bind_ok hs v c) body none _ fun _ _ => CQ_end)
  | .fornum v a b none body, s, hs => CS_fornum (st := none) (sst := none) (exp_ok a s hs).1 (exp_ok b s hs).1
      trivial fun c => CK_block (seq_ok body (s.bind v c) (Sc.bind_ok hs v c) body none _ fun _ _ => CQ_end)
  | .forin vs es body, s, hs => CS_forin (list_ok es s hs) fun n => lets_ok vs s _ hs fun s' hs' =>
      CK_block (seq_ok body s' hs' body none _ fun _ _ => CQ_end) n
  | .ret es, s, hs => CS_return (list_ok es s hs)
  | .brk, _, _ => CS_break
  | .goto _, _, _ => CS_goto
  | .site _ a, s, hs => CS_site (stat_ok a s hs)
  | .label _, _, _ => CS_label
  | .loc .., _, _ | .locfn .., _, _ => fun n => by cases n <;> rw [execStat] <;> rfl

theorem seq_ok : (rest : Block) → (s : Sc) → s.ok → (full : Block) → (fin : Option Exp) → (k : Sc → SB) →
    (∀ s' : Sc, s'.ok → CQ I (k s') s'.cx full [] fin) → CQ I (seq I s full rest k) s.cx full rest fin
  | [], s, hs, _, _, _, hk => hk s hs
  | st :: rest, s, hs, full, fin, k, hk => by
    have hq := seq_ok rest s hs full fin k hk
    have hst := stat_ok st s hs
    cases st with
    | loc ns es =>
      exact CQ_local (list_ok es s hs) fun n => lets_ok ns s _ hs fun s' hs' => seq_ok rest s' hs' full fin k hk n
    | locfn x ps va b => exact CQ_localFn rfl fun c => seq_ok rest (s.bind x c) (Sc.bind_ok hs x c) full fin k hk
    | _ => exact CQ_stat hst hq rfl rfl rfl
end

/-- the translator is correct, for every function: `fn` of a closure is the interpreter's call of it -/
theorem fn_ok (I : Sem) (res : String → Option Nat) (c : Clo) (hr : ∀ x, c.env.lookup x = res x) :
    CFn I (fn I res c) c :=
  CFn_fn fun args n => lets_ok c.params ⟨⟨c.env, []⟩, res⟩ _ hr fun s' hs' =>
    CK_block (seq_ok c.body ⟨⟨s'.cx.env, if c.va then args.drop c.params.length else []⟩, s'.res⟩ hs' c.body none _
      fun _ _ => CQ_end) n

end

end D
end Lua
