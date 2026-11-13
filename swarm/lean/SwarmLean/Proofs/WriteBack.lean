import SwarmLean.Proofs.Store

/-! The write-back (board #134): `rowsPlan old new`, run by SQLite (`SqlExec`) on a table holding exactly `old`, leaves
it holding exactly `new`, with every column Lean does not know as it was, and changes no other table; loading it then
gives `new` back. -/

set_option linter.unusedSectionVars false

namespace SwarmLean
open Sqlite (Val)

/-- The executor (`runStmts`) as SQLite runs it: each statement in turn on what the one before left; none at a
failure, which rolls the transaction back. -/
def Sql.runs (S : Sql) : List Stmt → SDb → Option SDb
  | [], db => some db
  | st :: p, db => (S.exec st db).bind (S.runs p)

theorem Sql.runs_append (S : Sql) (p q : List Stmt) (db : SDb) :
    S.runs (p ++ q) db = (S.runs p db).bind (S.runs q) := by
  induction p generalizing db with
  | nil => rfl
  | cons st p ih => simp only [List.cons_append, Sql.runs]; cases S.exec st db <;> simp [ih]

theorem SDb.set_self (db : SDb) (t : String) : db.set t (db t) = db := by
  funext u; simp only [SDb.set]; split <;> simp_all

/-- A table row's cells in α's columns. -/
def cellsOf (α : Type) [Row α] (r : String → Val) : List Val := (Row.cols α).map r

/-- A table row's key in α's key columns. -/
def keyOf (α : Type) [Row α] (r : String → Val) : List Int :=
  (((Row.cols α).take (Row.nkey α)).map r).flatMap Val.ord

/-- A row's ints fit int64: binding its cells changes none. -/
def InRange [Row α] (x : α) : Prop := (Row.enc x).map Val.bound = Row.enc x

/-- Table `T` is shaped for α's rows: α's key columns are its primary key, and every encoded value fits its column. -/
def Shaped (α : Type) [Row α] (T : STable) : Prop :=
  T.keys = (Row.cols α).take (Row.nkey α) ∧ ∀ x : α, Fits T (Row.cols α) (Row.enc x)

/-- Table `T` holds exactly the rows `xs`: its rows' cells in α's columns are their encodings, in some order. -/
def Holds (α : Type) [Row α] (T : STable) (xs : List α) : Prop := (T.rows.map (cellsOf α)).Perm (xs.map Row.enc)

section
variable {α : Type} [Row α] [RowLaws α] [DecidableEq α]

theorem keyOf_eq (r : String → Val) : keyOf α r = ((cellsOf α r).take (Row.nkey α)).flatMap Val.ord := by
  simp [keyOf, cellsOf, List.map_take]

theorem keyOf_cells {r : String → Val} {x : α} (h : cellsOf α r = Row.enc x) : keyOf α r = Row.key x := by
  rw [keyOf_eq, h]; rfl

theorem key_take {x y : α} (h : Row.key x = Row.key y) :
    (Row.enc x).take (Row.nkey α) = (Row.enc y).take (Row.nkey α) :=
  ord_inj (RowLaws.key_it x) (RowLaws.key_it y) h

theorem enc_inj {x y : α} (h : Row.enc x = Row.enc y) : Row.key x = Row.key y := by
  simp [Row.key, h]

theorem take_disjoint {c : String} (h : c ∈ (Row.cols α).take (Row.nkey α)) : c ∉ (Row.cols α).drop (Row.nkey α) := by
  have hn := RowLaws.nodup (α := α)
  rw [← List.take_append_drop (Row.nkey α) (Row.cols α), List.nodup_append] at hn
  exact fun h' => hn.2.2 c h c h' rfl

theorem keyAt_eq {r : String → Val} {x : α} (hx : InRange x) :
    keyAt r ((Row.cols α).take (Row.nkey α)) (((Row.enc x).take (Row.nkey α)).map Val.bound) =
      (keyOf α r == Row.key x) := by
  simp only [keyAt, keyOf, Row.key, List.map_take, show (Row.enc x).map Val.bound = Row.enc x from hx]

theorem fits_drop {T : STable} {cs : List String} {vs : List Val} (h : Fits T cs vs) (n : Nat) :
    Fits T (cs.drop n) (vs.drop n) := by
  obtain ⟨hl, hc, hv⟩ := h
  refine ⟨by simp [hl], fun c hc' => hc c (List.mem_of_mem_drop hc'), fun p hp => hv p ?_⟩
  clear hl hc hv
  induction n generalizing cs vs with
  | zero => simpa using hp
  | succ n ih =>
    cases cs with
    | nil => simp at hp
    | cons c cs => cases vs with
      | nil => simp at hp
      | cons v vs => exact List.mem_cons_of_mem _ (ih (by simpa using hp))

/-- The key cells of a row with α's columns set to `x`'s encoding are `x`'s. -/
theorem take_setCells (r : String → Val) (x : α) :
    ((Row.cols α).take (Row.nkey α)).map (setCells r (Row.cols α) (Row.enc x)) = (Row.enc x).take (Row.nkey α) := by
  rw [List.map_take, setCells_map RowLaws.nodup (RowLaws.len x).symm]

/-- Setting the non-key columns keeps the key cells. -/
theorem take_setCells_drop (r : String → Val) (vs : List Val) :
    ((Row.cols α).take (Row.nkey α)).map (setCells r ((Row.cols α).drop (Row.nkey α)) vs) =
      ((Row.cols α).take (Row.nkey α)).map r :=
  List.map_congr_left fun _ hc => setCells_other (take_disjoint hc)

theorem keyAt_take (r : String → Val) (x : α) :
    keyAt r ((Row.cols α).take (Row.nkey α)) ((Row.enc x).take (Row.nkey α)) = (keyOf α r == Row.key x) := rfl

/-- Every row of `R` has the key cells of some row of α. -/
def KeyRows (α : Type) [Row α] (R : List (String → Val)) : Prop :=
  ∀ r ∈ R, ∃ y : α, ((Row.cols α).take (Row.nkey α)).map r = (Row.enc y).take (Row.nkey α)

theorem keyClass_of {T : STable} (hT : Shaped α T) {R : List (String → Val)} (hR : KeyRows α R) (x : α) :
    KeyClass { T with rows := R } ((Row.cols α).take (Row.nkey α)) ((Row.enc x).take (Row.nkey α)) := by
  refine ⟨fun c hc => (hT.2 x).2.1 c (List.mem_of_mem_take hc), RowLaws.key_it x, fun r hr => ?_⟩
  obtain ⟨y, hy⟩ := hR r hr
  rw [hy]; exact RowLaws.key_cls y x

/-! The old rows by key, as `rowsPlan` looks them up. -/

theorem byKey_contains (l : List α) (k : List Int) : (byKey l).contains k = (l.map Row.key).contains k := by
  simp [byKey, Std.HashMap.contains_ofList, List.map_map, Function.comp_def]

theorem byKey_get {l : List α} (hl : Keyed l) {k : List Int} {o : α} (h : (byKey l)[k]? = some o) :
    o ∈ l ∧ Row.key o = k := by
  by_cases hk : (l.map Row.key).contains k
  · obtain ⟨o', ho', rfl⟩ : ∃ o' ∈ l, Row.key o' = k := by simpa using hk
    have hp : (l.map fun r => (Row.key r, r)).Pairwise fun a b => (a.1 == b.1) = false := by
      rw [List.pairwise_map]; exact hl.imp fun h => by simpa using h
    rw [byKey, Std.HashMap.getElem?_ofList_of_mem (k := Row.key o') (by simp) hp (List.mem_map_of_mem ho')] at h
    cases h; exact ⟨ho', rfl⟩
  · rw [byKey, Std.HashMap.getElem?_ofList_of_contains_eq_false (by simpa [List.map_map, Function.comp_def] using hk)] at h
    cases h

theorem byKey_none {l : List α} {k : List Int} (h : (byKey l)[k]? = none) : ∀ o ∈ l, Row.key o ≠ k := by
  intro o ho e; subst e
  have : (byKey l).contains (Row.key o) := by rw [byKey_contains]; simpa using ⟨o, ho, rfl⟩
  rw [Std.HashMap.contains_eq_isSome_getElem?, h] at this; cases this

theorem byKey_self {l : List α} (hl : Keyed l) {x : α} (hx : x ∈ l) : (byKey l)[Row.key x]? = some x := by
  have hp : (l.map fun r => (Row.key r, r)).Pairwise fun a b => (a.1 == b.1) = false := by
    rw [List.pairwise_map]; exact hl.imp fun h => by simpa using h
  exact Std.HashMap.getElem?_ofList_of_mem (k := Row.key x) (by simp) hp (List.mem_map_of_mem hx)

/-- Past a prefix `p` none of whose keys is `k`, the lookup of `k` is the suffix's. -/
theorem byKey_append {p o : List α} (hl : Keyed (p ++ o)) {k : List Int} (hk : ∀ y ∈ p, Row.key y ≠ k) :
    (byKey (p ++ o))[k]? = (byKey o)[k]? := by
  cases h : (byKey o)[k]? with
  | some y =>
    obtain ⟨hy, rfl⟩ := byKey_get (List.pairwise_append.mp hl).2.1 h
    exact byKey_self hl (List.mem_append_right p hy)
  | none =>
    have hc : (byKey (p ++ o)).contains k = false := by
      rw [byKey_contains]
      simpa using ⟨hk, byKey_none h⟩
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
    simpa using hc

/-- `dropSame` drops a common prefix. -/
theorem dropSame_spec (old new : List α) :
    ∃ p, old = p ++ (dropSame old new).1 ∧ new = p ++ (dropSame old new).2 := by
  induction old generalizing new with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons a as ih =>
    cases new with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons b bs =>
      by_cases h : a = b
      · subst h
        obtain ⟨p, h1, h2⟩ := ih bs
        refine ⟨a :: p, ?_, ?_⟩ <;> simp only [dropSame, beq_self_eq_true, ite_true, List.cons_append] <;> congr
      · exact ⟨[], by simp [dropSame, h], by simp [dropSame, h]⟩

theorem filterMap_congr {f g : β → Option γ} {l : List β} (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.filterMap_cons, h a (by simp), ih fun x hx => h x (by simp [hx])]

/-- A common prefix of keyed rows gets no statement. -/
theorem planOf_prefix {p o n : List α} (ko : Keyed (p ++ o)) (kn : Keyed (p ++ n)) :
    planOf (p ++ o) (p ++ n) = planOf o n := by
  have dp : ∀ y ∈ p, ∀ x ∈ o, Row.key y ≠ Row.key x := (List.pairwise_append.mp ko).2.2
  have dn : ∀ y ∈ p, ∀ x ∈ n, Row.key y ≠ Row.key x := (List.pairwise_append.mp kn).2.2
  simp only [planOf, List.filterMap_append]
  congr 1
  · rw [List.filterMap_eq_nil_iff.mpr fun x hx => ?_, List.nil_append]
    · refine filterMap_congr fun x hx => ?_
      have : (byKey (p ++ n)).contains (Row.key x) = (byKey n).contains (Row.key x) := by
        have : (p.map Row.key).contains (Row.key x) = false := by simpa using fun y hy => dp y hy x hx
        rw [byKey_contains, byKey_contains, List.map_append, List.contains_append, this, Bool.false_or]
      simp only [delOf, this]
    · have : (byKey (p ++ n)).contains (Row.key x) = true := by rw [byKey_contains]; simpa using Or.inl ⟨x, hx, rfl⟩
      simp [delOf, this]
  · rw [List.filterMap_eq_nil_iff.mpr fun x hx => ?_, List.nil_append]
    · refine filterMap_congr fun x hx => ?_
      simp only [upOf, byKey_append ko fun y hy => dn y hy x hx]
    · simp [upOf, byKey_self ko (List.mem_append_left o hx)]

/-- On keyed rows the plan is `planOf` the whole lists. -/
theorem rowsPlan_keyed {old new : List α} (ko : Keyed old) (kn : Keyed new) : rowsPlan old new = planOf old new := by
  obtain ⟨p, h1, h2⟩ := dropSame_spec old new
  have := planOf_prefix (p := p) (h1 ▸ ko) (h2 ▸ kn)
  rw [← h1, ← h2] at this
  exact this.symm

/-- The plan, its two halves named. -/
theorem rowsPlan_eq {old new : List α} (ko : Keyed old) (kn : Keyed new) : rowsPlan old new =
    old.filterMap (fun r => if (byKey new).contains (Row.key r) then none else
      some (.del (Row.table α) ((Row.cols α).take (Row.nkey α)) ((Row.enc r).take (Row.nkey α)))) ++
    new.filterMap (upOf (byKey old)) := rowsPlan_keyed ko kn

/-! The deletes. -/

theorem runs_dels (S : Sql) (hS : SqlExec S) {T : STable} (hT : Shaped α T) (db : SDb) (f : α → Bool) (L : List α)
    (hL : ∀ x ∈ L, InRange x) (R : List (String → Val)) (hR : KeyRows α R) :
    S.runs (L.filterMap fun r => if f r then none else
      some (.del (Row.table α) ((Row.cols α).take (Row.nkey α)) ((Row.enc r).take (Row.nkey α))))
      (db.set (Row.table α) { T with rows := R }) =
    some (db.set (Row.table α) { T with rows := R.filter fun r => L.all fun x => f x || keyOf α r != Row.key x }) := by
  induction L generalizing R with
  | nil =>
    simp only [List.filterMap_nil, Sql.runs, List.all_nil]; rw [List.filter_eq_self.mpr (fun _ _ => rfl)]
  | cons x L ih =>
    have hx := hL x (by simp)
    have hL' := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    by_cases hf : f x
    · simp only [List.filterMap_cons, hf, ite_true]
      rw [ih hL' R hR]; simp [hf]
    · simp only [List.filterMap_cons, hf]
      simp only [Bool.false_eq_true, ite_false, Sql.runs]
      rw [hS _ _ (by simpa [Stmt.Pre] using keyClass_of hT hR x)]
      simp only [Stmt.run, SDb.set_same, SDb.set_set, keyAt_eq hx, Option.bind_some]
      rw [ih hL' _ (fun r hr => hR r (List.mem_filter.mp hr).1)]
      simp only [List.filter_filter, List.all_cons, hf, Bool.false_or]
      congr 3; apply List.filter_congr; intro r _; simp [bne, Bool.and_comm]

/-! The updates and inserts. -/

/-- A table row once the updates of the new rows `p` ran: the one of its key, if any, set in the columns but the key. -/
def applyUpds (p : List α) (r : String → Val) : String → Val :=
  match p.find? (fun y => Row.key y == keyOf α r) with
  | some x => setCells r ((Row.cols α).drop (Row.nkey α)) ((Row.enc x).drop (Row.nkey α))
  | none => r

/-- The row an insert of `x` adds to `T`. -/
def insRow (T : STable) (x : α) : String → Val := setCells T.dflt (Row.cols α) (Row.enc x)

/-- The table's rows once `upOf` ran for each of `p`, from the rows `R` the deletes left. -/
def upRows (old : List α) (T : STable) (R : List (String → Val)) (p : List α) : List (String → Val) :=
  R.map (applyUpds p) ++ (p.filter fun x => ((byKey old)[Row.key x]?).isNone).map (insRow T)

theorem take_applyUpds (p : List α) (r : String → Val) :
    ((Row.cols α).take (Row.nkey α)).map (applyUpds p r) = ((Row.cols α).take (Row.nkey α)).map r := by
  unfold applyUpds; split
  · exact take_setCells_drop r _
  · rfl

theorem keyOf_applyUpds (p : List α) (r : String → Val) : keyOf α (applyUpds p r) = keyOf α r := by
  simp only [keyOf, take_applyUpds]

theorem keyOf_insRow (T : STable) (x : α) : keyOf α (insRow T x) = Row.key x := by
  simp only [keyOf, insRow, take_setCells]; rfl

theorem applyUpds_other {p : List α} {x : α} {r : String → Val} (h : Row.key x ≠ keyOf α r) :
    applyUpds (p ++ [x]) r = applyUpds p r := by
  simp only [applyUpds, List.find?_append, List.find?_cons, List.find?_nil]
  have : (Row.key x == keyOf α r) = false := by simpa using h
  simp [this]

theorem applyUpds_fresh {p : List α} {x : α} {r : String → Val} (hp : ∀ y ∈ p, Row.key y ≠ Row.key x)
    (h : Row.key x = keyOf α r) : applyUpds p r = r ∧
      applyUpds (p ++ [x]) r = setCells r ((Row.cols α).drop (Row.nkey α)) ((Row.enc x).drop (Row.nkey α)) := by
  have hn : p.find? (fun y => Row.key y == keyOf α r) = none :=
    List.find?_eq_none.mpr fun y hy => by simpa [← h] using hp y hy
  simp [applyUpds, List.find?_append, hn, h]

theorem upRows_keyRows {old : List α} {T : STable} {R : List (String → Val)}
    (hR : ∀ r ∈ R, ∃ o ∈ old, cellsOf α r = Row.enc o) (p : List α) : KeyRows α (upRows old T R p) := by
  intro r hr
  simp only [upRows, List.mem_append, List.mem_map, List.mem_filter] at hr
  rcases hr with ⟨r, hr, rfl⟩ | ⟨y, -, rfl⟩
  · obtain ⟨o, -, ho⟩ := hR r hr
    exact ⟨o, by rw [take_applyUpds, List.map_take]; exact congrArg (List.take _) ho⟩
  · exact ⟨y, take_setCells _ y⟩

/-- One new row's statement, run on the rows the ones before it left. -/
theorem runs_up (S : Sql) (hS : SqlExec S) {T : STable} (hT : Shaped α T) (db : SDb) {old : List α} (ko : Keyed old)
    {R : List (String → Val)} (hR : ∀ r ∈ R, ∃ o ∈ old, cellsOf α r = Row.enc o)
    (p : List α) (x : α) (kp : Keyed (p ++ [x])) (hx : InRange x) :
    S.runs (upOf (byKey old) x).toList (db.set (Row.table α) { T with rows := upRows old T R p }) =
      some (db.set (Row.table α) { T with rows := upRows old T R (p ++ [x]) }) := by
  have hp : ∀ y ∈ p, Row.key y ≠ Row.key x := by
    simp only [Keyed, List.pairwise_append, List.pairwise_cons] at kp
    exact fun y hy => kp.2.2 y hy x (by simp)
  have hkR : KeyRows α (upRows old T R p) := upRows_keyRows hR p
  -- the key of a row the deletes left is an old row's
  have hRo : ∀ r ∈ R, ∃ o ∈ old, keyOf α r = Row.key o := fun r hr => by
    obtain ⟨o, ho, h⟩ := hR r hr; exact ⟨o, ho, keyOf_cells h⟩
  cases hk : (byKey old)[Row.key x]? with
  | none =>
    have hfresh := byKey_none hk
    have hup : upOf (byKey old) x = some (.ins (Row.table α) (Row.cols α) (Row.enc x)) := by simp [upOf, hk]
    rw [hup]
    simp only [Option.toList, Sql.runs]
    rw [hS _ _ (by
      simp only [Stmt.Pre, SDb.set_same, hT.1, take_setCells]; exact ⟨hT.2 x, keyClass_of hT hkR x⟩)]
    have hnot : ∀ r ∈ upRows old T R p, keyOf α r ≠ Row.key x := by
      intro r hr
      simp only [upRows, List.mem_append, List.mem_map, List.mem_filter] at hr
      rcases hr with ⟨r, hr, rfl⟩ | ⟨y, ⟨hy, -⟩, rfl⟩
      · obtain ⟨o, ho, h⟩ := hRo r hr; rw [keyOf_applyUpds, h]; exact hfresh o ho
      · rw [keyOf_insRow]; exact hp y hy
    have hany : ((upRows old T R p).any fun r =>
        keyAt r ((Row.cols α).take (Row.nkey α)) ((Row.enc x).take (Row.nkey α))) = false :=
      List.any_eq_false.mpr fun r hr => by simpa [keyAt_take] using hnot r hr
    simp only [Stmt.run, SDb.set_same, SDb.set_set, show (Row.enc x).map Val.bound = Row.enc x from hx, hT.1,
      take_setCells, hany, Bool.false_eq_true, ite_false, Option.bind_some]
    congr 3
    simp only [upRows, List.filter_append, List.filter_cons, List.filter_nil, hk, Option.isNone_none, ite_true,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, insRow]
    congr 1
    apply List.map_congr_left; intro r hr
    obtain ⟨o, ho, h⟩ := hRo r hr
    exact (applyUpds_other (by rw [h]; exact (hfresh o ho).symm)).symm
  | some o =>
    obtain ⟨ho, hko⟩ := byKey_get ko hk
    have hfilt : (p ++ [x]).filter (fun y => ((byKey old)[Row.key y]?).isNone) =
        p.filter (fun y => ((byKey old)[Row.key y]?).isNone) := by simp [List.filter_append, hk]
    by_cases hox : o = x
    · have hup : upOf (byKey old) x = none := by simp [upOf, hk, hox]
      rw [hup]; simp only [Option.toList, Sql.runs]
      congr 3
      simp only [upRows, hfilt]; congr 1
      apply List.map_congr_left; intro r hr
      by_cases hkr : Row.key x = keyOf α r
      · obtain ⟨h1, h2⟩ := applyUpds_fresh hp hkr
        rw [h1, h2]
        obtain ⟨o', ho', hc⟩ := hR r hr
        have : o' = o := Keyed.eq ko ho' ho (by rw [← keyOf_cells hc, ← hkr, hko])
        have hcx : Row.enc x = cellsOf α r := by rw [hc, this, hox]
        rw [hcx, cellsOf, ← List.map_drop, setCells_self]
      · exact (applyUpds_other hkr).symm
    · have hup : upOf (byKey old) x = some (.upd (Row.table α) ((Row.cols α).take (Row.nkey α))
          ((Row.enc x).take (Row.nkey α)) ((Row.cols α).drop (Row.nkey α)) ((Row.enc x).drop (Row.nkey α))) := by
        simp [upOf, hk, hox]
      rw [hup]; simp only [Option.toList, Sql.runs]
      rw [hS _ _ (by simp only [Stmt.Pre, SDb.set_same]; exact ⟨keyClass_of hT hkR x, fits_drop (hT.2 x) _⟩)]
      have hb : ((Row.enc x).drop (Row.nkey α)).map Val.bound = (Row.enc x).drop (Row.nkey α) := by
        rw [List.map_drop, show (Row.enc x).map Val.bound = Row.enc x from hx]
      simp only [Stmt.run, SDb.set_same, SDb.set_set, keyAt_eq hx, hb, Option.bind_some]
      congr 3
      simp only [upRows, hfilt, List.map_append, List.map_map]
      congr 1
      · apply List.map_congr_left; intro r hr
        simp only [Function.comp, keyOf_applyUpds]
        by_cases hkr : keyOf α r = Row.key x
        · obtain ⟨h1, h2⟩ := applyUpds_fresh hp hkr.symm; simp [hkr, h1, h2]
        · have := applyUpds_other (p := p) (Ne.symm hkr); simp [hkr, this]
      · apply List.map_congr_left; intro y hy
        have : Row.key y ≠ Row.key x := by
          intro e; simp [List.mem_filter, e, hk] at hy
        simp [Function.comp, keyOf_insRow, this]

/-- The updates and inserts of `q`, run after those of `p`. -/
theorem runs_ups (S : Sql) (hS : SqlExec S) {T : STable} (hT : Shaped α T) (db : SDb) {old : List α} (ko : Keyed old)
    {R : List (String → Val)} (hR : ∀ r ∈ R, ∃ o ∈ old, cellsOf α r = Row.enc o)
    (q p : List α) (kp : Keyed (p ++ q)) (hq : ∀ x ∈ q, InRange x) :
    S.runs (q.filterMap (upOf (byKey old))) (db.set (Row.table α) { T with rows := upRows old T R p }) =
      some (db.set (Row.table α) { T with rows := upRows old T R (p ++ q) }) := by
  induction q generalizing p with
  | nil => simp [Sql.runs]
  | cons x q ih =>
    have kx : Keyed (p ++ [x]) := List.Pairwise.sublist (by simp) kp
    have e : S.runs ((x :: q).filterMap (upOf (byKey old))) =
        fun d => (S.runs (upOf (byKey old) x).toList d).bind (S.runs (q.filterMap (upOf (byKey old)))) := by
      funext d; cases h : upOf (byKey old) x <;> simp [List.filterMap_cons, Sql.runs, h]
    rw [e]; simp only
    rw [runs_up S hS hT db ko hR p x kx (hq x (by simp)), Option.bind_some,
      ih (p ++ [x]) (by simpa using kp) (fun y hy => hq y (by simp [hy]))]
    simp

/-! The table the plan leaves. -/

theorem cellsOf_upd {r : String → Val} {o x : α} (hc : cellsOf α r = Row.enc o) (hk : Row.key x = Row.key o) :
    cellsOf α (setCells r ((Row.cols α).drop (Row.nkey α)) ((Row.enc x).drop (Row.nkey α))) = Row.enc x := by
  have h := congrArg (List.map (setCells r ((Row.cols α).drop (Row.nkey α)) ((Row.enc x).drop (Row.nkey α))))
    (List.take_append_drop (Row.nkey α) (Row.cols α))
  rw [cellsOf, ← h, List.map_append, take_setCells_drop,
    setCells_map (RowLaws.nodup.sublist (List.drop_sublist _ _)) (by simp [RowLaws.len x])]
  rw [List.map_take, show (Row.cols α).map r = Row.enc o from hc, key_take hk.symm, List.take_append_drop]

theorem cellsOf_insRow (T : STable) (x : α) : cellsOf α (insRow T x) = Row.enc x :=
  setCells_map RowLaws.nodup (RowLaws.len x).symm

theorem nodup_enc {l : List α} (h : Keyed l) : (l.map Row.enc).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]; exact h.imp fun h e => h (enc_inj e)

/-- The rows of a table holding a keyed list have distinct keys. -/
theorem holds_keyed {T : STable} {l : List α} (h : Holds α T l) (kl : Keyed l) :
    T.rows.Pairwise fun a b => keyOf α a ≠ keyOf α b := by
  have hp : (l.map Row.enc).Pairwise fun a b =>
      (a.take (Row.nkey α)).flatMap Val.ord ≠ (b.take (Row.nkey α)).flatMap Val.ord := by
    rw [List.pairwise_map]; exact kl
  have := (h.symm.pairwise hp fun h e => h e.symm)
  rw [List.pairwise_map] at this
  exact this.imp fun h => by rwa [keyOf_eq, keyOf_eq]

/-- The write-back on a table holding exactly `old` (all its rows: the table was loaded) leaves it holding exactly
`new`, changes no column Lean does not know of a row it keeps (and gives a new row the defaults there), and changes no
other table; it fails at no statement. -/
theorem write_back (S : Sql) (hS : SqlExec S) (db : SDb) (hT : Shaped α (db (Row.table α))) {old new : List α}
    (hold : Holds α (db (Row.table α)) old) (ko : Keyed old) (kn : Keyed new)
    (ro : ∀ x ∈ old, InRange x) (rn : ∀ x ∈ new, InRange x) :
    ∃ R', S.runs (rowsPlan old new) db = some (db.set (Row.table α) { db (Row.table α) with rows := R' }) ∧
      Holds α { db (Row.table α) with rows := R' } new ∧
      ∀ r' ∈ R', (∃ r ∈ (db (Row.table α)).rows, keyOf α r = keyOf α r' ∧ ∀ c ∉ Row.cols α, r' c = r c) ∨
        ((∀ r ∈ (db (Row.table α)).rows, keyOf α r ≠ keyOf α r') ∧
          ∀ c ∉ Row.cols α, r' c = (db (Row.table α)).dflt c) := by
  generalize hTdef : db (Row.table α) = T at hT hold ⊢
  have hdb : db = db.set (Row.table α) { T with rows := T.rows } := by rw [← hTdef]; exact (SDb.set_self db _).symm
  have h0 : ∀ r ∈ T.rows, ∃ o ∈ old, cellsOf α r = Row.enc o := fun r hr => by
    have := hold.mem_iff.mp (List.mem_map_of_mem (f := cellsOf α) hr)
    simpa [eq_comm] using this
  have hk0 : ∀ r ∈ T.rows, ∃ o ∈ old, keyOf α r = Row.key o := fun r hr => by
    obtain ⟨o, ho, h⟩ := h0 r hr; exact ⟨o, ho, keyOf_cells h⟩
  have kr0 : KeyRows α T.rows := fun r hr => by
    obtain ⟨o, -, h⟩ := h0 r hr
    exact ⟨o, by rw [List.map_take]; exact congrArg (List.take _) h⟩
  let P := fun r => old.all fun x => (byKey new).contains (Row.key x) || keyOf α r != Row.key x
  let R₁ := T.rows.filter P
  have h1 : ∀ r ∈ R₁, ∃ o ∈ old, cellsOf α r = Row.enc o := fun r hr => h0 r (List.mem_filter.mp hr).1
  have hR₁ : R₁.map (applyUpds ([] : List α)) = R₁ := by
    rw [show applyUpds (α := α) [] = id from funext fun r => by simp [applyUpds], List.map_id]
  have hupds := runs_ups S hS hT db ko h1 new [] (by simpa using kn) rn
  rw [show upRows old T R₁ [] = R₁ by simp [upRows, hR₁]] at hupds
  refine ⟨upRows old T R₁ new, ?_, ?_, ?_⟩
  · rw [rowsPlan_eq ko kn, Sql.runs_append, hdb, runs_dels S hS hT db _ old ro T.rows kr0, Option.bind_some, SDb.set_set]
    simpa using hupds
  · -- each kept row now holds the new row of its key
    have hkept : ∀ r ∈ R₁, ∃ x ∈ new, keyOf α r = Row.key x ∧ cellsOf α (applyUpds new r) = Row.enc x := by
      intro r hr
      obtain ⟨hrT, hP⟩ := List.mem_filter.mp hr
      obtain ⟨o, ho, hc⟩ := h0 r hrT
      have := List.all_eq_true.mp hP o ho
      rw [keyOf_cells hc] at this
      simp only [bne_self_eq_false, Bool.or_false, byKey_contains, List.contains_iff_mem, List.mem_map] at this
      obtain ⟨x₀, hx₀, hkx₀⟩ := this
      obtain ⟨x, hfind⟩ : ∃ x, new.find? (fun y => Row.key y == keyOf α r) = some x := by
        cases h : new.find? (fun y => Row.key y == keyOf α r) with
        | some x => exact ⟨x, rfl⟩
        | none =>
          have := List.find?_eq_none.mp h x₀ hx₀
          simp [keyOf_cells hc, hkx₀] at this
      have hkx : Row.key x = keyOf α r := by simpa using List.find?_some hfind
      refine ⟨x, List.mem_of_find?_eq_some hfind, hkx.symm, ?_⟩
      simp only [applyUpds, hfind]
      exact cellsOf_upd hc (by rw [hkx, keyOf_cells hc])
    have kR : (upRows old T R₁ new).Pairwise fun a b => keyOf α a ≠ keyOf α b := by
      simp only [upRows, List.pairwise_append, List.pairwise_map, keyOf_applyUpds, keyOf_insRow]
      refine ⟨(holds_keyed hold ko).sublist (List.filter_sublist), (kn.sublist List.filter_sublist), ?_⟩
      intro a ha b hb
      simp only [List.mem_map, List.mem_filter] at ha hb
      obtain ⟨r, hr, rfl⟩ := ha; obtain ⟨y, ⟨-, hy⟩, rfl⟩ := hb
      obtain ⟨o, ho, h⟩ := hk0 r (List.mem_filter.mp hr).1
      rw [keyOf_applyUpds, h, keyOf_insRow]
      exact (byKey_none (by simpa using hy) o ho)
    refine (List.perm_ext_iff_of_nodup ?_ (nodup_enc kn)).mpr fun c => ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact kR.imp fun h e => h (by rw [keyOf_eq, keyOf_eq, e])
    · simp only [List.mem_map, upRows, List.mem_append, List.mem_filter] at hc
      obtain ⟨r', (⟨r, hr, rfl⟩ | ⟨y, ⟨hy, -⟩, rfl⟩), rfl⟩ := hc
      · obtain ⟨x, hx, -, h⟩ := hkept r hr; exact List.mem_map.mpr ⟨x, hx, h.symm⟩
      · exact List.mem_map.mpr ⟨y, hy, (cellsOf_insRow T y).symm⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
      cases hk : (byKey old)[Row.key x]? with
      | none =>
        refine List.mem_map.mpr ⟨insRow T x, List.mem_append.mpr (Or.inr (List.mem_map.mpr
          ⟨x, List.mem_filter.mpr ⟨hx, by rw [hk]; rfl⟩, rfl⟩)), cellsOf_insRow T x⟩
      | some o =>
        obtain ⟨ho, hko⟩ := byKey_get ko hk
        obtain ⟨r, hr, hc⟩ := List.mem_map.mp (hold.mem_iff.mpr (List.mem_map_of_mem ho))
        have hrP : r ∈ R₁ := by
          refine List.mem_filter.mpr ⟨hr, List.all_eq_true.mpr fun o' ho' => ?_⟩
          by_cases e : keyOf α r = Row.key o'
          · have : o' = o := Keyed.eq ko ho' ho (by rw [← e, keyOf_cells hc])
            subst this
            simp [byKey_contains, hko]; first | exact Or.inl ⟨x, hx, rfl⟩ | exact ⟨x, hx, rfl⟩
          · simp [e]
        obtain ⟨x', hx', hk', h'⟩ := hkept r hrP
        have : x' = x := Keyed.eq kn hx' hx (by rw [← hk', keyOf_cells hc, hko])
        subst this
        exact List.mem_map.mpr ⟨applyUpds new r, by simp [upRows, List.mem_map]; exact Or.inl ⟨r, hrP, rfl⟩, h'⟩
  · intro r' hr'
    simp only [upRows, List.mem_append, List.mem_map, List.mem_filter] at hr'
    rcases hr' with ⟨r, hr, rfl⟩ | ⟨y, ⟨-, hy⟩, rfl⟩
    · refine Or.inl ⟨r, (List.mem_filter.mp hr).1, (keyOf_applyUpds _ _).symm, fun c hc => ?_⟩
      rcases h : new.find? (fun y => Row.key y == keyOf α r) with _ | x
      · simp [applyUpds, h]
      · simp only [applyUpds, h]; exact setCells_other fun h => hc (List.mem_of_mem_drop h)
    · refine Or.inr ⟨fun r hr => ?_, fun c hc => setCells_other hc⟩
      obtain ⟨o, ho, h⟩ := hk0 r hr
      rw [h, keyOf_insRow]; exact byKey_none (Option.isNone_iff_eq_none.mp hy) o ho

/-! Loading. -/

theorem mapM_ok {l : List β} {g : β → Except ε γ} {h : β → γ} (hg : ∀ a ∈ l, g a = .ok (h a)) :
    l.mapM g = .ok (l.map h) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.mapM_cons, hg a (by simp), ih fun b hb => hg b (List.mem_cons_of_mem _ hb)]; rfl

/-- Rows in strict key order. -/
def Sorted (xs : List α) : Prop := xs.Pairwise fun a b => Row.key a < Row.key b

theorem Sorted.keyed {xs : List α} (h : Sorted xs) : Keyed xs :=
  h.imp fun hab e => by rw [e] at hab; exact List.lt_irrefl _ hab

theorem keysSorted_pairwise : ∀ {l : List (List Int × α)}, keysSorted l = true → l.Pairwise fun a b => a.1 ≤ b.1
  | [], _ => .nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [keysSorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := keysSorted_pairwise h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact List.le_trans h.1 (List.rel_of_pairwise_cons ih hc)

/-- Sorting by key gives back a list in key order from any order of it. -/
theorem sortRows_eq {ys xs : List α} (hp : ys.Perm xs) (srt : Sorted xs) : sortRows ys = xs := by
  -- a permutation of `xs` in key order is `xs`
  have uniq : ∀ {zs : List α}, zs.Perm xs → zs.Pairwise (fun a b => Row.key a ≤ Row.key b) → zs = xs := fun hz hs => by
    apply List.Perm.eq_of_pairwise (le := fun a b => decide (Row.key a ≤ Row.key b) = true)
    · intro a b ha hb h1 h2
      exact Keyed.eq srt.keyed (hz.mem_iff.mp ha) hb (List.le_antisymm (by simpa using h1) (by simpa using h2))
    · exact hs.imp fun h => by simpa using h
    · exact srt.imp fun h => by simpa using List.le_of_lt h
    · exact hz
  let le := fun (a b : List Int × α) => decide (a.1 ≤ b.1)
  have total : ∀ a b, (le a b || le b a) = true := fun a b => by
    rcases List.le_total a.1 b.1 with h | h <;> simp [le, h]
  have trans : ∀ a b c, le a b = true → le b c = true → le a c = true := fun a b c h1 h2 => by
    simp only [le, decide_eq_true_eq] at *; exact List.le_trans h1 h2
  let ps := ys.map fun r => (Row.key r, r)
  show (if keysSorted ps then ys else (ps.mergeSort le).map (·.2)) = xs
  split
  · next h => exact uniq hp (by simpa [ps, List.pairwise_map] using keysSorted_pairwise h)
  · have hkey : ∀ q ∈ ps.mergeSort le, q.1 = Row.key q.2 := fun q hq => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp ((List.mergeSort_perm ps le).mem_iff.mp hq); rfl
    refine uniq (((List.mergeSort_perm ps le).map _).trans (by simpa [ps, List.map_map, Function.comp_def] using hp)) ?_
    rw [List.pairwise_map]
    refine (List.pairwise_mergeSort trans total ps).imp_of_mem fun ha hb h => ?_
    rw [← hkey _ ha, ← hkey _ hb]; simpa [le] using h

/-- Loading a table that holds exactly `xs`, in key order, gives `xs`: SQLite returns its rows in some order, each
decodes, and `decodeRows` sorts them. -/
theorem load_rows [Inhabited α] (S : Sql) (hQ : SqlSelect S) (db : SDb) (hT : Shaped α (db (Row.table α)))
    {xs : List α} (h : Holds α (db (Row.table α)) xs) (srt : Sorted xs) :
    decodeRows (α := α) (S.select db (Row.table α) (Row.cols α)) = .ok xs := by
  have hp := hQ db (Row.table α) (Row.cols α) (hT.2 default).2.1
  have hp' : (S.select db (Row.table α) (Row.cols α)).Perm (xs.map fun x => (Row.enc x).toArray) := by
    refine hp.trans ?_
    have := h.map List.toArray
    simpa [List.map_map, Function.comp_def, cellsOf] using this
  let dec := fun v => match (Row.dec v : Except String α) with | .ok x => x | .error _ => default
  have hdec : ∀ v ∈ S.select db (Row.table α) (Row.cols α),
      (Row.dec v : Except String α).mapError (fun e => s!"{Row.table α}: {e}") = .ok (dec v) := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp (hp'.mem_iff.mp hv)
    simp [dec, decode_encode, Except.mapError]
  simp only [decodeRows, mapM_ok hdec]
  show Except.ok (sortRows _) = _
  congr 1
  apply sortRows_eq _ srt
  have := hp'.map dec
  simpa [List.map_map, Function.comp_def, dec, decode_encode] using this

/-- Load after store is the identity: the write-back of `new` (keyed, in key order, its ints in int64) over a table
holding exactly `old`, then a load, gives `new`. -/
theorem store_load [Inhabited α] (S : Sql) (hS : SqlExec S) (hQ : SqlSelect S) (db : SDb)
    (hT : Shaped α (db (Row.table α))) {old new : List α} (hold : Holds α (db (Row.table α)) old) (ko : Keyed old)
    (srt : Sorted new) (ro : ∀ x ∈ old, InRange x) (rn : ∀ x ∈ new, InRange x) :
    ∃ db', S.runs (rowsPlan old new) db = some db' ∧ decodeRows (α := α) (S.select db' (Row.table α) (Row.cols α)) = .ok new := by
  obtain ⟨R', hrun, hh, -⟩ := write_back S hS db hT hold ko srt.keyed ro rn
  exact ⟨_, hrun, load_rows S hQ _ (by rw [SDb.set_same]; exact hT) (by rw [SDb.set_same]; exact hh) srt⟩

/-- A table the step left as loaded gets no statement. -/
theorem rowsPlan_same {l : List α} (k : Keyed l) : rowsPlan l l = [] := by
  rw [rowsPlan_eq k k, List.append_eq_nil_iff]
  constructor
  · apply List.filterMap_eq_nil_iff.mpr; intro x hx
    have : (byKey l).contains (Row.key x) = true := by rw [byKey_contains]; simpa using ⟨x, hx, rfl⟩
    simp [this]
  · apply List.filterMap_eq_nil_iff.mpr; intro x hx
    have hp : (l.map fun r => (Row.key r, r)).Pairwise fun a b => (a.1 == b.1) = false := by
      rw [List.pairwise_map]; exact k.imp fun h => by simpa using h
    have : (byKey l)[Row.key x]? = some x :=
      Std.HashMap.getElem?_ofList_of_mem (k := Row.key x) (by simp) hp (List.mem_map_of_mem hx)
    simp [upOf, this]

/-- A table that was not loaded gets an insert of each row the step added (which fails, rolling back, on a key the
table has). -/
theorem rowsPlan_unloaded (new : List α) :
    rowsPlan [] new = new.map fun x => .ins (Row.table α) (Row.cols α) (Row.enc x) := by
  have h0 : ∀ k : List Int, (byKey ([] : List α))[k]? = none := fun k => by
    simp only [byKey, List.map_nil]; exact Std.HashMap.getElem?_ofList_of_contains_eq_false (by simp)
  show planOf [] new = _
  simp only [planOf, List.filterMap_nil, List.nil_append]
  induction new with
  | nil => rfl
  | cons x l ih => simp [List.filterMap_cons, upOf, h0, ih]

end

end SwarmLean
