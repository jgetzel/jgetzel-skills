import SwarmLean.Assumptions

/-! The store layer (board #134): each row type's codec round-trips and refuses what it would misread; the write-back
plan, run by SQLite (`SqlExec`), leaves each table holding exactly the step's rows with unknown columns as they were;
load after store is the identity; each migration takes schema version n to n+1 and is idempotent. -/

namespace SwarmLean
open Sqlite (Val)

/-! ### The codec -/

/-- Cell `v` read as the value `w` a field encodes to: the same, or one of the decoders' coercions (a number as its
text; integral text, or an integral float under 9e15, as the integer). -/
inductive Reads : Val → Val → Prop
  | same : Reads v v
  | intText : Reads (.int i) (.text (toString i))
  | realText : Reads (.real f) (.text (toString f))
  | textInt : parseInt s = some i → Reads (.text s) (.int i)
  | realInt : (f == f.floor && f.abs < 9.0e15) = true → Reads (.real f) (.int f.toInt64.toInt)

theorem Except.bind_ok {x : Except ε α} {f : α → Except ε β} : (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

@[simp] theorem Except.pure_ok : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

@[simp] theorem os_oS (o : Option String) : (oS o).os = .ok o := by cases o <;> rfl
@[simp] theorem oi_oI (o : Option Int) : (oI o).oi = .ok o := by cases o <;> rfl
@[simp] theorem id_int (n : Nat) : (Val.int n).id = .ok n := rfl
@[simp] theorem os_text (s : String) : (Val.text s).os = .ok (some s) := rfl
@[simp] theorem key_text (s : String) : (Val.text s).key = .ok s := rfl
@[simp] theorem ofText_text (s : Status) : Status.ofText s.text = .ok s := by cases s <;> rfl

theorem reads_os {v : Val} (h : v.os = .ok o) : Reads v (oS o) := by
  cases v <;> simp [Val.os] at h <;> subst h <;> first | exact .same | exact .intText | exact .realText

theorem reads_oi {v : Val} (h : v.oi = .ok o) : Reads v (oI o) := by
  cases v with
  | null => simp [Val.oi] at h; subst h; exact .same
  | int i => simp [Val.oi] at h; subst h; exact .same
  | text s =>
    simp only [Val.oi] at h; split at h <;> simp at h; subst h; exact .textInt ‹_›
  | real f =>
    simp only [Val.oi] at h; split at h <;> simp at h; subst h; exact .realInt ‹_›

theorem reads_id {v : Val} (h : v.id = .ok n) : Reads v (.int n) := by
  simp only [Val.id, Except.bind_ok] at h
  obtain ⟨o, ho, h⟩ := h
  have := reads_oi ho
  split at h <;> simp_all [oI, Except.pure_ok, throw, throwThe, MonadExceptOf.throw]

theorem reads_key {v : Val} (h : v.key = .ok s) : Reads v (.text s) := by
  simp only [Val.key, Except.bind_ok] at h
  obtain ⟨o, ho, h⟩ := h
  have := reads_os ho
  split at h <;> simp_all [oS, throw, throwThe, MonadExceptOf.throw]

theorem ofText_ok (h : Status.ofText s = .ok st) : s = st.text := by
  unfold Status.ofText at h; split at h <;> first | (cases h; rfl) | simp at h

/-- Each cell of `vs` reads as the value in the same place of `ws`, the lists as long. -/
def AllReads : List Val → List Val → Prop
  | a :: as, b :: bs => Reads a b ∧ AllReads as bs
  | [], [] => True
  | _, _ => False

@[simp] theorem Except.map_ok' {f : α → β} : (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

/-- What the store proofs need of a row type's codec. -/
class RowLaws (α : Type) [Row α] where
  len : ∀ x : α, (Row.enc x).length = (Row.cols α).length
  nodup : (Row.cols α).Nodup
  nkey : 0 < Row.nkey α ∧ Row.nkey α ≤ (Row.cols α).length
  dec_enc : ∀ x : α, Row.dec (Row.enc x).toArray = .ok x
  key_cls : ∀ x y : α, ((Row.enc x).take (Row.nkey α)).map Val.cls = ((Row.enc y).take (Row.nkey α)).map Val.cls
  key_it : ∀ x : α, ∀ v ∈ (Row.enc x).take (Row.nkey α), v.cls = 1 ∨ v.cls = 3
  dec_reads : ∀ v (x : α), Row.dec v = .ok x →
    AllReads ((List.range (Row.cols α).length).map (col v)) (Row.enc x)

theorem ofText_reads {v : Val} (h1 : v.os = .ok (some s)) (h2 : Status.ofText s = .ok st) : Reads v (.text st.text) := by
  have := reads_os h1; rwa [ofText_ok h2] at this

/-- Proves a `RowLaws` instance: each field by cases on the row, simp and the cell lemmas. -/
macro "row_laws" : tactic => `(tactic| exact {
  len := fun x => by cases x; rfl
  nodup := by decide
  nkey := by decide
  dec_enc := fun x => by cases x; simp [Row.dec, Row.enc, col, Except.bind_ok]
  key_cls := fun x y => by cases x; cases y; rfl
  key_it := fun x => by cases x; simp [Row.enc, Val.cls, Row.nkey]
  dec_reads := fun v x h => by
    simp only [Row.dec, Except.bind_ok] at h
    repeat' (first
      | obtain ⟨_, _, h⟩ := h
      | (split at h <;> simp only [Except.bind_ok, throw, throwThe, MonadExceptOf.throw, Except.bind_ok] at h))
    all_goals try contradiction
    try (simp at h; subst h)
    simp only [Row.cols, List.range, List.range.loop, List.map_nil, List.map_cons, Row.enc, AllReads, and_true]
    try dsimp only
    repeat' apply And.intro
    all_goals first
      | (apply reads_key; assumption) | (apply reads_id; assumption) | (apply reads_os; assumption)
      | (apply reads_oi; assumption) | exact True.intro | (apply ofText_reads <;> assumption) })

instance : RowLaws Meta := by row_laws
instance : RowLaws Task := by row_laws
instance : RowLaws Agent := by row_laws
instance : RowLaws Msg := by row_laws
instance : RowLaws Cursor := by row_laws
instance : RowLaws Lock := by row_laws
instance : RowLaws Conflict := by row_laws
instance : RowLaws Pairkey := by row_laws
instance : RowLaws Event := by row_laws
instance : RowLaws Workspace := by row_laws
instance : RowLaws Ci := by row_laws

/-- A row type's codec round-trips: decoding what a row encodes to gives the row (every row type, `RowLaws`). -/
theorem decode_encode [Row α] [RowLaws α] (x : α) : Row.dec (Row.enc x).toArray = .ok x := RowLaws.dec_enc x

/-- Decoding refuses rather than misreads: a row decoded from cells `v` encodes, column by column, to what each cell
reads as (itself, or a documented coercion); any other cell is an error. -/
theorem decode_reads [Row α] [RowLaws α] (v : Array Val) (x : α) (h : Row.dec v = .ok x) :
    AllReads ((List.range (Row.cols α).length).map (col v)) (Row.enc x) := RowLaws.dec_reads v x h

/-! ### Keys and cells -/

theorem ord_ne_nil (v : Val) : v.ord ≠ [] := by cases v <;> simp [Val.ord]

/-- The text part of `Val.ord`: code points, then -1. -/
theorem sentinel_inj {a b r r' : List Int} (ha : ∀ x ∈ a, 0 ≤ x) (hb : ∀ x ∈ b, 0 ≤ x)
    (h : a ++ [-1] ++ r = b ++ [-1] ++ r') : a = b ∧ r = r' := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simpa using h
    | cons y b => simp at h; have := hb y (by simp); omega
  | cons x a ih =>
    cases b with
    | nil => simp at h; have := ha x (by simp); omega
    | cons y b =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (fun z hz => ha z (by simp [hz])) (fun z hz => hb z (by simp [hz])) h
      exact ⟨by rw [this.1], this.2⟩

theorem chars_inj {s t : String} (h : s.toList.map (fun c => (c.toNat : Int)) = t.toList.map (fun c => (c.toNat : Int))) :
    s = t := by
  apply String.ext
  generalize s.toList = a at h; generalize t.toList = b at h
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.map_cons, List.cons.injEq] at h
      have : x = y := Char.toNat_inj.mp (by omega)
      rw [this, ih b h.2]

/-- Two lists of int and text cells with the same `Val.ord`s are the same: a key's ints are its cells. -/
theorem ord_inj {a b : List Val} (ha : ∀ v ∈ a, v.cls = 1 ∨ v.cls = 3) (hb : ∀ v ∈ b, v.cls = 1 ∨ v.cls = 3)
    (h : a.flatMap Val.ord = b.flatMap Val.ord) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons y b => cases y <;> simp [Val.ord] at h
  | cons x a ih =>
    cases b with
    | nil => cases x <;> simp [Val.ord] at h
    | cons y b =>
      have ha' := fun v hv => ha v (List.mem_cons_of_mem _ hv)
      have hb' := fun v hv => hb v (List.mem_cons_of_mem _ hv)
      simp only [List.flatMap_cons] at h
      have hx := ha x (by simp); have hy := hb y (by simp)
      cases x <;> cases y <;> simp only [Val.cls] at hx hy <;> (try omega)
      · simp [Val.ord] at h; rw [h.1, ih ha' hb' h.2]
      · simp [Val.ord] at h
      · simp [Val.ord] at h
      · rename_i s t
        simp only [Val.ord, List.cons_append, List.cons.injEq, true_and] at h
        have := sentinel_inj (by simp) (by simp) h
        rw [chars_inj this.1, ih ha' hb' this.2]

/-- `r` with columns `cs` set: a column not among them keeps its cell. -/
theorem setCells_other {r : String → Val} {cs : List String} {vs : List Val} (h : c ∉ cs) :
    setCells r cs vs c = r c := by
  induction cs generalizing vs with
  | nil => rfl
  | cons d cs ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      have hd : (c == d) = false := by simp; exact fun e => h (e ▸ List.mem_cons_self)
      have := ih (vs := vs) (fun m => h (List.mem_cons_of_mem _ m))
      simpa [setCells, List.lookup_cons, hd] using this

/-- `r` with columns `cs` (none twice) set to `vs` holds `vs` there. -/
theorem setCells_map {r : String → Val} {cs : List String} {vs : List Val} (hn : cs.Nodup)
    (hl : cs.length = vs.length) : cs.map (setCells r cs vs) = vs := by
  induction cs generalizing vs with
  | nil => cases vs <;> simp_all
  | cons d cs ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.nodup_cons] at hn
      simp only [List.map_cons, List.cons.injEq]
      refine ⟨by simp [setCells], ?_⟩
      calc cs.map (setCells r (d :: cs) (v :: vs)) = cs.map (setCells r cs vs) := by
            apply List.map_congr_left; intro c hc
            have : (c == d) = false := by simp; exact fun e => hn.1 (e ▸ hc)
            simp [setCells, List.lookup_cons, this]
        _ = vs := ih hn.2 (by simpa using hl)

/-- Setting columns to the cells a row has there changes nothing. -/
theorem setCells_self (r : String → Val) (cs : List String) : setCells r cs (cs.map r) = r := by
  funext c
  induction cs with
  | nil => rfl
  | cons d cs ih =>
    by_cases hd : c = d
    · subst hd; simp [setCells]
    · have : (c == d) = false := by simpa using hd
      simpa [setCells, List.lookup_cons, this] using ih

@[simp] theorem SDb.set_same (db : SDb) : (db.set t T) t = T := by simp [SDb.set]
@[simp] theorem SDb.set_set (db : SDb) : (db.set t T).set t T' = db.set t T' := by
  funext u; simp only [SDb.set]; split <;> rfl
theorem SDb.set_other (db : SDb) (h : u ≠ t) : (db.set t T) u = db u := by simp [SDb.set, h]

/-- The rows of a list with no key twice. -/
def Keyed [Row α] (l : List α) : Prop := l.Pairwise fun a b => Row.key a ≠ Row.key b

theorem Keyed.eq [Row α] {l : List α} (h : Keyed l) (ha : a ∈ l) (hb : b ∈ l) (e : Row.key a = Row.key b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [Keyed, List.pairwise_cons] at h
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd e (h.1 _ hb)
    · exact absurd e.symm (h.1 _ ha)
    · exact ih h.2 ha hb

end SwarmLean
