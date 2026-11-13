import SwarmLean.Db.Msgs
import SwarmLean.Lib.Agents
import SwarmLean.Proofs

/-! Messages (board #104): S4 about the real steps. Db/Msgs.lean's `post`, `take` (what `swarm read` runs) and
`deliverStep` (the hooks' and the waiter's delivery), in any order with any other transaction that only adds messages
and new agents' cursors, show each message to its addressee exactly once, in order, and move its cursor past nothing
they didn't show. -/

namespace SwarmLean.Inbox
open Msgs

/-- Message `r` is for agent `n`: from another sender, to `n` or to all. -/
def ToIt (n : String) (r : Msg) : Prop :=
  r.frm ≠ none ∧ r.frm ≠ some n ∧ (r.dest = some n ∨ r.dest = some "@all")

instance (n : String) : DecidablePred (ToIt n) := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The messages for `n` with ids past cursor `a` up to cursor `b`, in log order. -/
def window (db : Db) (n : String) (a b : Int) : List Msg :=
  db.msgs.filter fun r => decide (ToIt n r ∧ a < r.id ∧ r.id ≤ b)

/-- The message log's invariant: ids increase along the log and stay below the next id, and so does every cursor; the
next id is positive. -/
def MInv (db : Db) : Prop :=
  (db.msgs.map (·.id)).Pairwise (· < ·) ∧ (∀ r ∈ db.msgs, r.id < db.msgNext) ∧ (∀ n, cursorOf db n < db.msgNext) ∧
    0 < db.msgNext

/-- `db'` only adds to `db`'s messages and cursors: messages after the old ones with fresh ids in order, and cursors
of agents that had none. -/
def Grows (db db' : Db) : Prop :=
  db.msgNext ≤ db'.msgNext ∧
  (∃ new, db'.msgs = db.msgs ++ new ∧ (new.map (·.id)).Pairwise (· < ·) ∧
    ∀ r ∈ new, db.msgNext ≤ r.id ∧ r.id < db'.msgNext) ∧
  ∃ more, db'.cursors = db.cursors ++ more ∧ ∀ c ∈ more, db.cursor c.agent = none ∧ c.last_msg_id.getD 0 < db'.msgNext

/-- A transaction the theorems cover: a post, `swarm read`, a delivery with a budget, or any other step that only grows
the messages and cursors of a db that keeps the invariant. -/
inductive MCmd
  | post (now : Int) (frm dest body : String) (urgent : Bool) (kind : Option String)
  | read (n : String)
  | deliver (n : String) (budget : Nat)
  | other (f : Db → Db) (h : ∀ db, MInv db → Grows db (f db))

/-- A transaction's effect and the messages it showed: the CLI's own step functions. -/
def MCmd.step : MCmd → Db → Db × List Msg
  | .post now f d b u k, db => ((Msgs.post db now f d b u k).1, [])
  | .read n, db => ((take n id db).1, (take n id db).2.2)
  | .deliver n b, db => ((deliverStep n b db).1, (deliverStep n b db).2.1)
  | .other f _, db => (f db, [])

/-- Whom a transaction delivers to. -/
def MCmd.to : MCmd → Option String
  | .read n | .deliver n _ => some n
  | _ => none

/-- What the deliveries to `n` among `t` showed, in order. -/
def shownTo (n : String) (t : List (MCmd × List Msg)) : List Msg :=
  t.flatMap fun (c, fit) => if c.to = some n then fit else []

/-! Lemmas on the steps. -/

theorem cursor_append (db : Db) (more : List Cursor) (n : String) :
    ({ db with cursors := db.cursors ++ more } : Db).cursor n = (db.cursor n).or (more.find? (·.agent == n)) := by
  simp [Db.cursor]

theorem cursorOf_eq {db db' : Db} {n : String} (h : db'.cursor n = db.cursor n) : cursorOf db' n = cursorOf db n := by
  simp [cursorOf, h]

theorem cursorOf_none {db : Db} {n : String} (h : db.cursor n = none) : cursorOf db n = 0 := by
  simp [cursorOf, h]

theorem grows_cursor {db db' : Db} (h : Grows db db') {n : String} (hn : (db.cursor n).isSome) :
    db'.cursor n = db.cursor n := by
  obtain ⟨-, -, more, hc, -⟩ := h
  obtain ⟨c, e⟩ := Option.isSome_iff_exists.1 hn
  have : db' = { db' with cursors := db.cursors ++ more } := by rw [← hc]
  rw [this, show ({ db' with cursors := db.cursors ++ more } : Db).cursor n = (db.cursors ++ more).find? (·.agent == n)
    from rfl, List.find?_append]
  simp [Db.cursor] at e ⊢; simp [e]

theorem grows_inv {db db' : Db} (g : Grows db db') (h : MInv db) : MInv db' := by
  obtain ⟨hn, ⟨new, hm, hp, hb⟩, more, hc, hmore⟩ := g
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, fun n => ?_, by omega⟩
  · rw [hm, List.map_append, List.pairwise_append]
    refine ⟨h1, hp, fun a ha b hb' => ?_⟩
    simp only [List.mem_map] at ha hb'
    obtain ⟨r, hr, rfl⟩ := ha; obtain ⟨s, hs, rfl⟩ := hb'
    have := h2 r hr; have := (hb s hs).1; omega
  · intro r hr; rw [hm] at hr
    rcases List.mem_append.1 hr with hr | hr
    · have := h2 r hr; omega
    · exact (hb r hr).2
  · have h3n := h3 n
    have e : db'.cursor n = (db.cursor n).or (more.find? (·.agent == n)) := by
      simp only [Db.cursor, hc, List.find?_append]
    cases hcn : db.cursor n with
    | some c =>
      rw [hcn, Option.some_or] at e
      rw [cursorOf_eq (db' := db') (db := db) (e.trans hcn.symm)]; omega
    | none =>
      rw [hcn, Option.none_or] at e
      rw [cursorOf_none hcn] at h3n
      cases hf : more.find? (·.agent == n) with
      | none => rw [hf] at e; rw [cursorOf_none e]; omega
      | some c =>
        rw [hf] at e
        have := (hmore c (List.mem_of_find?_eq_some hf)).2
        simp only [cursorOf, e, Option.bind_some]; exact this

theorem grows_of_eq {db db' : Db} (hm : db'.msgs = db.msgs) (hc : db'.cursors = db.cursors) (hn : db'.msgNext = db.msgNext) :
    Grows db db' :=
  ⟨by omega, ⟨[], by simp [hm], by simp, by simp⟩, [], by simp [hc], by simp⟩

theorem grows_congr {a a' b : Db} (hm : a'.msgs = a.msgs) (hc : a'.cursors = a.cursors) (hn : a'.msgNext = a.msgNext)
    (h : Grows a b) : Grows a' b := by
  unfold Grows Db.cursor at *; rw [hm, hc, hn]; exact h

theorem grows_refl (db : Db) : Grows db db := grows_of_eq rfl rfl rfl

theorem grows_trans {a b c : Db} (h1 : Grows a b) (h2 : Grows b c) : Grows a c := by
  obtain ⟨n1, ⟨new1, m1, p1, b1⟩, more1, c1, k1⟩ := h1
  obtain ⟨n2, ⟨new2, m2, p2, b2⟩, more2, c2, k2⟩ := h2
  refine ⟨by omega, ⟨new1 ++ new2, by rw [m2, m1, List.append_assoc], ?_, ?_⟩, more1 ++ more2, by rw [c2, c1, List.append_assoc], ?_⟩
  · rw [List.map_append, List.pairwise_append]
    refine ⟨p1, p2, fun x hx y hy => ?_⟩
    simp only [List.mem_map] at hx hy
    obtain ⟨r, hr, rfl⟩ := hx; obtain ⟨s, hs, rfl⟩ := hy
    have := (b1 r hr).2; have := (b2 s hs).1; omega
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · have := b1 r hr; omega
    · have := b2 r hr; omega
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · have := k1 x hx; exact ⟨this.1, by omega⟩
    · have ⟨e, hl⟩ := k2 x hx
      refine ⟨?_, hl⟩
      have : b.cursor x.agent = (a.cursor x.agent).or (more1.find? (·.agent == x.agent)) := by
        simp only [Db.cursor, c1, List.find?_append]
      rw [e] at this
      cases h : a.cursor x.agent with
      | none => rfl
      | some _ => rw [h] at this; cases this

@[simp] theorem log_msgs (db : Db) ts a k p x : (db.log ts a k p x).msgs = db.msgs := rfl
@[simp] theorem log_cursors (db : Db) ts a k p x : (db.log ts a k p x).cursors = db.cursors := rfl
@[simp] theorem log_msgNext (db : Db) ts a k p x : (db.log ts a k p x).msgNext = db.msgNext := rfl
@[simp] theorem setAgent_msgs (db : Db) n f : (db.setAgent n f).msgs = db.msgs := rfl
@[simp] theorem setAgent_cursors (db : Db) n f : (db.setAgent n f).cursors = db.cursors := rfl
@[simp] theorem setAgent_msgNext (db : Db) n f : (db.setAgent n f).msgNext = db.msgNext := rfl

theorem grows_log (db : Db) ts a k p x : Grows db (db.log ts a k p x) := grows_of_eq rfl rfl rfl

/-- The message `post` appends. -/
def posted (db : Db) (now : Int) (frm dest body : String) (urgent : Bool) (kind : Option String) : Msg :=
  { id := db.msgNext, ts := some now, frm := some frm, dest := some dest, body := some body,
    urgent := some (if urgent then 1 else 0), kind := some (kind.getD (if dest == "@all" then "all" else "dm")) }

theorem post_eq (db : Db) now frm dest body urgent kind :
    (Msgs.post db now frm dest body urgent kind).1.msgs = db.msgs ++ [posted db now frm dest body urgent kind] ∧
    (Msgs.post db now frm dest body urgent kind).1.cursors = db.cursors ∧
    (Msgs.post db now frm dest body urgent kind).1.msgNext = db.msgNext + 1 ∧
    (Msgs.post db now frm dest body urgent kind).2 = db.msgNext := ⟨rfl, rfl, rfl, rfl⟩

theorem grows_post (db : Db) now frm dest body urgent kind : Grows db (Msgs.post db now frm dest body urgent kind).1 := by
  obtain ⟨hm, hc, hn, -⟩ := post_eq db now frm dest body urgent kind
  exact ⟨by omega, ⟨_, hm, by simp, by simp [hn, posted]⟩, [], by simp [hc], by simp⟩

theorem grows_newInbox (db : Db) (n : String) (h : 0 < db.msgNext) : Grows db (Agents.newInbox db n) := by
  unfold Agents.newInbox
  split
  · exact grows_refl db
  · rename_i hc
    refine ⟨Nat.le_refl _, ⟨[], by simp, by simp, by simp⟩, _, rfl, ?_⟩
    simp only [List.mem_singleton]
    rintro c rfl
    refine ⟨?_, by simp; omega⟩
    simp only [Db.cursor]; simpa using hc

theorem grows_touch (db : Db) n cwd here now (h : 0 < db.msgNext) : Grows db (Agents.touch db n cwd here now) := by
  unfold Agents.touch
  split
  · exact grows_refl db
  · split
    · exact grows_refl db
    · refine grows_congr (a := { db with agents := db.agents ++ _ }) rfl rfl rfl (grows_newInbox _ n ?_)
      exact h

theorem grows_touchWith (db : Db) n cwd here now bind f (h : 0 < db.msgNext) :
    Grows db (Agents.touchWith db n cwd here now bind f).1 := by
  unfold Agents.touchWith
  split
  · exact grows_refl db
  · split
    · exact grows_refl db
    · dsimp only
      refine grows_trans (grows_touch db n cwd here now h) ?_
      split <;> exact grows_of_eq rfl rfl rfl

/-! `take` and `unread`. -/

theorem take_eq (n : String) (pick : List Msg → List Msg) (db : Db) :
    (take n pick db).2.1 = unread db n ∧ (take n pick db).2.2 = pick (unread db n) ∧
    (take n pick db).1.msgs = db.msgs ∧ (take n pick db).1.msgNext = db.msgNext := by
  unfold take; dsimp only
  cases h : (pick (unread db n)).getLast? with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some l => dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem take_none {n : String} {pick : List Msg → List Msg} {db : Db} (h : (pick (unread db n)).getLast? = none) :
    (take n pick db).1 = db := by
  unfold take; simp only []; rw [h]

theorem take_cursor_other {n m : String} {pick : List Msg → List Msg} {db : Db} (h : m ≠ n) :
    (take n pick db).1.cursor m = db.cursor m := by
  unfold take; dsimp only
  cases hl : (pick (unread db n)).getLast? with
  | none => rfl
  | some l =>
    dsimp only
    split
    · simp only [Db.cursor, List.find?_map]
      have e : ((fun c : Cursor => c.agent == m) ∘ fun c => if c.agent = n then { c with last_msg_id := some (l.id : Int) } else c)
          = fun c => c.agent == m := by
        funext c; simp only [Function.comp]; split <;> rfl
      rw [e]
      cases hf : db.cursors.find? (·.agent == m) with
      | none => rfl
      | some c =>
        have := List.find?_some hf
        simp only [beq_iff_eq] at this
        simp [this, h]
    · simp only [Db.cursor, List.find?_append]
      have : ([{ agent := n, last_msg_id := some (l.id : Int) }] : List Cursor).find? (·.agent == m) = none := by
        simp [Ne.symm h]
      rw [this, Option.or_none]

theorem take_cursor_self {n : String} {pick : List Msg → List Msg} {db : Db} {l : Msg}
    (h : (pick (unread db n)).getLast? = some l) : cursorOf (take n pick db).1 n = l.id := by
  unfold take; simp only []; rw [h]; simp only []
  split
  · rename_i ha
    obtain ⟨c, hc, hca⟩ := List.any_eq_true.1 ha
    simp only [cursorOf, Db.cursor, List.find?_map]
    have e : ((fun c : Cursor => c.agent == n) ∘ fun c => if c.agent = n then { c with last_msg_id := some (l.id : Int) } else c)
        = fun c => c.agent == n := by
      funext c; simp only [Function.comp]; split <;> rfl
    rw [e]
    cases hf : db.cursors.find? (·.agent == n) with
    | none => exact absurd hf (List.find?_isSome.2 ⟨c, hc, hca⟩ |> Option.isSome_iff_ne_none.1)
    | some c' =>
      have := List.find?_some hf
      simp only [beq_iff_eq] at this
      simp [this]
  · rename_i ha
    simp only [cursorOf, Db.cursor, List.find?_append]
    have : db.cursors.find? (·.agent == n) = none := by
      rw [List.find?_eq_none]; intro c hc hca; exact ha (List.any_eq_true.2 ⟨c, hc, hca⟩)
    simp [this]

theorem take_isSome {n m : String} {pick : List Msg → List Msg} {db : Db} (h : (db.cursor m).isSome) :
    ((take n pick db).1.cursor m).isSome := by
  by_cases e : m = n
  · subst e
    cases hl : (pick (unread db m)).getLast? with
    | none => rw [take_none hl]; exact h
    | some l =>
      unfold take; simp only []; rw [hl]; simp only []
      split
      · simp only [Db.cursor, List.find?_map, Option.isSome_map]
        have e : ((fun c : Cursor => c.agent == m) ∘ fun c => if c.agent = m then { c with last_msg_id := some (l.id : Int) } else c)
            = fun c => c.agent == m := by
          funext c; simp only [Function.comp]; split <;> rfl
        rw [e]; exact h
      · simp [Db.cursor]
  · rw [take_cursor_other e]; exact h

theorem toIt_bool (n : String) (r : Msg) :
    (r.frm.any (· != n) && (r.dest == some n || r.dest == some "@all")) = decide (ToIt n r) := by
  rcases r with ⟨id, ts, frm, dest, body, urgent, kind⟩
  cases frm <;> cases dest <;> simp [ToIt]
  rename_i a b
  by_cases h1 : a = n <;> by_cases h2 : b = n <;> by_cases h3 : b = "@all" <;> simp [h1, h2, h3]

theorem unread_eq (db : Db) (n : String) (h : (db.msgs.map (·.id)).Pairwise (· < ·)) :
    unread db n = db.msgs.filter fun r => decide (ToIt n r ∧ cursorOf db n < r.id) := by
  unfold unread
  rw [List.mergeSort_of_pairwise]
  · apply List.filter_congr; intro r _
    rw [Bool.and_assoc, toIt_bool]; simp [Bool.and_comm]
  · refine List.Pairwise.sublist List.filter_sublist ?_
    rw [List.pairwise_map] at h
    exact h.imp fun e => by simp; omega

theorem mem_unread {db : Db} {n : String} {r : Msg} :
    r ∈ unread db n ↔ r ∈ db.msgs ∧ ToIt n r ∧ cursorOf db n < r.id := by
  unfold unread
  simp only [List.mem_mergeSort, List.mem_filter]
  rw [Bool.and_assoc, toIt_bool]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, by omega⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h2⟩

/-! What one delivery shows. -/

theorem fits_go_prefix (budget size : Nat) (rows : List Msg) : fits.go budget size rows <+: rows := by
  induction rows generalizing size with
  | nil => exact List.prefix_refl _
  | cons r rs ih =>
    unfold fits.go; dsimp only; split
    · exact List.nil_prefix
    · exact (List.prefix_cons_inj r).2 (ih _)

/-- deliver's pick keeps a prefix of the unread rows: the rest stay unread. -/
theorem fits_prefix (budget : Nat) (rows : List Msg) : fits budget rows <+: rows := fits_go_prefix budget 120 rows

theorem last_max {fit : List Msg} {l : Msg} (hf : (fit.map (·.id)).Pairwise (· < ·)) (hl : fit.getLast? = some l)
    {x : Msg} (hx : x ∈ fit) : x.id ≤ l.id := by
  obtain ⟨init, e⟩ : ∃ init, fit = init ++ [l] := by
    obtain ⟨init, e⟩ := List.getLast?_eq_some_iff.1 hl; exact ⟨init, e⟩
  rw [e, List.map_append, List.pairwise_append] at hf
  rw [e] at hx
  rcases List.mem_append.1 hx with hi | hi
  · have := hf.2.2 x.id (List.mem_map_of_mem hi) l.id (by simp); omega
  · simp at hi; subst hi; exact Nat.le_refl _

theorem prefix_filter {fit rest : List Msg} {l : Msg} (hp : ((fit ++ rest).map (·.id)).Pairwise (· < ·))
    (hl : fit.getLast? = some l) : (fit ++ rest).filter (fun r => decide ((r.id : Int) ≤ l.id)) = fit := by
  rw [List.map_append, List.pairwise_append] at hp
  obtain ⟨hf, -, hx⟩ := hp
  have hlm : l ∈ fit := List.mem_of_getLast? hl
  rw [List.filter_append, List.filter_eq_self.2, List.filter_eq_nil_iff.2, List.append_nil]
  · intro y hy; have := hx l.id (List.mem_map_of_mem hlm) y.id (List.mem_map_of_mem hy); simp; omega
  · intro x hx'; have := last_max hf hl hx'; simp; omega

theorem filter_split {l : List Msg} (hp : (l.map (·.id)).Pairwise (· < ·)) (P Q : Msg → Bool) (c : Int)
    (hP : ∀ r, P r = true → (r.id : Int) ≤ c) (hQ : ∀ r, Q r = true → c < r.id) :
    l.filter (fun r => P r || Q r) = l.filter P ++ l.filter Q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.pairwise_cons, List.mem_map] at hp
    have ih := ih hp.2
    by_cases px : P x = true
    · have : Q x = false := by
        cases e : Q x; rfl; have := hP x px; have := hQ x e; omega
      simp [px, this, ih]
    · by_cases qx : Q x = true
      · have : xs.filter P = [] := List.filter_eq_nil_iff.2 fun y hy py => by
          have := hP y py; have := hQ x qx; have := hp.1 y.id ⟨y, hy, rfl⟩; omega
        simp [px, qx, ih, this]
      · simp [px, qx, ih]

/-- A delivery to `n` whose pick keeps a prefix shows exactly the messages for `n` its cursor moves past, in order, and
the cursor only moves forward. -/
theorem take_window {db : Db} {n : String} {pick : List Msg → List Msg} (hpick : ∀ rows, pick rows <+: rows)
    (h : MInv db) {c0 : Int} (hc0 : c0 ≤ cursorOf db n) :
    window db n c0 (cursorOf db n) ++ (take n pick db).2.2 =
      window (take n pick db).1 n c0 (cursorOf (take n pick db).1 n) ∧
    cursorOf db n ≤ cursorOf (take n pick db).1 n := by
  obtain ⟨-, hfit, hm, -⟩ := take_eq n pick db
  rw [hfit]
  cases hl : (pick (unread db n)).getLast? with
  | none =>
    rw [take_none hl, List.getLast?_eq_none_iff.1 hl, List.append_nil]; exact ⟨rfl, Int.le_refl _⟩
  | some l =>
    rw [take_cursor_self hl]
    obtain ⟨rest, hr⟩ := hpick (unread db n)
    have hlu : l ∈ unread db n := hr ▸ List.mem_append_left _ (List.mem_of_getLast? hl)
    have hlc := (mem_unread.1 hlu).2.2
    refine ⟨?_, by omega⟩
    have hu := unread_eq db n h.1
    have hp : ((pick (unread db n) ++ rest).map (·.id)).Pairwise (· < ·) := by
      rw [hr, hu]; exact h.1.sublist (List.filter_sublist.map _)
    have e := prefix_filter hp hl
    rw [hr] at e
    conv at e => lhs; rw [hu]
    rw [List.filter_filter] at e
    rw [← e, window, window, hm, ← filter_split h.1 _ _ (cursorOf db n)]
    · apply List.filter_congr; intro r _
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨t, a, b⟩ | ⟨b, t, a⟩)
        · exact ⟨t, a, by omega⟩
        · exact ⟨t, by omega, b⟩
      · rintro ⟨t, a, b⟩
        by_cases hb : (r.id : Int) ≤ cursorOf db n
        · exact .inl ⟨t, a, hb⟩
        · exact .inr ⟨b, t, by omega⟩
    · intro r hr; simp at hr; exact hr.2.2
    · intro r hr; simp at hr; exact hr.2.2

theorem take_inv {db : Db} {n : String} {pick : List Msg → List Msg} (hpick : ∀ rows, pick rows <+: rows)
    (h : MInv db) : MInv (take n pick db).1 := by
  obtain ⟨-, -, hm, hn⟩ := take_eq n pick db
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hm ▸ h1, hm ▸ hn ▸ h2, fun m => ?_, hn ▸ h4⟩
  rw [hn]
  by_cases e : m = n
  · subst e
    cases hl : (pick (unread db m)).getLast? with
    | none => rw [take_none hl]; exact h3 m
    | some l =>
      rw [take_cursor_self hl]
      obtain ⟨rest, hr⟩ := hpick (unread db m)
      have hlu : l ∈ unread db m := hr ▸ List.mem_append_left _ (List.mem_of_getLast? hl)
      have := h2 l (mem_unread.1 hlu).1; omega
  · rw [cursorOf_eq (take_cursor_other e)]; exact h3 m

/-! Any order of transactions. -/

/-- The db after `cs` from `db`. -/
def run (db : Db) (cs : List MCmd) : Db := (replay MCmd.step db cs).1

/-- Each transaction of `cs`, from `db`, with what it showed. -/
def trace (db : Db) (cs : List MCmd) : List (MCmd × List Msg) := (replay MCmd.step db cs).2

theorem deliverStep_eq (n : String) (b : Nat) (db : Db) :
    (deliverStep n b db).1 = (take n (fits b) db).1 ∧ (deliverStep n b db).2.1 = (take n (fits b) db).2.2 := ⟨rfl, rfl⟩

theorem inv_empty : MInv {} := ⟨by simp, by simp, fun n => by simp [cursorOf, Db.cursor], by decide⟩

theorem step_inv (c : MCmd) {db : Db} (h : MInv db) : MInv (c.step db).1 := by
  cases c with
  | post now f d b u k => exact grows_inv (grows_post ..) h
  | read n => exact take_inv (fun _ => List.prefix_refl _) h
  | deliver n b => exact (deliverStep_eq n b db).1 ▸ take_inv (fits_prefix b) h
  | other f hf => exact grows_inv (hf db h) h

theorem run_inv (db : Db) (cs : List MCmd) (h : MInv db) : MInv (run db cs) := by
  induction cs generalizing db with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_inv c h)

theorem grows_window {db db' : Db} (g : Grows db db') (h : MInv db) {n : String} (hn : (db.cursor n).isSome) (c0 : Int) :
    window db' n c0 (cursorOf db' n) = window db n c0 (cursorOf db n) ∧ cursorOf db' n = cursorOf db n := by
  have hc := cursorOf_eq (grows_cursor g hn)
  refine ⟨?_, hc⟩
  obtain ⟨-, ⟨new, hm, -, hb⟩, -⟩ := g
  rw [window, window, hm, List.filter_append, hc]
  have : new.filter (fun r => decide (ToIt n r ∧ c0 < r.id ∧ r.id ≤ cursorOf db n)) = [] :=
    List.filter_eq_nil_iff.2 fun r hr => by have := (hb r hr).1; have := h.2.2.1 n; simp; omega
  rw [this, List.append_nil]

theorem take_other {db : Db} {n m : String} {pick : List Msg → List Msg} (e : m ≠ n) (c0 : Int) :
    window (take m pick db).1 n c0 (cursorOf (take m pick db).1 n) = window db n c0 (cursorOf db n) ∧
    cursorOf (take m pick db).1 n = cursorOf db n := by
  have hc := cursorOf_eq (take_cursor_other (pick := pick) (db := db) (Ne.symm e))
  exact ⟨by rw [window, window, (take_eq m pick db).2.2.1, hc], hc⟩

theorem step_window (c : MCmd) {db : Db} {n : String} (h : MInv db) (hn : (db.cursor n).isSome) {c0 : Int}
    (hc0 : c0 ≤ cursorOf db n) :
    window db n c0 (cursorOf db n) ++ (if c.to = some n then (c.step db).2 else []) =
      window (c.step db).1 n c0 (cursorOf (c.step db).1 n) ∧
    cursorOf db n ≤ cursorOf (c.step db).1 n ∧ ((c.step db).1.cursor n).isSome := by
  cases c with
  | post now f d b u k =>
    have g := grows_post db now f d b u k
    obtain ⟨e1, e2⟩ := grows_window g h hn c0
    exact ⟨by simp [MCmd.to, MCmd.step, e1], by simp [MCmd.step, e2], by simp [MCmd.step, grows_cursor g hn, hn]⟩
  | other f hf =>
    have g := hf db h
    obtain ⟨e1, e2⟩ := grows_window g h hn c0
    exact ⟨by simp [MCmd.to, MCmd.step, e1], by simp [MCmd.step, e2], by simp [MCmd.step, grows_cursor g hn, hn]⟩
  | read m =>
    simp only [MCmd.to, MCmd.step, Option.some.injEq]
    by_cases e : m = n
    · subst e; simp only [ite_true]
      exact ⟨(take_window (fun _ => List.prefix_refl _) h hc0).1, (take_window (fun _ => List.prefix_refl _) h hc0).2,
        take_isSome hn⟩
    · obtain ⟨e1, e2⟩ := take_other (pick := id) (db := db) e c0
      simp only [e, ite_false, List.append_nil]; rw [e1, e2]; exact ⟨rfl, Int.le_refl _, take_isSome hn⟩
  | deliver m b =>
    simp only [MCmd.to, MCmd.step, Option.some.injEq, (deliverStep_eq m b db).1, (deliverStep_eq m b db).2]
    by_cases e : m = n
    · subst e; simp only [ite_true]
      exact ⟨(take_window (fits_prefix b) h hc0).1, (take_window (fits_prefix b) h hc0).2, take_isSome hn⟩
    · obtain ⟨e1, e2⟩ := take_other (pick := fits b) (db := db) e c0
      simp only [e, ite_false, List.append_nil]; rw [e1, e2]; exact ⟨rfl, Int.le_refl _, take_isSome hn⟩

theorem trace_cons (db : Db) (c : MCmd) (cs : List MCmd) :
    trace db (c :: cs) = (c, (c.step db).2) :: trace (c.step db).1 cs := rfl

theorem window_run (db : Db) (cs : List MCmd) {n : String} (h : MInv db) (hn : (db.cursor n).isSome) {c0 : Int}
    (hc0 : c0 ≤ cursorOf db n) :
    window db n c0 (cursorOf db n) ++ shownTo n (trace db cs) = window (run db cs) n c0 (cursorOf (run db cs) n) := by
  induction cs generalizing db with
  | nil => simp [shownTo, trace, run, replay]
  | cons c cs ih =>
    obtain ⟨e, hle, hs⟩ := step_window c h hn hc0
    rw [trace_cons, shownTo, List.flatMap_cons, ← shownTo, ← List.append_assoc]
    dsimp only
    rw [e]
    exact ih _ (step_inv c h) hs (Int.le_trans hc0 hle)

/-- S4. From a db that keeps the invariant, where agent `n` has its cursor (it joined), any transactions in any order
show `n`, over all their deliveries to it and in order, exactly the messages for it that its cursor moved past: each
once, in log order, and nothing else. -/
theorem exactly_once (db : Db) (cs : List MCmd) (n : String) (h : MInv db) (hn : (db.cursor n).isSome) :
    shownTo n (trace db cs) = window (run db cs) n (cursorOf db n) (cursorOf (run db cs) n) := by
  have := window_run db cs h hn (Int.le_refl _)
  have e : window db n (cursorOf db n) (cursorOf db n) = [] :=
    List.filter_eq_nil_iff.2 fun r _ => by simp
  rwa [e, List.nil_append] at this

theorem window_nodup {db : Db} (h : MInv db) (n : String) (a b : Int) : (window db n a b).Nodup := by
  have : db.msgs.Nodup := by
    have := h.1; rw [List.pairwise_map] at this
    exact this.imp fun e f => by rw [f] at e; omega
  exact this.filter _

/-- S4 under the store's assumption (`Atomic`): when processes ran transactions at once on a store that keeps the
invariant, where `n` has its cursor, what their deliveries showed `n` is, up to order, exactly the messages for `n` its
cursor moved past. -/
theorem exactly_once_atomic (before after : Db) (ran : List (MCmd × List Msg)) (n : String)
    (h : Atomic MCmd.step before after ran) (hi : MInv before) (hn : (before.cursor n).isSome) :
    (shownTo n ran).Perm (window after n (cursorOf before n) (cursorOf after n)) := by
  obtain ⟨order, hp, e⟩ := h
  have ht : trace before (order.map (·.1)) = order := congrArg Prod.snd e
  have hr : run before (order.map (·.1)) = after := congrArg Prod.fst e
  have := exactly_once before (order.map (·.1)) n hi hn
  rw [ht, hr] at this
  rw [← this]
  exact hp.symm.flatMap_right _

/-- The invariant holds after the transactions processes ran at once (`Atomic`). -/
theorem atomic_inv {before after : Db} {ran : List (MCmd × List Msg)} (h : Atomic MCmd.step before after ran)
    (hi : MInv before) : MInv after := by
  obtain ⟨order, -, e⟩ := h
  have hr : run before (order.map (·.1)) = after := congrArg Prod.fst e
  exact hr ▸ run_inv _ _ hi

/-- No message is shown twice: under `Atomic`, the deliveries to `n` show each message at most once. -/
theorem shown_once (before after : Db) (ran : List (MCmd × List Msg)) (n : String)
    (h : Atomic MCmd.step before after ran) (hi : MInv before) (hn : (before.cursor n).isSome) :
    (shownTo n ran).Nodup :=
  (exactly_once_atomic before after ran n h hi hn).nodup_iff.2 (window_nodup (atomic_inv h hi) n _ _)

/-- Only the addressee is shown a message: under `Atomic`, every message shown to `n` is for `n`, and in the log. -/
theorem shown_for_it (before after : Db) (ran : List (MCmd × List Msg)) (n : String)
    (h : Atomic MCmd.step before after ran) (hi : MInv before) (hn : (before.cursor n).isSome) {r : Msg}
    (hr : r ∈ shownTo n ran) : ToIt n r ∧ r ∈ after.msgs := by
  have := (exactly_once_atomic before after ran n h hi hn).mem_iff.1 hr
  simp only [window, List.mem_filter, decide_eq_true_eq] at this
  exact ⟨this.2.1, this.1⟩

/-- No cursor passes a message it didn't show: under `Atomic`, a message for `n` its cursor moved past was shown to
`n` by one of the deliveries. -/
theorem cursor_passes_only_shown (before after : Db) (ran : List (MCmd × List Msg)) (n : String)
    (h : Atomic MCmd.step before after ran) (hi : MInv before) (hn : (before.cursor n).isSome) {r : Msg}
    (hr : r ∈ after.msgs) (ht : ToIt n r) (h1 : cursorOf before n < r.id) (h2 : (r.id : Int) ≤ cursorOf after n) :
    r ∈ shownTo n ran :=
  (exactly_once_atomic before after ran n h hi hn).mem_iff.2 (by simp [window, hr, ht, h1, h2])

/-! Joining, posting and broadcast. -/

/-- A new agent's cursor starts after the messages there are, so `exactly_once` applies to it from then on; one already
there stays (agents.new_inbox). -/
theorem newInbox_cursor (db : Db) (n : String) :
    ((Agents.newInbox db n).cursor n).isSome ∧
    (db.cursor n = none → cursorOf (Agents.newInbox db n) n = (db.msgNext - 1 : Nat)) ∧
    ((db.cursor n).isSome → (Agents.newInbox db n).cursor n = db.cursor n) := by
  unfold Agents.newInbox
  split
  · rename_i ha
    obtain ⟨c, hc, hca⟩ := List.any_eq_true.1 ha
    have : (db.cursor n).isSome := by simp only [Db.cursor]; exact List.find?_isSome.2 ⟨c, hc, hca⟩
    exact ⟨this, fun e => by simp [e] at this, fun _ => rfl⟩
  · rename_i ha
    have e : db.cursor n = none := by
      simp only [Db.cursor]; rw [List.find?_eq_none]; intro c hc hca; exact ha (List.any_eq_true.2 ⟨c, hc, hca⟩)
    have e' : db.cursors.find? (·.agent == n) = none := e
    refine ⟨by simp [Db.cursor], fun _ => by simp [cursorOf, Db.cursor, List.find?_append, e'],
      fun hs => by simp [e] at hs⟩

/-- A post's message is for exactly the agents other than its sender that it names, or all of them for `@all`. -/
theorem posted_toIt (db : Db) now frm dest body urgent kind (n : String) :
    ToIt n (posted db now frm dest body urgent kind) ↔ n ≠ frm ∧ (dest = n ∨ dest = "@all") := by
  simp only [ToIt, posted, ne_eq, reduceCtorEq, not_false_eq_true, Option.some.injEq, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun e => h1 e.symm, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun e => h1 e.symm, h2⟩

/-- A post is unread by each agent it is for, right after it: the next delivery to that agent shows it (broadcast:
every agent but the sender, for `@all`). -/
theorem post_unread {db : Db} (h : MInv db) now frm dest body urgent kind {n : String} (hf : n ≠ frm)
    (hd : dest = n ∨ dest = "@all") :
    posted db now frm dest body urgent kind ∈ unread (Msgs.post db now frm dest body urgent kind).1 n := by
  obtain ⟨hm, hc, -, -⟩ := post_eq db now frm dest body urgent kind
  refine mem_unread.2 ⟨by rw [hm]; simp, (posted_toIt ..).2 ⟨hf, hd⟩, ?_⟩
  rw [cursorOf_eq (db' := (Msgs.post db now frm dest body urgent kind).1) (db := db) (by simp only [Db.cursor, hc])]
  exact h.2.2.1 n

/-- A post is urgent exactly when it was sent with `--urgent`. -/
theorem posted_urgent (db : Db) now frm dest body urgent kind :
    (posted db now frm dest body urgent kind).urgent.getD 0 ≠ 0 ↔ urgent = true := by
  cases urgent <;> simp [posted]

/-! The waiter's decision (msgs.wakes, Decide.wakesL). -/

/-- An urgent row. -/
def Urgent (r : Msg) : Prop := r.urgent.getD 0 ≠ 0

/-- A row the waiter wakes on: anything but a notice, and an urgent notice. -/
def Wakes (r : Msg) : Prop := r.kind ≠ some "notice" ∨ Urgent r

instance : DecidablePred Urgent := fun _ => inferInstanceAs (Decidable (_ ≠ _))
instance : DecidablePred Wakes := fun _ => inferInstanceAs (Decidable (_ ∨ _))

theorem wake_filter (rows : List Msg) :
    rows.filter (fun r => r.kind != some "notice" || r.urgent.getD 0 != 0) = rows.filter fun r => decide (Wakes r) := by
  apply List.filter_congr; intro r _; rw [Bool.eq_iff_iff, decide_eq_true_iff]; simp [Wakes, Urgent]

theorem wake_urgent (rows : List Msg) :
    ((rows.filter fun r => decide (Wakes r)).any fun r => r.urgent.getD 0 != 0) = decide (∃ r ∈ rows, Urgent r) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_filter, decide_eq_true_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨r, ⟨hr, -⟩, hu⟩; exact ⟨r, hr, hu⟩
  · rintro ⟨r, hr, hu⟩; exact ⟨r, ⟨hr, .inr hu⟩, hu⟩

/-- An urgent row always wakes the waiter, and `cold` is not asked (msgs.wakes calls `cold()` only for a non-urgent
wake). -/
theorem wakes_urgent {m : Type → Type} [Monad m] [LawfulMonad m] (rows : List Msg) (cold : m Bool)
    (hu : ∃ r ∈ rows, Urgent r) : wakes rows cold = pure (some (rows.filter fun r => decide (Wakes r), true)) := by
  have e := wake_urgent rows
  rw [decide_eq_true hu] at e
  have hne : (rows.filter fun r => decide (Wakes r)) ≠ [] := by
    obtain ⟨r, hr, hu⟩ := hu
    exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hr, by simp [Wakes, hu]⟩)
  unfold wakes; dsimp only; rw [wake_filter, ite_eq_right (by simpa using hne), ite_eq_left e]

/-- With no row it wakes on (only non-urgent notices, or none), the waiter sleeps, and `cold` is not asked. -/
theorem wakes_none {m : Type → Type} [Monad m] [LawfulMonad m] (rows : List Msg) (cold : m Bool)
    (hw : ∀ r ∈ rows, ¬ Wakes r) : wakes rows cold = pure none := by
  have : (rows.filter fun r => decide (Wakes r)) = [] := List.filter_eq_nil_iff.2 fun r hr => by simp [hw r hr]
  unfold wakes; dsimp only; rw [wake_filter, ite_eq_left (by simp [this])]

/-- The waiter wakes on `rows` exactly when one of them wakes it and one is urgent or the agent is not cold; it wakes
with those rows, in order, and says whether one is urgent. -/
theorem wakes_spec (rows : List Msg) (cold : Bool) :
    Id.run (wakes rows (pure cold)) =
      if (∃ r ∈ rows, Wakes r) ∧ ((∃ r ∈ rows, Urgent r) ∨ cold = false)
      then some (rows.filter fun r => decide (Wakes r), decide (∃ r ∈ rows, Urgent r)) else none := by
  by_cases hu : ∃ r ∈ rows, Urgent r
  · rw [wakes_urgent rows _ hu]
    obtain ⟨r, hr, hu'⟩ := hu
    rw [ite_eq_left ⟨⟨r, hr, .inr hu'⟩, .inl ⟨r, hr, hu'⟩⟩, decide_eq_true ⟨r, hr, hu'⟩]; rfl
  · by_cases hw : ∃ r ∈ rows, Wakes r
    · have hne : (rows.filter fun r => decide (Wakes r)) ≠ [] := by
        obtain ⟨r, hr, hw⟩ := hw; exact List.ne_nil_of_mem (List.mem_filter.2 ⟨hr, by simp [hw]⟩)
      have e := wake_urgent rows
      rw [decide_eq_false hu] at e
      unfold wakes; dsimp only
      rw [wake_filter, ite_eq_right (by simpa using hne), ite_eq_right (by rw [e]; simp), decide_eq_false hu]
      cases cold <;> simp [hu, hw] <;> rfl
    · rw [wakes_none rows _ (fun r hr h => hw ⟨r, hr, h⟩), ite_eq_right (fun h => hw h.1)]; rfl

/-- The waiter's decision on its unread messages (Decide.wakes_lifted): `swarm wait` wakes agent `n` exactly when a
message for `n` past its cursor wakes it, and one such is urgent or `n` is not cold. -/
theorem waiter_wakes (db : Db) (n : String) (cold : Bool) :
    (Id.run (wakes (unread db n) (pure cold))).isSome ↔
      (∃ r ∈ db.msgs, ToIt n r ∧ cursorOf db n < r.id ∧ Wakes r) ∧
      ((∃ r ∈ db.msgs, ToIt n r ∧ cursorOf db n < r.id ∧ Urgent r) ∨ cold = false) := by
  rw [wakes_spec]
  have e : ∀ P : Msg → Prop, (∃ r ∈ unread db n, P r) ↔ ∃ r ∈ db.msgs, ToIt n r ∧ cursorOf db n < r.id ∧ P r :=
    fun P => ⟨fun ⟨r, hr, hp⟩ => let h := mem_unread.1 hr; ⟨r, h.1, h.2.1, h.2.2, hp⟩,
              fun ⟨r, h1, h2, h3, hp⟩ => ⟨r, mem_unread.2 ⟨h1, h2, h3⟩, hp⟩⟩
  split
  · rename_i h; simp only [Option.isSome_some, true_iff]; rw [← e, ← e]; exact h
  · rename_i h; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; rw [← e, ← e]; exact h

/-! The stop (board #53): the user's release of another's task stops it until its ex-owner reads the stop. -/

theorem take_shown_le {db : Db} {n : String} {pick : List Msg → List Msg} (hpick : ∀ rows, pick rows <+: rows)
    (h : MInv db) {r : Msg} (hr : r ∈ (take n pick db).2.2) : (r.id : Int) ≤ cursorOf (take n pick db).1 n := by
  rw [(take_eq n pick db).2.1] at hr
  cases hl : (pick (unread db n)).getLast? with
  | none => rw [List.getLast?_eq_none_iff.1 hl] at hr; cases hr
  | some l =>
    rw [take_cursor_self hl]
    have hp : ((pick (unread db n)).map (·.id)).Pairwise (· < ·) := by
      refine List.Pairwise.sublist ((hpick _).sublist.map _) ?_
      rw [unread_eq db n h.1]; exact h.1.sublist (List.filter_sublist.map _)
    have := last_max hp hl hr; omega

/-- A task's stop is pending only while its ex-owner's cursor is short of the stop message (tasks.stop_pending). -/
theorem stopPending_read (db : Db) (t : Task) (o : String) (ho : py t.stop_to = some o)
    (hc : t.stop_msg.getD 0 ≤ cursorOf db o) : Tasks.stopPending db t = false := by
  unfold Tasks.stopPending
  rw [ho]; dsimp only
  split
  · rfl
  · split
    · rfl
    · simp only [cursorOf] at hc; simp; omega

/-- A delivery to the ex-owner that shows it the stop lifts the stop (Release.deliver_released: the belief the stop
drops is the ex-owner's claim, which the task no longer holds; what the code keeps of it is `stopPending`). -/
theorem delivery_lifts_stop {db : Db} (h : MInv db) {o : String} {pick : List Msg → List Msg}
    (hpick : ∀ rows, pick rows <+: rows) {t : Task} (ho : py t.stop_to = some o) {r : Msg}
    (hr : r ∈ (take o pick db).2.2) (hs : t.stop_msg = some r.id) : Tasks.stopPending (take o pick db).1 t = false :=
  stopPending_read _ t o ho (by rw [hs]; exact take_shown_le hpick h hr)

theorem find_set_self {db : Db} {i : Int} {t : Task} {g : Task → Task} (hg : ∀ u, (g u).id = u.id)
    (h : db.find i = some t) : (db.set i g).find i = some (g t) := by
  rw [find_set _ _ _ _ hg, h]; simp [find_id h]

theorem fromA_ne {o : Option String} {me f : String} {b : Bool}
    (h : (if (o != some me && b) = true then py o else none) = some f) : o = some f ∧ f ≠ me := by
  by_cases hc : (o != some me && b) = true
  · rw [ite_eq_left hc] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    cases o with
    | none => cases h
    | some o =>
      simp [py] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨rfl, fun e => hc.1 (by rw [e])⟩
  · rw [ite_eq_right hc] at h; cases h

/-- The user's or the communicator's release of a task another holds (Release.releaseOther_unread): it posts the
ex-owner an urgent stop that the ex-owner has unread, and records that stop on the task. -/
theorem release_stop (c : Tasks.Ctx) (i : Int) (af : Option (List Int)) (db : Db) (h : MInv db) (f : String)
    (hr : (Tasks.release c i af db).2 = .ok (some f)) :
    ∃ r ∈ unread (Tasks.release c i af db).1 f, r.urgent = some 1 ∧
      ∃ t, (Tasks.release c i af db).1.find i = some t ∧ t.stop_to = some f ∧ t.stop_msg = some r.id := by
  unfold Tasks.release at hr ⊢
  split at hr
  · cases hr
  · rename_i r hfind
    dsimp only at hr ⊢
    split at hr
    · cases hr
    · rename_i db1 h1
      split at hr
      · cases hr
      · rename_i db2 h2
        generalize hA : (if (r.owner != some c.me && Agents.inCharge db c.comms c.me) = true then py r.owner else none) = A
          at h1 hr ⊢
        cases A with
        | none => cases hr
        | some f' =>
          cases hr
          dsimp only at h1 ⊢
          -- f ≠ me
          have hne := (fromA_ne hA).2
          -- db1, db2 keep messages, cursors, ids; task i is there
          have e1 : db1.msgs = db.msgs ∧ db1.cursors = db.cursors ∧ db1.msgNext = db.msgNext ∧ ∃ t, db1.find i = some t := by
            split at h1
            · cases h1; exact ⟨rfl, rfl, rfl, _, find_set_self (fun _ => rfl) hfind⟩
            · cases h1
          obtain ⟨m1, c1, n1, t1, ht1⟩ := e1
          have e2 : db2.msgs = db.msgs ∧ db2.cursors = db.cursors ∧ db2.msgNext = db.msgNext ∧ ∃ t, db2.find i = some t := by
            split at h2
            · rename_i l
              cases hs : Tasks.setDeps db1 i l with
              | error e => rw [hs] at h2; cases h2
              | ok p =>
                rw [hs] at h2; cases h2
                unfold Tasks.setDeps at hs; split at hs
                · cases hs
                · cases hs; exact ⟨m1, c1, n1, _, find_set_self (fun _ => rfl) ht1⟩
            · cases h2; exact ⟨m1, c1, n1, t1, ht1⟩
          obtain ⟨m2, c2, n2, t2, ht2⟩ := e2
          refine ⟨posted (db2.log c.now (some c.me) "release" none _) c.now c.me f
            (toString (if (c.me == Agents.HUMAN) = true then "the user" else c.me) ++ toString " released #" ++
              toString (d i) ++ toString ": stop work on it") true none, ?_, rfl, _,
            find_set_self (fun _ => rfl) (by rw [find_congr (by rfl)]; exact ht2), rfl, rfl⟩
          refine mem_unread.2 ⟨by simp [Db.set, post_eq], (posted_toIt ..).2 ⟨hne, .inl rfl⟩, ?_⟩
          have := h.2.2.1 f
          rw [cursorOf_eq (db := db) (by simp [Db.cursor, Db.set, post_eq, c2])]
          simp [posted, n2]; omega

/-! Nudge (board #50). -/

/-- N1', the db half (Nudge.N1'_frame): `swarm nudge` writes only its event; the log is the only table it changes. -/
theorem nudge_frame (db : Db) (now : Int) (me ag : String) :
    { db.log now (some me) "nudge" (some ag) none with events := db.events, eventNext := db.eventNext } = db := rfl


end SwarmLean.Inbox
