import SwarmLean.Proofs
import SwarmLean.Db.Locks

/-! Locks (board #105): what swarm/model proves of locks.lua's patterns (`Glob.lean`) and of S3, about the code that
runs: `Locks.covers`, `Locks.overlaps` (Glob.lean's own functions on a string's bytes), and the steps `Locks.lock` and
`Locks.unlock` in any order with the task commands of `Proofs.lean`. -/

namespace SwarmLean.Locks
open Swarm

theorem bytes_ok (s : String) : Glob.Bytes (bytes s) := by
  intro c hc
  simp only [bytes, List.mem_map] at hc
  obtain ⟨b, -, rfl⟩ := hc
  exact Glob.byte_ofNat b.toNat_lt

/-- covers is its forms: the pattern as a literal path, its glob, and (no `*`, `?`, `[` in it) everything under it. -/
theorem covers_iff (path pat : String) :
    covers path pat = true ↔ ∃ f ∈ Glob.forms true (bytes pat), Glob.gm f (bytes path) = true :=
  Glob.covers_iff (bytes_ok path)

/-- overlaps is exactly "some file both cover", a file name being bytes. -/
theorem overlaps_iff (p q : String) :
    overlaps p q = true ↔ ∃ w, Glob.Bytes w ∧ Glob.covers true w (bytes p) = true ∧ Glob.covers true w (bytes q) = true :=
  Glob.overlaps_iff (bytes_ok p) (bytes_ok q)

/-- A path both patterns cover makes them overlap. -/
theorem overlaps_of_covers {x p q : String} (h1 : covers x p = true) (h2 : covers x q = true) : overlaps p q = true :=
  Glob.overlaps_complete (bytes_ok x) h1 h2

theorem overlaps_comm (p q : String) : overlaps p q = overlaps q p := Glob.overlaps_comm _ _

-- Findings #6 and #25 of swarm/model, on the code that runs.
example : overlaps "m/*.lua" "m/a*" = true := by decide +kernel
example : covers "m/?/x" "m/?" = false := by decide +kernel
example : overlaps "[!]a]" "b" = true := by decide +kernel
example : overlaps "?" "[z-a]" = false := by decide +kernel


/-! S3: no two locks of different agents that hold at a time overlap. -/

open Agents

/-- Agent `a` has a row that hasn't ended (the agent join of `others`). -/
def Live (db : Db) (a : String) : Bool := db.agents.any fun g => g.name == a && g.ended.isNone

/-- Lock `l` holds at time `t`: its agent is live and its lease runs past `t` (the locks `others` reads at `t`). -/
def HeldAt (db : Db) (t : Int) (l : Lock) : Prop :=
  ∃ a, l.agent = some a ∧ l.lease_until.any (· > t) = true ∧ Live db a = true

/-- S3 at time `t`: two locks of different agents that both hold at `t` don't overlap. -/
def Disjoint (db : Db) (t : Int) : Prop :=
  ∀ l ∈ db.locks, ∀ m ∈ db.locks, HeldAt db t l → HeldAt db t m → l.agent ≠ m.agent → overlaps l.path m.path = false

/-- Every lock's agent is live, or is the user (whom `touch` gives no row and `join` refuses). -/
def Rows (db : Db) : Prop := ∀ l ∈ db.locks, ∀ a, l.agent = some a → a = HUMAN ∨ Live db a = true

/-- The invariant at time `t`. -/
def Good (db : Db) (t : Int) : Prop := Rows db ∧ Disjoint db t

/-- From `db` to `db'` no agent stops being live, and the user doesn't start. -/
def Grows (db db' : Db) : Prop :=
  (∀ a, Live db a = true → Live db' a = true) ∧ (∀ a, Live db' a = true → Live db a = true ∨ a ≠ HUMAN)

theorem grows_refl {db db' : Db} (h : db'.agents = db.agents) : Grows db db' :=
  ⟨fun _ h' => by simpa [Live, h] using h', fun _ h' => .inl (by simpa [Live, h] using h')⟩

/-- A step that keeps the lock table and lets only agents other than the user become live keeps the invariant: an agent
that becomes live had no lock. -/
theorem good_grow {db db' : Db} {t : Int} (hl : db'.locks = db.locks) (hg : Grows db db') (h : Good db t) :
    Good db' t := by
  obtain ⟨hr, hd⟩ := h
  have hb : ∀ l ∈ db.locks, HeldAt db' t l → HeldAt db t l := fun l hl ⟨a, h1, h2, h3⟩ => by
    refine ⟨a, h1, h2, ?_⟩
    rcases hg.2 a h3 with h | h
    · exact h
    · exact (hr l hl a h1).resolve_left h
  refine ⟨fun l hl' a e => ?_, fun l hl1 m hm1 h1 h2 hne => ?_⟩
  · rw [hl] at hl'
    exact (hr l hl' a e).imp id (hg.1 a)
  · rw [hl] at hl1 hm1
    exact hd l hl1 m hm1 (hb l hl1 h1) (hb m hm1 h2) hne

/-- A step that drops locks, ends agents but starts none, and keeps the agents of the locks it keeps live keeps the
invariant. -/
theorem good_sub {db db' : Db} {t : Int} (hl : ∀ l ∈ db'.locks, l ∈ db.locks)
    (hdown : ∀ a, Live db' a = true → Live db a = true)
    (hup : ∀ l ∈ db'.locks, ∀ a, l.agent = some a → Live db a = true → Live db' a = true) (h : Good db t) : Good db' t := by
  have hh : ∀ l, HeldAt db' t l → HeldAt db t l := fun l ⟨a, h1, h2, h3⟩ => ⟨a, h1, h2, hdown a h3⟩
  exact ⟨fun l hl' a e => (h.1 l (hl l hl') a e).imp id (hup l hl' a e),
    fun l hl1 m hm1 h1 h2 hne => h.2 l (hl l hl1) m (hl m hm1) (hh l h1) (hh m h2) hne⟩

theorem live_setAgent {db : Db} {n a : String} {f : Agent → Agent} (hn : ∀ g, (f g).name = g.name) (hne : a ≠ n) :
    Live (db.setAgent n f) a = Live db a := by
  simp only [Live, Db.setAgent]
  generalize db.agents = l
  induction l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    by_cases e : g.name = n
    · have : (n == a) = false := by simp [Ne.symm hne]
      simp [e, hn, this]
    · simp [e]

theorem live_setAgent_le {db : Db} {n a : String} {f : Agent → Agent} (hn : ∀ g, (f g).name = g.name)
    (he : ∀ g, (f g).ended.isNone = true → g.ended.isNone = true) (h : Live (db.setAgent n f) a = true) :
    Live db a = true := by
  simp only [Live, Db.setAgent, List.any_map, List.any_eq_true, Function.comp_apply, Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨g, hg, h1, h2⟩ := h
  refine ⟨g, hg, ?_⟩
  by_cases e : g.name = n
  · simp only [e, ↓reduceIte, hn] at h1 h2; exact ⟨e ▸ h1, he g h2⟩
  · simp only [e, ↓reduceIte] at h1 h2; exact ⟨h1, h2⟩

theorem live_setAgent_self {db : Db} {n : String} {f : Agent → Agent} (hn : ∀ g, (f g).name = g.name)
    (he : ∀ g, (f g).ended = none) (h : db.agents.any (·.name == n) = true) : Live (db.setAgent n f) n = true := by
  simp only [Live, Db.setAgent, List.any_map, List.any_eq_true, Function.comp_apply, Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨g, hg, h1⟩ := h
  exact ⟨g, hg, by simp [h1, hn, he]⟩

theorem touch_locks (db : Db) n cwd here now : (touch db n cwd here now).locks = db.locks := by
  unfold touch newInbox; split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem touch_live {db : Db} {a : String} n cwd here now (h : Live (touch db n cwd here now) a = true) :
    Live db a = true ∨ (a = n ∧ a ≠ HUMAN) := by
  revert h; unfold touch newInbox; split
  · exact .inl
  · rename_i h0
    split
    · exact .inl
    · have hn : n ≠ HUMAN := fun e => h0 (by simp [e])
      intro h
      have h' : Live db a = true ∨ n = a := by
        split at h <;> simpa [Live, List.any_append, or_comm (b := _ = a), and_comm] using h
      rcases h' with h' | rfl
      · exact .inl h'
      · exact .inr ⟨rfl, hn⟩

theorem touch_grows (db : Db) n cwd here now : Grows db (touch db n cwd here now) := by
  refine ⟨fun a h => ?_, fun a h => (touch_live n cwd here now h).imp id (·.2)⟩
  unfold touch newInbox; split
  · exact h
  · split
    · exact h
    · simp only [Live] at h ⊢
      split <;> simp [List.any_append, h]

theorem fence_row {db : Db} {n : String} {here : Option String} {f : Fence} (h : fence db n here = some f) :
    db.agents.any (·.name == n) = true := by
  unfold fence at h
  split at h
  · cases h
  · rename_i r hr
    simp only [Db.agent] at hr
    exact List.any_eq_true.2 ⟨r, List.mem_of_find?_eq_some hr, by simpa using List.find?_some hr⟩

/-- A row that the fence doesn't call ended is live. -/
theorem fence_live {db : Db} {n : String} {here : Option String} (hf : ∀ t w, fence db n here ≠ some (.ended t w))
    (h : db.agents.any (·.name == n) = true) : Live db n = true := by
  cases e : db.agents.find? (·.name == n) with
  | none =>
    obtain ⟨g, hg, hn⟩ := List.any_eq_true.1 h
    exact absurd hn (List.find?_eq_none.1 e g hg)
  | some r =>
    have hn : r.name = n := by simpa using List.find?_some e
    cases hre : r.ended with
    | none => exact List.any_eq_true.2 ⟨r, List.mem_of_find?_eq_some e, by simp [hn, hre]⟩
    | some t0 =>
      exfalso
      unfold fence at hf
      simp only [Db.agent, e, hre, Option.isSome_some, ↓reduceIte] at hf
      exact hf _ _ rfl

/-- `touch` of a name not the user's and not ended leaves it live. -/
theorem touch_self (db : Db) n cwd here now (hn : n ≠ HUMAN) (hf : ∀ t w, fence db n here ≠ some (.ended t w)) :
    Live (touch db n cwd here now) n = true := by
  unfold touch newInbox; split
  · rename_i h
    simp only [Bool.or_eq_true, beq_iff_eq, hn, false_or, Option.isSome_iff_exists] at h
    obtain ⟨f, hf'⟩ := h
    exact fence_live hf (fence_row hf')
  · split
    · rename_i h; exact fence_live hf h
    · simp only [Live]; split <;> simp

theorem any_gt {o : Option Int} {s t : Int} (h : o.any (· > t) = true) (hs : s ≤ t) : o.any (· > s) = true := by
  cases o <;> simp_all; omega

theorem mem_others {db : Db} {me : String} {now t : Int} {m : Lock} (hm : m ∈ db.locks) (h : HeldAt db t m)
    (hne : m.agent ≠ some me) (ht : now ≤ t) : m ∈ others db me now := by
  obtain ⟨b, hb, hl, hv⟩ := h
  simp only [others, List.mem_filter]
  refine ⟨hm, ?_⟩
  rw [hb]
  have : b ≠ me := fun e => hne (by rw [hb, e])
  simpa [this, any_gt hl ht, Live] using hv

theorem of_others {db : Db} {me : String} {now : Int} {m : Lock} (h : m ∈ others db me now) :
    m ∈ db.locks ∧ HeldAt db now m ∧ m.agent ≠ some me := by
  simp only [others, List.mem_filter] at h
  obtain ⟨hm, h⟩ := h
  refine ⟨hm, ?_⟩
  revert h; cases e : m.agent with
  | none => simp
  | some b =>
    intro h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact ⟨⟨b, e, h.1.2, h.2⟩, fun e' => h.1.1 (Option.some.inj e')⟩

@[simp] theorem log_locks (db : Db) ts a k p x : (db.log ts a k p x).locks = db.locks := rfl
@[simp] theorem log_agents (db : Db) ts a k p x : (db.log ts a k p x).agents = db.agents := rfl

/-- `swarm lock`, as of a clock no later than `t`, keeps S3 at `t`: it is refused, or every lock of another agent that
holds at `t` held at its clock and doesn't overlap it. -/
theorem lock_good (c : Tasks.Ctx) (path reason lease : String) {db : Db} {t : Int} (ht : c.now ≤ t) (h : Good db t) :
    Good (lock c path reason lease db).1 t := by
  unfold lock
  split
  · exact h
  · rename_i hfe
    dsimp only
    cases hf : (others (touch db c.me none c.here c.now) c.me c.now).find? fun o => overlaps path o.path with
    | some o => exact h
    | none =>
      cases hl : dur lease with
      | none => exact h
      | some l =>
        simp only [Good]
        have hD := good_grow (touch_locks db c.me none c.here c.now) (touch_grows ..) h
        have hs := fun hn => touch_self db c.me none c.here c.now hn fun t w e => hfe t w e
        generalize touch db c.me none c.here c.now = D at hD hf hs ⊢
        obtain ⟨hr, hd⟩ := hD
        have key : ∀ m ∈ D.locks, HeldAt D t m → m.agent ≠ some c.me → overlaps path m.path = false := by
          intro m hm hh hne
          have := List.find?_eq_none.1 hf m (mem_others hm hh hne ht)
          simpa using this
        refine ⟨fun l hl a e => ?_, fun l hl m hm h1 h2 hne => ?_⟩
        · simp only [log_locks, List.mem_append, List.mem_filter, List.mem_singleton] at hl
          rcases hl with ⟨hl, -⟩ | rfl
          · exact hr l hl a e
          · cases e
            by_cases hh : c.me = HUMAN
            · exact .inl hh
            · exact .inr (hs hh)
        · simp only [log_locks, List.mem_append, List.mem_filter, List.mem_singleton] at hl hm
          rcases hl with ⟨hl, -⟩ | rfl <;> rcases hm with ⟨hm, -⟩ | rfl
          · exact hd l hl m hm h1 h2 hne
          · rw [overlaps_comm]; exact key l hl h1 hne
          · exact key m hm h2 (Ne.symm hne)
          · exact absurd rfl hne

/-- `swarm unlock` keeps S3. -/
theorem unlock_good (me path : String) (now : Int) {db : Db} {t : Int} (h : Good db t) : Good (unlock me path now db) t :=
  good_sub (fun _ hl => (List.mem_filter.1 hl).1) (fun _ h => h) (fun _ _ _ _ h => h) h

/-- `swarm leave` (and every end that releases: `Agents.release`) keeps S3. -/
theorem leave_good (name : String) (now : Int) {db : Db} {t : Int} (h : Good db t) : Good (leave db name now) t := by
  have hL : ∀ a, Live (leave db name now) a = Live ((db.setAgent name fun x =>
      { x with ended := some now, status := some "ended" }).setAgent name fun x => { x with stay := none }) a :=
    fun _ => rfl
  refine good_sub (db := db) (db' := leave db name now) (fun l hl => (List.mem_filter.1 hl).1) (fun a h => ?_)
    (fun l hl a e hv => ?_) h
  · rw [hL] at h
    have h1 := live_setAgent_le (f := fun x => { x with stay := none }) (fun _ => rfl) (fun _ e => e) h
    exact live_setAgent_le (f := fun x => { x with ended := some now, status := some "ended" }) (fun _ => rfl)
      (fun _ e => by simp at e) h1
  · have hne : a ≠ name := by
      have := (List.mem_filter.1 hl).2; rw [e] at this; simpa using this
    rw [hL, live_setAgent (f := fun x => { x with stay := none }) (fun _ => rfl) hne,
      live_setAgent (f := fun x => { x with ended := some now, status := some "ended" }) (fun _ => rfl) hne]
    exact hv

theorem grows_trans {x y z : Db} (h1 : Grows x y) (h2 : Grows y z) : Grows x z :=
  ⟨fun a h => h2.1 a (h1.1 a h), fun a h => (h2.2 a h).elim (h1.2 a) .inr⟩

theorem grows_of_agents {db x y : Db} (h : x.agents = y.agents) (g : Grows db y) : Grows db x := by
  have e : ∀ a, Live x a = Live y a := fun a => by simp [Live, h]
  exact ⟨fun a h' => (e a).symm ▸ g.1 a h', fun a h' => g.2 a ((e a) ▸ h')⟩

/-- Bringing back a row of a name not the user's lets only that name become live. -/
theorem grows_setAgent {D : Db} {n : String} {G : Agent → Agent} (hn : ∀ g, (G g).name = g.name)
    (he : ∀ g, (G g).ended = none) (hrow : D.agents.any (·.name == n) = true) (hN : n ≠ HUMAN) :
    Grows D (D.setAgent n G) := by
  refine ⟨fun a h => ?_, fun a h => ?_⟩
  · by_cases e : a = n
    · subst e; exact live_setAgent_self hn he hrow
    · rw [live_setAgent hn e]; exact h
  · by_cases e : a = n
    · exact .inr (e ▸ hN)
    · rw [live_setAgent hn e] at h; exact .inl h

/-- `swarm join` (`bind`, after `notHuman`) keeps S3: the agent it brings back held no lock. -/
theorem bind_good (name : String) (cwd hc model : Option String) (r : Binding) (now : Int) (hn : name ≠ HUMAN)
    {db : Db} {t : Int} (h : Good db t) : Good (Agents.bind db name cwd hc model r now).1 t := by
  unfold Agents.bind
  split
  · exact h
  · dsimp only
    generalize hD1 : (if db.agents.any (·.name == name) then db else _) = D1
    have g1 : D1.locks = db.locks ∧ Grows db D1 ∧ D1.agents.any (·.name == name) = true := by
      subst hD1; split
      · exact ⟨rfl, grows_refl rfl, by assumption⟩
      · refine ⟨rfl, ⟨fun a h' => by simp only [Live] at h' ⊢; simp [List.any_append, h'], fun a h' => ?_⟩, by simp⟩
        by_cases e : a = name
        · exact .inr (e ▸ hn)
        · left; simpa [Live, List.any_append, Ne.symm e] using h'
    have g2 : (if r.isNone then newInbox D1 name else D1).locks = D1.locks ∧
        (if r.isNone then newInbox D1 name else D1).agents = D1.agents := by
      unfold newInbox; split
      · split <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    generalize (if r.isNone then newInbox D1 name else D1) = D2 at g2
    have g12 : Grows db D2 := grows_of_agents g2.2 g1.2.1
    have hrow : D2.agents.any (·.name == name) = true := by rw [g2.2]; exact g1.2.2
    split
    all_goals (try split)
    all_goals
      refine good_grow ?_ (grows_of_agents rfl (grows_trans g12 (grows_setAgent ?_ ?_ hrow hn))) h
      · exact g2.1.trans g1.1
      · intro g; rfl
      · intro g; rfl

/-! What `swarm lock` grants, and what the edit hook's `lockHolder` names. -/

theorem touch_held {db : Db} {n cwd here now} {t : Int} {m : Lock} (hne : m.agent ≠ some n)
    (h : HeldAt (touch db n cwd here now) t m) : HeldAt db t m := by
  obtain ⟨b, hb, hl, hv⟩ := h
  refine ⟨b, hb, hl, ?_⟩
  rcases touch_live n cwd here now hv with h | ⟨rfl, -⟩
  · exact h
  · exact absurd hb hne

/-- `swarm lock` is granted exactly when the agent hasn't ended, the lease parses, and no lock of another agent that
holds at its clock (agent live, lease not expired) overlaps the path: an expired lock or a dead agent's never refuses. -/
theorem lock_ok_iff (c : Tasks.Ctx) (path reason lease : String) (db : Db) :
    (lock c path reason lease db).2 = .ok () ↔
      (∀ t w, fence db c.me c.here ≠ some (.ended t w)) ∧ (dur lease).isSome ∧
      ∀ m ∈ db.locks, HeldAt db c.now m → m.agent ≠ some c.me → overlaps path m.path = false := by
  unfold lock
  split
  · rename_i hfe
    exact ⟨nofun, fun ⟨h, _⟩ => (h _ _ hfe).elim⟩
  · rename_i hfe
    dsimp only
    cases hf : (others (touch db c.me none c.here c.now) c.me c.now).find? fun o => overlaps path o.path with
    | some o =>
      refine ⟨nofun, fun ⟨_, _, h⟩ => ?_⟩
      obtain ⟨hm, hh, hne⟩ := of_others (List.mem_of_find?_eq_some hf)
      rw [touch_locks] at hm
      have := h o hm (touch_held hne hh) hne
      have h2 := List.find?_some hf
      simp only [this] at h2; cases h2
    | none =>
      cases hl : dur lease with
      | none => exact ⟨nofun, fun ⟨_, h, _⟩ => by cases h⟩
      | some l =>
        refine ⟨fun _ => ⟨fun t w e => hfe t w e, rfl, fun m hm hh hne => ?_⟩, fun _ => rfl⟩
        have hm' : m ∈ (touch db c.me none c.here c.now).locks := by rw [touch_locks]; exact hm
        have hh' : HeldAt (touch db c.me none c.here c.now) c.now m :=
          let ⟨b, h1, h2, h3⟩ := hh; ⟨b, h1, h2, (touch_grows ..).1 b h3⟩
        simpa using List.find?_eq_none.1 hf m (mem_others hm' hh' hne (Int.le_refl _))

/-- A lock `lockHolder` names (the edit hook refuses the edit to it) is another agent's, holds now and covers the path. -/
theorem lockHolder_some {db : Db} {me path : String} {now : Int} {l : Lock} (h : lockHolder db me path now = some l) :
    l ∈ db.locks ∧ HeldAt db now l ∧ l.agent ≠ some me ∧ covers path l.path = true :=
  let ⟨h1, h2, h3⟩ := of_others (List.mem_of_find?_eq_some h)
  ⟨h1, h2, h3, by simpa using List.find?_some h⟩

/-- When `lockHolder` names none (the edit hook allows the edit), no lock of another agent that holds now covers the
path. -/
theorem lockHolder_none {db : Db} {me path : String} {now : Int} (h : lockHolder db me path now = none) :
    ∀ l ∈ db.locks, HeldAt db now l → l.agent ≠ some me → covers path l.path = false := fun l hl hh hne => by
  simpa using List.find?_eq_none.1 h l (mem_others hl hh hne (Int.le_refl _))

/-- Under S3 every lock that holds now and covers the path is of the agent `lockHolder` names: which row it picks
(PORT.md: row order) never changes whom the hook names. -/
theorem lockHolder_agent {db : Db} {me path : String} {now : Int} {l m : Lock} (hd : Disjoint db now)
    (h : lockHolder db me path now = some l) (hm : m ∈ db.locks) (hh : HeldAt db now m)
    (hc : covers path m.path = true) : m.agent = l.agent := by
  obtain ⟨hl, hlh, -, hlc⟩ := lockHolder_some h
  apply Classical.byContradiction; intro e
  have := hd m hm l hl hh hlh e
  rw [overlaps_of_covers hc hlc] at this; cases this

/-! The task commands of `Proofs.lean` leave the lock table, and touch the agents at most. -/

theorem setDeps_frame {db db' : Db} {i : Int} {ds' : List Int} {ds : List String} (h : Tasks.setDeps db i ds' = .ok (db', ds)) :
    db'.locks = db.locks ∧ db'.agents = db.agents := by
  unfold Tasks.setDeps at h; split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

theorem step_frame (c : Cmd) (db : Db) : (c.step db).1.locks = db.locks ∧ Grows db (c.step db).1 := by
  cases c with
  | add c a =>
    show (Tasks.add c a db).1.locks = db.locks ∧ Grows db (Tasks.add c a db).1
    unfold Tasks.add
    repeat' split
    all_goals exact ⟨rfl, grows_refl rfl⟩
  | claim c i l =>
    show (Tasks.claim c i l db).1.locks = db.locks ∧ Grows db (Tasks.claim c i l db).1
    unfold Tasks.claim
    dsimp only
    have hD : (touch db c.me none c.here c.now).locks = db.locks ∧ Grows db (touch db c.me none c.here c.now) :=
      ⟨touch_locks db c.me none c.here c.now, touch_grows ..⟩
    generalize touch db c.me none c.here c.now = D at hD ⊢
    repeat' split
    all_goals first | exact ⟨rfl, grows_refl rfl⟩ | exact hD
  | release c i af =>
    show (Tasks.release c i af db).1.locks = db.locks ∧ Grows db (Tasks.release c i af db).1
    unfold Tasks.release
    split
    · exact ⟨rfl, grows_refl rfl⟩
    · dsimp only
      split
      · exact ⟨rfl, grows_refl rfl⟩
      · rename_i db1 h1
        have e1 : db1.locks = db.locks ∧ db1.agents = db.agents := by
          split at h1 <;> (split at h1 <;> first | (cases h1; exact ⟨rfl, rfl⟩) | cases h1)
        split
        · exact ⟨rfl, grows_refl rfl⟩
        · rename_i db2 h2
          have e2 : db2.locks = db1.locks ∧ db2.agents = db1.agents := by
            split at h2
            · cases h' : Tasks.setDeps db1 i _ with
              | error e => rw [h'] at h2; cases h2
              | ok p => rw [h'] at h2; cases h2; exact setDeps_frame h'
            · cases h2; exact ⟨rfl, rfl⟩
          split
          · exact ⟨e2.1.trans e1.1, grows_refl (e2.2.trans e1.2)⟩
          · exact ⟨e2.1.trans e1.1, grows_refl (e2.2.trans e1.2)⟩
  | board => exact ⟨rfl, grows_refl rfl⟩

/-! Any order of transactions. -/

/-- A command the lock theorems cover: `swarm lock`, `unlock`, `leave`, `join`'s transaction (`r`, the row as it read
it before), or a task command of `Proofs.lean`. -/
inductive LCmd
  | lock (c : Tasks.Ctx) (path reason lease : String)
  | unlock (me path : String) (now : Int)
  | leave (name : String) (now : Int)
  | join (name : String) (cwd hc model : Option String) (r : Binding) (now : Int)
  | task (c : Cmd)

/-- What a lock command answers. -/
inductive LResult
  | locked (r : Except String Unit)
  | unlocked
  | left
  | joined (r : Except String Unit)
  | task (r : Result)

/-- A command's whole effect on the db, and its answer: the CLI's own step functions. -/
def LCmd.step : LCmd → Db → Db × LResult
  | .lock c p r l, db => ((Locks.lock c p r l db).1, .locked (Locks.lock c p r l db).2)
  | .unlock me p now, db => (Locks.unlock me p now db, .unlocked)
  | .leave n now, db => (Agents.leave db n now, .left)
  | .join n cwd hc model r now, db => match notHuman n with
    | .error e => (db, .joined (.error e))
    | .ok () => ((Agents.bind db n cwd hc model r now).1, .joined (Agents.bind db n cwd hc model r now).2)
  | .task c, db => ((c.step db).1, .task (c.step db).2)

/-- The time `t` is no earlier than the clock each `swarm lock` among `cs` read: what a clock that never runs back
gives at any moment after they ran. -/
def Before (t : Int) (cs : List LCmd) : Prop := ∀ x ∈ cs, ∀ c p r l, x = .lock c p r l → c.now ≤ t

theorem step_good (x : LCmd) {db : Db} {t : Int} (ht : Before t [x]) (h : Good db t) : Good (x.step db).1 t := by
  cases x with
  | lock c p r l => exact lock_good c p r l (ht _ (List.mem_singleton_self _) c p r l rfl) h
  | unlock me p now => exact unlock_good me p now h
  | leave n now => exact leave_good n now h
  | join n cwd hc model r now =>
    cases hn : notHuman n with
    | error e => simp only [LCmd.step, hn]; exact h
    | ok u =>
      simp only [LCmd.step, hn]
      have : n ≠ HUMAN := fun e => by simp [notHuman, e] at hn
      exact bind_good n cwd hc model r now this h
  | task c => exact good_grow (step_frame c db).1 (step_frame c db).2 h

theorem replay_good (cs : List LCmd) {db : Db} {t : Int} (ht : Before t cs) (h : Good db t) :
    Good (replay LCmd.step db cs).1 t := by
  induction cs generalizing db with
  | nil => exact h
  | cons x xs ih =>
    exact ih (fun y hy => ht y (List.mem_cons_of_mem _ hy))
      (step_good x (fun y hy => ht y (by rw [List.mem_singleton.1 hy]; exact List.mem_cons_self ..)) h)

theorem good_empty (t : Int) : Good {} t := by
  exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-- S3: after any lock, unlock, leave, join and task commands by any agents in any order from the empty db, at any time `t` no
earlier than each lock's clock, no two locks of different agents that hold at `t` (agent live, lease past `t`)
overlap. -/
theorem locks_disjoint (cs : List LCmd) (t : Int) (ht : Before t cs) : Disjoint (replay LCmd.step {} cs).1 t :=
  (replay_good cs ht (good_empty t)).2

/-- S3 as files: no path is covered by two locks of different agents that hold at `t`. -/
theorem no_shared_file (cs : List LCmd) (t : Int) (ht : Before t cs) {l m : Lock}
    (hl : l ∈ (replay LCmd.step {} cs).1.locks) (hm : m ∈ (replay LCmd.step {} cs).1.locks)
    (h1 : HeldAt (replay LCmd.step {} cs).1 t l) (h2 : HeldAt (replay LCmd.step {} cs).1 t m) (hne : l.agent ≠ m.agent)
    (x : String) : ¬ (covers x l.path = true ∧ covers x m.path = true) := fun ⟨c1, c2⟩ => by
  have := locks_disjoint cs t ht l hl m hm h1 h2 hne
  rw [overlaps_of_covers c1 c2] at this; cases this

/-- Under the store's assumption (`Atomic`), when processes ran lock, unlock, leave, join and task commands at once on a store
where S3 held at `t` (with every lock's agent live or the user), it still holds at `t`, if `t` is no earlier than
their locks' clocks. -/
theorem atomic_good (before after : Db) (ran : List (LCmd × LResult)) (t : Int) (h : Atomic LCmd.step before after ran)
    (ht : Before t (ran.map (·.1))) (hg : Good before t) : Good after t := by
  obtain ⟨order, hp, e⟩ := h
  have : after = (replay LCmd.step before (order.map (·.1))).1 := (congrArg Prod.fst e).symm
  rw [this]
  exact replay_good _ (fun x hx => ht x ((hp.map _).mem_iff.1 hx)) hg

end SwarmLean.Locks
