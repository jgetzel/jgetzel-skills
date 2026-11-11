import SwarmModel.Sql

/-! sqlite's isolation as the swarm uses it (board #33). Rung 4 treats each transaction as one step; this is why that
holds. The engine is what sqlite documents for a WAL db, not its internals: committed versions, the one write lock,
each connection's transaction, and SQLITE_BUSY. `Env.lean` assumes real sqlite is this engine, one named assumption
per operation, each with a stress test in `../lua/test/sqlite_spec.lua`.

What the code uses (db.lua): `pragma journal_mode=wal` and `busy_timeout(10000)` on every connection; `db:tx` is
`begin immediate` .. `commit`, or `rollback` when its function errors; every other statement runs alone, outside a
transaction (autocommit). The engine:

- A statement is a function of the db it runs on (`Lang.run`; `sqlLang` is `Sql.exec`'s), atomic: an error changes
  nothing. Whether it writes is known before it runs (sqlite compiles it).
- Outside a transaction a read runs on the latest committed version, and a write takes the write lock, runs on the
  latest version and commits it as the next, at once.
- `begin immediate` takes the write lock and its transaction runs on the latest version; a deferred `begin` takes
  nothing until its first statement. A WAL reader never waits; a transaction that has read (a snapshot) and then writes
  gets SQLITE_BUSY at once if the lock is held, and SQLITE_BUSY_SNAPSHOT if a commit came after its snapshot: the
  busy handler isn't called, and the transaction stays open.
- `commit` makes the next version from the transaction's db (WAL: it never waits), `rollback` and the process ending
  discard it; both free the lock.
- Waiting on the lock: the step is blocked (`none`), or, once the busy timeout runs out, SQLITE_BUSY and nothing changes.

Proved: `serializable` (every committed version is the serial run of the transaction that made it on the one before,
and a transaction holding the lock runs on the latest version, which only it can extend) and `stmt_out` (a statement
answers on its transaction's db): the db is always that of running the committed transactions one after another, and
every answer is the one it would get there. Whatever the `Cfg`. `busyClean_of`: with `begin immediate`, SQLITE_BUSY
comes only after waiting on another's lock, to a connection with no transaction open, and changes nothing, so a command
that dies of it did nothing and holds nothing; with a deferred `begin` it doesn't (`not_busyClean_deferred`).

`migrate_ok`: db.connect's column migration, run by any number of processes at once, never fails, with `migrateTx`
on; with it off (the Lua before), two connects of an old db fail (`not_migrate_ok`). -/

namespace Swarm.Iso

/-- the code's choices; the defaults are the code's -/
structure Cfg where
  /-- `db:tx` begins with `begin immediate`; off, a deferred `begin` -/
  immediate : Bool := true
  /-- db.connect adds the missing columns in one write transaction that reads them again; off, each `alter` on its own
  after reading them outside one (the Lua before board #33) -/
  migrateTx : Bool := true
  deriving DecidableEq, Repr

/-- a statement language: what statement `s` answers on db `d` and the db after, or its error (nothing changes);
whether it writes -/
structure Lang (σ ρ S : Type) where
  run : S → σ → Except String (ρ × σ)
  writes : S → Bool

variable {σ ρ S : Type}

/-- the db after s (an error changes nothing) -/
def Lang.apply (L : Lang σ ρ S) (s : S) (d : σ) : σ := match L.run s d with | .ok (_, d') => d' | .error _ => d
/-- the db after a transaction's statements, one after another -/
def Lang.runU (L : Lang σ ρ S) (u : List S) (d : σ) : σ := u.foldl (fun d s => L.apply s d) d
/-- what s answers on d -/
def Lang.out (L : Lang σ ρ S) (s : S) (d : σ) : Except String ρ := (L.run s d).map (·.1)

/-- what a connection asks of sqlite -/
inductive Op (S : Type) where
  | begin
  | stmt (s : S)
  | commit
  | rollback
  /-- the process ends (exits, or is killed) -/
  | close

/-- what it gets back -/
inductive Res (ρ : Type) where
  | ok
  | out (r : Except String ρ)
  /-- SQLITE_BUSY; `waited`: the busy handler waited out the timeout on another connection's lock -/
  | busy (waited : Bool)
  /-- `begin` in a transaction, `commit` or `rollback` outside one -/
  | misuse

/-- a connection's transaction -/
inductive Mode (σ S : Type) where
  /-- none open (autocommit) -/
  | auto
  /-- a deferred `begin`, nothing run yet -/
  | begun
  /-- a deferred transaction that has read: its snapshot, committed version v -/
  | read (v : Nat)
  /-- holds the write lock: began on version v, its db, its statements so far (ghost) -/
  | write (v : Nat) (d : σ) (u : List S)

structure Eng (σ S : Type) where
  /-- the latest committed version -/
  n : Nat
  /-- version i's db, i ≤ n -/
  ver : Nat → σ
  /-- the statements of the transaction that made version i + 1 from version i (ghost) -/
  unit : Nat → List S
  mode : Nat → Mode σ S
  /-- the connection holding the write lock -/
  lock : Option Nat

/-- a fresh db, d0 -/
def Eng.init (d0 : σ) : Eng σ S := { n := 0, ver := fun _ => d0, unit := fun _ => [], mode := fun _ => .auto, lock := none }

def Eng.setMode (e : Eng σ S) (c : Nat) (m : Mode σ S) : Eng σ S := { e with mode := fun x => if x = c then m else e.mode x }

/-- version n + 1 is d, made by u -/
def Eng.commitV (e : Eng σ S) (d : σ) (u : List S) : Eng σ S :=
  { e with n := e.n + 1, ver := fun i => if i = e.n + 1 then d else e.ver i, unit := fun i => if i = e.n then u else e.unit i }

/-- c's transaction ends (committed or not), and the lock with it if it held it -/
def Eng.release (e : Eng σ S) (c : Nat) : Eng σ S :=
  { e.setMode c .auto with lock := if e.lock = some c then none else e.lock }

/-- the db c's next statement runs on -/
def Eng.view (e : Eng σ S) (c : Nat) : σ :=
  match e.mode c with
  | .read v => e.ver v
  | .write _ d _ => d
  | _ => e.ver e.n

/-- c waits on another connection's write lock: blocked, or SQLITE_BUSY once the timeout (t) runs out -/
def wait (e : Eng σ S) (t : Bool) : Option (Res ρ × Eng σ S) := if t then some (.busy true, e) else none

/-- c takes the lock on the latest version and runs s, its transaction's first statement -/
def Eng.firstWrite (L : Lang σ ρ S) (e : Eng σ S) (c : Nat) (s : S) : Eng σ S :=
  { e.setMode c (.write e.n (L.apply s (e.ver e.n)) [s]) with lock := some c }

/-- connection c does op; t: the busy timeout has run out (if c would wait). `none`: c waits -/
def step (cfg : Cfg) (L : Lang σ ρ S) (e : Eng σ S) (c : Nat) (op : Op S) (t : Bool) : Option (Res ρ × Eng σ S) :=
  match op, e.mode c with
  | .begin, .auto =>
    if cfg.immediate then
      if e.lock = none then some (.ok, { e.setMode c (.write e.n (e.ver e.n) []) with lock := some c }) else wait e t
    else some (.ok, e.setMode c .begun)
  | .begin, _ => some (.misuse, e)
  | .stmt s, .auto =>
    if L.writes s then
      if e.lock = none then
        match L.run s (e.ver e.n) with
        | .ok (r, d) => some (.out (.ok r), e.commitV d [s])
        | .error m => some (.out (.error m), e)
      else wait e t
    else some (.out (L.out s (e.ver e.n)), e)
  | .stmt s, .begun =>
    if L.writes s then
      if e.lock = none then some (.out (L.out s (e.ver e.n)), e.firstWrite L c s) else wait e t
    else some (.out (L.out s (e.ver e.n)), e.setMode c (.read e.n))
  | .stmt s, .read v =>
    if L.writes s then
      if e.lock = none ∧ v = e.n then some (.out (L.out s (e.ver v)), e.firstWrite L c s)
      else some (.busy false, e)
    else some (.out (L.out s (e.ver v)), e)
  | .stmt s, .write v d u => some (.out (L.out s d), e.setMode c (.write v (L.apply s d) (u ++ [s])))
  | .commit, .auto => some (.misuse, e)
  | .commit, .write _ d u => some (.ok, (e.commitV d u).release c)
  | .commit, _ => some (.ok, e.release c)
  | .rollback, .auto => some (.misuse, e)
  | .rollback, _ => some (.ok, e.release c)
  | .close, _ => some (.ok, e.release c)

/-- the states any interleaving of any connections' ops reaches from d0 -/
inductive Reach (cfg : Cfg) (L : Lang σ ρ S) (d0 : σ) : Eng σ S → Prop
  | init : Reach cfg L d0 (Eng.init d0)
  | step {e e' c op t r} : Reach cfg L d0 e → step cfg L e c op t = some (r, e') → Reach cfg L d0 e'

/-- serializability, as an invariant: every committed version is its transaction's statements run on the version
before; a transaction holding the lock began on the latest version and its db is its statements run on it; only it
holds the lock; a snapshot is a committed version -/
structure Inv (L : Lang σ ρ S) (e : Eng σ S) : Prop where
  chain : ∀ i, i < e.n → e.ver (i + 1) = L.runU (e.unit i) (e.ver i)
  writer : ∀ c v d u, e.mode c = .write v d u → v = e.n ∧ d = L.runU u (e.ver v) ∧ e.lock = some c
  locked : ∀ c, e.lock = some c → ∃ v d u, e.mode c = .write v d u
  snap : ∀ c v, e.mode c = .read v → v ≤ e.n

theorem runU_append (L : Lang σ ρ S) (u : List S) (s : S) (d : σ) : L.runU (u ++ [s]) d = L.apply s (L.runU u d) := by
  simp [Lang.runU, List.foldl_append]

theorem inv_init (L : Lang σ ρ S) (d0 : σ) : Inv L (Eng.init d0 : Eng σ S) where
  chain _ h := absurd h (Nat.not_lt_zero _)
  writer _ _ _ _ h := by simp [Eng.init] at h
  locked _ h := by simp [Eng.init] at h
  snap _ _ h := by simp [Eng.init] at h

section
variable {L : Lang σ ρ S} {e : Eng σ S}

theorem wait_some {e' : Eng σ S} {t : Bool} {r : Res ρ} (h : wait e t = some (r, e')) : r = .busy true ∧ e' = e := by
  unfold wait at h; split at h <;> simp at h; exact ⟨h.1.symm, h.2.symm⟩

/-- with c holding no lock, the other connections' writers stay (c's mode is set to m) -/
theorem inv_setMode (hi : Inv L e) (c : Nat) (m : Mode σ S) (hl : e.lock ≠ some c)
    (hm : ∀ v d u, m ≠ .write v d u) (hr : ∀ v, m = .read v → v ≤ e.n) : Inv L (e.setMode c m) where
  chain := hi.chain
  writer c' v d u h := by
    simp only [Eng.setMode] at h ⊢
    split at h
    · exact absurd h (hm v d u)
    · exact hi.writer c' v d u h
  locked c' h := by
    simp only [Eng.setMode] at h ⊢
    split
    · subst_vars; exact absurd h hl
    · exact hi.locked c' h
  snap c' v h := by
    simp only [Eng.setMode] at h ⊢
    split at h
    · exact hr v h
    · exact hi.snap c' v h

/-- c's transaction ends, whatever it was -/
theorem inv_release (hi : Inv L e) (c : Nat) : Inv L (e.release c) where
  chain := hi.chain
  writer c' v d u h := by
    simp only [Eng.release, Eng.setMode] at h ⊢
    split at h
    · cases h
    · rename_i hne
      obtain ⟨h1, h2, h3⟩ := hi.writer c' v d u h
      exact ⟨h1, h2, by simp [h3, hne]⟩
  locked c' h := by
    simp only [Eng.release, Eng.setMode] at h ⊢
    split at h
    · cases h
    · rename_i hne
      split
      · subst_vars; exact absurd h hne
      · exact hi.locked c' h
  snap c' v h := by
    simp only [Eng.release, Eng.setMode] at h
    split at h
    · cases h
    · exact hi.snap c' v h

/-- once the lock's holder ends its transaction, no connection holds the lock or writes -/
theorem release_free (hi : Inv L e) {c : Nat} (hl : e.lock = some c) :
    (e.release c).lock = none ∧ ∀ c' v d u, (e.release c).mode c' ≠ .write v d u := by
  refine ⟨by simp [Eng.release, hl], fun c' v d u h => ?_⟩
  simp only [Eng.release, Eng.setMode] at h
  split at h
  · cases h
  · rename_i hne; have := (hi.writer c' v d u h).2.2; rw [hl] at this; cases this; exact hne rfl

/-- c takes the free lock and a transaction on the latest version, with u run -/
theorem inv_take (hi : Inv L e) (c : Nat) (u : List S) (hl : e.lock = none) :
    Inv L { e.setMode c (.write e.n (L.runU u (e.ver e.n)) u) with lock := some c } where
  chain := hi.chain
  writer c' v d u' h := by
    simp only [Eng.setMode] at h ⊢
    split at h
    · cases h; subst_vars; exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, _, h⟩ := hi.writer c' v d u' h; simp [hl] at h
  locked c' h := by simp at h; subst h; simp [Eng.setMode]
  snap c' v h := by
    simp only [Eng.setMode] at h
    split at h
    · cases h
    · exact hi.snap c' v h

/-- a new version made with the lock free and no writer (an autocommit write, or a commit once released) -/
theorem inv_commit (hi : Inv L e) (d : σ) (u : List S) (hd : d = L.runU u (e.ver e.n))
    (hw : ∀ c' v d' u', e.mode c' ≠ .write v d' u') (hl : e.lock = none) : Inv L (e.commitV d u) where
  chain i h := by
    simp only [Eng.commitV] at h ⊢
    by_cases hi' : i = e.n
    · subst hi'; simp [hd]
    · have : i < e.n := by omega
      simp [hi', show i ≠ e.n + 1 by omega, hi.chain i this]
  writer c' v d' u' h := absurd h (hw c' v d' u')
  locked c' h := by simp [Eng.commitV, hl] at h
  snap c' v h := by have := hi.snap c' v h; simp only [Eng.commitV]; omega

end

/-- the invariant holds of every reachable state, whatever the `Cfg` -/
theorem serializable {cfg : Cfg} {L : Lang σ ρ S} {d0 : σ} {e : Eng σ S} (h : Reach cfg L d0 e) : Inv L e := by
  induction h with
  | init => exact inv_init L d0
  | @step e e' c op t r _ hs hi =>
    have notMe (hm : ∀ v d u, e.mode c ≠ .write v d u) : e.lock ≠ some c := fun hl => by
      obtain ⟨v, d, u, h⟩ := hi.locked c hl; exact hm v d u h
    have noW (hl : e.lock = none) : ∀ c' v d u, e.mode c' ≠ .write v d u := fun c' v d u hm => by
      have := (hi.writer c' v d u hm).2.2; simp [hl] at this
    cases op with
    | begin =>
      cases hm : e.mode c <;> simp only [step, hm] at hs
      case auto =>
        split at hs
        · split at hs
          · next hl => cases hs; simpa [Lang.runU] using inv_take hi c [] hl
          · rw [(wait_some hs).2]; exact hi
        · cases hs; exact inv_setMode hi c .begun (notMe (by simp [hm])) (by simp) (by simp)
      all_goals (cases hs; exact hi)
    | stmt s =>
      cases hm : e.mode c with
      | auto =>
        simp only [step, hm] at hs
        split at hs
        · split at hs
          · next hl =>
            split at hs
            · next r' d hr => cases hs; exact inv_commit hi d [s] (by simp [Lang.runU, Lang.apply, hr]) (noW hl) hl
            · cases hs; exact hi
          · rw [(wait_some hs).2]; exact hi
        · cases hs; exact hi
      | begun =>
        simp only [step, hm] at hs
        split at hs
        · split at hs
          · next hl => cases hs; simpa [Lang.runU, Eng.firstWrite] using inv_take hi c [s] hl
          · rw [(wait_some hs).2]; exact hi
        · cases hs; exact inv_setMode hi c (.read e.n) (notMe (by simp [hm])) (by simp) (by simp)
      | read v =>
        simp only [step, hm] at hs
        split at hs
        · split at hs
          · next hl => cases hs; simpa [Lang.runU, Eng.firstWrite] using inv_take hi c [s] hl.1
          · cases hs; exact hi
        · cases hs; exact hi
      | write v d u =>
        simp only [step, hm] at hs
        cases hs
        obtain ⟨hv, hd, hl⟩ := hi.writer c v d u hm
        refine ⟨hi.chain, fun c' v' d' u' h => ?_, fun c' h => ?_, fun c' v' h => ?_⟩
        · simp only [Eng.setMode] at h
          split at h
          · cases h; subst_vars; exact ⟨rfl, by rw [runU_append]; rfl, hl⟩
          · exact hi.writer c' v' d' u' h
        · simp only [Eng.setMode]
          split
          · exact ⟨_, _, _, rfl⟩
          · exact hi.locked c' h
        · simp only [Eng.setMode] at h
          split at h
          · cases h
          · exact hi.snap c' v' h
    | commit =>
      cases hm : e.mode c with
      | auto => simp only [step, hm] at hs; cases hs; exact hi
      | write v d u =>
        simp only [step, hm] at hs; cases hs
        obtain ⟨hv, hd, hl⟩ := hi.writer c v d u hm
        obtain ⟨hl', hw'⟩ := release_free hi hl
        exact inv_commit (inv_release hi c) d u (by rw [hd, hv]; rfl) hw' hl'
      | _ => simp only [step, hm] at hs; cases hs; exact inv_release hi c
    | rollback =>
      cases hm : e.mode c with
      | auto => simp only [step, hm] at hs; cases hs; exact hi
      | _ => simp only [step, hm] at hs; cases hs; exact inv_release hi c
    | close => simp only [step] at hs; cases hs; exact inv_release hi c

/-- a statement answers on its transaction's db (`Inv.writer`: a writer's is the latest version with its own
statements run; a snapshot's, its committed version; else the latest version) -/
theorem stmt_out {cfg : Cfg} {L : Lang σ ρ S} {e e' : Eng σ S} {c : Nat} {s : S} {t : Bool} {r : Except String ρ}
    (hs : step cfg L e c (.stmt s) t = some (.out r, e')) : r = L.out s (e.view c) := by
  cases hm : e.mode c <;> simp only [step, hm, Eng.view] at hs ⊢
  case auto =>
    split at hs
    · split at hs
      · split at hs
        · next r' d hr => cases hs; simp only [Lang.out, hr]; rfl
        · next m hr => cases hs; simp only [Lang.out, hr]; rfl
      · exact absurd (wait_some hs).1 (by simp)
    · cases hs; rfl
  case begun =>
    split at hs
    · split at hs
      · cases hs; rfl
      · exact absurd (wait_some hs).1 (by simp)
    · cases hs; rfl
  case read =>
    split at hs
    · split at hs
      · cases hs; rfl
      · cases hs
    · cases hs; rfl
  case write => cases hs; rfl

/-- SQLITE_BUSY comes only after waiting out the timeout on another connection's lock, to a connection with no
transaction open, and changes nothing: a command that dies of it did nothing and holds nothing -/
def BusyClean (cfg : Cfg) (L : Lang σ ρ S) (d0 : σ) : Prop :=
  ∀ e c op t w e', Reach cfg L d0 e → step cfg L e c op t = some (.busy w, e') → w = true ∧ e.mode c = .auto ∧ e' = e

/-- a step changes no other connection's transaction -/
theorem step_other {cfg : Cfg} {L : Lang σ ρ S} {e e' : Eng σ S} {c : Nat} {op : Op S} {t : Bool} {r : Res ρ}
    (hs : step cfg L e c op t = some (r, e')) (q : Nat) (hq : q ≠ c) : e'.mode q = e.mode q := by
  have hset (m : Mode σ S) : (e.setMode c m).mode q = e.mode q := by simp [Eng.setMode, hq]
  have hwait (h : wait e t = some (r, e')) : e'.mode q = e.mode q := by rw [(wait_some h).2]
  cases op with
  | begin =>
    cases hm : e.mode c with
    | auto =>
      simp only [step, hm] at hs
      split at hs
      · split at hs
        · cases hs; exact hset _
        · exact hwait hs
      · cases hs; exact hset _
    | _ => simp only [step, hm] at hs; cases hs; rfl
  | stmt s =>
    cases hm : e.mode c with
    | auto =>
      simp only [step, hm] at hs
      split at hs
      · split at hs
        · split at hs <;> cases hs <;> rfl
        · exact hwait hs
      · cases hs; rfl
    | begun =>
      simp only [step, hm] at hs
      split at hs
      · split at hs
        · cases hs; exact hset _
        · exact hwait hs
      · cases hs; exact hset _
    | read v =>
      simp only [step, hm] at hs
      split at hs
      · split at hs
        · cases hs; exact hset _
        · cases hs; rfl
      · cases hs; rfl
    | write v d u => simp only [step, hm] at hs; cases hs; exact hset _
  | commit =>
    cases hm : e.mode c with
    | auto => simp only [step, hm] at hs; cases hs; rfl
    | write v d u => simp only [step, hm] at hs; cases hs; simp [Eng.release, Eng.setMode, Eng.commitV, hq]
    | _ => simp only [step, hm] at hs; cases hs; exact hset _
  | rollback =>
    cases hm : e.mode c with
    | auto => simp only [step, hm] at hs; cases hs; rfl
    | _ => simp only [step, hm] at hs; cases hs; exact hset _
  | close => simp only [step] at hs; cases hs; exact hset _

/-- c's own transaction after a step, with `begin immediate`: never a deferred one -/
theorem step_self_imm {cfg : Cfg} {L : Lang σ ρ S} {e e' : Eng σ S} {c : Nat} {op : Op S} {t : Bool} {r : Res ρ}
    (hc : cfg.immediate = true) (hd : e.mode c ≠ .begun ∧ ∀ v, e.mode c ≠ .read v)
    (hs : step cfg L e c op t = some (r, e')) : e'.mode c ≠ .begun ∧ ∀ v, e'.mode c ≠ .read v := by
  have hset (m : Mode σ S) (h1 : m ≠ .begun) (h2 : ∀ v, m ≠ .read v) :
      (e.setMode c m).mode c ≠ .begun ∧ ∀ v, (e.setMode c m).mode c ≠ .read v := by simp [Eng.setMode, h1, h2]
  have hwait (h : wait e t = some (r, e')) : e'.mode c ≠ .begun ∧ ∀ v, e'.mode c ≠ .read v := by
    rw [(wait_some h).2]; exact hd
  cases op with
  | begin =>
    cases hm : e.mode c with
    | auto =>
      simp only [step, hm, hc, ite_true] at hs
      split at hs
      · cases hs; exact hset _ (by simp) (by simp)
      · exact hwait hs
    | _ => simp only [step, hm] at hs; cases hs; exact hd
  | stmt s =>
    cases hm : e.mode c with
    | auto =>
      simp only [step, hm] at hs
      split at hs
      · split at hs
        · split at hs <;> cases hs <;> simp [Eng.commitV, hm]
        · exact hwait hs
      · cases hs; simp [hm]
    | begun => exact absurd hm hd.1
    | read v => exact absurd hm (hd.2 v)
    | write v d u => simp only [step, hm] at hs; cases hs; exact hset _ (by simp) (by simp)
  | commit =>
    cases hm : e.mode c with
    | auto => simp only [step, hm] at hs; cases hs; simp [hm]
    | write v d u => simp only [step, hm] at hs; cases hs; simp [Eng.release, Eng.setMode, Eng.commitV]
    | _ => simp only [step, hm] at hs; cases hs; exact hset _ (by simp) (by simp)
  | rollback =>
    cases hm : e.mode c with
    | auto => simp only [step, hm] at hs; cases hs; simp [hm]
    | _ => simp only [step, hm] at hs; cases hs; exact hset _ (by simp) (by simp)
  | close => simp only [step] at hs; cases hs; exact hset _ (by simp) (by simp)

/-- with `begin immediate` no connection is in a deferred transaction -/
theorem immediate_noDeferred {cfg : Cfg} {L : Lang σ ρ S} {d0 : σ} {e : Eng σ S} (hc : cfg.immediate = true)
    (h : Reach cfg L d0 e) : ∀ c, e.mode c ≠ .begun ∧ ∀ v, e.mode c ≠ .read v := by
  induction h with
  | init => simp [Eng.init]
  | @step e e' c op t r _ hs ih =>
    intro x
    by_cases hx : x = c
    · subst hx; exact step_self_imm hc (ih x) hs
    · rw [step_other hs x hx]; exact ih x

theorem busyClean_of {cfg : Cfg} {L : Lang σ ρ S} {d0 : σ} (hc : cfg.immediate = true) : BusyClean cfg L d0 := by
  intro e c op t w e' h hs
  have hd := immediate_noDeferred hc h c
  have hwait (hm : e.mode c = .auto) (h : wait (ρ := ρ) e t = some (Res.busy w, e')) : w = true ∧ e.mode c = .auto ∧ e' = e := by
    obtain ⟨h1, h2⟩ := wait_some h; cases h1; exact ⟨rfl, hm, h2⟩
  cases op with
  | begin =>
    cases hm : e.mode c with
    | auto =>
      simp only [step, hm, hc, ite_true] at hs
      split at hs
      · cases hs
      · obtain ⟨h1, -, h3⟩ := hwait hm hs; exact ⟨h1, rfl, h3⟩
    | _ => simp only [step, hm] at hs; cases hs
  | stmt s =>
    cases hm : e.mode c with
    | auto =>
      simp only [step, hm] at hs
      split at hs
      · split at hs
        · split at hs <;> cases hs
        · obtain ⟨h1, -, h3⟩ := hwait hm hs; exact ⟨h1, rfl, h3⟩
      · cases hs
    | begun => exact absurd hm hd.1
    | read v => exact absurd hm (hd.2 v)
    | write v d u => simp only [step, hm] at hs; cases hs
  | commit => cases hm : e.mode c <;> simp only [step, hm] at hs <;> cases hs
  | rollback => cases hm : e.mode c <;> simp only [step, hm] at hs <;> cases hs
  | close => simp only [step] at hs; cases hs

/-! ## The counterexample for a deferred `begin`, and the engine's runs -/

/-- one counter: `get` reads it, `inc` adds one -/
inductive CS where | get | inc
  deriving DecidableEq

def counter : Lang Nat Nat CS where
  run | .get, d => .ok (d, d) | .inc, d => .ok (d, d + 1)
  writes | .get => false | .inc => true

/-- the state after ops, each by its connection, none blocked; and their answers -/
def runOps (cfg : Cfg) (L : Lang σ ρ S) (e : Eng σ S) : List (Nat × Op S × Bool) → Option (Eng σ S)
  | [] => some e
  | (c, op, t) :: rest => match step cfg L e c op t with
    | none => none
    | some (_, e') => runOps cfg L e' rest

theorem runOps_reach {cfg : Cfg} {L : Lang σ ρ S} {d0 : σ} : ∀ {e : Eng σ S} {ops e'}, Reach cfg L d0 e →
    runOps cfg L e ops = some e' → Reach cfg L d0 e'
  | _, [], _, h, hr => by simp only [runOps, Option.some.injEq] at hr; exact hr ▸ h
  | e, (c, op, t) :: rest, e', h, hr => by
    simp only [runOps] at hr
    split at hr
    · cases hr
    · next r e1 hx => exact runOps_reach (Reach.step h hx) hr

/-- deferred: connection 0 begins and reads; 1 adds one outside a transaction; 0's add gets SQLITE_BUSY_SNAPSHOT at
once, its transaction still open -/
def deferredRun : List (Nat × Op CS × Bool) := [(0, .begin, false), (0, .stmt .get, false), (1, .stmt .inc, false)]

theorem not_busyClean_deferred : ¬ BusyClean { immediate := false } counter 0 := by
  intro h
  have hsome : (runOps { immediate := false } counter (Eng.init 0) deferredRun).isSome = true := rfl
  have hR := runOps_reach Reach.init (Option.some_get hsome).symm
  have hs : step { immediate := false } counter (Option.get _ hsome) 0 (.stmt .inc) false =
    some (.busy false, Option.get _ hsome) := rfl
  exact absurd (h _ 0 _ false false _ hR hs).1 (by decide)

/-- with `begin immediate` the same connections: 0 holds the lock, so 1's add waits (blocked), and 0's add runs -/
theorem immediate_waits : (runOps {} counter (Eng.init 0) [(0, .begin, false), (0, .stmt .get, false)]).bind
    (fun e => step {} counter e 1 (.stmt .inc) false) = none := rfl

/-! ## db.connect's column migration (board #33)

The columns as numbers: `cols` is `pragma table_info`, `add x` is `alter table .. add column x`, an error if x is there.
A process runs db.connect: it reads the columns; with `migrateTx` off it adds each missing one on its own, with it on
it takes `begin immediate` when one is missing, reads them again, adds those missing and commits. -/

inductive MS where | cols | add (x : Nat)
  deriving DecidableEq

def schema : Lang (List Nat) (List Nat) MS where
  run | .cols, d => .ok (d, d) | .add x, d => if x ∈ d then .error "duplicate column name" else .ok ([], x :: d)
  writes | .cols => false | .add _ => true

/-- where a connect is -/
inductive Pc where
  | start
  /-- adding these on their own (`migrateTx` off) -/
  | add (todo : List Nat)
  | begin
  /-- in the transaction, before reading the columns again -/
  | read
  | txAdd (todo : List Nat)
  | done
  /-- died: of SQLITE_BUSY (`busy`), or of an error -/
  | failed (busy : Bool)
  deriving DecidableEq

/-- its next op; none once it is done or failed -/
def Pc.op : Pc → Option (Op MS)
  | .start | .read => some (.stmt .cols)
  | .add (x :: _) | .txAdd (x :: _) => some (.stmt (.add x))
  | .begin => some .begin
  | .txAdd [] => some .commit
  | _ => none

/-- where it goes on the answer; W the columns db.connect wants -/
def Pc.next (cfg : Cfg) (W : List Nat) : Pc → Res (List Nat) → Pc
  | _, .busy _ => .failed true
  | .start, .out (.ok d) =>
    let todo := W.filter (· ∉ d)
    if cfg.migrateTx then (if todo = [] then .done else .begin) else .add todo
  | .add (_ :: t), .out (.ok _) => .add t
  | .begin, .ok => .read
  | .read, .out (.ok d) => .txAdd (W.filter (· ∉ d))
  | .txAdd (_ :: t), .out (.ok _) => .txAdd t
  | .txAdd [], .ok => .done
  | _, _ => .failed false

/-- the db and every process's place -/
structure MW where
  e : Eng (List Nat) MS
  pc : Nat → Pc

/-- process p takes its next op -/
def mstep (cfg : Cfg) (W : List Nat) (w : MW) (p : Nat) (t : Bool) : Option MW :=
  match (w.pc p).op with
  | none => none
  | some op => match step cfg schema w.e p op t with
    | none => none
    | some (r, e) => some { e, pc := fun q => if q = p then (w.pc p).next cfg W r else w.pc q }

/-- every interleaving of any number of connects, from a db with columns d0 -/
inductive MReach (cfg : Cfg) (W d0 : List Nat) : MW → Prop
  | init : MReach cfg W d0 ⟨Eng.init d0, fun _ => .start⟩
  | step {w w' p t} : MReach cfg W d0 w → mstep cfg W w p t = some w' → MReach cfg W d0 w'

/-- what a connect's place says of its connection: no transaction before `begin` and after it's over; in one, holding
the lock, and the columns it still adds are missing from its db, each once -/
def pcOk (e : Eng (List Nat) MS) (p : Nat) : Pc → Prop
  | .read => ∃ v d u, e.mode p = .write v d u
  | .txAdd todo => ∃ v d u, e.mode p = .write v d u ∧ todo.Nodup ∧ ∀ x ∈ todo, x ∉ d
  | .add _ => False
  | _ => e.mode p = .auto

theorem migrate_inv {cfg : Cfg} {W d0 : List Nat} (hc : cfg.migrateTx = true) (hi : cfg.immediate = true) (hW : W.Nodup)
    {w : MW} (h : MReach cfg W d0 w) : ∀ p, pcOk w.e p (w.pc p) ∧ w.pc p ≠ .failed false := by
  induction h with
  | init => intro p; simp [pcOk, Eng.init]
  | @step w w' p t _ hs ih =>
    simp only [mstep] at hs
    split at hs
    · cases hs
    next op hop =>
    split at hs
    · cases hs
    next r e hx =>
    cases hs
    -- the other processes' modes stay: step sets only p's
    have other : ∀ q, q ≠ p → e.mode q = w.e.mode q := step_other hx
    intro q
    by_cases hq : q = p
    · subst hq
      simp only [ite_true]
      have ⟨hok, _⟩ := ih q
      generalize hpc : w.pc q = pc at hok hop
      cases pc with
      | start =>
        simp only [Pc.op, Option.some.injEq] at hop; subst hop
        simp only [pcOk] at hok
        have h2 : step cfg schema w.e q (.stmt .cols) t = some (.out (.ok (w.e.ver w.e.n)), w.e) := by
          simp only [step, hok]; rfl
        rw [h2] at hx; cases hx
        have : Pc.next cfg W .start (.out (.ok (w.e.ver w.e.n))) = if cfg.migrateTx then
            (if W.filter (· ∉ w.e.ver w.e.n) = [] then .done else .begin) else .add (W.filter (· ∉ w.e.ver w.e.n)) := rfl
        rw [this]
        split
        · split <;> simp [pcOk, hok]
        · next h => exact absurd hc h
      | add todo => exact absurd hok (by simp [pcOk])
      | begin =>
        simp only [Pc.op, Option.some.injEq] at hop; subst hop
        simp only [pcOk] at hok
        simp only [step, hok, hi, ite_true] at hx
        split at hx
        · cases hx; exact ⟨⟨w.e.n, w.e.ver w.e.n, [], by simp [Eng.setMode]⟩, by intro h; cases h⟩
        · obtain ⟨h1, h2⟩ := wait_some hx; subst h1 h2; exact ⟨hok, by intro h; cases h⟩
      | read =>
        simp only [Pc.op, Option.some.injEq] at hop; subst hop
        obtain ⟨v, d, u, hm⟩ := hok
        simp only [step, hm] at hx; cases hx
        have : Pc.next cfg W .read (.out (schema.out .cols d)) = .txAdd (W.filter (· ∉ d)) := rfl
        rw [this]
        refine ⟨⟨v, d, u ++ [.cols], by simp [Eng.setMode, Lang.apply, schema], hW.filter _, fun x hx => ?_⟩, by intro h; cases h⟩
        simp at hx; exact hx.2
      | txAdd todo =>
        obtain ⟨v, d, u, hm, hnd, hmiss⟩ := hok
        cases todo with
        | nil =>
          simp only [Pc.op, Option.some.injEq] at hop; subst hop
          simp only [step, hm] at hx; cases hx
          exact ⟨by simp [pcOk, Pc.next, Eng.release, Eng.setMode], by intro h; cases h⟩
        | cons x rest =>
          simp only [Pc.op, Option.some.injEq] at hop; subst hop
          have hx' : x ∉ d := hmiss x (by simp)
          simp only [step, hm] at hx; cases hx
          have ho : schema.out (.add x) d = .ok [] := by simp [Lang.out, schema, hx']; rfl
          have : Pc.next cfg W (.txAdd (x :: rest)) (.out (.ok [])) = .txAdd rest := rfl
          rw [ho, this]
          refine ⟨⟨v, x :: d, u ++ [.add x], by simp [Eng.setMode, Lang.apply, schema, hx'], (List.nodup_cons.mp hnd).2,
            fun y hy => ?_⟩, by intro h; cases h⟩
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => (List.nodup_cons.mp hnd).1 (h ▸ hy), hmiss y (by simp [hy])⟩
      | done => simp [Pc.op] at hop
      | failed b => simp [Pc.op] at hop
    · simp only [hq, ite_false]
      refine ⟨?_, (ih q).2⟩
      have := (ih q).1
      generalize w.pc q = pc at this ⊢
      cases pc <;> simp only [pcOk] at this ⊢ <;> (try rw [other q hq]) <;> exact this

/-- with `migrateTx` on, no connect ever fails but of SQLITE_BUSY (the 10 s timeout), however many run at once -/
theorem migrate_ok {cfg : Cfg} {W d0 : List Nat} (hc : cfg.migrateTx = true) (hi : cfg.immediate = true) (hW : W.Nodup)
    {w : MW} (h : MReach cfg W d0 w) (p : Nat) : w.pc p ≠ .failed false :=
  (migrate_inv hc hi hW h p).2

/-- with it off, two connects of a db missing column 0: both read, both add, the second fails ("duplicate column name") -/
def migrateRun : List (Nat × Bool) := [(0, false), (1, false), (0, false), (1, false)]

def mrun (cfg : Cfg) (W : List Nat) (w : MW) : List (Nat × Bool) → Option MW
  | [] => some w
  | (p, t) :: rest => (mstep cfg W w p t).bind (mrun cfg W · rest)

theorem mrun_reach {cfg : Cfg} {W d0 : List Nat} : ∀ {w w' : MW} {ps}, MReach cfg W d0 w → mrun cfg W w ps = some w' →
    MReach cfg W d0 w'
  | _, _, [], h, hr => by simp [mrun] at hr; exact hr ▸ h
  | w, w', (p, t) :: rest, h, hr => by
    simp only [mrun, Option.bind] at hr
    split at hr
    · cases hr
    · rename_i x hx; exact mrun_reach (MReach.step h hx) hr

theorem not_migrate_ok : ¬ ∀ w, MReach { migrateTx := false } [0] [] w → ∀ p, w.pc p ≠ .failed false := by
  intro h
  have hsome : (mrun { migrateTx := false } [0] ⟨Eng.init [], fun _ => .start⟩ migrateRun).isSome = true := rfl
  exact h _ (mrun_reach MReach.init (Option.some_get hsome).symm) 1 rfl

/-! ## The swarm's SQL as the engine's statements -/

/-- a statement of `Sql.lean` with its parameters, on the tables; `select`, `union all`, `pragma table_info` and
`pragma journal_mode` read (the db is WAL after its first connect, so the pragma changes nothing). `begin`, `commit` and
`rollback` are the engine's ops, not statements. `changes()` and `last_insert_rowid()` are the connection's, not the
db's, and not kept here -/
def sqlLang : Lang Sql.DB Sql.Out (Sql.Stmt × List Sql.Val) where
  run | (s, ps), db => (Sql.exec { db } s ps).map fun (o, c) => (o, c.db)
  writes
    | (.select _, _) | (.unionAll _ _, _) | (.tableInfo _, _) | (.journal _, _) => false
    | _ => true

end Swarm.Iso
