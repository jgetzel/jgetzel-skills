import LuaLean.Shallow

/-! A program logic for the interpreter (board #39): `RunP m h P` says the computation `m` (a function of the fuel),
started in heap `h`, returns a result and heap satisfying `P` at every fuel from some bound on. Running out of
fuel is never the answer for a large enough fuel: so a `RunP` is total correctness, and says what the run is
(for every fuel that suffices), which is what the Lua suite sees from LuaJIT. One rule per interpreter clause. -/

namespace Lua

def RunP {α : Type} (m : Nat → M α) (h : Heap) (P : α → Heap → Prop) : Prop :=
  ∃ N a h', (∀ n ≥ N, m n h = .ok a h') ∧ P a h'

section rules
variable {α β : Type} {m : Nat → M α} {h : Heap} {P Q : α → Heap → Prop}

theorem RunP.mono (r : RunP m h P) (hq : ∀ a h', P a h' → Q a h') : RunP m h Q := by
  obtain ⟨N, a, h', e, p⟩ := r; exact ⟨N, a, h', e, hq _ _ p⟩

/-- a computation that does not use the fuel -/
theorem RunP.const {m : M α} {a : α} {h' : Heap} (e : m h = .ok a h') (p : P a h') : RunP (fun _ => m) h P :=
  ⟨0, a, h', fun _ _ => e, p⟩

theorem RunP.pure' {a : α} (p : P a h) : RunP (fun _ => (pure a : M α)) h P := RunP.const rfl p

theorem RunP.bind {f : Nat → α → M β} {R : β → Heap → Prop}
    (r : RunP m h (fun a h1 => RunP (fun n => f n a) h1 R)) : RunP (fun n => m n >>= f n) h R := by
  obtain ⟨N, a, h1, e, N2, b, h2, e2, p⟩ := r
  refine ⟨max N N2, b, h2, fun n hn => ?_, p⟩
  have e1 := e n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have e2 := e2 n (Nat.le_trans (Nat.le_max_right _ _) hn)
  show EStateM.bind (m n) (f n) h = _
  rw [EStateM.bind, e1]; exact e2

/-- a step of one more fuel: the clauses of the interpreter match on `n + 1` -/
theorem RunP.succ {m : Nat → M α} (r : RunP (fun n => m (n + 1)) h P) : RunP m h P := by
  obtain ⟨N, a, h', e, p⟩ := r
  exact ⟨N + 1, a, h', fun n hn => by obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩; exact e k (by omega), p⟩

/-- a site changes only where an error is reported: a run that returns is the same run -/
theorem RunP.site {s : Site} (r : RunP m h P) : RunP (fun n => atSite s (m n)) h P := by
  obtain ⟨N, a, h', e, p⟩ := r
  exact ⟨N, a, h', fun n hn => by simp only [atSite, e n hn], p⟩

/-- and so does a call's frame -/
theorem RunP.frame (r : RunP m h P) : RunP (fun n => frame (m n)) h P := by
  obtain ⟨N, a, h', e, p⟩ := r
  exact ⟨N, a, h', fun n hn => by simp only [Lua.frame, e n hn], p⟩

theorem RunP.cong {m m' : Nat → M α} (e : ∀ n, m n = m' n) (r : RunP m h P) : RunP m' h P := by
  have : m = m' := funext e
  subst this; exact r

/-- `load(s)`, `loadstring(s)`, with a chunk name or none: the closure of `s`'s parse -/
theorem RunP.load {I : Sem} {fname : String} (hf : fname = "load" ∨ fname = "loadstring") {s : List Char}
    {cn : Option (List Char)} {b : Block} {P : List Val → Heap → Prop}
    (hb : s.head? ≠ some '\x1b') (hp : parseChunk s (shortSrc (cn.getD s)) = .ok b)
    (p : P [.fn h.size] (h.push (.clo ⟨[], true, b, []⟩))) :
    RunP (fun n => call I.srcs I.oracle I.tgt n (.prim fname []) (.str s :: cn.toList.map .str)) h P :=
  ⟨2, _, _, fun n hn => by
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩; exact call_load I n fname hf s cn b h hb hp, p⟩

/-- `dofile(p)` of a file given as source, its chunk `k`: what `k` does on no arguments -/
theorem RunP.dofile {I : Sem} {p : List Char} {b : Block} {k : List Val → Nat → M (List Val)}
    {P : List Val → Heap → Prop} (hk : CFn I k ⟨[], true, b, []⟩) (hs : I.srcs (String.ofList p) = some b)
    (r : RunP (fun n => bounded 1 (do let _ ← alloc (.clo ⟨[], true, b, []⟩); k [] n)) h P) :
    RunP (fun n => call I.srcs I.oracle I.tgt n (.prim "dofile" []) [.str p]) h P := by
  obtain ⟨N, a, h', e, q⟩ := RunP.frame r
  refine ⟨N + 3, a, h', fun n hn => ?_, q⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  show call _ _ _ _ _ _ h = _; rw [call_dofile I n p b k h hk hs]; exact e n (by omega)

/-- `require m` of a module given as source and not yet loaded, its chunk `k`: `S.requireK` -/
theorem RunP.require {I : Sem} {m p : List Char} {b : Block} {k : List Val → Nat → M (List Val)} {v : Val}
    {P : List Val → Heap → Prop} (hk : CFn I k ⟨[], true, b, []⟩)
    (hl : rawget LOADED (.str m) h = .ok v h) (hv : v.truthy = false)
    (hn : m ≠ "table.new".toList ∧ m ≠ "table.clear".toList)
    (hp : rawget PACKAGE (lstr "path") h = .ok (.str p) h)
    (hf : (pathFiles p (modPath m)).findSome? I.srcs = some b)
    (r : RunP (S.requireK m ⟨[], true, b, []⟩ k) h P) :
    RunP (fun n => call I.srcs I.oracle I.tgt n (.prim "require" []) [.str m]) h P := by
  obtain ⟨N, a, h', e, q⟩ := RunP.frame r
  refine ⟨N + 3, a, h', fun n hN => ?_, q⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  show call _ _ _ _ _ _ h = _; rw [call_require I n m p b k h v hk hl hv hn hp hf]; exact e n (by omega)

-- ---------- coroutines ----------

/-- `m` suspends: from some fuel on, the running coroutine yields values and a heap satisfying `P` (`Err.yld`); its
resume replays it to there (DESIGN.md, *Coroutines*) -/
def SuspP {α : Type} (m : Nat → M α) (h : Heap) (P : List Val → Heap → Prop) : Prop :=
  ∃ N vs h', (∀ n ≥ N, m n h = .error (.yld vs) h') ∧ P vs h'

theorem SuspP.mono {Q : List Val → Heap → Prop} {P' : List Val → Heap → Prop} (r : SuspP m h Q)
    (hq : ∀ vs h', Q vs h' → P' vs h') : SuspP m h P' := by
  obtain ⟨N, vs, h', e, p⟩ := r; exact ⟨N, vs, h', e, hq _ _ p⟩

/-- what runs after a suspension does not run: the replay runs it -/
theorem SuspP.bind {f : Nat → α → M β} {Q : List Val → Heap → Prop} (r : SuspP m h Q) :
    SuspP (fun n => m n >>= f n) h Q := by
  obtain ⟨N, vs, h', e, p⟩ := r
  exact ⟨N, vs, h', fun n hn => by show EStateM.bind (m n) (f n) h = _; rw [EStateM.bind, e n hn], p⟩

/-- a computation that runs, then one that suspends -/
theorem SuspP.seq {f : Nat → α → M β} {Q : List Val → Heap → Prop}
    (r : RunP m h (fun a h1 => SuspP (fun n => f n a) h1 Q)) : SuspP (fun n => m n >>= f n) h Q := by
  obtain ⟨N, a, h1, e, N2, vs, h2, e2, p⟩ := r
  refine ⟨max N N2, vs, h2, fun n hn => ?_, p⟩
  show EStateM.bind (m n) (f n) h = _
  rw [EStateM.bind, e n (Nat.le_trans (Nat.le_max_left _ _) hn)]
  exact e2 n (Nat.le_trans (Nat.le_max_right _ _) hn)

theorem SuspP.succ {Q : List Val → Heap → Prop} (r : SuspP (fun n => m (n + 1)) h Q) : SuspP m h Q := by
  obtain ⟨N, vs, h', e, p⟩ := r
  exact ⟨N + 1, vs, h', fun n hn => by obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩; exact e k (by omega), p⟩

/-- a yield passes sites, frames and pcall: none of them looks at it -/
theorem SuspP.site {s : Site} {Q : List Val → Heap → Prop} (r : SuspP m h Q) :
    SuspP (fun n => atSite s (m n)) h Q := by
  obtain ⟨N, vs, h', e, p⟩ := r
  exact ⟨N, vs, h', fun n hn => by simp only [atSite, e n hn], p⟩

theorem SuspP.frame {Q : List Val → Heap → Prop} (r : SuspP m h Q) : SuspP (fun n => frame (m n)) h Q := by
  obtain ⟨N, vs, h', e, p⟩ := r
  exact ⟨N, vs, h', fun n hn => by simp only [Lua.frame, e n hn], p⟩

theorem SuspP.catchVal {ok : α → M β} {bad : Val → M β} {Q : List Val → Heap → Prop} (r : SuspP m h Q) :
    SuspP (fun n => catchVal (m n) ok bad) h Q := by
  obtain ⟨N, vs, h', e, p⟩ := r
  exact ⟨N, vs, h', fun n hn => by simp only [Lua.catchVal, e n hn], p⟩

/-- `coroutine.yield(vs)` in coroutine `a` with no resume left to replay, and not inside a builtin calling back: the
coroutine suspends with `vs` -/
theorem SuspP.yield {I : Sem} {a : Nat} {t : Thr Heap} {vs : List Val} (hc : h[CUR]? = some (.cell (.thr a)))
    (ht : h[a]? = some (.thr t)) (hb : t.bound = 0) (hs : t.script = []) :
    SuspP (fun n => call I.srcs I.oracle I.tgt n (.prim "coroutine.yield" []) vs) h (fun ws h' => ws = vs ∧ h' = h) := by
  refine ⟨2, vs, h, fun n hn => ?_, rfl, rfl⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  show call _ _ _ _ _ _ h = _; rw [call_yield]; simp only [Lua.frame, yield_susp hc ht hb hs]

/-- `coroutine.yield` in a replay: the next resume's arguments `ws`, in the heap it went on in, `h1` -/
theorem RunP.yield {I : Sem} {a : Nat} {t t1 : Thr Heap} {vs ws : List Val} {h1 : Heap} {rest : List (List Val × Heap)}
    {P : List Val → Heap → Prop} (hc : h[CUR]? = some (.cell (.thr a))) (ht : h[a]? = some (.thr t))
    (hb : t.bound = 0) (hs : t.script = (ws, h1) :: rest) (ht1 : h1[a]? = some (.thr t1))
    (p : P ws (h1.set! a (.thr { t1 with script := rest }))) :
    RunP (fun n => call I.srcs I.oracle I.tgt n (.prim "coroutine.yield" []) vs) h P := by
  refine ⟨2, ws, _, fun n hn => ?_, p⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  show call _ _ _ _ _ _ h = _; rw [call_yield]; simp only [Lua.frame, yield_replay hc ht hb hs ht1]

/-- a coroutine's run that returns -/
theorem RunP.coRun_ret {m : Nat → M (List Val)} {Q : List Val → Heap → Prop} (r : RunP m h Q) :
    RunP (fun n => coRun (m n)) h (fun o h' => ∃ vs, o = .ok (false, vs) ∧ Q vs h') := by
  obtain ⟨N, vs, h', e, p⟩ := r
  exact ⟨N, _, h', fun n hn => by simp only [coRun, e n hn], vs, rfl, p⟩

/-- a coroutine's run that suspends -/
theorem RunP.coRun_yield {m : Nat → M (List Val)} {Q : List Val → Heap → Prop} (r : SuspP m h Q) :
    RunP (fun n => coRun (m n)) h (fun o h' => ∃ vs, o = .ok (true, vs) ∧ Q vs h') := by
  obtain ⟨N, vs, h', e, p⟩ := r
  exact ⟨N, _, h', fun n hn => by simp only [coRun, e n hn], vs, rfl, p⟩

/-- `coroutine.resume(co, args)` of a coroutine that can be resumed (`resumeBegin`, which gives the heap `h0` its run
starts from): what its run's outcome and `resumeEnd` give -/
theorem RunP.resume {I : Sem} {a : Nat} {args a1 : List Val} {prev f : Val} {hist : List (List Val × Heap)}
    {h0 : Heap} {P : List Val → Heap → Prop}
    (hb : resumeBegin a args h = .ok (.ok (prev, hist, f, a1)) h0)
    (r : RunP (fun n => coRun (call I.srcs I.oracle I.tgt n f a1)) h0
      (fun o h1 => RunP (fun _ => resumeEnd a prev hist o) h1 (fun _ h2 => P (resumeVals o) h2))) :
    RunP (fun n => call I.srcs I.oracle I.tgt n (.prim "coroutine.resume" []) (.thr a :: args)) h P := by
  obtain ⟨N, o, h1, e, N2, u, h2, e2, p⟩ := r
  refine ⟨N + 2, _, h2, fun n hn => ?_, p⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  show call _ _ _ _ _ _ h = _; rw [call_resume]
  have ef : ∀ X : M (List Val), X h = .ok (resumeVals o) h2 → Lua.frame X h = .ok (resumeVals o) h2 :=
    fun X ex => by simp only [Lua.frame, ex]
  apply ef
  rw [bind_ok hb]; dsimp only
  rw [bind_ok (e n (by omega)), bind_ok (e2 N2 (Nat.le_refl _))]; rfl

/-- `coroutine.resume(co, args)` of a coroutine that cannot be: false and LuaJIT's message -/
theorem RunP.resume_fail {I : Sem} {a : Nat} {args : List Val} {m : String} {h0 : Heap} {P : List Val → Heap → Prop}
    (hb : resumeBegin a args h = .ok (.error m) h0) (p : P [.bool false, lstr m] h0) :
    RunP (fun n => call I.srcs I.oracle I.tgt n (.prim "coroutine.resume" []) (.thr a :: args)) h P := by
  refine ⟨2, _, h0, fun n hn => ?_, p⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  show call _ _ _ _ _ _ h = _; rw [call_resume]
  have ef : ∀ X : M (List Val), X h = .ok [.bool false, lstr m] h0 → Lua.frame X h = .ok [.bool false, lstr m] h0 :=
    fun X ex => by simp only [Lua.frame, ex]
  apply ef
  rw [bind_ok hb]; rfl

/-! Operators' metamethods: where the operands are not numbers (or strings, for `..`) and `metaOf2` finds one, the
operator is its call's first value -/

/-- the shape all three share: a metamethod found, then its call -/
private theorem RunP.metaStep {I : Sem} {ev : String} {x y a b f : Val} {err : M Val} {k : Nat → M Val}
    {P : Val → Heap → Prop}
    (hk : ∀ n, k (n + 1) = (do
      match ← metaOf2 ev x y with
      | .nil => err
      | f => do pure ((← mmFrame ev (call I.srcs I.oracle I.tgt n f [a, b])).headD .nil)))
    (hm : metaOf2 ev x y h = .ok f h) (hf : f ≠ .nil)
    (r : RunP (fun n => call I.srcs I.oracle I.tgt n f [a, b]) h fun vs h' => P (vs.headD .nil) h') :
    RunP k h P := by
  obtain ⟨N, vs, h', e, p⟩ := r
  dsimp only at e
  refine ⟨N + 1, vs.headD .nil, h', fun n hn => ?_, p⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hk]
  show EStateM.bind _ _ h = _
  rw [EStateM.bind, hm]
  cases f <;> first | exact (hf rfl).elim | (show EStateM.bind _ _ h = _; rw [EStateM.bind, mmFrame, e n (by omega)]; rfl)

theorem RunP.arith_meta {I : Sem} {op : BinOp} {x y f : Val} {P : Val → Heap → Prop}
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod ∨ op = .pow)
    (hn : x.toNum = none ∨ y.toNum = none) (hm : metaOf2 (arithEv op) x y h = .ok f h) (hf : f ≠ .nil)
    (r : RunP (fun n => call I.srcs I.oracle I.tgt n f [x, y]) h fun vs h' => P (vs.headD .nil) h') :
    RunP (fun n => binop I.srcs I.oracle I.tgt n op x y) h P := by
  refine RunP.metaStep (err := if x.toNum.isNone then opErr "perform arithmetic on" (some 0) x
    else opErr "perform arithmetic on" (some 1) y) (fun n => ?_) hm hf r
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [binop] <;> (try (intro hc; cases hc)) <;> split <;>
    first | rfl | (rcases hn with hn | hn <;> simp_all)

theorem RunP.concat_meta {I : Sem} {x y f : Val} {P : Val → Heap → Prop}
    (hn : concatText x = none ∨ concatText y = none) (hm : metaOf2 "__concat" x y h = .ok f h) (hf : f ≠ .nil)
    (r : RunP (fun n => call I.srcs I.oracle I.tgt n f [x, y]) h fun vs h' => P (vs.headD .nil) h') :
    RunP (fun n => binop I.srcs I.oracle I.tgt n .concat x y) h P := by
  refine RunP.metaStep (err := if (concatText x).isNone then opErr "concatenate" (some 0) x
    else opErr "concatenate" (some 1) y) (fun n => ?_) hm hf r
  rw [binop]; split <;> first | rfl | (rcases hn with hn | hn <;> simp_all)

theorem RunP.unm_meta {I : Sem} {x f : Val} {P : Val → Heap → Prop}
    (hn : x.toNum = none) (hm : metaOf2 "__unm" x x h = .ok f h) (hf : f ≠ .nil)
    (r : RunP (fun n => call I.srcs I.oracle I.tgt n f [x, x]) h fun vs h' => P (vs.headD .nil) h') :
    RunP (fun n => unop I.srcs I.oracle I.tgt n .neg x) h P := by
  refine RunP.metaStep (err := opErr "perform arithmetic on" (some 0) x) (fun n => ?_) hm hf r
  rw [unop]; split <;> first | rfl | simp_all

/-! Comparisons' metamethods (lj_meta_equal, lj_meta_comp) for two tables of one metatable: the comparison is the
truth of the metamethod's first value; `<=` without `__le` is `not (y < x)`. A spec of `tostring` takes its
metamethod's call through `callPrim_tostring` and `RunP.unframe` -/

/-- two tables of one metatable `m` whose `ev` is the function `f` -/
structure SameMeta (h : Heap) (a b m : Nat) (ev : String) (f : Val) : Prop where
  ha : ∃ ta, h[a]? = some (.tbl ta) ∧ ta.mt = some m
  hb : ∃ tb, h[b]? = some (.tbl tb) ∧ tb.mt = some m
  hm : ∃ tm, h[m]? = some (.tbl tm) ∧ tm.get (lstr ev) = f
  hf : ∃ c, f = .fn c

/-- `x == y`: `__eq` -/
theorem RunP.eq_meta {h : Heap} {I : Sem} {a b m : Nat} {f : Val} {P : Bool → Heap → Prop}
    (hab : a ≠ b) (hs : SameMeta h a b m "__eq" f)
    (r : RunP (fun n => call I.srcs I.oracle I.tgt n f [.tbl a, .tbl b]) h fun vs h' => P (vs.headD .nil).truthy h') :
    RunP (fun n => eqv I.srcs I.oracle I.tgt n (.tbl a) (.tbl b)) h P := by
  obtain ⟨⟨ta, ha, hma⟩, ⟨tb, hb, hmb⟩, ⟨tm, hm, rfl⟩, ⟨c, hc⟩⟩ := hs
  obtain ⟨N, vs, h', e, p⟩ := r
  refine ⟨N + 1, _, h', fun n hn => ?_, p⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e := e n (by omega); dsimp only at e ⊢
  have b1 : ∀ {β} (k : Val → M β), (metaOf (.tbl a) "__eq" >>= k) h = k (tm.get (lstr "__eq")) h :=
    fun k => bind_ok (metaOf_ok ha hma hm)
  have b2 : ∀ {β} (k : Val → M β), (metaOf (.tbl b) "__eq" >>= k) h = k (tm.get (lstr "__eq")) h :=
    fun k => bind_ok (metaOf_ok hb hmb hm)
  have b3 : ∀ {β} (k : Tbl → M β), (getTbl a >>= k) h = k ta h := fun k => bind_ok (getTbl_ok ha)
  have b4 : ∀ {β} (k : Tbl → M β), (getTbl b >>= k) h = k tb h := fun k => bind_ok (getTbl_ok hb)
  have b5 : ∀ {β} (k : Val → M β), (metaFn (tm.get (lstr "__eq")) >>= k) h = k (tm.get (lstr "__eq")) h :=
    fun k => bind_ok (by rw [hc]; rfl)
  have b6 : ∀ {β} (k : List Val → M β), (mmFrame "__eq" (call I.srcs I.oracle I.tgt n (tm.get (lstr "__eq"))
      [.tbl a, .tbl b]) >>= k) h = k vs h' := fun k => bind_ok (by simp only [mmFrame]; rw [e])
  rw [eqv.eq_def]; dsimp only
  split
  · next hh => exact absurd (by simpa using hh) hab
  rw [b1]; simp only [hc, Val.isNil, Bool.false_eq_true, ↓reduceIte]; rw [← hc]
  rw [b3, b4, b2]; simp only [hma, hmb, bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; rw [b5, b6]; rfl

/-- `x < y` and `x <= y`: `__lt`, `__le` -/
theorem RunP.lt_meta {h : Heap} {I : Sem} {a b m : Nat} {f : Val} {orEq : Bool} {nm : Option String}
    {P : Bool → Heap → Prop} (hs : SameMeta h a b m (if orEq then "__le" else "__lt") f)
    (r : RunP (fun n => call I.srcs I.oracle I.tgt n f [.tbl a, .tbl b]) h fun vs h' => P (vs.headD .nil).truthy h') :
    RunP (fun n => less I.srcs I.oracle I.tgt n (.tbl a) (.tbl b) orEq nm) h P := by
  obtain ⟨⟨ta, ha, hma⟩, ⟨tb, hb, hmb⟩, ⟨tm, hm, rfl⟩, ⟨c, hc⟩⟩ := hs
  obtain ⟨N, vs, h', e, p⟩ := r
  refine ⟨N + 1, _, h', fun n hn => ?_, p⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e := e n (by omega); dsimp only at e ⊢
  generalize hev : (if orEq then "__le" else "__lt") = ev at hc e
  have b1 : ∀ {β} (k : Val → M β), (metaOf (.tbl a) ev >>= k) h = k (tm.get (lstr ev)) h :=
    fun k => bind_ok (metaOf_ok ha hma hm)
  have b2 : ∀ {β} (k : Val → M β), (metaOf (.tbl b) ev >>= k) h = k (tm.get (lstr ev)) h :=
    fun k => bind_ok (metaOf_ok hb hmb hm)
  have b5 : ∀ {β} (k : Val → M β), (metaFn (tm.get (lstr ev)) >>= k) h = k (tm.get (lstr ev)) h :=
    fun k => bind_ok (by rw [hc]; rfl)
  rw [less.eq_def]; dsimp only
  simp only [Val.typeName, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hev]
  rw [b1]; rw [b2]
  simp only [hc, Val.isNil, Val.rawEq, Bool.not_false, Bool.true_and, beq_self_eq_true, ↓reduceIte]; rw [← hc]
  cases nm <;> dsimp only <;> rw [b5]
  · rw [bind_ok e]; rfl
  · rw [bind_ok (by simp only [mmFrame]; rw [e])]; rfl

/-- `x <= y` without `__le`: `not (y < x)` -/
theorem RunP.le_lt {h : Heap} {I : Sem} {a b m : Nat} {f : Val} {nm : Option String} {P : Bool → Heap → Prop}
    (hs : SameMeta h a b m "__lt" f) (hle : ∃ tm, h[m]? = some (.tbl tm) ∧ tm.get (lstr "__le") = .nil)
    (r : RunP (fun n => call I.srcs I.oracle I.tgt n f [.tbl b, .tbl a]) h fun vs h' => P (!(vs.headD .nil).truthy) h') :
    RunP (fun n => less I.srcs I.oracle I.tgt n (.tbl a) (.tbl b) true nm) h P := by
  have r := RunP.lt_meta (orEq := false) (nm := nm) (P := fun x h' => P (!x) h') ⟨hs.hb, hs.ha, hs.hm, hs.hf⟩ r
  obtain ⟨N, x, h', e, p⟩ := r
  refine ⟨N + 1, _, h', fun n hn => ?_, p⟩
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e := e n (by omega); dsimp only at e ⊢
  obtain ⟨⟨ta, ha, hma⟩, ⟨tb, hb, hmb⟩, ⟨tm, hm, -⟩, -⟩ := hs
  obtain ⟨tm', hm', hle⟩ := hle
  rw [hm] at hm'; cases hm'
  have b1 : ∀ {β} (k : Val → M β), (metaOf (.tbl a) "__le" >>= k) h = k .nil h :=
    fun k => bind_ok (hle ▸ metaOf_ok ha hma hm)
  have b2 : ∀ {β} (k : Val → M β), (metaOf (.tbl b) "__le" >>= k) h = k .nil h :=
    fun k => bind_ok (hle ▸ metaOf_ok hb hmb hm)
  rw [less.eq_def]; dsimp only
  simp only [Val.typeName, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [b1, b2]
  simp only [Val.isNil, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [bind_ok e]; rfl

/-- a builtin's tail call changes only where an error is reported -/
theorem RunP.unframe {α} {m : Nat → M α} {h : Heap} {P : α → Heap → Prop} (r : RunP m h P) :
    RunP (fun n => unframe (m n)) h P := by
  obtain ⟨N, a, h', e, p⟩ := r
  exact ⟨N, a, h', fun n hn => by simp only [Lua.unframe, e n hn], p⟩

end rules

/-- whatever the order (`Tbl.rank` is opaque), `next` gives an entry of the table, one with a value: what a spec
about a traversal can rest on -/
theorem Tbl.next_mem {a : Nat} {t : Tbl} {k k' v : Val} (e : t.next a k = some (some (k', v))) :
    (k', v) ∈ t.kv ∧ v.isNil = false := by
  simp only [Tbl.next] at e
  generalize hl : t.kv.mergeSort _ = l at e
  have hm : ∀ x, x ∈ l → x ∈ t.kv := fun x hx => by rw [← hl] at hx; exact (List.mem_mergeSort).1 hx
  have hr : ∀ r, (if k.isNil then some l else match l.findIdx? (fun (x, _) => Val.rawEq x k) with
      | some i => some (l.drop (i + 1)) | none => none) = some r → ∀ x, x ∈ r → x ∈ t.kv := by
    intro r hr x hx
    split at hr
    · cases hr; exact hm x hx
    · split at hr
      · cases hr; exact hm x (List.mem_of_mem_drop hx)
      · cases hr
  revert e hr
  generalize (if k.isNil then some l else _) = o
  intro e hr
  cases o with
  | none => cases e
  | some r =>
    simp only [Option.map_some, Option.some.injEq] at e
    have := List.find?_some e
    exact ⟨hr r rfl _ (List.mem_of_find?_eq_some e), by simpa using this⟩

/-! ## Effects

A call into the world adds its event to the trace (`trace`, the heap's cell `LOG`); a spec says what a function adds
there, under axioms of the user's about what the world answers (`Oracle`; DESIGN.md, *Effects*). -/

theorem trace_push {h : Heap} (o : Obj) (hs : LOG < h.size) : trace (h.push o) = trace h := by
  simp [trace, Array.getElem?_push, Nat.ne_of_lt hs]

theorem trace_set {h : Heap} (l : List Event) (hs : LOG < h.size) : trace (h.setIfInBounds LOG (.log l)) = l := by
  simp [trace, hs]

theorem effect_ok {o : Oracle} {name : String} {args vs : List Val} {h : Heap} (e : o name args (trace h) = some vs) :
    effect o name args h = .ok vs (h.setIfInBounds LOG (.log (⟨name, args, vs⟩ :: trace h))) := by
  simp [effect, e]

/-- an effect the world answers: its answer, and the trace one event longer -/
theorem RunP.effect {o : Oracle} {name : String} {args vs : List Val} {h : Heap} {P : List Val → Heap → Prop}
    (e : o name args (trace h) = some vs) (p : P vs (h.setIfInBounds LOG (.log (⟨name, args, vs⟩ :: trace h)))) :
    RunP (fun _ => Lua.effect o name args) h P :=
  RunP.const (effect_ok e) p

end Lua
