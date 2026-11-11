/-! locks.lua's lock patterns lifted: `tokens`, `one`, `meet`, `covers`, `overlaps`, line for line with the Lua
(a Lua string is its bytes; here, a list of `Char`s below 256). `fix` is `Cfg.lockForms`: false is the Lua before
board #26. Recursion runs on fuel so `decide` evaluates it; `meet`'s fuel is the Lua's memo table's size.

The glob semantics is `gm`, the textbook matcher (no FNM_PATHNAME: `*` and `?` match `/`). Proved, with the fix on:
`covers_iff` (covers is the pattern's forms: itself, its glob, and, with no `*`, `?` or `[` in it, everything under
it as a directory), `overlaps_iff` (overlaps is exactly "some path both cover"). `../lua/test/locks_model_spec.lua` checks the Lua
against these functions, and `gm` against fnmatch, on random patterns (`GlobCases.lean`). -/

namespace Swarm.Glob

/-- a glob token: `*`, `?`, one character, or a `[...]` class (its text, without the brackets) -/
inductive Tok where | star | any | ch (c : Char) | set (s : List Char)
  deriving DecidableEq, Repr, Inhabited

/-- a [...] class's text: a leading ! or ^ negates, x-y is a range, anything else is itself -/
def inSet (s : List Char) (c : Char) : Bool :=
  match s with
  | '!' :: b | '^' :: b => !mem b
  | b => mem b
where mem : List Char → Bool
  | x :: '-' :: y :: r => (x ≤ c && c ≤ y) || mem r
  | x :: r => x == c || mem r
  | [] => false

/-- the one character a token other than `*` matches -/
def single : Tok → Char → Bool
  | .any, _ => true
  | .ch d, c => d == c
  | .set s, c => inSet s c
  | .star, _ => false

def lit (s : List Char) : List Tok := s.map .ch
def strip (s : List Char) : List Char := (s.reverse.dropWhile (· == '/')).reverse
/-- the pattern as a directory: a literal prefix, then anything -/
def dir (pat : List Char) : List Tok := lit (strip pat ++ ['/']) ++ [.star]

/-- the glob form; `r` is the tokens so far, last first; `n` is fuel -/
def tokensGo (fix : Bool) : Nat → List Char → List Tok → List Tok
  | 0, _, r | _, [], r => r.reverse
  | n + 1, '*' :: s, r => tokensGo fix n s (if r.head? == some .star then r else .star :: r)
  | n + 1, '?' :: s, r => tokensGo fix n s (.any :: r)
  | n + 1, '[' :: s, r =>
    -- the class ends at the first `]` after one character, or (fix) after the negation and one character
    let k := if fix && (s.head? == some '!' || s.head? == some '^') then 2 else 1
    match (s.drop k).idxOf? ']' with
    | some m => tokensGo fix n (s.drop (k + m + 1)) (.set (s.take (k + m)) :: r)
    | none => tokensGo fix n s (.ch '[' :: r)
  | n + 1, '\\' :: c :: s, r => tokensGo fix n s (.ch c :: r)
  | n + 1, c :: s, r => tokensGo fix n s (.ch c :: r)

def tokens (fix : Bool) (pat : List Char) : List Tok := tokensGo fix (pat.length + 1) pat []

/-- whether two single-character tokens match a common byte -/
def oneExact (a b : Tok) : Bool :=
  match a, b with
  | .ch c, _ => single b c
  | _, .ch c => single a c
  | _, _ => (List.range 256).any fun k => single a (Char.ofNat k) && single b (Char.ofNat k)
/-- before the fix: a `?`, or two classes, always met -/
def oneOld (a b : Tok) : Bool :=
  match a, b with
  | .any, _ | _, .any => true
  | .ch c, .ch d => c == d
  | .set _, .set _ => true
  | .set s, .ch c => inSet s c
  | .ch c, .set s => inSet s c
  | _, _ => false
def one (fix : Bool) (a b : Tok) : Bool := if fix then oneExact a b else oneOld a b

/-- whether some string both token lists match; `n` is fuel -/
def meetF (fix : Bool) : Nat → List Tok → List Tok → Bool
  | 0, _, _ => false
  | n + 1, .star :: p, [] => meetF fix n p []
  | n + 1, .star :: p, b :: q => meetF fix n p (b :: q) || ((!fix || b == .star || one fix b b) && meetF fix n (.star :: p) q)
  | _ + 1, [], [] => true
  | n + 1, [], .star :: q => meetF fix n [] q
  | n + 1, a :: p, .star :: q => meetF fix n (a :: p) q || ((!fix || one fix a a) && meetF fix n p (.star :: q))
  | _ + 1, [], _ :: _ | _ + 1, _ :: _, [] => false
  | n + 1, a :: p, b :: q => one fix a b && meetF fix n p q

def meet (fix : Bool) (p q : List Tok) : Bool := meetF fix (p.length + q.length + 1) p q

/-- has a `*`, `?` or `[`: then the pattern is a glob only, not also a directory -/
def isGlob (x : List Char) : Bool := x.any fun c => c == '*' || c == '?' || c == '['

/-- locks.covers(path, pat): the path is the pattern, or the glob matches it, or it is under the pattern as a
directory; before the fix, a glob was a directory too (`m/*.lua` covered `m/*.lua/a.txt`), and the Lua asked fnmatch
for the glob, which reads escapes and odd brackets otherwise (README.md, Lifted) -/
def covers (fix : Bool) (x pat : List Char) : Bool :=
  x == pat || meet true (tokens true pat) (lit x) || ((!fix || !isGlob pat) && (strip pat ++ ['/']).isPrefixOf x)

/-- the token lists of covers' forms; before the fix, overlaps left out the literal form and a glob's
directory form -/
def forms (fix : Bool) (x : List Char) : List (List Tok) :=
  if fix then [lit x, tokens true x] ++ (if isGlob x then [] else [dir x])
  else if isGlob x then [tokens false x] else [tokens false x, dir x]

/-- locks.overlaps: some path both patterns cover -/
def overlaps (fix : Bool) (p q : List Char) : Bool :=
  (forms fix p).any fun x => (forms fix q).any fun y => meet fix x y

/-- the glob semantics: whether tokens `p` match all of `w` -/
def gm : List Tok → List Char → Bool
  | [], w => w.isEmpty
  | .star :: p, [] => gm p []
  | .star :: p, c :: w => gm p (c :: w) || gm (.star :: p) w
  | _ :: _, [] => false
  | t :: p, c :: w => single t c && gm p w
termination_by p w => p.length + w.length

-- ---------- proofs, with the fix on ----------

/-- a Lua string's character: one byte -/
def Byte (c : Char) : Prop := c.toNat < 256
def Bytes (w : List Char) : Prop := ∀ c ∈ w, Byte c
def TB : Tok → Prop | .ch c => Byte c | _ => True
def TBs (p : List Tok) : Prop := ∀ t ∈ p, TB t

theorem bytes_cons {c : Char} {w : List Char} : Bytes (c :: w) ↔ Byte c ∧ Bytes w := by simp [Bytes]
theorem tbs_cons {t : Tok} {p : List Tok} : TBs (t :: p) ↔ TB t ∧ TBs p := by simp [TBs]
theorem tbs_append {p q : List Tok} : TBs (p ++ q) ↔ TBs p ∧ TBs q := by
  simp only [TBs, List.mem_append]; exact ⟨fun h => ⟨fun t ht => h t (.inl ht), fun t ht => h t (.inr ht)⟩,
    fun h t ht => ht.elim (h.1 t) (h.2 t)⟩
theorem tbs_lit {s : List Char} (h : Bytes s) : TBs (lit s) := by
  intro t ht; simp only [lit, List.mem_map] at ht; obtain ⟨c, hc, rfl⟩ := ht; exact h c hc

theorem byte_ofNat {k : Nat} (h : k < 256) : Byte (Char.ofNat k) := by
  unfold Byte Char.ofNat; split
  · simp [Char.ofNatAux, Char.toNat]; omega
  · simp

-- ---------- one ----------

theorem one_sound {a b : Tok} (h : one true a b = true) :
    ∃ c, single a c = true ∧ single b c = true ∧ (TB a → TB b → Byte c) := by
  simp only [one, ite_true, oneExact] at h
  split at h
  · next c => exact ⟨c, by simp [single], h, fun ha _ => ha⟩
  · next c _ => exact ⟨c, h, by simp [single], fun _ hb => hb⟩
  · obtain ⟨k, hk, h⟩ := List.any_eq_true.mp h
    simp only [List.mem_range, Bool.and_eq_true] at hk h
    exact ⟨Char.ofNat k, h.1, h.2, fun _ _ => byte_ofNat hk⟩

theorem one_complete {a b : Tok} {c : Char} (hc : Byte c) (ha : single a c = true) (hb : single b c = true) :
    one true a b = true := by
  simp only [one, ite_true, oneExact]
  split
  · next d => simp [single] at ha; subst ha; exact hb
  · next d _ => simp [single] at hb; subst hb; exact ha
  · exact List.any_eq_true.mpr ⟨c.toNat, List.mem_range.mpr hc, by simp [ha, hb]⟩

-- ---------- meet and gm, one clause at a time ----------

section
variable {n : Nat} {a b t : Tok} {p q : List Tok} {c : Char} {w : List Char}
theorem meetF_s_nil : meetF true (n + 1) (.star :: p) [] = meetF true n p [] := by simp [meetF]
theorem meetF_s_cons : meetF true (n + 1) (.star :: p) (b :: q) =
    (meetF true n p (b :: q) || ((b == .star || one true b b) && meetF true n (.star :: p) q)) := by simp [meetF]
theorem meetF_nil_s : meetF true (n + 1) [] (.star :: q) = meetF true n [] q := by simp [meetF]
theorem meetF_t_s (ha : a ≠ .star) : meetF true (n + 1) (a :: p) (.star :: q) =
    (meetF true n (a :: p) q || (one true a a && meetF true n p (.star :: q))) := by
  rw [meetF.eq_6 _ _ _ _ _ ha]; simp
theorem meetF_nil_t (hb : b ≠ .star) : meetF true (n + 1) [] (b :: q) = false := by cases b <;> simp_all [meetF]
theorem meetF_t_nil (ha : a ≠ .star) : meetF true (n + 1) (a :: p) [] = false := by cases a <;> simp_all [meetF]
theorem meetF_t_t (ha : a ≠ .star) (hb : b ≠ .star) : meetF true (n + 1) (a :: p) (b :: q) =
    (one true a b && meetF true n p q) := by cases a <;> cases b <;> simp_all [meetF]

theorem gm_nil : gm [] w = w.isEmpty := by simp [gm]
theorem gm_s_nil : gm (.star :: p) [] = gm p [] := by simp [gm]
theorem gm_s_cons : gm (.star :: p) (c :: w) = (gm p (c :: w) || gm (.star :: p) w) := by rw [gm]
theorem gm_t_nil (ht : t ≠ .star) : gm (t :: p) [] = false := by cases t <;> simp_all [gm]
theorem gm_t_cons (ht : t ≠ .star) : gm (t :: p) (c :: w) = (single t c && gm p w) := gm.eq_5 _ _ _ _ ht
theorem gm_star_of (h : gm p w = true) : gm (.star :: p) w = true := by
  cases w with
  | nil => rw [gm_s_nil]; exact h
  | cons c w => rw [gm_s_cons, h]; rfl
end

/-- meet: some string both match -/
theorem meetF_sound : ∀ (n : Nat) (p q : List Tok), meetF true n p q = true →
    ∃ w, gm p w = true ∧ gm q w = true ∧ (TBs p → TBs q → Bytes w) := by
  intro n
  induction n with
  | zero => intro p q h; simp [meetF] at h
  | succ n ih =>
    intro p q h
    rcases p with _ | ⟨a, p⟩ <;> rcases q with _ | ⟨b, q⟩
    · exact ⟨[], by simp [gm_nil], by simp [gm_nil], fun _ _ c hc => by simp at hc⟩
    · by_cases hb : b = .star
      · subst hb; rw [meetF_nil_s] at h
        obtain ⟨w, h1, h2, hB⟩ := ih _ _ h
        exact ⟨w, h1, gm_star_of h2, fun hp hq => hB hp (tbs_cons.mp hq).2⟩
      · rw [meetF_nil_t hb] at h; cases h
    · by_cases ha : a = .star
      · subst ha; rw [meetF_s_nil] at h
        obtain ⟨w, h1, h2, hB⟩ := ih _ _ h
        exact ⟨w, gm_star_of h1, h2, fun hp hq => hB (tbs_cons.mp hp).2 hq⟩
      · rw [meetF_t_nil ha] at h; cases h
    · by_cases ha : a = .star
      · subst ha; rw [meetF_s_cons] at h
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with h | ⟨hg, h⟩
        · obtain ⟨w, h1, h2, hB⟩ := ih _ _ h
          exact ⟨w, gm_star_of h1, h2, fun hp hq => hB (tbs_cons.mp hp).2 hq⟩
        · obtain ⟨w, h1, h2, hB⟩ := ih _ _ h
          by_cases hb : b = .star
          · subst hb; exact ⟨w, h1, gm_star_of h2, fun hp hq => hB hp (tbs_cons.mp hq).2⟩
          · have hbb : one true b b = true := by simpa [hb] using hg
            obtain ⟨c, hc, -, hcB⟩ := one_sound hbb
            refine ⟨c :: w, by rw [gm_s_cons, h1]; simp, by rw [gm_t_cons hb, hc, h2]; rfl, fun hp hq => ?_⟩
            have hq' := tbs_cons.mp hq
            exact bytes_cons.mpr ⟨hcB hq'.1 hq'.1, hB hp hq'.2⟩
      · by_cases hb : b = .star
        · subst hb; rw [meetF_t_s ha] at h
          simp only [Bool.or_eq_true, Bool.and_eq_true] at h
          rcases h with h | ⟨hg, h⟩
          · obtain ⟨w, h1, h2, hB⟩ := ih _ _ h
            exact ⟨w, h1, gm_star_of h2, fun hp hq => hB hp (tbs_cons.mp hq).2⟩
          · obtain ⟨w, h1, h2, hB⟩ := ih _ _ h
            obtain ⟨c, hc, -, hcB⟩ := one_sound hg
            refine ⟨c :: w, by rw [gm_t_cons ha, hc, h1]; rfl, by rw [gm_s_cons, h2]; simp, fun hp hq => ?_⟩
            have hp' := tbs_cons.mp hp
            exact bytes_cons.mpr ⟨hcB hp'.1 hp'.1, hB hp'.2 hq⟩
        · rw [meetF_t_t ha hb] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨c, hca, hcb, hcB⟩ := one_sound h.1
          obtain ⟨w, h1, h2, hB⟩ := ih _ _ h.2
          refine ⟨c :: w, by rw [gm_t_cons ha, hca, h1]; rfl, by rw [gm_t_cons hb, hcb, h2]; rfl, fun hp hq => ?_⟩
          have hp' := tbs_cons.mp hp; have hq' := tbs_cons.mp hq
          exact bytes_cons.mpr ⟨hcB hp'.1 hq'.1, hB hp'.2 hq'.2⟩

theorem meetF_complete : ∀ (n : Nat) (p q : List Tok) (w : List Char), p.length + q.length < n → Bytes w →
    gm p w = true → gm q w = true → meetF true n p q = true := by
  intro n
  induction n with
  | zero => intro p q w hl; omega
  | succ n ih =>
    intro p q w hl hw hp hq
    rcases p with _ | ⟨a, p⟩ <;> rcases q with _ | ⟨b, q⟩
    · simp [meetF]
    · rw [gm_nil] at hp; cases w with
      | cons => simp at hp
      | nil =>
        by_cases hb : b = .star
        · subst hb; rw [meetF_nil_s]; rw [gm_s_nil] at hq
          exact ih _ _ [] (by simp at hl ⊢; omega) hw (by simp [gm_nil]) hq
        · rw [gm_t_nil hb] at hq; cases hq
    · rw [gm_nil] at hq; cases w with
      | cons => simp at hq
      | nil =>
        by_cases ha : a = .star
        · subst ha; rw [meetF_s_nil]; rw [gm_s_nil] at hp
          exact ih _ _ [] (by simp at hl ⊢; omega) hw hp (by simp [gm_nil])
        · rw [gm_t_nil ha] at hp; cases hp
    · simp only [List.length_cons] at hl
      by_cases ha : a = .star <;> by_cases hb : b = .star
      · subst ha hb; rw [meetF_s_cons]
        have key : ∀ w, Bytes w → gm (.star :: p) w = true → gm (.star :: q) w = true →
            meetF true n p (.star :: q) = true ∨ meetF true n (.star :: p) q = true := by
          intro w
          induction w with
          | nil =>
            intro hw h1 _; rw [gm_s_nil] at h1
            exact .inr (ih _ _ [] (by simp; omega) hw (gm_star_of h1) (by rw [gm_s_nil] at *; assumption))
          | cons c w iw =>
            intro hw h1 h2
            by_cases e1 : gm p (c :: w) = true
            · exact .inl (ih _ _ _ (by simp; omega) hw e1 h2)
            by_cases e2 : gm q (c :: w) = true
            · exact .inr (ih _ _ _ (by simp; omega) hw h1 e2)
            rw [gm_s_cons] at h1 h2
            simp [e1] at h1; simp [e2] at h2
            exact iw (bytes_cons.mp hw).2 h1 h2
        rcases key w hw hp hq with h | h <;> simp [h]
      · subst ha; rw [meetF_s_cons]
        cases w with
        | nil => rw [gm_t_nil hb] at hq; cases hq
        | cons c w =>
          by_cases e1 : gm p (c :: w) = true
          · simp [ih _ _ _ (by simp; omega) hw e1 hq]
          rw [gm_s_cons] at hp; simp [e1] at hp
          rw [gm_t_cons hb] at hq; simp only [Bool.and_eq_true] at hq
          have hc := (bytes_cons.mp hw)
          simp [one_complete hc.1 hq.1 hq.1, ih _ _ _ (by simp; omega) hc.2 hp hq.2]
      · subst hb; rw [meetF_t_s ha]
        cases w with
        | nil => rw [gm_t_nil ha] at hp; cases hp
        | cons c w =>
          by_cases e2 : gm q (c :: w) = true
          · simp [ih _ _ _ (by simp; omega) hw hp e2]
          rw [gm_s_cons] at hq; simp [e2] at hq
          rw [gm_t_cons ha] at hp; simp only [Bool.and_eq_true] at hp
          have hc := (bytes_cons.mp hw)
          simp [one_complete hc.1 hp.1 hp.1, ih _ _ _ (by simp; omega) hc.2 hp.2 hq]
      · rw [meetF_t_t ha hb]
        cases w with
        | nil => rw [gm_t_nil ha] at hp; cases hp
        | cons c w =>
          rw [gm_t_cons ha] at hp; rw [gm_t_cons hb] at hq
          simp only [Bool.and_eq_true] at hp hq
          have hc := (bytes_cons.mp hw)
          simp [one_complete hc.1 hp.1 hq.1, ih _ _ _ (by omega) hc.2 hp.2 hq.2]

theorem meet_sound {p q : List Tok} (h : meet true p q = true) :
    ∃ w, gm p w = true ∧ gm q w = true ∧ (TBs p → TBs q → Bytes w) := meetF_sound _ _ _ h
theorem meet_complete {p q : List Tok} {w : List Char} (hw : Bytes w) (hp : gm p w = true) (hq : gm q w = true) :
    meet true p q = true := meetF_complete _ _ _ w (by omega) hw hp hq

-- ---------- the forms ----------

theorem gm_lit {s w : List Char} : gm (lit s) w = true ↔ w = s := by
  induction s generalizing w with
  | nil => cases w <;> simp [lit, gm_nil]
  | cons c s ih =>
    cases w with
    | nil => simp [lit, gm_t_nil]
    | cons d w =>
      simp only [lit, List.map_cons] at ih ⊢
      rw [gm_t_cons (by simp)]
      simp only [single, Bool.and_eq_true, beq_iff_eq, ih, List.cons.injEq]
      exact ⟨fun h => ⟨h.1.symm, h.2⟩, fun h => ⟨h.1.symm, h.2⟩⟩

theorem gm_star_all {w : List Char} : gm [.star] w = true := by
  induction w with
  | nil => simp [gm_s_nil, gm_nil]
  | cons c w ih => rw [gm_s_cons, ih]; simp

theorem gm_dir {s w : List Char} : gm (lit s ++ [.star]) w = s.isPrefixOf w := by
  induction s generalizing w with
  | nil => simp [lit, gm_star_all]
  | cons c s ih =>
    cases w with
    | nil => simp [lit, gm_t_nil]
    | cons d w =>
      simp only [lit, List.map_cons, List.cons_append] at ih ⊢
      rw [gm_t_cons (by simp), ih, List.isPrefixOf_cons_cons]; simp [single]

theorem tbs_tokensGo (fix : Bool) (n : Nat) (s : List Char) (r : List Tok) (hs : Bytes s) (hr : TBs r) :
    TBs (tokensGo fix n s r) := by
  fun_induction tokensGo fix n s r with
  | case1 | case2 => intro t ht; exact hr t (List.mem_reverse.mp ht)
  | case3 _ _ _ ih => exact ih (bytes_cons.mp hs).2 (by split; exact hr; exact tbs_cons.mpr ⟨trivial, hr⟩)
  | case4 _ _ _ ih => exact ih (bytes_cons.mp hs).2 (tbs_cons.mpr ⟨trivial, hr⟩)
  | case5 _ _ _ _ _ _ ih =>
    exact ih (fun c hc => (bytes_cons.mp hs).2 c (List.mem_of_mem_drop hc)) (tbs_cons.mpr ⟨trivial, hr⟩)
  | case6 _ _ _ _ _ ih => exact ih (bytes_cons.mp hs).2 (tbs_cons.mpr ⟨by simp [TB, Byte], hr⟩)
  | case7 _ _ _ _ ih =>
    have h := (bytes_cons.mp (bytes_cons.mp hs).2)
    exact ih h.2 (tbs_cons.mpr ⟨h.1, hr⟩)
  | case8 _ _ _ _ _ _ _ _ ih =>
    have h := bytes_cons.mp hs
    exact ih h.2 (tbs_cons.mpr ⟨h.1, hr⟩)

theorem tbs_forms {s : List Char} (h : Bytes s) : ∀ f ∈ forms true s, TBs f := by
  have hd : TBs (dir s) := tbs_append.mpr ⟨tbs_lit (fun c hc => by
      simp only [strip, List.mem_append, List.mem_reverse, List.mem_singleton] at hc
      rcases hc with hc | rfl
      · exact h c (List.mem_reverse.mp (List.dropWhile_subset _ hc))
      · simp [Byte]), fun t ht => by simp at ht; subst ht; trivial⟩
  intro f hf
  unfold forms at hf
  have ht : TBs (tokens true s) := tbs_tokensGo _ _ _ _ h (by simp [TBs])
  cases hG : isGlob s <;> simp [hG] at hf <;> rcases hf with rfl | rfl | rfl
  all_goals first | exact tbs_lit h | exact ht | exact hd

/-- covers is its forms: the pattern itself, its glob, and (a pattern with no `*`, `?`, `[`) everything under it -/
theorem covers_eq {x pat : List Char} (hx : Bytes x) : covers true x pat = (forms true pat).any (gm · x) := by
  have hl : gm (lit pat) x = (x == pat) := by rw [Bool.eq_iff_iff, gm_lit]; simp
  have hg : meet true (tokens true pat) (lit x) = gm (tokens true pat) x := by
    rw [Bool.eq_iff_iff]; constructor
    · intro h; obtain ⟨w, h1, h2, -⟩ := meet_sound h; rw [gm_lit.mp h2] at h1; exact h1
    · intro h; exact meet_complete hx h (gm_lit.mpr rfl)
  have hd : gm (dir pat) x = (strip pat ++ ['/']).isPrefixOf x := gm_dir
  unfold covers forms
  cases isGlob pat <;> simp [hl, hg, hd, Bool.or_assoc]

theorem covers_iff {x pat : List Char} (hx : Bytes x) :
    covers true x pat = true ↔ ∃ f ∈ forms true pat, gm f x = true := by
  rw [covers_eq hx, List.any_eq_true]

/-- overlaps: exactly when some path is covered by both patterns -/
theorem overlaps_iff {p q : List Char} (hp : Bytes p) (hq : Bytes q) :
    overlaps true p q = true ↔ ∃ x, Bytes x ∧ covers true x p = true ∧ covers true x q = true := by
  simp only [overlaps, List.any_eq_true]
  constructor
  · rintro ⟨f, hf, g, hg, h⟩
    obtain ⟨w, h1, h2, hB⟩ := meet_sound h
    have hw := hB (tbs_forms hp f hf) (tbs_forms hq g hg)
    exact ⟨w, hw, (covers_iff hw).mpr ⟨f, hf, h1⟩, (covers_iff hw).mpr ⟨g, hg, h2⟩⟩
  · rintro ⟨x, hx, h1, h2⟩
    obtain ⟨f, hf, h1⟩ := (covers_iff hx).mp h1
    obtain ⟨g, hg, h2⟩ := (covers_iff hx).mp h2
    exact ⟨f, hf, g, hg, meet_complete hx h1 h2⟩

/-- the half S3 needs, for any patterns: a path both cover makes overlaps true -/
theorem overlaps_complete {p q x : List Char} (hx : Bytes x) (h1 : covers true x p = true)
    (h2 : covers true x q = true) : overlaps true p q = true := by
  obtain ⟨f, hf, h1⟩ := (covers_iff hx).mp h1
  obtain ⟨g, hg, h2⟩ := (covers_iff hx).mp h2
  simp only [overlaps, List.any_eq_true]
  exact ⟨f, hf, g, hg, meet_complete hx h1 h2⟩

/-- Board #26 asked for "covers p q iff every path matching q matches p". False either way round: covers takes a
path and a pattern, and a path is not a pattern (`m/b.lua` matches `m/*.lua` but isn't `m/a.lua`; `m/a.lua/x` is
under `m/a.lua` but doesn't end in `.lua`). `covers_iff` is what holds. -/
theorem covers_not_subsumed : ¬ ∀ p q : List Char,
    covers true p q = true ↔ ∀ x, covers true x q = true → covers true x p = true := fun h =>
  absurd ((h "m/a.lua".toList "m/*.lua".toList).mp (by decide) "m/b.lua".toList (by decide)) (by decide)
theorem covers_not_subsumes : ¬ ∀ p q : List Char,
    covers true p q = true ↔ ∀ x, covers true x p = true → covers true x q = true := fun h =>
  absurd ((h "m/a.lua".toList "m/*.lua".toList).mp (by decide) "m/a.lua/x".toList (by decide)) (by decide)

-- ---------- symmetry ----------

theorem oneExact_comm (a b : Tok) : oneExact a b = oneExact b a := by
  cases a <;> cases b <;> simp [oneExact, single, Bool.and_comm, Bool.beq_comm]

theorem meetF_comm : ∀ (n : Nat) (p q : List Tok), meetF true n p q = meetF true n q p := by
  intro n
  induction n with
  | zero => intro p q; rfl
  | succ n ih =>
    intro p q
    have h1 : ∀ a, one true a a = oneExact a a := fun _ => rfl
    rcases p with _ | ⟨a, p⟩ <;> rcases q with _ | ⟨b, q⟩
    · rfl
    · by_cases hb : b = .star
      · subst hb; rw [meetF_nil_s, meetF_s_nil, ih]
      · rw [meetF_nil_t hb, meetF_t_nil hb]
    · by_cases ha : a = .star
      · subst ha; rw [meetF_nil_s, meetF_s_nil, ih]
      · rw [meetF_nil_t ha, meetF_t_nil ha]
    · by_cases ha : a = .star <;> by_cases hb : b = .star
      · subst ha hb; rw [meetF_s_cons, meetF_s_cons, ih p, ih (.star :: p)]; simp [Bool.or_comm]
      · subst ha; rw [meetF_s_cons, meetF_t_s hb, ih p, ih (.star :: p), beq_false_of_ne hb, Bool.false_or]
      · subst hb; rw [meetF_s_cons, meetF_t_s ha, ih q, ih (.star :: q), beq_false_of_ne ha, Bool.false_or]
      · rw [meetF_t_t ha hb, meetF_t_t hb ha, ih p]; simp [one, oneExact_comm]

theorem overlaps_comm (p q : List Char) : overlaps true p q = overlaps true q p := by
  rw [Bool.eq_iff_iff]; simp only [overlaps, List.any_eq_true]
  have hm : ∀ x y, meet true x y = meet true y x := fun x y => by
    simp only [meet]; rw [meetF_comm, Nat.add_comm x.length]
  constructor <;> rintro ⟨f, hf, g, hg, h⟩ <;> exact ⟨g, hg, f, hf, by rw [hm]; exact h⟩

end Swarm.Glob
