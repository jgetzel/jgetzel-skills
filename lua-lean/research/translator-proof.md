# One translator-correctness proof for all programs

Board #24. Today `tools/Lift.lean` writes, for each Lua function, a shallow Lean function `f` and a proof `f_ok`
that mirrors it lemma for lemma. The question: can one theorem replace those proofs?

**Answer: yes, and for the whole language, not a fragment.** `LuaLean/Denote.lean` (244 lines) has the translator
as a Lean function `D.fn` and one theorem `D.fn_ok`. `lua-lean lift1` emits the same file as `lift` with each
`f_ok` a one-line use of that theorem. All 83 functions of `test/` and all 385 of the swarm's own Lua modules check
this way. Recommendation: switch `lift` to it (section 5).

## 1. The form the translator takes

A theorem can only quantify over a function inside Lean's logic, and such a function cannot return code with Lean
binders in it: it returns the meaning. So the translator becomes

```lean
def D.fn (I : Sem) (res : String → Option Nat) (c : Clo) : List Val → Nat → M (List Val)
theorem D.fn_ok (I) (res) (c : Clo) (hr : ∀ x, c.env.lookup x = res x) : CFn I (D.fn I res c) c
```

`D.fn` is structural recursion over the syntax tree (`D.exp`, `list`, `fields`, `places`, `stat`, `seq`), one case
per constructor, each case the `Shallow.lean` combinator `Lift.lean` prints today. `D.fn_ok` is the same recursion
over the same tree, each case the `C*_` lemma `Lift.lean` prints today. Nothing in `Shallow.lean` changed.

**The readable shallow code survives.** `D.fn` applied to a concrete body *computes* to exactly the term `lift`
prints: a `local x` is `S.let1 fun c => …` with the rest translated under the binder, so the Lean variable naming
the cell appears by reduction. A per-output step remains, but it is a conversion, not a proof:

```lean
def greet (I : Sem) (env0 : Env) : List Val → Nat → M (List Val) := S.fn fun args n => S.let1 fun c_name => …
theorem greet_ok (I : Sem) (env0 : Env) (h_io : env0.lookup "io" = none) :
    CFn I (greet I env0) ⟨["name"], false, greet_body, env0⟩ :=
  D.fn_ok I (res1 "io" none (fun x => env0.lookup x)) ⟨["name"], false, greet_body, env0⟩ (res1_ok h_io (fun _ => rfl))
```

The statement of `greet_ok` is today's, so users of a lifted file (`Examples/WorldSpec.lean`, `swarm/model`) see no
difference. The term type-checks only if `greet I env0` and `D.fn … greet_body …` are the same by computation; Lean
decides that. The shallow text is still written by the untrusted printer in `Lift.lean`; a wrong one fails (checked:
one `.add` turned into `.sub` in a `lift1` file gives a type mismatch). The trusted base is unchanged.

What had to bend to make it a structural Lean function:

- **Free names.** `env0` is a variable, so `env0.lookup "io"` does not compute. `D.fn` takes `res`, a scope that does
  (`res1 "io" none (res1 "c" (some c_c) …)`), and the hypotheses `h_io`, `h_c` prove once that it is `env0`'s
  (`res1_ok`). Locals extend it (`Sc.bind`).
- **One value or several.** `eval` and `evalMulti` both recurse on the same expression, and "a single expression is
  `[eval e]`" does not decrease. `D.exp` returns the pair.
- **`repeat`'s condition and `local`'s scope** are passed to `seq` as continuations over the scope.
- **Catch-all cases** (`st :: rest` when `st` is not a declaration) are proved by `cases`, since a catch-all gives
  no negative information.

Other shapes, not built: `def f := D.fn …` with no printed shallow form and Lean asked to unfold it (drops the
printer, about half of `Lift.lean`, but error messages and file diffs get worse), or specs proved against `D.fn`
directly. Neither is needed to get the benefit.

## 2. The prototype

`LuaLean/Denote.lean`: `res1`, `Sc`, `D.lets`, the mutual `D.exp … D.seq`, `D.fn`, and the proofs. No `sorry`, no
axiom; it is in the library, so `Audit.lean` covers it. The task asked for the expression fragment; every case had
its lemma already, so it covers every construct `Lift.lean` does (calls, loops, `goto`, closures, varargs, `load`).

`lua-lean lift1 f.lua` writes the module, `lua-lean prove1 f.lua...` checks it. `check.sh` runs
`prove1 test/stmts.lua`, the script with every statement form.

## 3. Measured cost

`research/measure.sh` (run from `lua-lean/`, `lake` and `bc` on the PATH), Lean 4.35, one run each on a shared
machine, so differences under 20% are noise. "Check" is `lean` on the lifted file and includes about 0.3 s to
import the library. Lifting is the same program in both modes: about 1.3 s per file, nearly all of it Lean starting.

| Corpus | Functions | Check today | Check, one theorem | Bytes today | Bytes, one theorem |
|---|---|---|---|---|---|
| `test/*.lua`, `test/mods/*.lua` (22 files) | 83 | 10.9 s | 12.0 s | 315 KB | 267 KB |
| `swarm/lua/swarm/*.lua` (21 files, 5308 lines) | 385 | 155.4 s | 87.5 s | 4.89 MB | 4.15 MB |

Per function on the swarm's modules: 0.40 s and 12.7 KB today, 0.23 s and 10.8 KB with the one theorem. The file
shrinks only 15% because the proof was a quarter of it: on `test/` the bodies are 37%, the shallow functions 36%,
the theorems 25% (78 KB, down to 29 KB, most of the rest being their statements).

Small files are a wash. The difference is in functions with many locals. Today's proof gets much slower with every
local in scope, the one theorem's much less so (one function, n times `local x = …; if … end`):

| Locals in one function | Check today | Check, one theorem |
|---|---|---|
| 12 | 1.7 s | 1.8 s |
| 50 | 12–35 s | 2–3 s |
| 100 | 77–89 s | 5–6 s |
| 200 | stopped after 10 min at 11 GB | 15 s |
| 400 | not run | 46 s |

That is where the swarm's slow files come from: `run.lua` 34.6 s → 8.0 s, `state.lua` 30.4 s → 6.7 s, `main.lua`
8.6 s → 3.2 s. The cause was not investigated; a likely one is that every lemma in the mirrored proof carries the
whole environment as an implicit argument.

## 4. What a semantics change costs

Over the history, 6 of the 12 commits that changed `Interp.lean` also changed `Lift.lean`, and 8 changed
`Shallow.lean`.

| Change | Today | With the one theorem |
|---|---|---|
| Inside `index`, `call`, `binop`, a builtin (metamethods, the library: most of G3, G4) | nothing | nothing |
| A clause of `eval`/`exec*` changes shape | combinator and lemma in `Shallow.lean`; the two strings in `Lift.lean` | the same combinator and lemma; the shallow string in `Lift.lean`; usually nothing in `Denote.lean` (it only names the combinator) |
| A new syntax node | combinator, lemma, a case in `Lift.lean` (a forgotten one shows up when a script uses it) | combinator, lemma, a case in `D.*` and one in its `_ok`: two lines, and Lean refuses to build the library without them |
| Scoping changes (function environments for `setfenv`) | `Ent`, `lookupPf`, `CE_cell`/`CE_glob` | `Sc`, `res1`, `bind_ok`, `lets_ok`, `var_ok`: about 30 lines to revisit |
| Later stages (G7 heap abstraction) | per-function proofs | still per-function proofs: what can be abstracted depends on facts about each function. The one theorem covers this first stage only |

Two costs are new. The mutual block is structural recursion over a nested inductive, which Lean accepts as written
but which is the kind of definition a new nesting (say a list of pairs in a node) can make it reject; the fix is
then local but not obvious. And the printer must keep printing exactly what `D.fn` computes; a drift is caught at
once (every lifted file fails), never silently.

## 5. Recommendation

**Do it, for the whole language.** Switch `lift` to emit `D.fn_ok` and delete the proof-printing half of
`tools/Lift.lean`. It is no fragment and no rewrite: the theorem is proved, the statements users see are
unchanged, real modules check in about half the time, and functions today's proofs cannot handle (200 locals)
check in seconds. Board #38 is that switch: `lift` and `prove` through the one theorem, `Examples/World.lean` and
`swarm/model`'s `Lifted/` regenerated, `lift1`/`prove1` removed, DESIGN.md's translator and trust paragraphs
updated.

Not recommended now: dropping the printed shallow form. It would save more code but costs readability for no
measured gain.
