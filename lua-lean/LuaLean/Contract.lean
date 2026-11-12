import LuaLean.Denote
import LuaLean.Hoare
import LuaLean.FrameCall

/-! The spec a reviewer of lua-lean reads (board #88), written to `../swarm/model/STYLE.md`: the statements a proof
about a lifted script builds on, each after the definitions it needs, each proof a reference to the module that owns
it. A reviewer reads this file and the definitions it shows or names, not the proofs. Every statement is about the
semantics `Interp.lean` runs, for every `I : Sem`: any source files, any oracle (the world answers what it will) and
both LuaJIT builds (`Target`). That this semantics is LuaJIT's is not a theorem: it is tested (DESIGN.md, *Trust*),
and what a spec assumes of the world is the user's, one named hypothesis each, never bundled (the last section).

Names: `I` the semantics' parameters, `h` a heap, `a` an address, `c` a closure, `args` a call's arguments, `n` the
fuel, `f` a lifted function, `cell` the address of a heap cell, `P` what a result or a cell's value satisfies. -/

namespace Lua

/-! ## What the lifting guarantees

`lua-lean lift` writes, for each function of a script, `f` (a Lean function) and `f_ok : CFn I (f I env0 fn0) fn0 clo`,
proved by `D.fn_ok` at the closure: Lean's kernel accepts that proof only if `f` computes to `D.fn`'s result, so the
printer is not trusted (DESIGN.md, *Trust*). The reviewer reads `CFn` and `f_ok`'s hypotheses, the closure's free
names (`env0.lookup "x" = none` for a global, `= some cell` for an upvalue). -/

/-- `CFn I f a c`: `f` is the call of closure `c` at address `a`. At every argument list and fuel, `f` is `callClo`,
the interpreter's call of the closure once its address has been read (`Shallow.lean`). Lean checks this line
against the definition. -/
example (I : Sem) (f : List Val → Nat → M (List Val)) (a : Nat) (c : Clo) :
    CFn I f a c = ∀ args n, f args n = callClo I n a c args := rfl

/-- The translator is correct for every function: `D.fn`, the translator as a Lean function, gives the call of the
closure. Rests on `frees_resolved`: `res` names the cell of each name as the closure's environment does (`none` for
a global). -/
theorem translator_gives_the_call (I : Sem) (res : String → Option Nat) (a : Nat) (c : Clo)
    (frees_resolved : ∀ x, c.env.lookup x = res x) : CFn I (D.fn I res a c) a c :=
  D.fn_ok I res a c frees_resolved

/-- The closure's call is the interpreter's: when heap `h` holds closure `c` at address `a`, the interpreter's `call`
of the value `.fn a` with one more fuel is `callClo` of `c`. Rests on `closure_at`. -/
theorem closure_call_is_the_interpreters (I : Sem) (n a : Nat) (args : List Val) (h : Heap) (c : Clo)
    (closure_at : h[a]? = some (.clo c)) :
    call I.srcs I.oracle I.tgt (n + 1) (.fn a) args h = callClo I n a c args h :=
  call_fn I n a args h c closure_at

/-! ## The program logic -/

/-- `RunP m h P`: total correctness. The computation `m`, a function of the fuel, started in heap `h`, returns from
some fuel on, the same result and heap at every fuel past it, and they satisfy `P`; running out of fuel is never the
answer. Lean checks this line against the definition. -/
example {α : Type} (m : Nat → M α) (h : Heap) (P : α → Heap → Prop) :
    RunP m h P = ∃ N a h', (∀ n ≥ N, m n h = .ok a h') ∧ P a h' := rfl

/-- A spec proved about a lifted function is a spec of the closure's call: what `RunP` says of `f args` it says of
`callClo` of the closure, and so (`closure_call_is_the_interpreters`) of the interpreter's run of the script.
Rests on `lifted`, the file's `f_ok`. -/
theorem spec_of_lifted_is_spec_of_the_call {I : Sem} {f : List Val → Nat → M (List Val)} {a : Nat} {c : Clo}
    (lifted : CFn I f a c) {args : List Val} {h : Heap} {P : List Val → Heap → Prop}
    (spec : RunP (f args) h P) : RunP (fun n => callClo I n a c args) h P :=
  RunP.cong (fun n => lifted args n) spec

/-! The rules of `RunP` (`Hoare.lean`: one per interpreter clause, `RunP.bind`, `RunP.effect`, `Tbl.next_mem`, …)
are theorems about the definition above, not a logic of their own: there is no soundness beside it to trust. -/

/-! ## The frame rule

A call leaves alone a cell it cannot name (`Frame.lean`, `FrameCall.lean`). `Own cell P h`, read at its definition
in `Frame.lean`: heap `h` holds at `cell` a value with `P`; `cell` is none of the semantics' fixed cells, is in no
closure's environment, and the same holds in every heap a coroutine keeps to replay from. `Own.fresh`
(`FrameCall.lean`) is where it starts: a cell just pushed on a heap whose coroutines hold no heaps. -/

/-- `Keeps cell P m Q`: from every heap where `cell` is own, `m` ends, returning or not, in a heap where it still is,
and its result has `Q` if it returns. Lean checks this line against the definition. -/
example {α : Type} (cell : Nat) (P : Val → Prop) (m : M α) (Q : α → Prop) :
    Keeps cell P m Q = ∀ h, Own cell P h → match m h with
      | .ok a h' => Own cell P h' ∧ Q a
      | .error _ h' => Own cell P h' := rfl

/-- The frame rule: a call of any value with any arguments, at any fuel, from a heap where `cell` is own ends in a
heap where it still is, whatever the sources, the oracle and the target. Rests on nothing. -/
theorem call_keeps_own_cell (cell : Nat) (P : Val → Prop) (srcs : String → Option Block) (oracle : Oracle)
    (tgt : Target) (n : Nat) (f : Val) (args : List Val) :
    Keeps cell P (call srcs oracle tgt n f args) fun _ => True :=
  call_keeps

/-- An own cell reads back: it holds a value with `P`. -/
theorem own_cell_holds_its_value {cell : Nat} {P : Val → Prop} {h : Heap} (own : Own cell P h) :
    ∃ v, h[cell]? = some (.cell v) ∧ P v :=
  own.cell

/-! ## What no proof here covers

Tested against the reference LuaJIT, not proved (DESIGN.md, *Trust*): that `call` and the rest of `Interp.lean` are
LuaJIT's (`test/luasem.lua` on the committed and on fresh random chunks); that the tree `f_body` a lifted file is
about is the script's, as the parser and `Show.lean` wrote it (`lua-lean parsecheck`: each file parsed and printed
back compiles under LuaJIT to the source's bytecode; no parse/print round trip is proved); the host's libm.

Assumed by the user, one named hypothesis each, never bundled, so a reader sees which a spec rests on: what the
world answers an effect (`Examples/WorldSpec.lean`: `TakesWrites real`, `ClockAnswers real`, `ClockMono real`, each
with its test against LuaJIT in `Examples/world_axioms.lua`).

Checked by Lean, so not read: every proof; that `f` is `D.fn`'s (the kernel computes it when it checks `f_ok`);
that each theorem rests on Lean's three and nothing else (`Audit.lean`, which `check.sh` runs). -/

end Lua
