# lua-lean

lua-lean turns a LuaJIT script into Lean: a semantics of Lua that runs, a parser into it, a translator that writes
each function of the script as a Lean function together with a kernel-checked proof that it *is* that function under
the semantics, and a program logic to prove things about the result. It is a library and a CLI with no dependency
on anything else in this repo. The swarm (`swarm/model`) is its first user.

## Who it is for

An LLM writes a LuaJIT script and, next to it, a spec in Lean: what the script's functions return and do to the
heap, for all inputs. lua-lean lifts the script; the spec is proved about the lifted functions; Lean's kernel checks
the proof. Nobody has to trust the LLM, the translator or the proof search, only what the next section lists.
LuaJIT because it is small, fast and embeddable, and its single implementation can be tested against.

## How it works

```
script.lua ──parse──▶ Block (LuaLean/Syntax) ──lift──▶ f_body, f, f_ok   (one triple per function)
                          │                                  │
                  Interp: the semantics              Hoare: RunP specs about f
```

- **Semantics** (`LuaLean/Interp.lean`): an interpreter on fuel in `M = EStateM Err Heap`. Every local is a heap
  cell (closures share upvalues as Lua's do); a value is nil, boolean, number, string (bytes), table, closure,
  builtin, or effect handle. Fuel bounds the evaluation's depth; running out is `Err.fuel`, never a Lua error.
- **Effects** are not interpreted. `io`, `os`, `print`, `debug` and every module not given as source are handles;
  calling one asks an *oracle* (`String → List Val → Option (List Val)`); `none` stops the run with `Err.eff`. What an
  oracle answer means in the world is the user's assumption, written as a named Lean axiom with its own test against
  the real thing (the swarm's `SwarmModel/Env.lean` and `swarm/lua/test/env_spec.lua` are the pattern).
- **Parser** (`LuaLean/Parse.lean`): Lua 5.1's grammar with LuaJIT's lexer and its constant folding.
- **Translator** (`tools/Lift.lean`), after AutoCorres's first stages: for each function `f` of the file (the chunk
  is `chunk`), `f_body` (its parsed body), `f` (a shallow function built from `LuaLean/Shallow.lean`'s combinators,
  one per interpreter clause, every local the Lean variable naming its cell) and `f_ok : CFn I (f I env0 …) clo`:
  for all arguments and every fuel, `f` gives the interpreter's result and heap for the closure. Its hypotheses are
  the closure's free names (`env0.lookup "x" = some c` for an upvalue, `= none` for a global).
- **Program logic** (`LuaLean/Hoare.lean`): `RunP m h P`, total correctness: from some fuel on, `m` returns, and the
  result and heap satisfy `P`. A spec is a `RunP` about a lifted `f`; `f_ok` carries it to the interpreter's run.

## Trust

What a proved spec rests on, and how each piece is checked:

| Trusted | Checked by |
|---|---|
| Lean's kernel and its three axioms (`propext`, `Classical.choice`, `Quot.sound`) | `Audit.lean`: every theorem of LuaLean uses those and nothing else; `check.sh` refuses `sorry`, `admit`, `native_decide`, `axiom` |
| The parser, and `LuaLean/Show.lean` (74 lines), which writes the parsed tree as the Lean term `f_body` the proof is about | `lua-lean parsecheck` (the parser; `Show.lean` by reading it): each file, parsed and printed back fully parenthesised, compiles under LuaJIT to the source's bytecode (number constants at `%.17g`). A tree of the wrong shape (a re-associated `a - b - c`) changes the bytecode |
| The semantics against LuaJIT | differential testing: `LuaLean/Gen.lean` writes random chunks with the interpreter's results for each target and `test/luasem.lua` runs each under stock LuaJIT 2.1 (never a 5.2-compat build), JIT on and off, against its target's results; results must be the same text, numbers to the last bit. 3000 are committed (`test/cases.lua.gz`, seed 28), `lua-lean difftest` runs fresh ones |
| The host's `pow` | `^` is libm's `pow` in LuaJIT and in Lean's `Float.pow`, so the two agree on one machine, and macOS's and glibc's may differ. The kernel cannot evaluate a `Float`, so no proof rests on a `pow` value, but two files carry the machine that wrote them: a lifted module (the parser folds a constant `a ^ b`, `Show.lean` writes it as `Float.ofBits`) and `test/cases.lua.gz`. A `pow` case that fails on another machine is this before anything else |
| The user's effect axioms | each its own test against the world, as above |

Not trusted: the translator (Lean checks each `f_ok`: one `+` turned into `-` in a lifted function and the proof
fails), the case generator, and any proof search.

## Targets

LuaJIT 2.1 is built dual-number (a number is a 32-bit integer or a double: arm64's default) or single-number (doubles
only: x86-64's default). The semantics has both, `Target` in `LuaLean/Num.lean`, carried by `Sem.tgt`, so every
`f_ok` holds for both. Its numbers are integers or doubles on both targets: `.int i` is the double `i` exactly, and
every operation on integers gives the double result but one, a product of 0 with a negative factor, which is 0 on
dual-number and -0 on single-number (`Num.mul`). The parser's constants are the same on both (its folder makes no
-0), so a lifted module is too. Every constant is narrowed, as LuaJIT's constant table is on dual-number: `-2147483648`
is the double 2^31 negated, and an integer (`Num.foldNeg`). `test/luasem.lua` tells the targets apart by that product (`1/(z*n)`), not by
`jit.arch`; a cases file holds the dual-number results (`out`) and the single-number ones where they differ
(`single`).

A double outside the integer range a C cast wants (int32 for `lj_lib_checkint`, int64 for `%d` and `%x`; inf and NaN
too) is undefined behaviour in C that LuaJIT leaves to the CPU (x86-64 gives the least integer; arm64 is expected to
saturate, unmeasured), so the semantics stops the run there (`argIntN`).

## The subset

In: Lua 5.1 syntax as LuaJIT parses it; metatables with `__index` and `__newindex` (a function, or a value to index
instead) and `__call`, each read from the metatable when the operation runs, as LuaJIT does; closures; varargs;
`pcall`/`error` (a failed call keeps what it wrote); `goto` as the continue idiom (a label ending its block); numbers as LuaJIT has
them on either target, with `tonumber` and `%.14g` exact; strings as bytes. Library: `string` (patterns after lstrlib.c,
`format` after lj_strfmt_num.c, `gsub` with string, table or function), `table` (`sort` is ltablib.c's quicksort,
so ties and bad comparators come out as LuaJIT's do), `math`, `select`, `unpack`, `pairs`, `ipairs`, `next`,
`type`, `tostring`, `tonumber`, `rawget`/`rawset`/`rawequal`, `setmetatable`/`getmetatable`, `assert`, `require` of
modules given as source.

Out: coroutines, `load`/`loadstring`/`dofile`, FFI, the other metamethods (G3b, G3c), `string.format("%a")`, the
rest of the standard library.

How a script outside it is reported, from strongest to weakest:

1. **Fails to parse**: syntax outside the grammar (`lua-lean lift` prints the parser's error and exits 1).
2. **Fails to translate**: an assignment target the translator does not handle (`not translated`).
3. **Stops the run**: a feature the semantics refuses is an effect no oracle answers, so no `RunP` about a run that
   reaches it can be proved: an operation that would call a metamethod the semantics does not model yet (`t + 1`
   with `__add` in `t`'s metatable: `effect metamethod __add`; likewise `__sub`…`__pow`, `__unm`, `__concat`, `__eq`,
   `__lt`, `__le`, `__tostring` in `tostring` and `%s`, `__metatable` in `getmetatable` and `setmetatable`; a table's
   `__len` LuaJIT 2.1 never calls), a metatable with `__mode` or one on `_G`, a chain of `__index` or `__newindex`
   tables that loops (LuaJIT stops it after 100 with an error; the semantics runs out of fuel),
   `%f` of a number below 1e-150 (where LuaJIT itself prints garbage), a double outside the integer range where a
   builtin wants an integer (`("x"):rep(2^32)`, `("%d"):format(1/0)`; "Targets"), a call into `io`, `os` or a module not given
   as source when no oracle answers it.
4. **Known gaps**, where the semantics answers and LuaJIT may answer otherwise, so a proof could be about the wrong
   behaviour. Each is a task on the roadmap; until then a spec must not depend on them:
   - `__mode` added to a metatable after `setmetatable`;
   - `pairs`/`next` order: the semantics visits keys in insertion order; LuaJIT's order is its hash layout (G4);
   - `#t` of a table with holes: the semantics takes the least border, LuaJIT may give another;
   - error values of runtime errors: the semantics' messages have no `file:line:` prefix;
   - `tostring` of a table or function (an address in LuaJIT).

G2 turns this list into a checker that names each construct with its line before anything is lifted.

## Layout and use

| Path | What it is |
|---|---|
| `LuaLean/Num.lean` | numbers: the targets, integer and double arithmetic, printf's conversions on the exact value, `tonumber` (lj_strscan, with its 2^20 exponent bound) |
| `LuaLean/Syntax.lean`, `Parse.lean` | the syntax tree and the parser |
| `LuaLean/Pat.lean` | Lua patterns, after lstrlib.c's matcher |
| `LuaLean/Interp.lean` | the semantics |
| `LuaLean/Run.lean` | running a chunk as `test/luasem.lua` does under LuaJIT, its results as text, modules from a directory |
| `LuaLean/Show.lean` | a syntax tree as the Lean term that builds it |
| `LuaLean/Shallow.lean` | the translator's target: one combinator and one lemma per interpreter clause |
| `LuaLean/Hoare.lean` | `RunP` and its rules |
| `LuaLean/Gen.lean` | random chunks for the differential test; a user adds its own (`swarm/model/SwarmModel/LuaCases.lean`) |
| `tools/*.lean` | the CLI's programs, run with `lake env lean --run` |
| `test/luasem.lua` | the LuaJIT side of the differential test |
| `test/cases.lua.gz` | the committed chunks |
| `test/*.lua` | scripts `check.sh` parses against LuaJIT and lifts with proofs |

```sh
lua-lean/check.sh                              # gates, build, audit, committed chunks, test scripts: about 15 s
lua-lean/lua-lean lift f.lua [Ns [Imp:Const]] > F.lean   # the module; import it with LuaLean on the path
lua-lean/lua-lean prove f.lua...               # lift each and check its proofs in a scratch directory
lua-lean/lua-lean parsecheck f.lua...          # the parser against LuaJIT's bytecode
lua-lean/lua-lean run [--lib p=dir] f.lua      # f.lua under the semantics; luajit lua-lean/test/luasem.lua f.lua under LuaJIT
lua-lean/lua-lean difftest 3000                # fresh chunks under LuaJIT
lua-lean/lua-lean dump Name f.lua              # the tree as `def NameSrc : Block`, for proofs about the source itself
```

A Lake package uses it with `[[require]] name = "lua-lean" path = "<dir>"` (as `swarm/model/lakefile.toml` does)
and `import LuaLean`. Needs Lean 4.35 (elan, or nix, which the scripts fall back to) and LuaJIT 2.1.

## Gates

Every change keeps these: each semantics change is differentially tested against stock LuaJIT 2.1 (new behaviour
gets generator cases, as the exponent bound did); no `sorry`, `native_decide`, or axiom beyond Lean's three and the
user's named effect axioms; a feature outside the subset fails to parse, translate or prove, never yields a wrong
proof; a statement is never weakened to make a proof go through.

## Roadmap

- **G2** subset checker: `lua-lean check f.lua` lists every construct and library call outside the subset with its
  line, and runs the differential test on the script's own pure functions; coverage on a corpus of real third-party
  LuaJIT scripts.
- **G3** metamethods as LuaJIT 2.1 does them, in the interpreter, translator and rules: `__index`, `__newindex`,
  `__call`, read when used (G3a, done); arithmetic, `__unm`, `__concat`, `__len` (G3b); `__eq`/`__lt`/`__le`,
  `__tostring`, `__metatable` (G3c). Each replaces a `noMeta` stop in `LuaLean/Interp.lean`.
- **G4** the standard library: the rest of string, table, math, `select`/`tostring`/`tonumber` corners, `pairs`
  order; `os` and `io` as effect interfaces with named axioms.
- **G5** `load`, `dofile`, `require` of arbitrary modules: multi-module scripts lift end to end.
- **G6** coroutines: thread state in the interpreter, a suspension effect in the shallow monad, rules for
  resume/yield.
- **G7** heap abstraction, proof-producing: functions whose tables are provably unshared become pure Lean functions,
  with a proof they equal the heap-monadic lift.
- **G8** end to end: an LLM writes a script and its spec, the tool lifts it, the spec is proved; measured on a few
  realistic scripts.
- Research: one proof that the translator is correct for every program, replacing the per-output proofs.
