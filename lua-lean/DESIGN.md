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
  A runtime error is raised without its place (`Err.rt lvl msg`): the innermost site of the frame it is reported in
  gives it `chunk:line:` and the operand's name (`atSite`), each call's frame passes it one frame out (`frame`), a
  tail call's site one further, and a builtin's frame, which has no place, leaves it bare.
- **Effects** are not interpreted. The world's part of `print`, `io` and `os`, and every module not given as
  source are effects: a handle (`io.open`, `os.getenv`, `math.random`), or a builtin's call into the world after the
  part LuaJIT computes, which the semantics computes too (`print` and `io.write` convert their arguments and make one
  write, `"print"` or `"io.write"`, print one more before each `__tostring` it calls; `os.time()` asks `"os.time"`, `os.time(t)` reads t's fields and asks
  `"os.mktime"` the struct tm's; `os.date` formats a UTC date itself and asks `"os.localtime"` a local one;
  `os.difftime` is computed). Calling one asks an *oracle* (`Oracle`: the effect, its arguments, and the trace of the
  effects before it), and the call joins the trace (`trace`, the heap's cell `LOG`, newest first: what it was, its
  arguments, the answer), so a world with state (a clock, files) is a function of the trace; `none` stops the run with
  `Err.eff`. What an oracle answer means in the world is the user's assumption, written as a named Lean axiom with its
  own test against the real thing (`Examples/WorldSpec.lean` and `Examples/world_axioms.lua`, or the swarm's
  `SwarmModel/Env.lean` and `swarm/lua/test/env_spec.lua`, are the pattern). A spec says what a function adds to the
  trace (`Examples/WorldSpec.lean`: `greet` writes its line, `readings` reads the clock twice, in order).
- **Files** are the ones given as source: `Sem.srcs` maps a path to its parsed chunk. `require` looks for a module
  through `package.path` (`./?.lua` to begin with: LUA_PATH=./?.lua; LuaJIT's default adds the system's directories)
  among them, as lib_package.c's Lua loader does, and `dofile` reads one; `load` and `loadstring` run the parser
  inside the semantics.
- **Parser** (`LuaLean/Parse.lean`): Lua 5.1's grammar with LuaJIT's lexer and its constant folding; an assignment
  to anything but a name or an index (`(x) = 1`, `f() = 1`) is a syntax error, as in LuaJIT.
- **Translator** (`tools/Lift.lean`), after AutoCorres's first stages: for each function `f` of the file (the chunk
  is `chunk`), `f_body` (its parsed body), `f` (a shallow function built from `LuaLean/Shallow.lean`'s combinators,
  one per interpreter clause, every local the Lean variable naming its cell) and `f_ok : CFn I (f I env0 …) clo`:
  for all arguments and every fuel, `f` gives the interpreter's result and heap for the closure. Its hypotheses are
  the closure's free names (`env0.lookup "x" = some c` for an upvalue, `= none` for a global). Its proof is one
  theorem for every program, `D.fn_ok` (`LuaLean/Denote.lean`): `D.fn` is the translator as a Lean function, from the
  closure to the combinators, and `D.fn_ok` that its result is the interpreter's call. `f` is the printed form of
  `D.fn` at `f_body`, so `f_ok` is `D.fn_ok` applied to the closure, and the kernel checks by computation that `f` is
  `D.fn`'s (`research/translator-proof.md`). A `load` or
  `loadstring` of a constant source is lifted too, as `f_loadN`: `call_load` says the call makes its closure, given
  the parse (`parseChunk s name = .ok f_loadN_body`, the parser's, as `f_body` is). A script of several modules is
  lifted one file at a time; `call_require` and `call_dofile` (`RunP.require`, `RunP.dofile`) say that requiring or
  running a file given as source is its lifted `chunk`.
- **Program logic** (`LuaLean/Hoare.lean`): `RunP m h P`, total correctness: from some fuel on, `m` returns, and the
  result and heap satisfy `P`. A spec is a `RunP` about a lifted `f`; `f_ok` carries it to the interpreter's run.

## Trust

What a proved spec rests on, and how each piece is checked:

| Trusted | Checked by |
|---|---|
| Lean's kernel and its three axioms (`propext`, `Classical.choice`, `Quot.sound`) | `Audit.lean`: every theorem of LuaLean uses those and nothing else; `check.sh` refuses `sorry`, `admit`, `native_decide`, `axiom` |
| The parser (also as `load` runs it, and as it made each `Sem.srcs` file a proof assumes), and `LuaLean/Show.lean` (74 lines), which writes the parsed tree as the Lean term `f_body` the proof is about | `lua-lean parsecheck` (the parser; `Show.lean` by reading it): each file, parsed and printed back fully parenthesised, compiles under LuaJIT to the source's bytecode (number constants at `%.17g`). A tree of the wrong shape (a re-associated `a - b - c`) changes the bytecode |
| The semantics against LuaJIT | differential testing: `LuaLean/Gen.lean` writes random chunks with the interpreter's results for each target and `test/luasem.lua` runs each under the reference LuaJIT ("The reference LuaJIT"), JIT on and off, against its target's results; results must be the same text, numbers to the last bit, and what the chunk wrote to stdout the same bytes (luasem.lua puts fd 1 on a file through the FFI; the Lean side's world is `Run.caseFx`, whose stdout takes every write and whose local zone is UTC, as luasem.lua sets `TZ`). 3000 are committed (`test/cases.lua.gz`, seed 28), `lua-lean difftest` runs fresh ones |
| The host's libm | `^`, `math.pow`, `exp`, `log`, `log10`, `sin`, `cos`, `tan`, their inverses and hyperbolics, `atan2` are libm's in LuaJIT and in Lean's `Float`, so the two agree on one machine, and macOS's and glibc's may differ. The kernel evaluates part of `Float` and not the rest (tested on Lean 4.35 with `decide` and `decide +kernel`). It computes `+ - *`, `/` (`decide +kernel` only; plain `decide` times out), `<`, `≤`, `==`, negation, `abs`, `isFinite`, `isNaN`, `Float.ofInt`, `Float.ofNat`, `toBits`, `ofBits`, `toUInt64` and `Float.sqrt` (`decide +kernel` only; plain `decide` is stuck). It cannot compute `Float.floor`, `ceil`, `round`, `scaleB`, `frExp`, `pow`, `exp`, `log`, `sin`, `cos`: `decide` is stuck on each, so `Num.narrow`, `floatToInt` and `fmod`, which use `floor`, and `ofRatio`, which uses `scaleB`, cannot be evaluated by a proof on a non-integer `Float`. No proof rests on such a value, but two files carry the machine that wrote them: a lifted module (the parser folds a constant `a ^ b`, `Show.lean` writes it as `Float.ofBits`) and `test/cases.lua.gz` (its generator prints the `math` ones at `%.12g`, `^` exactly). A `pow` case that fails on another machine is this before anything else. `fmod`, `modf`, `frexp`, `ldexp` are exact and modelled exactly (`Num.fmodC`, …) |
| The parser's sites: the line and the operands' names each runtime error is reported with | the differential test: `Gen.lean`'s `errors` chunks raise errors under `pcall` from statements broken across lines at random, and the error values must be LuaJIT's |
| The user's effect axioms | each its own test against the world, as above (`check.sh` runs the example's, `Examples/world_axioms.lua`, and refuses an axiom there without a case of its name) |

Not trusted: the translator. `D.fn_ok` is proved once, in the library, so `Audit.lean` covers it; `tools/Lift.lean`
only prints `f`, and a printed `f` that is not `D.fn`'s fails `f_ok` (one `+` turned into `-` in a lifted function
and its `f_ok` does not check: a type mismatch, or the kernel gives up computing). Nor are the case generator and any proof search.

## The reference LuaJIT

LuaJIT 2.1 is a rolling release whose parser and library move between versions, so lua-lean is checked against one:
**LuaJIT 2.1.1791890110**, the repo flake's (`nix build .#luajit`, pinned by `flake.lock`; a default build: not
5.2-compatible, FFI and JIT on). CI runs that one; `check.sh`, `lua-lean parsecheck` and `difftest` run `$LUAJIT` if
it is set, else the flake's (through nix), else the PATH's, print the version, and warn when it is not this one
(`ref` in `lua-lean`). To bump it: update `flake.lock`, set `ref` and this paragraph to the new version, regenerate
`test/cases.lua.gz` (`lua-lean cases 3000 <seed> test/cases.lua`, then `gzip`), and run `check.sh` and `lua-lean
difftest`; a difference is the semantics' to follow, and new syntax goes under "The subset" as in or out.

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

The table library's functions written in Lua (`remove`, `move`) check an integer argument with `CHECK_int`, which
dual-number makes an integer (truncated) and single-number leaves the number it was; their raw accesses truncate a
key. So `table.remove(t, 1.5)` shifts by halves on single-number (`libInt`, `libKey`).

## Tables

LuaJIT visits a table's keys in its layout's order: the array part, then the hash nodes, where a string sits by a hash
seeded per process and a table or function by its address, so `pairs` over the same string keys comes out in another
order on each run. No model predicts that. The semantics' order is `Tbl.rank` (`LuaLean/Interp.lean`), an opaque
function of the table's address, its version and the key: the kernel never unfolds it, so a proof about a traversal
holds for every rank, LuaJIT's in each process among them. The version moves on when a key gets a value it lacked,
the one operation after which LuaJIT may move keys (a new node, a rehash); between, the order is fixed, as LuaJIT's
is. A key cleared during a traversal stays, dead, until a key is added; then it goes, as LuaJIT's rehash drops it.
`next` from a key the table does not hold is LuaJIT's error, `invalid key to 'next'`, but where LuaJIT may still hold
it: an integer (its array part holds every index below its size) or a key the table had (a dead node); there the run
stops. What a spec about a traversal rests on is `Tbl.next_mem` (`LuaLean/Hoare.lean`): `next` gives an entry of
the table with a value, whatever the rank. Run (`lua-lean run`, the cases), the rank keeps the insertion order; the
generator's traversals are ones whose result does not hang on the order, and they agree with LuaJIT under a
scrambled rank too. Number keys have a fixed order in LuaJIT, but the semantics does not model
the layout, so theirs is opaque as well.

`#t` is a border (an n with t[n] not nil or n = 0, and t[n+1] nil): lj_tab_len's binary search finds one by the array
part's size, which the rehashes set. A table with one border gives it; one with more stops the run, and so does each
library function that takes the length (`table.insert`, `remove`, `concat` and `unpack` without an end, `sort`,
`foreachi`, `getn`).

A weak table (`__mode`) loses an entry when the collector frees its weak key or value, and when the collector runs
is not a function of the program (an allocation anywhere, the JIT's own among them). The semantics never collects, so
a weak table is an ordinary one, and a read that could see an entry the collector freed stops the run; every other
read is the same with or without a collection. The weak parts are those of the metatable's `__mode` at the time
(LuaJIT reads it at each collection: `k` and `v` up to a NUL, a value not a string none), and the collector frees an
object (a table, function, coroutine or userdata), never a string, number or boolean (lj_gc's gc_mayclear). A read
by key holds the key, so a weak key keeps its entry; what stops (`weakOf`, `held`, `wget` in `LuaLean/Interp.lean`):
an object read as a weak value (indexing, `rawget`, `ipairs`, the table library, a metamethod from a weak metatable,
the presence check of an assignment where `__newindex` would run), `next` to an entry with an object as a weak part
or from a key whose weak value is one, and `#t` with an object as a weak value at an integer key. A mode stays once
set: changing or clearing `__mode` (`table.clear` too), or giving a weak table another metatable, stops, since the
entries it may have lost under the old mode would come back; and `package.loaded`, read raw by `require`, takes no
metatable. A proof about a weak table's traversal with objects in it needs a model of the collector's choice (an
opaque one, as `Tbl.rank` is for the order); none is written yet. The generator's chunks hold their objects in
locals, so LuaJIT's collector frees none of them.

## Coroutines

A coroutine is a heap object (`Thr` in `LuaLean/Interp.lean`), and `M` stays `EStateM Err Heap`: the heap cannot hold
a Lean continuation (the heap would occur in its own argument), so a coroutine is resumed by replay. It keeps its
function and, for each resume so far, the arguments and the heap the coroutine went on in. Resume number k adds its
own, sets the heap to the first one's and calls the function on the first arguments; each yield of the replay sets
the heap to the next resume's and returns its arguments (`yieldFn`), so the run comes to resume k's heap with its
locals as they were, and goes on from there; the yield after that stops the run with `Err.yld`, which `resume`
catches (`coRun`). The interpreter is a function of the heap and the arguments, so each replayed stretch is the
stretch that ran, and putting the next heap in place undoes what it wrote again; what the main thread changed
between two resumes is in the heap the coroutine goes on in. So is an effect's: the trace is in the heap and the
oracle a function of it, so a replayed call into the world gets the answer it got, and its event goes with the heap
the replay leaves. A cell at a fixed address holds the running coroutine
(nil in the main thread), for `running`, `status` and `isyieldable`.

`Err.yld` is not a Lua error: `pcall`, sites and frames let it pass, so a yield crosses `pcall`, metamethods
(`__index`, `__newindex`, `__call`, the operators' and comparisons', `__tostring` in `tostring`), `for` iterators and `table.foreach`/`foreachi` (Lua in LuaJIT 2.1), as LuaJIT's
fully resumable VM lets it. A builtin that calls back into Lua from C (`table.sort`'s comparator and `__lt`, `gsub`'s function
or table, `__tostring` in `print` and `string.format`, `require`'s and `dofile`'s chunks, `load`'s reader) marks the coroutine (`bounded`), and a yield there is
LuaJIT's error, `attempt to yield across C-call boundary`, as it is in the main thread. A resume returns LuaJIT's
values and messages (`cannot resume dead coroutine`, `cannot resume running coroutine` for a running or normal one);
a function of `wrap` raises the coroutine's error again, a string with its caller's place. The rules
(`LuaLean/Hoare.lean`) are `SuspP` (a run that suspends) and its passage through bind, sites, frames and `pcall`,
yield with and without a resume to replay, and resume in terms of its coroutine's run. A resume replays every earlier
stretch, so k resumes cost k^2 / 2 stretches; and an effect a coroutine called is asked of the oracle again in each
replay, which a stateless oracle answers as before.

## The subset

In: Lua 5.1 syntax as LuaJIT parses it, with its lexer's `\u{...}` escapes, empty statements (`;;`) anywhere, and
`continue` and `const` as names (soft keywords in LuaJIT; `test/lex.lua`); metatables with `__index` and
`__newindex` (a function, or a value to index
instead), `__call`, the arithmetic ones (`__add`, `__sub`, `__mul`, `__div`, `__mod`, `__pow`), `__unm` (given its
operand twice) and `__concat` (`a .. b .. c` right to left, as BC_CAT), each read from the metatable when the
operation runs, the left operand's before the right's, as LuaJIT does; an operator's metamethod is called as a call
is (a table through its `__call`), its first value the result (a builtin's bad argument names it by the event,
`bad argument #1 to '__add'`), and one that cannot be called is LuaJIT's error with no place; `__eq` (two distinct tables, by the left one's, when
the right has the same metatable or one with the same `__eq`: lj_meta_equal), `__lt` and `__le` (two values of one
type neither numbers nor strings, both with the same metamethod; `a <= b` without `__le` is `not (b < a)`, a bad
argument of a builtin one still named `'__le'`), each its first value's truth, `__lt` also in `table.sort` (a builtin
one's bad argument named `'?'`, as from C); `__tostring` in `tostring` (a tail call: all its values, its frame in
tostring's place), `print` (its first value, a string or number, else `'tostring' must return a string to 'print'`;
print writes what it has before each call, as LuaJIT writes each argument) and `%s`/`%q` (called once, in order, its
first value as tostring would give it); `__metatable` (getmetatable gives it instead of the metatable,
setmetatable is `cannot change a protected metatable`); `#t` the border whatever `__len` is (LuaJIT 2.1 without its 5.2 compatibility); closures; varargs;
`pcall`/`error` (a failed call keeps what it wrote); error values as LuaJIT's: a runtime error, a builtin's
(`bad argument #1 to 'rep' (...)`, named as the call names the callee) and `error`/`assert` with a string or number
carry `chunk:line:` of the place LuaJIT reports (the operator or call raising it, or the call `error`'s level counts
out to, a tail call's frame gone), or none where that place is a builtin, and the operand's name (`attempt to index
local 't' (a nil value)`); `goto` as the continue idiom (a label ending its block); numbers as LuaJIT has
them on either target, with `tonumber` and `%.14g` exact; strings as bytes. Library: `string` (patterns after
lstrlib.c, `format` after lj_strfmt_num.c, `gsub` with string, table or function), `table`, all of LuaJIT 2.1's
(`sort` is ltablib.c's quicksort, so ties and bad comparators come out as LuaJIT's do; `move`, `remove`, `foreach`,
`foreachi`, `getn` after lib_table.c's Lua; `table.new` and `table.clear` through `require`; `string.dump`
below), `math` but `random` and
`randomseed` (effects: the generator's state is the oracle's), `select`, `unpack` (at most 8000 values with its
arguments, lua_checkstack's bound), `pairs`, `next` and `table.foreach` in an order no proof can know ("Tables"),
`#t` with one border, `ipairs`, `type`, `tostring`, `tonumber` (a base other than 10
as lib_base.c's strtoul reads it: a sign, `0x` in base 16, saturated at 2^64 - 1), `rawget`/`rawset`/`rawequal`,
`setmetatable`/`getmetatable` (weak tables too: "Tables"), `assert`; `load` and `loadstring` of a source (a string, or a reader function's pieces)
with a chunk name and a mode, or of a dump: `string.dump(f, strip)` of a Lua function is a string whose bytes, LuaJIT's
bytecode, are not modelled (`Val.dump`: the closure and the strip flag, an `s` in a string or any other true value).
What does not read the bytes is LuaJIT's: `type` is `"string"`, `tostring` gives it back, it is a value in tables,
calls and coroutines, `==` with itself (true when both or neither are stripped) or with a value not a string, an error
value at level 0, `tonumber` nil, and arithmetic, a comparison with a number, a call, an index assignment or a `for`
fail with LuaJIT's message for a string; a builtin cannot be dumped. `load` of it (mode with `b`) is a closure of the
dumped function, each upvalue a new cell holding nil; an unstripped one keeps its chunk name and lines whatever load
calls it, a stripped one is the chunk load names (`=?` if none) at line 0, its upvalues without names (in errors and
`debug.getupvalue`; `Site.strip`), `dofile` and `require` of files given as source, `require` through `package.path`,
`package.loaded` (a module that sets its own entry, one returning nothing, a loop, a failed load) and the modules
LuaJIT has loaded at the start (`_G`, `package`, `string`, `table`, `math`), each chunk named in its errors as
lj_debug_shortname names it (`[string "..."]`, `=name`, `@file`); `coroutine`, all of LuaJIT 2.1's (`create`,
`resume`, `yield`, `status`, `wrap`, `running`, `isyieldable`; "Coroutines"); `debug` without a call stack
(`debugFn`): `getmetatable` and `setmetatable` of a table raw (`__metatable` neither hides nor protects it;
setmetatable returns true), `getupvalue` and `setupvalue` of a closure (its upvalues are the outer locals its body
names, numbered in the order LuaJIT's parser meets them: `Clo.upvals`) or of a builtin that has none, `getinfo` of
a function (`u`, `f`, `l`, `n`, a builtin's `S` and `L` too: `[C]`, its count of upvalues LuaJIT's), of a negative
level (nil) and its bad arguments, `traceback` of a value neither a string nor a number (returned as it is), a
thread as the first argument of either; `bit`, all of LuaJIT 2.1's (`tobit`, `tohex`, `bnot`, `band`, `bor`, `bxor`,
`lshift`, `rshift`, `arshift`, `rol`, `ror`, `bswap`; the global and `require "bit"`), on int32: each argument a
number or a string read as one, an integer mod 2^32 and a double through lj_num2bit (plus 2^52 + 2^51, the low 32
bits: rounded to even, inf and NaN 0; `Num.toBit`, which the kernel computes), a shift's count mod 32, each result an
int32 (an integer on dual-number, a double on single-number), `tohex`'s width negative for upper case and at most 254;
`bitFn`, `RunP.bit` and `bit_tobit`, `bit_band`, `bit_lshift`. The world (*Effects*): `print` (with
the builtin `tostring`) and `io.write` as LuaJIT writes their arguments, `io.write`'s bad argument raised after the
arguments before it are written; `os.time` of a date table (each field through `__index`, truncated, the defaults and
`field 'day' missing in date table`); `os.date` with or without `!`, `*t`, and strftime's conversions in the C locale
but those below; `os.difftime` (each time truncated, as C's cast does); the rest of `io` and `os` as handles.

Out: LuaJIT's syntax beyond Lua 5.1 backported from 3.0 (its `doc/extensions.html`), each a parse error
(`test/out.txt`, which `check.sh` loads under LuaJIT and has the parser refuse): the bit operators (`~x`, `&`, `|`,
`~`, `<<`, `>>`, `~>>`), `!`, `&&`, `||`, `!=`, the conditional `a ? b : c`, safe navigation (`t?.k`, `t?.[k]`,
`f?.()`, `o?.:m()`, `o:m?.()`), `??`, compound assignment (`+= -= *= /= %= &= |= ~= <<= >>= ~>>= ..=`), the
`continue` statement, `const` declarations, short functions (`x -> e`, `|a, b| -> e`, `|| -> do ... end`),
underscores in numerals (`1_000`), FFI numerals (`1LL`, `2i`); `setfenv` and `load`'s environment argument, FFI,
`__gc`, `string.format("%a")`, and the rest of LuaJIT 2.1's library: `jit`, `debug`'s `getlocal`, `setlocal`,
`getregistry`, `getfenv`, `setfenv`, `upvalueid`, `upvaluejoin`, `sethook`, `gethook`, `debug.debug`,
`collectgarbage`, `gcinfo`, `getfenv`, `setfenv`, `module`, `newproxy`, `loadfile`, `arg` and
`package` but `path` and `loaded` are handles (`unmodelled` in `LuaLean/Interp.lean`), so a call of one stops the
run; `_VERSION` is LuaJIT's `"Lua 5.1"`.

How a script outside it is reported, from strongest to weakest. `lua-lean check f.lua` (`tools/Check.lean`) names,
by line and before anything is lifted, what of it the source shows: a parse error; a global LuaJIT has and the
semantics holds as a handle, or one neither defines (a host's: `ngx`, `love`); a library field that is a handle; a
`require` of a module outside the subset or not found as a file under the script's directories; `string.format`'s
`%a %o %u %p` in a constant format; `load` with an environment; `setmetatable(_G, …)`; a `goto` but the continue
idiom; `debug.getinfo` of a constant level or with `S` or `L` (or its default options), `debug.traceback` of a
constant message or none, `xpcall(f, debug.traceback)`, `debug.setmetatable` of a constant not a table. It lists the world's effects too (`io.open`), which are in the subset but make a function impure. Then it
calls each function the chunk defines at its top level with random arguments under the semantics and under LuaJIT
(`test/luasem.lua`, JIT on and off), the calls that reach no effect, and the results must be the same text. What only
a run meets (a `#t` with two borders, a double past a C cast's range) only that test, or a proof, finds.

1. **Fails to parse**: syntax outside the grammar (`lua-lean lift` prints the parser's error and exits 1). The
   translator handles every statement and assignment target the parser accepts (`test/stmts.lua` has each), so
   nothing that parses fails to translate.
2. **Stops the run**: a feature the semantics refuses is an effect no oracle answers, so no `RunP` about a run that
   reaches it can be proved: a read of a weak table that could see an entry the collector freed and a change of its
   mode or metatable ("Tables"), a metatable on `_G` or `package.loaded`, a chain of `__index` or `__newindex`
   tables that loops (LuaJIT stops it after 100 with an error; the semantics runs out of fuel),
   `%f` of a number below 1e-150 (where LuaJIT itself prints garbage), `error` with a level that counts out past a
   builtin (`pcall(error, "x", 2)`: its place is a call the builtin's frame hides), `string.format`'s `%a`, `%o`, `%u`
   and `%p`, a double outside the integer range where a
   builtin wants an integer (`("x"):rep(2^32)`, `("%d"):format(1/0)`, `math.ldexp(1, 2^31)`, a key of `table.move`
   past 32 bits; "Targets"), `tonumber(s, 2)` of `0b` and a binary digit (glibc 2.38's strtoul reads the prefix,
   older C libraries do not), `table.new` of a size above 65536, `#t` of a table with more than one border and `next`
   from an integer or a dropped key the table does not hold ("Tables"), a call into the world (*Effects*) no oracle
   answers or answers out of its form (`os.time`'s and `os.mktime`'s answer `[.num (.int t)]`, `os.localtime`'s the
   `*t` fields or none), `print` with a `tostring` of the script's own (its calls would come between print's writes),
   `os.date`'s `%Z %z %s %G %g %V`, glibc's flags, widths and `%E`/`%O`, a conversion it does not have or a year
   outside 1000..9999 in a format (C libraries print them their own ways), a format after `os.setlocale` (its names
   are the C locale's), a time past 2^53 to `os.date` or a difference past 2^53 from `os.difftime`, a field of
   `os.time`'s table past 2^30 or a date in it before 1900 (C libraries differ: macOS's mktime answers -1; the test's
   world, `Run.caseFx`, does not answer), `os.exit`; `load` or `loadstring` of a source the parser rejects (its
   message would be LuaJIT's parser's), of bytecode, with an environment table, or of a reader that raises an error,
   returns something neither nil nor a string, or comes with a mode without `t` (LuaJIT reads one piece first);
what reads a dump's bytes (`dumpBytes`): its length, `..` with a string or number, its methods (`d:sub`), a builtin
taking it as a string (`string.*`, `format`'s `%s`, `print`, `io.write`, `table.concat`, a `gsub` replacement,
`error` at a level, `assert`'s message, string.dump's flag), a table key, `==`, `<` or `rawequal` with a string or
another closure's dump, a result of the chunk; a message of a stripped function that names a local (LuaJIT finds
the name by scanning the bytecode back);
   `dofile` of a file not given as source, or of stdin; `require` when `package.path` is not a string; a yield in
   `xpcall`'s error handler (LuaJIT's xpcall then fails with `error in error handling`); a call of one of LuaJIT's
   functions outside the subset (`jit.flush`, `collectgarbage`, `debug.getlocal`; above); a `goto` to a label of its
   block that does not end it (`effect goto: …`, pcall or not); what of `debug` needs a call stack the semantics does
   not keep or lines a closure does not carry: `debug.getinfo` of a level 0 or above or with `S` or `L` for a Lua
   function (its default options have `S`), `debug.traceback` of a string, a number or nothing (its text is the
   stack's, the host's frames below the script's among them); `debug.setmetatable` of a value not a table (the
   metatable of its type), `debug.getmetatable` of a string, and the upvalues of a builtin that has some (`print`,
   `pairs`, `ipairs`, `type`, a `gmatch` iterator, a `coroutine.wrap` function: LuaJIT's own values).
3. **Known gaps**, where the semantics answers and LuaJIT may answer otherwise, so a proof could be about the wrong
   behaviour. Each is a task on the roadmap; until then a spec must not depend on them:
   - the place of an error where LuaJIT's line is not the parser's (`LuaLean/Parse.lean`'s sites follow where
     lj_parse.c emits each instruction): `o:m(...)` with `:m` and `(` on two lines reports a failed index of `o` on the
     line of `(`, LuaJIT on that of `m`; a constructor's `[k] = v` with `k` nil or NaN is reported at the enclosing
     site, or with no place; the name of an `and`/`or` operand, which LuaJIT may find by scanning the bytecode back;
     a builtin called as `__index` is named `?`;
   - the chunk's name: `c` in the differential test (`loadstring(src, "=c")`), a lifted file's base name, where
     LuaJIT names a file as it was given to it, and `require` and `dofile` by the path they open (the name `lua-lean
     run --lib` and the generator give a module);
   - `tostring` of a table, function or coroutine (an address in LuaJIT);
   - `getmetatable` of a string: nil, where LuaJIT gives the string metatable (`{__index = string}`);
   - a source `load` is given that LuaJIT rejects and the parser accepts (a `goto` with no visible label, more than
     200 locals, a call's `(` on the line after its function: "ambiguous syntax"): LuaJIT returns nil and a message,
     the semantics a function. `lua-lean parsecheck` finds these in a file, nothing in a string made at run time;
   - what `require` leaves in `package.loaded` while a module loads and after its load fails: an effect handle, a
     light userdata in LuaJIT (which LuaJIT 2.1 may show as a number);
   - a module not found on `package.path` is a handle, a C module the oracle answers, where LuaJIT may find no such
     module and raise an error;
   - a dump as the metamethod of two tables' different metatables, compared to decide `__eq`, `__lt` or `__le`: two
     dumps of distinct closures are unequal, where LuaJIT's bytes may be equal (one function made twice), and calls
     the dump (an error);
   - `getmetatable` of a dump: nil, as of any string above;
   - `type` of an effect handle (`io.read`, `os.getenv`, `math.random`): `userdata`, a function in LuaJIT; and a
     handle read rather than called (`jit.os`, `package.preload`) is a handle where LuaJIT has a
     string or a table. `lua-lean check` names each use.

The corpus (`test/corpus.txt`: 59 files of 29 projects, MIT, BSD or public domain, fetched at a pinned commit by
`lua-lean corpus`, never committed) measures the subset on scripts written for LuaJIT by others. `corpus` runs the
checker under the semantics only (it runs no effect, so nothing fetched runs outside it); `lua-lean check` on one of
them adds LuaJIT. On 2026-11-11: 53 of 59 parse (the 6 that do not are LuaJIT's own `jit/*.lua` at its master, in
the 3.0-backport syntax the subset leaves out: `&`, `>>`, `!=`, `a ? b : c`), 29 are in the subset (20 before
G3c's metamethods), and their 1192 top-level functions give 4575 calls that reach no effect. Outside it, by the
files that use each: `debug` 8, FFI 5, `__mode` 4, `string.dump` 3 (in the subset since #34), `setfenv` 3, `getfenv` 2, `jit` 2,
`bit` 2 (in the subset since #35),
`package.config` 2.

## Layout and use

| Path | What it is |
|---|---|
| `LuaLean/Num.lean` | numbers: the targets, integer and double arithmetic, printf's conversions on the exact value, `tonumber` (lj_strscan, with its 2^20 exponent bound) |
| `LuaLean/Syntax.lean`, `Parse.lean` | the syntax tree, with a `Site` (chunk, line, operand names) on each node that can raise an error, and the parser |
| `LuaLean/Pat.lean` | Lua patterns, after lstrlib.c's matcher |
| `LuaLean/Interp.lean` | the semantics |
| `LuaLean/Run.lean` | running a chunk as `test/luasem.lua` does under LuaJIT, its results as text, modules from a directory |
| `LuaLean/Show.lean` | a syntax tree as the Lean term that builds it |
| `LuaLean/Print.lean` | a syntax tree printed back as Lua (`lua-lean print`, `parsecheck`, `check`'s chunks) |
| `LuaLean/Shallow.lean` | the translator's target: one combinator and one lemma per interpreter clause |
| `LuaLean/Denote.lean` | the translator as a Lean function, `D.fn`, and the one proof for every program, `D.fn_ok`, that each `f_ok` is (`research/translator-proof.md`) |
| `LuaLean/Hoare.lean` | `RunP` and its rules |
| `LuaLean/Gen.lean` | random chunks for the differential test; a user adds its own (`swarm/model/SwarmModel/LuaCases.lean`) |
| `tools/*.lean` | the CLI's programs, run with `lake env lean --run` |
| `test/luasem.lua` | the LuaJIT side of the differential test |
| `test/cases.lua.gz` | the committed chunks |
| `test/*.lua` | scripts `check.sh` parses against LuaJIT and lifts with proofs |
| `test/out.txt`, `Refused.lean` | LuaJIT's syntax the subset leaves out, a chunk a line, and the check that the parser refuses each |
| `test/check/` | `lua-lean check`'s test: a script with each kind of construct outside the subset, and what check says |
| `test/corpus.txt` | the third-party scripts `lua-lean corpus` fetches and checks |
| `test/mods/*.lua` | modules the generator's chunks `require` and `dofile` (so LuaJIT runs a cases file from lua-lean/), lifted too |
| `Examples/` | `test/world.lua` lifted (`World.lean`, `check.sh` keeps it current) and its specs under named axioms about the world (`WorldSpec.lean`, the axioms each spec rests on pinned by `#guard_msgs`), each axiom tested against LuaJIT (`world_axioms.lua`) |

```sh
lua-lean/check.sh                              # gates, build, audit, committed chunks, test scripts: about 15 s
lua-lean/lua-lean lift f.lua [Ns [Imp:Const]] > F.lean   # the module; import it with LuaLean on the path
lua-lean/lua-lean prove f.lua...               # lift each and check its proofs in a scratch directory
lua-lean/lua-lean parsecheck f.lua...          # the parser against LuaJIT's bytecode
lua-lean/lua-lean run [--lib p=dir] f.lua      # f.lua under the semantics; luajit lua-lean/test/luasem.lua f.lua under LuaJIT
lua-lean/lua-lean difftest 3000                # fresh chunks under LuaJIT
lua-lean/lua-lean check f.lua...               # what is outside the subset, by line; its functions under LuaJIT
lua-lean/lua-lean corpus [dir]                 # the third-party corpus, fetched and checked (the semantics only)
lua-lean/lua-lean dump Name f.lua              # the tree as `def NameSrc : Block`, for proofs about the source itself
```

A Lake package uses it with `[[require]] name = "lua-lean" path = "<dir>"` (as `swarm/model/lakefile.toml` does)
and `import LuaLean`. Needs Lean 4.35 (elan, or nix, which the scripts fall back to) and the reference LuaJIT
(nix, or a `luajit` on the PATH).

## Gates

Every change keeps these: each semantics change is differentially tested against the reference LuaJIT (new behaviour
gets generator cases, as the exponent bound did); no `sorry`, `native_decide`, or axiom beyond Lean's three and the
user's named effect axioms; a feature outside the subset fails to parse, translate or prove, never yields a wrong
proof; a statement is never weakened to make a proof go through.

## Roadmap

- **G2** subset checker: `lua-lean check f.lua` and the corpus (done; "The subset"). Its commonest misses are
  tasks of their own: `debug` (#31, done without a call stack: "The subset"), weak tables (#32, done: "Tables"), function environments (#33),
  `string.dump` (#34, done: "The subset"), `bit` (#35, done: "The subset"), an FFI subset (#36), check's own (#37: a script's sibling modules as source). What #31 left for a model of the call stack (a level
  to `getinfo`, `traceback`'s text, a closure's source and lines) is #44.
- **G3** metamethods as LuaJIT 2.1 does them, in the interpreter, translator and rules: `__index`, `__newindex`,
  `__call`, read when used (G3a, done); arithmetic, `__unm`, `__concat`, `__len` (G3b, done); `__eq`/`__lt`/`__le`,
  `__tostring`, `__metatable` (G3c, done). `LuaLean/Hoare.lean` has a rule for each operator's metamethod and for
  comparisons of two tables of one metatable (`RunP.eq_meta`, `lt_meta`, `le_lt`).
- **G4** the standard library. Done: the rest of string, table and math, `select`/`tostring`/`tonumber` corners
  (G4a); `pairs` order opaque, `#t` with holes a stop (G4b); `os` and `io` as effects with named axioms (G4c). A model
  of LuaJIT's layout for number keys would make their order and every `#t` known.
- **G5** `load`, `dofile`, `require` of arbitrary modules: done (see the subset; `setfenv` and `load`'s environment
  wait for a model of function environments).
- **G6** coroutines: done ("Coroutines").
- **G7** heap abstraction, proof-producing: functions whose tables are provably unshared become pure Lean functions,
  with a proof they equal the heap-monadic lift.
- **G8** end to end: an LLM writes a script and its spec, the tool lifts it, the spec is proved; measured on a few
  realistic scripts.
- Done: one proof that the translator is correct for every program (`D.fn_ok`, `LuaLean/Denote.lean`) replaces the
  per-output proofs (boards #24, #38; `research/translator-proof.md`).
