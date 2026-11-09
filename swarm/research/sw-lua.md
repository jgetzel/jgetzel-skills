# sw-lua: porting the swarm CLI to LuaJIT, feasibility and plan

Task #69, 2026-11-08, sr-38. The question: can `swarm/swarm` (2,352 lines of stdlib Python) become LuaJIT
with the same CLI, db and hook interface, and how would the port and the cutover go? This doc is the
plan only. Nothing is ported; the user decides before any port task starts.

Evidence in this directory:
- `sw-lua-probe.lua` runs 56 checks of the libraries against what the Python code relies on.
- `sw-lua-hook.lua` is a line-for-line prototype of `swarm hook pre-tool` (Bash and Edit), used for §7.

Both ran under the LuaJIT in the user's flake pin (nixos-unstable, LuaJIT 2.1.1785763465).

## Verdict

**Feasible. Every stdlib piece has a library that works under LuaJIT and is in nixpkgs, for x86_64-linux,
aarch64-linux and aarch64-darwin.** The libraries are not the risk. These are:

1. **Semantic port bugs.** Python's truthiness, `None`/JSON `null`, 0-based slices, ordered dicts and
   stable sort all differ in Lua (§2).
2. **Code with no library equivalent.** `difflib.SequenceMatcher` has none and needs a faithful port of
   about 150 lines. The conflict tests depend on its exact opcodes.
3. **About 20 tests that call Python internals.** They have to become CLI tests or Lua specs (§5).
4. **Install outside Nix.** It means the interpreter plus 4 C rocks, where today the CLI needs only
   `python3`. The Homebrew and apt routes are written down, but they were not tried here (§4).

The speed gain is large (each hook call drops from ~520M instructions to ~18M, §7), though speed was
not the goal.

**Recommendation:** port it as below if moving off Python is the goal. Prepare the oracle in Python first
(task P0), so the test suite is proven language-neutral before any Lua exists.

## 1. Libraries

Each row was checked by `sw-lua-probe.lua` under LuaJIT, unless it says otherwise.

| Python | Lua (nixpkgs `luajitPackages.*`, rock) | Checked | Notes |
|---|---|---|---|
| `sqlite3` | `lsqlite3` 0.9.7 | WAL; `begin immediate`; SQLITE_BUSY after `busy_timeout`; read-only `file:…?mode=ro` URI (`cmd_state`); NULL → `nil` in `nrows`; 2^53 round-trips | No `in_transaction`: `tx()` tracks its nesting depth in Lua. Python's `OperationalError` becomes a return code, so check every `exec` |
| `json` | `lua-cjson` 2.1.0.10 | decode errors raise; `empty_array` and `array_mt` exist | `null` decodes to the **truthy** `cjson.null`, so wrap decode to turn it into `nil`. `{}` encodes as an object, so mark arrays. Set `encode_number_precision(16)`: the default of 14 prints 2^53 as `9.007199254741e+15`. Set `encode_escape_forward_slash(false)`. Output is raw UTF-8 where Python writes `\u` escapes; both are valid JSON. `dkjson` can decode null to nil, but it is pure Lua and slower on the 300 KB transcript tail |
| `subprocess.run` | `luaposix` 37.0 (`posix.unistd` fork/exec/pipe/dup2, `posix.poll`, `posix.sys.wait`) | stdout and stderr kept apart, exit code, stdin input, cwd, env; 300 KB on both pipes without deadlock; timeout kill; a missing binary exits 127 | The code uses no timeouts today. A `proc.run(argv, {cwd, input, env, merge, stdout_file})` helper is ~50 lines; the probe has a working one |
| `re` | `lrexlib-pcre2` 2.9.4 (`rex_pcre2`) | `HEAVY_RE` alternation and `\b`; `HUNK` with `re.S\|re.M` and lazy groups; lookbehind; a bad pattern raises | **Must be PCRE2, not LPeg or Lua patterns**: users write Python regexes into `.claude/swarm.json` (`heavy`, `run.env`, `find`). Compile with `UTF\|UCP`, or `TOK = \w+\|…` splits `é` into bytes (checked). `fullmatch` becomes `^(?:p)\z`, not `$`. `re.escape`, `findall` and `sub` are small wrappers in `re.lua` |
| `argparse` | `argparse` 0.7.2 | nested subcommands, `convert`, defaults, flags between positionals, `--` passes the rest through | Bad usage exits **1**; the tests expect Python's **2** (`test_claim_lease_done`), so use `pparse` and exit 2. `swarm run make -j4` without `--` is an error; Python's `REMAINDER` accepts it, so give `run` a pre-split at its first positional. Usage text differs (no test checks it) |
| `os.path`, `glob`, `fnmatch`, `os.readlink/symlink/kill/sysconf/getppid` | `luaposix` (`posix.stdlib.realpath`, `posix.glob`, `posix.fnmatch`, `posix.unistd`, `posix.signal`) | all of these | `fnmatch` without `FNM_PATHNAME` lets `*` cross `/`, as Python's does |
| `os.makedirs`, `listdir`, `getmtime`, `shutil.copy2` | `luafilesystem` 1.9.0 | mkdir, attributes, `touch` sets mtime | `copy2` must keep the index mtime (racy-git comment in `snapshot`): copy, then `lfs.touch` |
| `tempfile` | `posix.stdlib.mkdtemp`, `$TMPDIR` or `/tmp` | mkdtemp | `TemporaryDirectory` cleanup is a small recursive rm |
| `time`, `datetime.fromisoformat` | `os.time`, `os.date`, `posix.time.nanosleep`, `posix.sys.time.gettimeofday` | 0.2 s sleep; `%H:%M`; ISO `…Z` → epoch matches Python in local TZ and UTC | Lua has no `timegm`: subtract the offset (5 lines, in the probe) |
| `difflib.SequenceMatcher` | **none** | — | Port `find_longest_match`, `get_matching_blocks` and `get_opcodes` with `autojunk=False` faithfully (~150 lines). Any other diff changes which conflict tests see a clash |
| `shlex.quote/join` | 3 lines | — | |
| str slicing `[:80]`, `{:<12}` | `luautf8` 0.2.1 | byte `sub` cuts `é` in half; `luautf8.sub` doesn't | Byte truncation can write invalid UTF-8 into the db and the panel JSON |
| `unittest` | Lua specs as plain `assert` scripts run by `luajit` (`busted` 2.3.0 also loads) | busted loads | Prefer plain scripts: busted is one more dependency for 5 specs (§5) |

Not needed: `fcntl` (imported, never used), `contextlib` (`tx(c, fn)` with `pcall`), `signal` (one
`kill(pid, SIGTERM)`). Considered and dropped:
- `luv`, a whole event loop for what fork/exec covers.
- `lua-subprocess`, scm-1 and unmaintained.
- `lsqlite3complete`, which isn't in nixpkgs.

## 2. LuaJIT caveats that bite this code

- **Lua 5.1 semantics.** LuaJIT is built with 5.2 compat (`goto` works), but there is no integer
  subtype, no `utf8` library and no `//`. `0` and `""` are truthy. Every `if x:` and `x or y` where x can
  be `""`, `0`, `[]` or `None` needs review. Examples: `p.get("cwd") or os.getcwd()`, and `if why:`
  where `why` comes back from `fence`. This is the largest bug source.
- **JSON null.** `cjson.null` is truthy. `(j.get("message") or {}).get("usage")` would index a userdata.
  Decode through one wrapper that turns null into nil.
- **Numbers are doubles.** sqlite int64 values are exact up to 2^53. Every value here (rowids,
  timestamps, PIDs, token counts, GitHub run ids around 2^35) is far below that. Use `("%d"):format(n)`,
  never `tostring`: `tostring(1e15)` is `"1e+15"`. `x // y` becomes `math.floor(x / y)`. `%` is floored
  in both languages.
- **1-based indexes and nil holes.** `#t` is undefined on a table with holes, so a row read
  positionally with a NULL in the middle breaks. Always use `nrows` with named columns, never positional
  `r[1]` (Python does `pragma table_info` → `r[1]`).
- **Table order.** Python dicts keep insertion order; `pairs` order is arbitrary. Anything printed
  (VIEWS, JSON key order, `{k: v}` loops in `touch(**kw)`) must iterate an array. JSON consumers don't
  care about key order; the board text does.
- **`table.sort` is not stable** (the probe saw ties reorder). Python's `sorted` always is. Sort on
  `(key, original index)` wherever ties can occur (the board, pool order, `hv` by RSS).
- **Strings are bytes.** Truncation, `%-12s` padding and `.lower()` all act on bytes. Use `luautf8` for
  `[:n]` cuts. Alignment of non-ASCII agent names is cosmetic.
- **`os.time()` and `os.date`.** `os.time()` is integral seconds, the same as `int(time.time())`.
  `os.time{…}` reads local time, hence the UTC fix in §1. Sub-second timing needs `gettimeofday`.
- **`die()` inside `tx`.** Python's `SystemExit` unwinds through `tx`'s rollback. In Lua, `die` should
  `error({exit = code})`, `tx` uses `pcall` → rollback → rethrow, and `main` turns it into `os.exit`.
  (SQLite also rolls back an open transaction at process exit, but the explicit path keeps tests honest.)
- **`require "posix"` loads every submodule** (33M instructions against 16M for the hook, §7). Require
  `posix.unistd` and the others individually.

## 3. Module layout and how the entry finds it

```
swarm/swarm                 POSIX sh launcher (§4): resolves symlinks, checks deps, execs luajit
swarm/lua/swarm/main.lua    argparse table, dispatch, the fence check
swarm/lua/swarm/util.lua    die, now, ago/hhmm/dur, strings (split, strip, utf8 cut), shlex
swarm/lua/swarm/proc.lua    run(argv, opts), git(args, cwd), gx
swarm/lua/swarm/json.lua    cjson configured; decode with null→nil; array marker
swarm/lua/swarm/re.lua      Python-shaped search/match/fullmatch/findall/sub/escape on rex_pcre2, UTF|UCP
swarm/lua/swarm/db.lua      SCHEMA, connect + column migrations, tx, one/all/exec, log
swarm/lua/swarm/agents.lua  fence, touch, bind, live_agents, cold rule, set_status
swarm/lua/swarm/msgs.lua    post, unread, advance, deliver, capped, peer_note; cmd post/read/wait
swarm/lua/swarm/tasks.lua   task_timing, deps/pool/dep_path, cmd task/board/rules, reserve/unreserve
swarm/lua/swarm/locks.lua   repo_rel, covers, lock_holder; cmd lock/unlock
swarm/lua/swarm/hook.lua    hook(), emit, ctx_from, handoff_nudge, comms_nudge, post_compact, is_heavy
swarm/lua/swarm/machine.lua /proc: read_procs, mem_psi, machine_note, claude_pid (the macOS seam, §8)
swarm/lua/swarm/difflib.lua SequenceMatcher port
swarm/lua/swarm/conflict.lua edits, clash, real_hunk, snapshot, trial_merge, conflict_tick
swarm/lua/swarm/watchd.lua  reap, landed, end_agent, sweep_worktrees, lifecycle, machine_tick, cmd watchd/spawn
swarm/lua/swarm/ci.lua      pr_ci, ci_poll, ci_check, cmd ci
swarm/lua/swarm/run.lua     cmd run, remote jobs, rsync/ssh
swarm/lua/swarm/state.lua   cmd state --json, VIEWS, watch
swarm/lua/test/*.lua        specs for what a CLI test can't reach (§5)
```

The sizes follow the Python sections, from ~35 lines (locks) to ~320 (commands). No module is
over ~350 lines.

**Convention:** a cross-module call goes through the module table (`proc.run(...)`, not a `local run`
upvalue), so a spec can patch it the way the Python tests patch `m.run`.

**How the entry finds its modules.** There are two symlink chains:
- `~/.claude/skills/swarm` (a dir symlink) → `<main checkout>/swarm`.
- `.git/swarm/bin/swarm` (a file symlink) → `<main checkout>/swarm/swarm`.

A worktree runs its own `swarm/swarm`. So the launcher resolves `$0` through file links with a portable
`readlink` loop, then `cd -P`s the directory for dir links. It sets
`LUA_PATH="$here/lua/?.lua;<user rock tree>;;"`, where the trailing `;;` keeps the defaults. Then it
execs `luajit "$here/lua/swarm/main.lua"`.

The Nix `luajit.withPackages` binary is an ELF wrapper that **prepends** its own paths to the caller's
`LUA_PATH`; it doesn't replace it (checked). So the launcher's path survives. Everything stays relative
to the real file: each worktree runs its own modules, and the live skill runs the main checkout's.

`HERE` in Python (spawn's `settings.template.json`, `brief.md`, `../relaunch/launch.sh`) becomes
`os.getenv("SWARM_HERE")`, which the launcher exports.

## 4. Install, per platform, and what happens when a piece is missing

**What is needed.** LuaJIT 2.1 plus 7 rocks: `lsqlite3`, `lua-cjson`, `luaposix`, `lrexlib-pcre2`,
`luafilesystem`, `argparse` and `luautf8`. Four of them are C (`lsqlite3`, `lua-cjson`, `luaposix`,
`lrexlib-pcre2`). The rockspecs, read from the nixpkgs build outputs, need the system headers
`SQLITE` (`sqlite3.h`) and `PCRE2` (`pcre2.h`, `-lpcre2-8`).

**NixOS (this machine and the laptop).** Both hosts import `home/modules/packages.nix` through
`common.nix`. The draft change below is for the user to apply; `/etc/nixos` was not edited.

```diff
--- a/home/modules/packages.nix
+++ b/home/modules/packages.nix
@@ -9,6 +9,9 @@
     nodejs
     pi-coding-agent
     python3
+
+    # swarm CLI (jgetzel-skills/swarm) runs on LuaJIT; see its research/sw-lua.md.
+    (luajit.withPackages (p: with p; [ lsqlite3 lua-cjson luaposix lrexlib-pcre2 luafilesystem argparse luautf8 ]))
     pwvucontrol
```

Checked on a copy of `/etc/nixos`:
- `home.packages` evaluates on **desktop and laptop**, and no other Lua package is there to collide.
- The resulting `luajit-2.1.1785763465-env` derivation built (all from cache) and loads all 7 modules.
- `luajit` is not on PATH today.

Apply it with `sudo nixos-rebuild switch --flake /etc/nixos` on each host. Keep `python3`: other skills
and `install.py` still use it.

**macOS with Nix** (nix-darwin or standalone home-manager). Add the same `luajit.withPackages …` to
`home.packages`. nixpkgs marks every piece available on **aarch64-darwin**. On **x86_64-darwin** this
pin has none of them, so an Intel Mac uses Homebrew.

**macOS with Homebrew** (not run here: no Mac, and luarocks.org downloads were refused in this session):

```sh
brew install luajit luarocks sqlite pcre2
LR="luarocks --lua-version=5.1 --lua-dir=$(brew --prefix luajit) --tree ${XDG_DATA_HOME:-$HOME/.local/share}/swarm/lua"
$LR install lsqlite3 SQLITE_DIR="$(brew --prefix sqlite)"
$LR install lrexlib-pcre2 PCRE2_DIR="$(brew --prefix pcre2)"
for r in lua-cjson luaposix luafilesystem argparse luautf8; do $LR install $r; done
```

**Plain Linux.** Debian/Ubuntu: `sudo apt install luajit libluajit-5.1-dev luarocks libsqlite3-dev
libpcre2-dev build-essential`. Fedora: `sudo dnf install luajit luajit-devel luarocks sqlite-devel
pcre2-devel gcc`. Then run the same `luarocks --lua-version=5.1 --tree …` lines, without the `_DIR`
arguments (headers are in standard paths). Distro `lua-*` packages exist for some rocks, but they
target the distro's default Lua (often 5.4), so the luarocks tree is the one uniform route.

**Why a per-user rock tree.** It lives at `~/.local/share/swarm/lua`, not inside the repo, because every
worktree runs its own `swarm/swarm` and a tree inside the repo would be missing from new worktrees. The
launcher adds that tree to `LUA_PATH`/`LUA_CPATH`, so nothing needs `eval $(luarocks path)` in a shell
profile. That matters because hooks run with whatever environment Claude Code has.

**`install.sh` detects the route:**
1. `luajit` on PATH and all 7 `require`s succeed → done.
2. Else `nix` is present → print the `home.packages` line (or `nix profile install` of the same
   `withPackages` expression for non-home-manager users).
3. Else `brew` → run the Homebrew lines.
4. Else `apt-get`/`dnf` → print the distro line (it needs sudo), then run the luarocks lines.

It re-checks at the end and exits nonzero with the missing list. It installs only into the user tree
and never runs sudo itself.

**When LuaJIT or a library is missing.** Today `#!/usr/bin/env luajit` would print
`env: 'luajit': No such file or directory` and exit 127. Claude Code treats an exit other than 2 as a
non-blocking hook error, so agents would run silently without swarm hooks, which is the worst outcome.
The design:

- **One check, two places.** The launcher checks `command -v luajit`. Then `main.lua` runs
  `pcall(require, m)` for each rock before any work. It has to require them anyway, so the check costs
  nothing. Both produce the same message: what is missing, and the install command for the detected
  platform (or "run `<repo>/install.sh`").
- **Commands** (`board`, `task`, `post`, …) print that message on stderr and exit 127.
  `swarm spawn` and `watchd` hit it before launching anything, so a half-installed machine can't start
  agents.
- **Hooks don't block.** Exit 2 on `PreToolUse` would block every tool, including the one that installs
  LuaJIT. Instead a hook prints valid hook JSON: `additionalContext` ("swarm hooks are OFF: <missing>;
  install with <cmd>") for the events that support it (SessionStart, UserPromptSubmit, Pre/PostToolUse),
  plus a top-level `systemMessage` so the human sees it too. It exits 0. The agent is told on every call
  and is never stuck. The `stop` hook (no context field) writes stderr and exits 1.
- **During the cutover window only,** the launcher falls back to `python3 swarm.py` when Lua deps are
  missing, so a host that pulls main before installing LuaJIT keeps working. It is removed in P11
  (compat cleanup).

## 5. Test strategy: `test_swarm.py` as the oracle

`test_swarm.py` (91 tests) drives the CLI as a subprocess with fakebins. It becomes language-neutral
with these changes:

- **Line 5:** `SWARM = os.environ.get("SWARM_CLI") or os.path.join(…, "swarm")`.
- **Exec the script directly.** The 9 call sites `[sys.executable, SWARM, …]` and
  `[sys.executable, "-B", SWARM, …]` (lines 33, 266, 362, 365, 1160, 1174, 1361, 1440, 1589) become
  `[SWARM, …]`. Both CLIs have a shebang.
- **Fakebins stay Python** (`#!{sys.executable}`). They are test infrastructure, not the CLI.
- **Lua specs run from the suite.** One Python test runs `luajit swarm/lua/test/run.lua` when
  `SWARM_CLI` is the Lua CLI. The gate stays one command: `python3 -B swarm/test_swarm.py`.

**20 tests import Python internals**, not 3. Each is one of three kinds.

**A. The patched thing is an external command or env. Make it a CLI test (15 tests).** Drive
`swarm watchd --once` (with `--max-agents`/`--min-free-mem`, `--ci`, `--comms`), `swarm spawn` or
`swarm board` / `state --json`, with fakes:

- A fake `hc` on PATH (`hc ls --json` prints the live terminals; `fake_remote` already writes one)
  replaces `m.hc_terminals = …` and `reap(live_addrs=…)`.
- A fake `gh` on PATH that logs its calls (`test_ci_red_is_one_task_closed_on_green` already does this)
  replaces `m.run = fake` for gh, and the `m.landed` call counter (count `gh pr list` lines in the log).
- A new env seam, **`SWARM_LAUNCH`**, replaces the absolute `HERE/../relaunch/launch.sh` path, which no
  PATH fakebin can replace. It follows the existing `SWARM_PROC` precedent.
- `m.pool(c)` order is read from `swarm board` / `state --json`.

The 15 tests: `test_reaping`, `test_takeover_then_predecessor_death_keeps_agent_claims_locks`,
`test_deps_list_holds_until_last_done`, `test_sweep_caches_not_landed`,
`test_missing_worktree_squash_merged_branch_ended`, `test_pr_ci_merge_to_green`,
`test_ci_poll_once_for_all`, `test_block_unblock`, `test_hc_blocked_marks_task`,
`test_auto_spawn_once_within_cap`, `test_spawn_task_claims_before_launch`,
`test_spawn_launch_failure_keeps_live_agent`, `test_spawn_task_launch_failure_rolls_back`,
`test_rules_appended_to_spawn` and `test_ci_red_is_one_task_closed_on_green`.

**B. Races: a peer writes between two statements (4 tests). Make them Lua specs.**
`test_reap_spares_row_rebound_after_hc_ls`, `test_done_after_reap_and_reclaim_fails`,
`test_reap_keeps_renew_after_its_select` and `test_auto_spawn_skips_lost_race`. The Python `racing()`
proxy maps directly onto patching `db.all`/`db.one` (or `tasks.pool`) in a spec. A CLI-level seam (an
env var naming a SQL fragment and a shell command) would also work, but it puts test code in every
`connect`; the specs keep production clean.

**C. A pure function (1 test). Make it a Lua spec.** `test_real_hunk_probe_asserts` becomes a spec on
`conflict.real_hunk`.

**Extra oracle with real data:** run both CLIs read-only on one **copy** of a real board (`board --all`,
`who`, `task show N`, `state --json --view …` for each view) and diff the output. It catches ordering
and formatting drift the fixtures don't. The copy uses `SWARM_DB`, as this doc's measurements did.

## 6. Splitting the port, and the cutover

**P0 (Python, before any Lua).** Make the oracle language-neutral:
- Add `SWARM_CLI` and direct exec.
- Add the `SWARM_LAUNCH` seam to the Python CLI.
- Convert the 15 kind-A tests.

Done when the suite is green on Python. This proves the oracle doesn't depend on Python internals.

**P1 (blocks all others; after P0).** Build the foundation:
- The launcher at `swarm/swarm-lua` and the missing-deps message.
- `util`, `proc`, `json`, `re` and `db`.
- `main.lua` with the full argparse table (exit 2), where every command not yet ported dies "not ported".
- The spec runner, and the suite hook that runs it.

Done when `SWARM_CLI=swarm/swarm-lua python3 -B swarm/test_swarm.py` runs, and the join/leave/who tests
pass.

**P2 tasks and P3 agents+messages (parallel, after P1).** Almost every other test calls `task add/claim`
and `join`, so these two come first.
- P2: `tasks.lua`. Done when the "tasks", deps/after, drop and block tests pass.
- P3: `agents.lua`, `msgs.lua` and the cold-cache rule. Done when the fencing, messages, cold-cache and
  wait tests pass.

**Then in parallel (after P2 and P3).** Each is done when its tests pass against the Lua CLI:

| Task | Modules | Done when these pass |
|---|---|---|
| P4 | `hook.lua` + `machine.lua` | ctx notes, post-compact, stop hook, shared-tree, `test_machine_note_and_patterns` |
| P5 | `locks.lua` + `difflib.lua` + `conflict.lua` | conflicts, locks sections + real_hunk spec |
| P6 | `watchd.lua` (reap, sweep, lifecycle, spawn, pressure) | lifecycle, sweep, spawn tests, `test_pressure_edge_oom_and_orphans` + the 4 race specs |
| P7 | `ci.lua` | the ci tests |
| P8 | `run.lua` | the "swarm run" section |
| P9 | `state.lua` | the `state_json*` tests, `test_board_who` |

**P10 (cutover, after all).** The full suite passes on Lua and the real-board diff is clean. Then one
atomic PR:
- `git mv swarm/swarm swarm/swarm.py` and `git mv swarm/swarm-lua swarm/swarm`.
- `herdr/mods/swarm/main.js` (both `exec`s) and the string in `herdr/install.py` drop `python3`, so
  the panel runs the script directly.
- `install.sh` gets the dependency check.
- Update the DESIGN.md lines that say "python3 stdlib".

What stays the same:
- The CLI (argv, output text, exit codes).
- The db (same `SCHEMA` and migrations).
- The hooks (stdin JSON in, stdout JSON out).
- `settings.template.json`'s `{{SWARM}}`, and the `.git/swarm/bin/swarm` symlink, which still point
  at `swarm/swarm`.

Live swarms switch when the main checkout pulls. Their next hook call runs Lua against the same db,
with the python fallback (§4) covering any host without LuaJIT. Rollback is a revert of that one PR.

**P11 (after live swarms have migrated).** Delete `swarm.py` and the launcher's python fallback.

**P12 (optional, separate).** A macOS backend for `machine.lua` (§8).

Install the flake change on both hosts before P10 lands.

## 7. Measurements

**Setup.** hyperfine 2.0, 200 runs, 10 warmups. Hooks ran against a **copy** of this repo's board
(54 agents, 1,515 events) via `SWARM_DB`. The machine was busy (load about 24 on 12 cores, from other
sessions' ghc, cargo and nix builds), so wall time is noisy. Instruction counts don't depend on load.

| | wall median | CPU median | instructions | peak RSS |
|---|---:|---:|---:|---:|
| `python3 -c pass` | 37.8 ms | 28.1 ms | 81 M | 12 MB |
| python3 + the CLI's 18 stdlib imports | 80.9 ms | 61.4 ms | 175 M | 17 MB |
| **py `hook pre-tool`, Bash `git status`** | 229.5 ms | 162.9 ms | **518 M** | 29 MB |
| **py `hook pre-tool`, Edit** | 161.5 ms | 148.3 ms | **521 M** | 29 MB |
| **py `hook post-tool`** | 148.9 ms | 133.2 ms | **518 M** | 29 MB |
| `luajit -e ''` | 7.8 ms | 4.9 ms | 11 M | 4 MB |
| luajit + `require "posix"` (all submodules) and the rest | 24.7 ms | 17.0 ms | 33 M | 5 MB |
| **lua prototype pre-tool, Bash** | 17.1 ms | 9.8 ms | **16 M** | 6 MB |
| **lua prototype pre-tool, Edit** | 15.7 ms | 12.8 ms | **18 M** | 6 MB |
| sh launcher (readlink loop + `cd -P`) + `luajit -e ''` | — | 11.8 ms | 23 M | — |
| `git rev-parse --show-toplevel` (both Edit hooks run one) | 5.6 ms | 4.9 ms | 11 M | 6 MB |

**Reading it:**
- A Python hook costs ~520M instructions. A third of its CPU (50 ms of ~150) is **compiling the
  2,352-line file on every call**: a script run as `__main__` never gets a `.pyc`. The imports are
  another ~95M.
- The Lua prototype does the same db work in 16–18M, about 30× fewer instructions. Adding the sh
  launcher brings it to about 30M, still about 17× fewer.
- The prototype skips the SendMessage, heavy-note and shared-tree branches; those are a few queries
  each. Its deny output matched Python's byte for byte apart from cjson's `\/`, which is fixed by
  `encode_escape_forward_slash(false)`.
- An aside, since speed wasn't the goal: a 3-line Python `swarm/swarm` that imports a `swarm_cli.py`
  module would get the `.pyc` and save that third without a port.

## 8. macOS: what is Linux-only today, in either language

The language doesn't change these:

| Python today | macOS equivalent |
|---|---|
| `/proc/meminfo` (`mem_available_gib`, `mem_psi`) | `sysctl -n hw.memsize` + `vm_stat` (free + inactive + speculative pages × page size) |
| `/proc/pressure/{memory,cpu}` (PSI avg10) | none. `sysctl kern.memorystatus_level` (free-memory %) or `memory_pressure -Q` as a stand-in |
| `read_procs` (`/proc/<pid>/stat`, `cmdline`, `uptime`) | one `ps -axo pid=,ppid=,rss=,etime=,comm=,args=` |
| `claude_pid` ppid walk (`/proc/<pid>/comm`, `stat`) | `ps -o ppid=,comm= -p <pid>` per step, or the `ps -ax` table above |
| `readlink /proc/<pid>/cwd` (sweep, orphan kills) | `lsof -a -d cwd -p <pid> -Fn` |
| `/proc/<pid>/oom_score_adj` (bias builds before agents) | none (jetsam isn't user-tunable); skip on macOS |
| `os.path.exists("/proc/<pid>")` (`waiter`) | `kill(pid, 0)`, which is portable; use it on Linux too |
| remote `nproc; cat /proc/loadavg /proc/meminfo /proc/pressure/memory` | `sysctl -n hw.ncpu vm.loadavg hw.memsize; vm_stat` |
| `rsync --mkpath --filter=':- .gitignore'` (swarm run) | macOS 15 ships openrsync; whether it supports both flags is unchecked. Requiring Homebrew `rsync` is the safe default |
| `git merge-tree --write-tree` (needs git ≥ 2.38) | Apple git 2.39+ is fine |

Whether `hc` and the Herdr app run on macOS was not checked; spawn, reap and the panel need them.

**Recommendation:** the port puts every one of these behind `machine.lua`, whose functions are
`mem()`, `psi()`, `procs()`, `proc_cwd(pid)`, `oom_bias(pid)` and `remote_probe_cmd()`. P6 is
otherwise behavior-preserving. A `darwin` branch is task P12, with its own fake `ps`/`sysctl` fakebins,
because nobody here can test on a Mac. Until then, on macOS, `machine.lua` returns "unknown" and the
machine note says so. Nothing crashes.

## 9. Against a compiled language (Rust or Go, prebuilt binaries)

| | Lua (this plan) | Go or Rust binary |
|---|---|---|
| Install | interpreter + 7 rocks (4 C, need sqlite and pcre2 headers outside Nix) | download one file per platform; no runtime or libraries. Go with `modernc.org/sqlite` (pure Go) is fully static; Rust `rusqlite` with `bundled` compiles sqlite in |
| Release | none: the checkout is the release | CI matrix (linux x86_64/aarch64, macOS arm64/x86_64) on every merge; GitHub Releases. Go cross-compiles from one runner (`GOOS/GOARCH`, CGO off). Rust needs per-target C toolchains (`cargo-zigbuild` or native runners) for bundled sqlite |
| macOS signing | none | arm64 binaries need an ad-hoc signature, which both linkers add. `curl` doesn't set the quarantine flag, so Gatekeeper doesn't block an `install.sh` download. Notarization is only needed for browser downloads |
| Agents editing the skill | edit, then run; the tests drive the file they just changed | edit, build, run. Go is ~1–2 s incremental, Rust ~5–30 s, per worktree. Worse: **the live skill is the main checkout, symlinked.** After a merge, the running binary is stale until someone rebuilds or downloads the release, so "merged = live" breaks. That needs a new step (watchd rebuilds on main moving, or install fetches the release for `HEAD`) |
| Regex for user patterns | PCRE2 ≈ Python `re` | Go `regexp` is RE2 (no lookbehind or backrefs; today's patterns would pass, users' future ones might not). Rust `regex` is the same; `fancy-regex` adds lookaround |
| Nix | `luajit.withPackages` | `buildGoModule`/`rustPlatform` with the repo as a flake input; each change is a `flake update` + rebuild, which fights the live-symlink model |

**Recommendation for this skill:** stay interpreted. Agents change its source many times a day, and it
runs live from a checkout. The edit-and-run loop and "merged means live" are worth more than a
zero-dependency install.

Between the interpreted options:
- Python has the smallest install (no dependencies).
- LuaJIT is faster (§7) and is what the user wants to standardize on.
- Go would be the pick only if the skill were shipped to many users who never edit it.

## Not done or not verified

- **No port.** That is per the task.
- **Homebrew and apt/dnf + luarocks commands were not run.** There is no Mac here, and luarocks.org
  downloads were refused in this session. Rock names and their external-dependency variables come from
  the rockspecs in the nixpkgs build outputs.
- **`/etc/nixos` was not edited.** The diff was tested on a copy.
- **openrsync flag support and `hc` on macOS are unchecked.**
- **Wall times are from a heavily loaded machine.** Compare the instruction counts instead.
