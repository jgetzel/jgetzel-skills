# sw-lua-runtime: ship swarm's Lua runtime as one prebuilt binary

**Decision (2026-11-08, user): not built.** No prebuilt runtime ships. Users get LuaJIT plus the 7 rocks from their own package manager (like pip for Python skills): the root `flake.nix` for Nix users, Homebrew via `install.sh`, or distro packages + luarocks.

Task #83, 2026-11-08, sr-65. The question: can swarm install with nothing to set up, the way Neovim embeds
LuaJIT so lazy.nvim needs no system Lua? The idea is one small prebuilt binary per platform: LuaJIT plus
the C libraries the CLI needs, linked in. It runs the `.lua` files from the checkout, so scripts stay
edit-and-run and "merged means live" still holds. Only the runtime is released, and it changes rarely.

This doc is research. No release pipeline, launcher change or install change was made. The user decides
before any of that is built.

Evidence in this directory:
- `sw-lua-runtime/build.sh` builds the runtime for any of the four targets with `zig cc`.
- `sw-lua-runtime/init.c` is the 58-line `luaL_openlibs` that preloads the rocks.

## Verdict

**It works, and it's cheap.** One script cross-built all four targets from this x86_64 NixOS machine with
nothing but zig and make:

| Target | Raw | gzip -9 | Links against | Checked |
|---|---|---|---|---|
| x86_64-linux (musl, static) | 2.70 MB | 1.27 MB | nothing (`not a dynamic executable`) | **full suite passes**: 93 tests OK, 6 skipped (the same Python-only ones the Lua specs cover) |
| aarch64-linux (musl, static) | 2.54 MB | 1.24 MB | nothing | **the suite under `qemu-aarch64`**: 93 OK, 6 skipped |
| aarch64-macos | 2.89 MB | 1.22 MB | `libSystem.B.dylib` only | builds; signed `ADHOC \| LINKER_SIGNED` (rcodesign). **Not run**: there's no Mac here |
| x86_64-macos | 2.81 MB | 1.24 MB | `libSystem.B.dylib` only | builds, unsigned (Intel Macs don't require a signature). **Not run** |

The binary is a drop-in `luajit`: it is LuaJIT's own `luajit.c` front end, so `-e`, the REPL and
`luajit spec.lua` all work, with every rock swarm needs already in `package.preload`. Startup is faster
too. 200 runs that require 8 of the rocks take 0.42 s with the static binary, against 1.35 s with the
Nix `luajit.withPackages` (which dlopens a `.so` per rock).

**Recommendation (§6): build it.** Use one Ubuntu job with zig for releases. The checksums live in the
repo, and the launcher fetches the pinned runtime by itself. Keep `luajit` on PATH as the fallback, so
the Nix, Homebrew and luarocks routes keep working unchanged.

## 1. How to build it

**The way that worked: LuaJIT's own Makefile for `libluajit.a` and `luajit.o`, plus each library's C files
compiled straight into one link.** No luarocks, no CMake, and no per-library build system. The whole
recipe is `build.sh`, about 70 lines. It needs only `zig`, `make` and `od`.

- **LuaJIT.** `make -C src libluajit.a luajit.o BUILDMODE=static CC="zig cc -target $T" HOST_CC="zig cc"
  TARGET_SYS=Linux|Darwin TARGET_AR="zig ar rcus"`. `HOST_CC` builds `minilua` and `buildvm` for the
  build machine. Those generate the VM assembly for the target. This is LuaJIT's documented cross-build
  path. No `LUAJIT_ENABLE_LUA52COMPAT`, to match the nixpkgs `luajit` the port was tested on.
- **Preloads.** `init.c` is a copy of LuaJIT's `lib_init.c` with more `lj_lib_preload` rows (`lsqlite3`,
  `cjson`, `lfs`, `rex_pcre2`, `lua-utf8`, `argparse` and 10 `posix.*`). It also sets a global
  `SWARM_RUNTIME` (the version string). It is linked **ahead of** `libluajit.a`, so the linker never
  pulls the archive's `lib_init.o`. There's no need to patch LuaJIT or run `ar d`. Preload is the first
  searcher, so a stale rock tree or `LUA_CPATH` can't shadow a built-in module.
- **argparse** is pure Lua. Its source goes into `init.c` as a byte array (`od -An -tu1`) and is
  `luaL_loadbuffer`ed on `require`. The C23 `#embed` would be neater, but zig 0.17 fails on it ("failed to
  read …init.o.d").
- **sqlite** is the 3.53.3 amalgamation from sqlite.org (sha256 `646421e1…0431`), not the older copy
  lsqlite3 ships. `-DSQLITE_OMIT_LOAD_EXTENSION` can't be used, because lsqlite3 calls
  `sqlite3_load_extension` unconditionally.
- **pcre2** 10.49 is built from `config.h.generic` with `-DSUPPORT_UNICODE` and no JIT. Linking
  `pcre2_jit_compile.c` without `SUPPORT_JIT` only provides the stubs lrexlib references. On macOS a
  JIT would need `MAP_JIT` and, under a hardened runtime, an entitlement. Swarm's patterns are tiny.
- **luaposix** builds only the 10 C modules swarm requires, and all of them in **one translation
  unit** (`posix_all.c` `#include`s each one). Every module pulls in `compat-5.2.c`, whose functions
  aren't `static`, so 10 separate objects give duplicate symbols. The `HAVE_*` defines that luke would
  probe are set by hand for each OS. `fdatasync` and `posix_fadvise` are Linux-only; the macOS build
  fails on `fdatasync` if they're on.
- **Linking.** `-static -s -Wl,--gc-sections` on Linux, `-Wl,-dead_strip` on macOS, and `-lunwind`. That
  last one matters: LuaJIT raises errors through the system unwinder (`_Unwind_RaiseException`), and zig
  links its bundled libunwind only when asked. Don't strip after linking. `zig objcopy --strip-all` in
  place left a 0-byte file, and on macOS it would also drop the linker's ad-hoc signature.

Getting the sources for the proof took one `nix build --print-out-paths nixpkgs#<x>.src` each
(`luajit`, `pcre2` and the 6 rocks' `luajitPackages.*.src`). The sqlite amalgamation came from sqlite.org,
because nixpkgs fetches the full `sqlite-src` zip. A release would pin URLs and SHA256s in a file, as
Neovim's `deps.txt` does (§2).

**What else was considered:**
- **luastatic** (`luastatic main.lua lib.a …`) generates a `main.c` that embeds the *scripts* and links
  static libraries. Embedding swarm's `.lua` is exactly what must not happen, because it breaks
  edit-and-run. Without that, luastatic is the same preload table plus a code generator. It also needs
  `.a` builds of each rock, which luarocks doesn't produce.
- **pkgsStatic (Nix musl)** builds Linux targets well. It doesn't build macOS from Linux, and CI would
  need Nix.
- **A hand-written `main.c`** (state, `luaL_openlibs`, run `argv[1]`) is no shorter than reusing
  `luajit.c`, and it loses `-e` and the REPL, which the Lua specs and debugging use.

**The proof run.** `shim/luajit` was a symlink to the static binary, put first on PATH, with
`LUA_CPATH=/nonexistent/?.so`. No `~/.local/share/swarm/lua` tree exists here. The binary's own
`package.cpath` is `/usr/local/lib/lua/5.1/?.so`, and static musl can't dlopen anyway, so every rock came
from the binary.

```
$ SWARM_CLI=$PWD/swarm/swarm LUA_CPATH=/nonexistent/?.so python3 -B swarm/test_swarm.py
Ran 93 tests in 50.934s
OK (skipped=6)
```

That run includes `test_lua_specs`, which runs `luajit swarm/lua/test/run.lua`, so those specs ran under
the static binary too.

The same suite with the aarch64 binary under `qemu-aarch64` (user mode, about 10× slower):
`Ran 93 tests in 439.946s, OK (skipped=6)`.

**One open flake.** 2 of 8 static-binary runs had one failure: x86_64 once while the qemu suite ran
beside it, and qemu once. Neither failure was captured, and the rerun passed each time. Two static runs
and two system-`luajit` runs side by side all passed. So the cause is unknown: it's either a
load-sensitive test or the binary. If it recurs, a release job that runs the suite 3 times will catch it.

## 2. How Neovim does it, and what to copy

Read from the Neovim 0.12.6 source in nixpkgs and its `v0.12.6` `.github/workflows/release.yml`:

- **Pinned sources.** `cmake.deps/deps.txt` gives each dependency a URL and a SHA256: LuaJIT by **commit**
  (it's a rolling release), libuv, luv, lpeg, utf8proc, tree-sitter, unibilium. `cmake.deps/CMakeLists.txt`
  is a CMake `ExternalProject` superbuild. `USE_BUNDLED` (and `USE_BUNDLED_LUAJIT` and so on) switches
  each dependency between bundled and system.
- **LuaJIT** is built by its own Makefile (`BuildLuajit.cmake`: `make CFLAGS+=-DLUA_USE_APICHECK
  CFLAGS+=-funwind-tables`, `BUILDMODE=static` on some platforms, `MACOSX_DEPLOYMENT_TARGET`), then
  linked into `nvim`.
- **C modules are opened in C** at state creation. `luaopen_luv` goes into `vim.uv` and
  `package.loaded.luv`. `luaopen_lpeg` and `luaopen_mpack` go into `vim.*` and `package.loaded`. lua-cjson
  is **vendored as source** in `src/cjson/` and becomes `vim.json`. These are the same `luaopen_*` calls
  as `init.c`, except that `init.c` registers them in `package.preload` rather than opening them eagerly.
- **Releases.** Builds are native, one runner per target: `ubuntu-22.04` and `ubuntu-22.04-arm` (tar.gz
  and AppImage), `macos-15-intel` and `macos-15` (`MACOSX_DEPLOYMENT_TARGET: 11.0`), and two Windows
  runners. Linux binaries link glibc dynamically. The workflow comment says to build "on the oldest
  supported images, so we have broader compatibility". One `gh release create` uploads them all. The
  workflow produces no checksum file and no signing step.

**Copy:** the pinned `deps.txt` (URL + SHA256, LuaJIT by commit); the bundled-or-system switch (here the
launcher prefers the runtime and falls back to `luajit` on PATH); LuaJIT through its own Makefile;
`MACOSX_DEPLOYMENT_TARGET=11.0`; C modules registered at state init.

**Don't copy:**
- The CMake superbuild. It's justified for ~10 dependencies with their own CMake builds. Here it's 7
  libraries whose C files compile directly.
- A native runner per target. Zig cross-builds all four from one job.
- Dynamic glibc. A 2.7 MB static musl binary has no "oldest image" problem at all.

## 3. Cross-building, static vs dynamic, macOS signing, size

- **Zig as the cross compiler.** `zig cc -target {x86_64,aarch64}-linux-musl` and
  `{aarch64,x86_64}-macos` each built from this one machine, with zig 0.17.1 from nixpkgs. A clean build
  takes about 2.5 min per target on a loaded machine, and seconds from the zig cache. Zig ships musl and
  macOS libc stubs, so **no macOS SDK and no Mac are needed to build.** A Mac is needed only to *run* the
  tests.
- **Static musl on Linux, not static glibc.** Fully static glibc warns about and breaks NSS
  (`getpwnam`) and `dlopen`. Musl reads `/etc/passwd` itself and has no NSS. Swarm uses neither (no
  `posix.pwd`, no `setlocale`), so musl's differences don't apply. The other musl costs don't matter here:
  - musl's slower malloc: LuaJIT uses its own allocator on 64-bit.
  - musl's C-only locale: cjson's `fpconv` wants `.` as the decimal point, and that's what it gets.

  One binary runs on any Linux kernel and distro, NixOS included, with no loader path.
- **macOS can't be static.** libSystem is the only stable syscall ABI. The binaries link only
  `/usr/lib/libSystem.B.dylib`, with deployment target 11.0, which covers every arm64 Mac.
- **Signing.** arm64 macOS refuses to run unsigned code. Zig's linker signs ad hoc
  (`CodeSignatureFlags(ADHOC | LINKER_SIGNED)`, read with `rcodesign print-signature-info`). The x86_64
  build is unsigned, which Intel Macs allow.

  `curl` doesn't set `com.apple.quarantine`, so Gatekeeper doesn't check a file `install.sh`
  downloads (sw-lua.md §9). A browser download would need notarization, which is a paid Apple Developer
  ID. Don't offer browser downloads.

  LuaJIT's own JIT uses plain `mmap(PROT_EXEC)`. That is allowed for an ad-hoc binary without the
  hardened runtime. **Not run on a Mac:** a macOS CI runner must prove this before the first release.
- **Size.** About 2.5–2.9 MB per binary and about 1.2 MB gzipped. By object size before `--gc-sections`: LuaJIT 0.59 MB, sqlite
  1.13 MB, pcre2 0.42 MB, the rest small. All four come to about 5 MB gzipped.

## 4. How install.sh and the launcher fetch it

**A pin in the repo.** `swarm/runtime.lock`, one line per platform:

```
1 x86_64-linux  <sha256>
1 aarch64-linux <sha256>
1 aarch64-macos <sha256>
1 x86_64-macos  <sha256>
```

The asset URL is derived: `https://github.com/jgetzel/jgetzel-skills/releases/download/runtime-v1/swarm-lua-<platform>`.
The checksum is committed in the repo, not fetched next to the binary. A tampered release asset can't
change the hash the checkout expects.

**Where it lives:** `${XDG_DATA_HOME:-~/.local/share}/swarm/runtime/<ver>/swarm-lua`. The version
directory lets a worktree still on an old commit keep its runtime after main moves on. Old versions are a
few MB each.

**The launcher** (`swarm/swarm`, a sketch, not done):
1. Read the version from `runtime.lock` and map `uname -sm` to a platform.
2. If `runtime/<ver>/swarm-lua` is executable, `exec` it on `main.lua`, in place of `luajit`.
3. If not, fetch it once, under a `mkdir` lock:
   `curl -fsSL --max-time 20` to a temp file, then `sha256sum`/`shasum -a 256`, compare to the lock,
   `chmod +x` and `mv` into place. This is 1.2 MB and about a second. The fetch has to happen here and not
   only in install.sh. **Otherwise a merged lock bump breaks every agent on every machine until someone
   runs install.sh,** and that breaks "merged means live".
4. If the fetch or the checksum fails, or there's no prebuilt for this platform, fall back to
   `luajit` on PATH. That keeps today's Nix, Homebrew and luarocks routes, with the same
   `main.lua` rock check.
5. Otherwise use today's "hooks are OFF" JSON, with "run install.sh" as the hint.

**install.sh.** It does the same fetch first, and prints where the runtime went. It runs the
`luajit`/rocks route only when there's no prebuilt or the user sets `SWARM_RUNTIME=system`. Nix users
who want everything in their config can keep `luajit.withPackages`. They can also fetch the asset with
`fetchurl` and the lock's sha256, since it's a static file.

**When scripts need a new runtime** (a new rock, a new posix module, or a LuaJIT/sqlite security bump):
1. A PR changes `init.c`/`deps.txt`.
2. Tag `runtime-v<N+1>`; CI builds and uploads.
3. A second PR updates `runtime.lock` together with the `.lua` that needs it.

`main.lua` can also check `SWARM_RUNTIME` and name the version it wants, for someone on a hand-built
`luajit`. Make versions additive: N+1 keeps every module N had. Then an old checkout never breaks on a
newer runtime, even if the version-directory scheme is later simplified to "newest installed".

## 5. The cost to keep it working

| | Prebuilt runtime | luarocks route (today) |
|---|---|---|
| User install | none: the launcher fetches 1.2 MB on first run | LuaJIT + luarocks + sqlite and pcre2 headers + a C compiler, then 7 `luarocks install` calls. Not run on Homebrew or apt/dnf yet (sw-lua.md "Not done") |
| Where it breaks | in CI, before release, once | on each user's machine, whenever brew/apt bumps LuaJIT or a rock, and differently on each one |
| CI | one workflow on `runtime-v*` tags. Job 1 (ubuntu, zig) builds all 4, runs the suite on x86_64, uploads assets + `SHA256SUMS`. Jobs 2–3 run the suite on `ubuntu-24.04-arm` and `macos-15` (and `macos-15-intel`) against the built binaries | none |
| CI cost | Public repo: GitHub-hosted runners are free, macOS included. About 5 min per release | none |
| Upkeep | Bump `deps.txt` for LuaJIT and sqlite security fixes, about 2–4 times a year. Watch for zig changes (0.17 already broke `#embed` here; pin the zig version in CI) | none in the repo; all of it falls on users |
| Hooks and agents | the edit-and-run loop is unchanged: only C changes need a release | same |

The real cost is a first workflow in a repo that has none, plus about 30 lines in the launcher and in
install.sh. The release CI runs only when the runtime changes, not on every merge. That differs from the
Go/Rust option sw-lua.md §9 rejected: there, every merge was a release.

## 6. Recommendation

**Build it as one runtime for four platforms.** Cross-compile with zig in one Ubuntu job, test on native
runners, pin checksums in `runtime.lock`, and have the launcher fetch on demand with `luajit` on PATH as
the fallback. It turns "install LuaJIT, a compiler, two -dev packages and 7 rocks" into nothing, and it
keeps every property the Lua port was chosen for.

Tasks, in order:
1. `swarm/runtime/` with `deps.txt` (URL + SHA256, LuaJIT by commit), `init.c` and `build.sh` (moved
   from here, fetching from `deps.txt`).
2. `.github/workflows/runtime.yml` as in §5, with zig pinned. Its first run on `macos-15` is the
   unverified Mac check.
3. `runtime.lock`, the launcher fetch and fallback (§4), and install.sh. Test it against a local file
   URL so the suite needs no network.
4. Docs: SKILL.md install becomes "nothing"; sw-lua.md §4 becomes the fallback route.

Keep the luarocks/Nix lines in install.sh as the fallback, not the main path.

## Not done or not verified

- **No pipeline, launcher or install change.** That is per the task.
- **No macOS binary was run.** They build and the arm64 one is ad-hoc signed, but JIT, `posix.*` and the
  suite on a real Mac are unchecked. That is the first thing the macOS CI job must show.
- **aarch64-linux ran only under qemu-user,** not on arm hardware.
- **The one-failure flake (§1) was never captured.** It hit 2 of 8 static runs, and both reruns passed.
- **The sources came from the nixpkgs pin plus sqlite.org.** There is no `deps.txt` yet, and the luaposix
  `HAVE_*` defines were set by hand per OS, not probed.
- **The Gatekeeper/quarantine claim for curl downloads** comes from sw-lua.md §9. It was not re-checked.
