#!/bin/sh
# The challenge gate (board #216): SwarmLean/Challenge.lean, the main theorems with `sorry` and the code's functions as
# holes, against SwarmLean/Solution.lean, the proofs, judged by the Lean FRO's Comparator (`lake comparator`, in Lean
# 4.35's lake; comparator.json names the pair, the theorems, the holes and the three axioms).
#
#   1. Challenge.lean builds, and its only diagnostics are its "declaration uses `sorry`" warnings;
#   2. its copies of Spec/Code.lean and of Assumptions/Code.lean's CwdsProc are word for word (each between
#      -- BEGIN CHALLENGE COPY and -- END CHALLENGE COPY lines);
#   3. Comparator accepts: every theorem has the challenge's statement and only Lean's three axioms, every constant a
#      statement reads is the same in both, each hole has its type, and the kernel replays the solution, and so does
#      every independent checker the toolchain bundles (--paranoid);
#   4. it rejects two mutants: the solution with a hypothesis's definition changed (ToolsKeep, no_work_lost's), and the
#      challenge with a statement changed (no_work_lost's), each naming the constant.
#
# The exports are made here, outside Comparator's sandbox, by the toolchain's leanexport from this tree's own build
# (lake comparator builds inside its bwrap sandbox, which cannot see ../../claim or ../model), and handed to it with
# --challenge-from-export/--solution-from-export; the sandbox holds the kernel's replay. Each export is of the names
# lake comparator itself exports: the theorems, the holes, the axioms and the kernel's built-in constants.
cd "$(dirname "$0")" || exit 1
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
t0=$(date +%s)
out=.lake/challenge
rm -rf "$out"; mkdir -p "$out"
read -r C S <<EOF
$(python3 -I -c 'import json; c=json.load(open("comparator.json")); print(c["challenge_module"], c["solution_module"])')
EOF
names=$(python3 -I -c 'import json; c=json.load(open("comparator.json")); print(" ".join(c["theorem_names"]+c["definition_names"]+c["permitted_axioms"]))')
# lake comparator's own export targets beside those (Lake/CLI/Check.lean: builtinTargets, primitiveTargets)
prim="Quot Quot.mk Quot.lift Quot.ind Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land
Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam
autoParam semiOutParam outParam"
# bwrap for the sandbox: on PATH, else nixpkgs'; where it cannot run (no user namespaces), the replay runs unsandboxed
bw=$(command -v bwrap) || bw=$(nix build --no-link --print-out-paths nixpkgs#bubblewrap 2>/dev/null)/bin/bwrap
sandbox=
if ! "$bw" --ro-bind / / --unshare-all true 2>/dev/null; then
  echo "challenge: bwrap cannot run here; the kernel's replay runs outside the sandbox"; sandbox=--inadvisably-no-sandbox
fi
# --paranoid (the accept only): also every independent checker the toolchain bundles (leanchecker-paranoid, lean4lean,
# nanoda, con-leche, con-ron), which elan's release toolchains have and nixpkgs' Lean has not
paranoid=
[ -x "$(lean_do env lean --print-prefix)/bin/lean4lean" ] && paranoid=--paranoid
cmp() { COMPARATOR_BWRAP="$bw" lean_do comparator --challenge-from-export "$1" --solution-from-export "$2" $sandbox $4 >"$3" 2>&1; }
export_of() { # module, olean dir first on LEAN_PATH (or ""), file
  # shellcheck disable=SC2086
  lean_do env sh -c 'LEAN_PATH="$1${1:+:}$LEAN_PATH" exec "$(lean --print-prefix)/bin/leanexport" "$2" -- $3' sh "$2" "$1" "$names $prim" >"$3" \
    || { echo "challenge: leanexport of $1 failed"; exit 1; }
}

# 1. the build; lake replays a built module's log, so the warnings show on a warm tree too
lean_do build "$C" "$S" >"$out/build.log" 2>&1 || { echo "challenge: lake build $C $S failed"; tail -30 "$out/build.log"; exit 1; }
bad=$(grep -E '^(warning|error)' "$out/build.log" | grep 'Challenge.lean' | grep -v "declaration uses .sorry.")
[ -z "$bad" ] || { echo "challenge: Challenge.lean has diagnostics beyond its sorry warnings:"; echo "$bad"; exit 1; }
nsorry=$(grep -c "Challenge.lean.*declaration uses .sorry." "$out/build.log")
# every sorried declaration of Challenge.lean is a theorem or a hole comparator.json names, and each it names is one
cat >"$out/Sorried.lean" <<'LEAN'
import Lean
open Lean
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let m := args[0]!.toName
  let env ← importModules #[{module := m}] {} (trustLevel := 1024)
  let some i := env.getModuleIdx? m | throw <| IO.userError s!"no module {m}"
  for (n, ci) in env.constants.map₁.toList do
    let v := match ci with | .thmInfo t => some t.value | .defnInfo d => some d.value | _ => none
    if env.getModuleIdxFor? n == some i && v.any (·.hasSorry) then IO.println n
LEAN
lean_do env lean --run "$out/Sorried.lean" "$C" | sort >"$out/sorried.txt"
python3 -I -c 'import json; c=json.load(open("comparator.json")); print("\n".join(c["theorem_names"]+c["definition_names"]))' \
  | grep -v '^SwarmLean.strLit' | sort >"$out/named.txt"
diff "$out/sorried.txt" "$out/named.txt" >"$out/sorried.diff" || {
  echo "challenge: Challenge.lean's sorried declarations are not comparator.json's names (< file, > comparator.json):"
  head -20 "$out/sorried.diff"; exit 1; }

# 2. the copies
region() { sed -n "\#^-- BEGIN CHALLENGE COPY$2\$#,\#^-- END CHALLENGE COPY$2\$#p" "$1"; }
region SwarmLean/Spec/Code.lean "" >"$out/code.lean"; region SwarmLean/Challenge.lean "" >"$out/code.copy"
region SwarmLean/Assumptions/Code.lean " Assumptions/Code.lean" >"$out/acode.lean"
region SwarmLean/Challenge.lean " Assumptions/Code.lean" >"$out/acode.copy"
for k in code acode; do
  [ -s "$out/$k.lean" ] || { echo "challenge: no CHALLENGE COPY region for $k"; exit 1; }
  diff "$out/$k.lean" "$out/$k.copy" >"$out/$k.diff" || { echo "challenge: Challenge.lean's copy differs (< source, > copy):"; head -20 "$out/$k.diff"; exit 1; }
done

# 3. the verdict
export_of "$C" "" "$out/challenge.ndjson"
export_of "$S" "" "$out/solution.ndjson"
if ! cmp "$out/challenge.ndjson" "$out/solution.ndjson" "$out/accept.out" $paranoid; then
  echo "challenge: Comparator rejects the solution:"; tail -12 "$out/accept.out"
  if grep -q 'kernel rejected' "$out/accept.out"; then
    # the replay adds each constant after those it names, in name-hash order; a string literal names none, so
    # ChallengeAnchor.lean's theorem must replay first (its name the lowest hash) to bring String.ofList in
    cat >"$out/FirstReplayed.lean" <<'LEAN'
import LeanExport.Parse
open Lean
def main (args : List String) : IO Unit := do
  let env ← IO.FS.withFile args[0]! .read fun h => LeanExport.parseStream (.ofHandle h)
  let first := env.constMap.toList.filter (fun (_, ci) => !ci.isUnsafe && !ci.isPartial) |>.foldl
    (fun (lo : Option Name) (n, _) => if lo.all (Name.quickCmp n · == .lt) then some n else lo) none
  IO.println s!"challenge: the kernel replays {first} first (ChallengeAnchor.lean's theorem must be first)"
LEAN
    lean_do env lean --run "$out/FirstReplayed.lean" "$out/solution.ndjson"
  fi
  exit 1
fi
t1=$(date +%s)

# 4. the mutants: each is compiled to its own olean dir, put first on LEAN_PATH for its export
mutant() { # file, from, to, module that exports, expected message
  d="$out/mutant-$(basename "$1" .lean)"; mkdir -p "$d"
  # Lean looks for a package's modules in the one search-path entry that has its root dir: $d gets a tree of links
  # to the build's oleans, the mutant's own in place of its module's
  cp -rs "$(realpath .lake/build/lib/lean/SwarmLean)" "$d/" || exit 1
  rm -f "$d/${1%.lean}".olean*
  python3 -I - "$1" "$d/$1" "$2" "$3" <<'PY' || exit 1
import sys
src, dst, a, b = sys.argv[1:]
t = open(src).read()
if t.count(a) != 1: sys.exit(f"challenge: the mutation's text occurs {t.count(a)} times in {src}")
open(dst, "w").write(t.replace(a, b))
PY
  lean_do env lean -o "$d/${1%.lean}.olean" "$d/$1" >"$d/build.log" 2>&1 || { echo "challenge: mutant $1 does not build"; tail -5 "$d/build.log"; exit 1; }
  export_of "$4" "$d" "$d/export.ndjson"
  if [ "$4" = "$C" ]; then cmp "$d/export.ndjson" "$out/solution.ndjson" "$d/verdict.out"; else cmp "$out/challenge.ndjson" "$d/export.ndjson" "$d/verdict.out"; fi
  e=$?
  if [ "$e" = 0 ] || ! grep -qF "$5" "$d/verdict.out"; then
    echo "challenge: Comparator did not reject mutant $1 with \"$5\" (exit $e):"; tail -5 "$d/verdict.out"; exit 1
  fi
  echo "challenge: rejects mutant $1: $(grep -F "$5" "$d/verdict.out" | head -1)"
}
mutant SwarmLean/Assumptions.lean "def ToolsKeep : Prop := ∀ w argv cwd, ToolRead argv →" \
  "def ToolsKeep : Prop := ∀ w argv cwd, GitRead argv →" "$S" "target 'SwarmLean.ToolsKeep'"
mutant SwarmLean/Challenge.lean "∀ i w m x, s0.log.length ≤ i → s.log[i]? = some" "∀ i w m x, s0.log.length < i → s.log[i]? = some" \
  "$C" "statement do not match: 'SwarmLean.SweepProofs.no_work_lost'"

nt=$(python3 -I -c 'import json; c=json.load(open("comparator.json")); print(len(c["theorem_names"]), len(c["definition_names"]))')
kernels=$(grep -c 'kernel accepts the solution' "$out/accept.out")
echo "challenge: ok: Comparator accepts $(echo "$nt" | cut -d' ' -f1) theorems over $(echo "$nt" | cut -d' ' -f2) holes ($kernels kernels) ($nsorry sorry warnings, $(wc -l <SwarmLean/Challenge.lean) lines), the verdict in $((t1 - t0))s, $(($(date +%s) - t0))s with the mutants"
