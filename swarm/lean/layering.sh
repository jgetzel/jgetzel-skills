#!/bin/sh
# The layering of swarm-lean's sources (board #216): the spec layer, the modules Challenge.lean may import, imports no
# proof and no implementation; nothing but the proofs (SwarmLean/Proofs.lean, SwarmLean/Proofs/), the lib root
# SwarmLean.lean, Solution.lean and Audit.lean imports a proof module; nothing imports Challenge.lean or Solution.lean.
# Reads the import lines of every .lean file here (not .lake/ or hpl/); exit 1 on an edge that breaks one of these.
cd "$(dirname "$0")" || exit 1
# the spec layer: the db's rows and the interfaces, the assumptions about the world, and SwarmLean/Spec/ but Code.lean
spec="SwarmLean.Util SwarmLean.Sqlite SwarmLean.Db SwarmLean.Db.Rows SwarmLean.Store SwarmLean.World SwarmLean.Sys
SwarmLean.Lib.Re SwarmLean.Lib.Json SwarmLean.Assumptions SwarmLean.ChallengeAnchor SwarmLean.Spec.Data SwarmLean.Spec.Board
SwarmLean.Spec.Locks SwarmLean.Spec.Msgs SwarmLean.Spec.Cross SwarmLean.Spec.Machine"
inspec() { echo "$spec" | tr ' ' '\n' | grep -qx "$1"; }
# Lean's own libraries and swarm/model's (../model, built from those files) stand below every layer
core() { case "$1" in Init|Init.*|Std|Std.*|Lean|Lean.*|SwarmModel.*) return 0;; esac; return 1; }
fail=0
for m in $spec; do
  f=$(echo "$m" | tr . /).lean
  [ -f "$f" ] || { echo "layering: spec module $m has no $f"; fail=1; }
done
edges=$(find . -name '*.lean' -not -path './.lake/*' -not -path './hpl/*' | sed 's|^\./||' | sort | while read -r f; do
  m=$(echo "${f%.lean}" | tr / .)
  awk '/^import /{print $2; next} /^(--|$)/{next} {exit}' "$f" | while read -r i; do echo "$m $i"; done
done)
bad=$(echo "$edges" | while read -r m i; do
  [ -n "$m" ] || continue
  if inspec "$m" && ! inspec "$i" && ! core "$i"; then echo "layering: spec module $m imports $i, outside the spec layer"; fi
  if [ "$m" = SwarmLean.Challenge ] && ! inspec "$i" && ! core "$i"; then echo "layering: Challenge.lean imports $i, outside the spec layer"; fi
  case "$i" in SwarmLean.Proofs|SwarmLean.Proofs.*)
    case "$m" in SwarmLean.Proofs|SwarmLean.Proofs.*|SwarmLean|SwarmLean.Solution|Audit) ;;
      *) echo "layering: $m imports the proof module $i";; esac;;
  esac
  case "$i" in SwarmLean.Challenge|SwarmLean.Solution) echo "layering: $m imports $i, which nothing may import";; esac
done)
[ -z "$bad" ] || { echo "$bad"; fail=1; }
[ "$fail" = 0 ] && echo "layering: ok ($(echo "$spec" | wc -w) spec modules; no proof imported outside the proofs)"
exit $fail
