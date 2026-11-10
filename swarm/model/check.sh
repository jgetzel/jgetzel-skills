#!/bin/sh
# Model-check swarm.qnt with TLC: each line is instance, property, and the verdict the README records.
# Exits 1 if any verdict differs. Usage: swarm/model/check.sh [instance-substring]; CHECK_TIMEOUT caps each (1800 s).
# Needs nix (quint and a JDK come from nixpkgs). One TLC at a time: each takes a few GB.
cd "$(dirname "$0")" || exit 1
fails=0
while read -r inst prop kind want; do
  case $inst in ''|'#'*) continue ;; esac
  [ -n "$1" ] && case $inst in *"$1"*) ;; *) continue ;; esac
  start=$(date +%s)
  if [ "$kind" = inv ]; then flag=--invariant; else flag=--temporal; fi
  out=$(timeout "${CHECK_TIMEOUT:-1800}" nix shell nixpkgs#quint nixpkgs#jdk21_headless -c quint verify --backend tlc --main "$inst" "$flag" "$prop" swarm.qnt 2>&1)
  case $out in
    *'[ok] No violation found'*) got=holds ;;
    *'[violation]'*) got=fails ;;
    *) got=error; [ -z "$out" ] || [ "$(printf '%s' "$out" | tail -c 300 | grep -c Progress)" = 0 ] || got=timeout ;;
  esac
  states=$(printf '%s\n' "$out" | grep -o '[0-9,]* distinct states found' | tail -1)
  printf '%-16s %-16s %-6s want %-6s %4ss  %s\n' "$inst" "$prop" "$got" "$want" "$(($(date +%s) - start))" "$states"
  if [ "$got" != "$want" ]; then
    fails=$((fails + 1))
    [ "$got" = error ] && printf '%s\n' "$out" | grep -v protobuf | tail -20
  fi
done <<'EOF'
s1_before        oneWorker        inv  holds
s1_first106      oneWorker        inv  fails
s1_after         oneWorker        inv  holds
s2_racy          noEarlyStart     inv  fails
s2_atomic        noEarlyStart     inv  holds
s2_fixed         noEarlyStart     inv  holds
s3_globs         locksDisjoint    inv  fails
s3_plain         locksDisjoint    inv  holds
s4_racy          inboxExact       inv  fails
s4_atomic        inboxExact       inv  holds
s4_atomic        doneHasEvidence  inv  fails
s5_fixed         doneHasEvidence  inv  holds
l_before         L2               temp fails
l_first106       L2               temp holds
l_after          L2               temp holds
l_before         L3               temp fails
l_after          L3               temp holds
l_after          L1               temp holds
l_after_waiter   L1               temp fails
l_after_waiter   L3               temp fails
EOF
exit $((fails > 0))
