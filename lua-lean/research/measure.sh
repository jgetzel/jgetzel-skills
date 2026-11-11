#!/bin/sh
# measure.sh <outdir> <file.lua>...: per file, lift+check seconds and bytes, today's proofs and the one theorem's
# run from lua-lean/, with lake and bc on the PATH (nix shell nixpkgs#elan nixpkgs#bc -c research/measure.sh /tmp/out test/*.lua)
out=$1; shift
t() { s=$(date +%s.%N); "$@" >/dev/null 2>"$out/err" ; r=$?; e=$(date +%s.%N); echo "$e - $s" | bc; return $r; }
printf '%-10s %4s %8s %8s %8s %8s %8s %8s\n' file fns lift0 chk0 bytes0 lift1 chk1 bytes1
for f in "$@"; do
  m=$(basename "$f" .lua)
  l0=$(t sh -c "./lua-lean lift $f Lifted > $out/$m.0.lean")
  c0=$(t lake env lean "$out/$m.0.lean") || c0="FAIL"
  l1=$(t sh -c "./lua-lean lift1 $f > $out/$m.1.lean")
  c1=$(t lake env lean "$out/$m.1.lean") || { c1="FAIL"; head -3 "$out/err" >&2; }
  printf '%-10s %4s %8.2f %8s %8s %8.2f %8s %8s\n' $m $(grep -c '^theorem .*_ok' $out/$m.0.lean) $l0 $c0 $(wc -c < $out/$m.0.lean) $l1 $c1 $(wc -c < $out/$m.1.lean)
done
