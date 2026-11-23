#!/usr/bin/env perl
# Usage: nopanic.pl FILE... — prints file:line for each partial def and panicking access (`]!`, .get!, .head!, .toNat!,
# .getLast!, .back!, panic!, unreachable!) outside comments and string literals; exits 1 when it printed any.
use strict; use warnings;
my $bad = 0;
my $pat = qr/\bpartial\b|\]!|\.(?:get|head|toNat|getLast|back)!|\bpanic!|\bunreachable!/;
for my $f (@ARGV) {
  open(my $fh, '<', $f) or die "$f: $!";
  local $/; my $s = <$fh>; close $fh;
  my ($out, $depth, $n) = ('', 0, length $s);
  for (my $i = 0; $i < $n; ) {
    my $c = substr($s, $i, 1); my $d = substr($s, $i, 2);
    if ($depth) {
      if ($d eq '/-') { $depth++; $i += 2; next }
      if ($d eq '-/') { $depth--; $i += 2; next }
      $out .= "\n" if $c eq "\n"; $i++; next;
    }
    if ($d eq '/-') { $depth = 1; $i += 2; next }
    if ($d eq '--') { $i++ while $i < $n && substr($s, $i, 1) ne "\n"; next }
    if ($c eq '"') {
      $i++;
      while ($i < $n && substr($s, $i, 1) ne '"') { $out .= "\n" if substr($s, $i, 1) eq "\n"; $i += substr($s, $i, 1) eq '\\' ? 2 : 1 }
      $i++; $out .= '""'; next;
    }
    if ($c eq "'" && ($i == 0 || substr($s, $i - 1, 1) !~ /[\w']/) && substr($s, $i) =~ /^'(?:\\.|[^\\'])'/) {
      $i += length($&); $out .= "' '"; next;
    }
    $out .= $c; $i++;
  }
  my $ln = 0;
  for my $l (split /\n/, $out, -1) { $ln++; if ($l =~ $pat) { print "$f:$ln: $l\n"; $bad = 1 } }
}
exit $bad;
