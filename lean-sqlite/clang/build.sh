#!/usr/bin/env bash
# The control build: stock Lean's C compiled by hpl's clang (no LTO, the toolchain's own runtime), `lake build` options pass through.
set -euo pipefail
cd "$(dirname "$0")"
H=${H:-$HOME/workspace/high-perf-lean}
nix develop "$H" -c bash -c 'cc=$(cd ../hpl && lake query hplcc -K lto=0 -K leanrt=off) && LEAN_CC=$cc/bin/hpl-cc exec lake build "$@"' _ "$@"
