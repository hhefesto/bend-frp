#!/usr/bin/env bash
# The laws must catch each mistake in probe/mutants/: every patch there breaks
# the library on purpose, one mistake at a time, and PROOF.bend must fail on
# each. Run from the repo root with bend on PATH (`nix flake check` runs it).
set -eu
root=$(pwd)
w=$(mktemp -d)
trap 'rm -rf "$w"' EXIT
bad=0
for p in "$root"/probe/mutants/*.patch; do
  n=$(basename "$p" .patch)
  mkdir "$w/$n"
  cp "$root"/*.bend "$w/$n/"
  cp -r "$root"/proof "$w/$n/"
  if ! (cd "$w/$n" && patch -s -p1 < "$p"); then
    echo "$n: the patch no longer applies"
    bad=1
  elif (cd "$w/$n" && bend PROOF.bend 2>&1) | grep -q 'SOME PROOFS FAIL'; then
    echo "$n: caught"
  else
    echo "$n: NOT CAUGHT"
    bad=1
  fi
done
exit $bad
