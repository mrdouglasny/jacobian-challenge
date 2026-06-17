#!/usr/bin/env bash
# scripts/verify.sh — one-command EXTERNAL re-verification of the headline theorems.
#
# Runs the real leanprover/comparator against this repo's solution: it checks
#   (1) statement match  — our theorems are identical to the verbatim Challenge spec,
#   (2) permitted axioms — every axiom used is on the allowlist (the standard 3),
#   (3) kernel replay    — every proof is re-exported (lean4export) and re-checked in a
#                          fresh kernel; the library .oleans are NOT trusted.
#
# Trust boundary: only the Lean kernel, Mathlib, comparator, and the workspace's
# Challenge.lean (the statement) are trusted. The ~50k LOC Jacobians library + the
# vendored port are re-derived independently. This is the strongest verification the
# kernel can express — stronger than `#print axioms` on our own build (which trusts our
# .oleans and our own report generator).
#
# Usage:
#   scripts/verify.sh                      # default config.json  (RR headline)
#   scripts/verify.sh config-buzzard.json  # the 11 Buzzard headlines
#
# Env:
#   COMPARATOR_WORK   cache dir for comparator/lean4export checkouts
#                     (default: ~/.cache/jacobian-comparator)
#   COMPARATOR_LANDRUN  path to a landrun (Linux landlock) sandbox binary; if unset and
#                     `landrun` is on PATH it is used, otherwise the replay runs
#                     unsandboxed (fine on a macOS dev box — the kernel replay still
#                     happens; use the sandbox on shared/Linux infra).
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS="$HERE/comparator"
CFG="${1:-config.json}"
[ -f "$WS/$CFG" ] || { echo "verify.sh: no such config: $WS/$CFG" >&2; exit 2; }

# comparator + lean4export MUST match the toolchain that built the library: the .olean
# export format is toolchain-locked, so lean4export can only read same-version oleans.
TOOLCHAIN_TAG="$(tr -d '[:space:]' < "$WS/lean-toolchain" | sed -e 's#^leanprover/lean4:##')"
WORK="${COMPARATOR_WORK:-$HOME/.cache/jacobian-comparator}"
mkdir -p "$WORK"

for repo in comparator lean4export; do
  if [ ! -d "$WORK/$repo" ]; then
    echo "verify.sh: cloning leanprover/$repo @ $TOOLCHAIN_TAG"
    git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
      "https://github.com/leanprover/$repo" "$WORK/$repo"
  fi
  ( cd "$WORK/$repo" && lake build )
done

# Optional landrun sandbox for isolated replay (Linux only).
if [ -z "${COMPARATOR_LANDRUN:-}" ] && command -v landrun >/dev/null 2>&1; then
  COMPARATOR_LANDRUN="$(command -v landrun)"
fi
[ -n "${COMPARATOR_LANDRUN:-}" ] && export COMPARATOR_LANDRUN
export PATH="$WORK/lean4export/.lake/build/bin:$PATH"

# Build the workspace (verbatim Challenge spec + Solution bridge → our library) and run.
echo "verify.sh: building comparator workspace (Challenge, Solution)"
cd "$WS"
lake build Challenge Solution
echo "verify.sh: running comparator on $CFG"
exec lake env "$WORK/comparator/.lake/build/bin/comparator" "$CFG"
