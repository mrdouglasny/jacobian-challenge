#!/usr/bin/env bash
# Axiom-count consistency guard.
#
# The kernel-verified axiom count is the single source of truth. This script
# checks that the count claimed in the canonical docs (AXIOM_AUDIT.md header +
# verification block, README at-a-glance) matches it, and fails otherwise.
# Catches the doc-drift that happens when an axiom is discharged but not every
# doc is reconciled (e.g. header says 60 while the verification block says 62).
#
# Run by CI after `lake build` (reuses cached oleans). Local: `bash scripts/check_axiom_consistency.sh`.
set -uo pipefail
fail=0
err(){ echo "::error::axiom-consistency: $*"; fail=1; }

# 1. Kernel-verified count (authoritative).
tmp=$(mktemp /tmp/axcount_check.XXXX.lean)
cat > "$tmp" <<'LEAN'
import Jacobians
open Lean
run_cmd do
  let env ← getEnv
  let internal : List Name := [`propext, `Classical.choice, `Quot.sound, `sorryAx,
    `lcProof, `lcCast, `lcErased, `lcAny, `lcUnreachable, `lcVoid, `Quot.lcInv,
    `isScalarObj, `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler]
  let mut n := 0
  for (nm, info) in env.constants.toList do
    if info matches .axiomInfo _ then
      let s := nm.toString
      if !s.startsWith "Jacobians.Vendor" && !(internal.contains nm) then n := n + 1
  IO.println s!"KERNEL_AXIOM_COUNT={n}"
LEAN
N=$(lake env lean "$tmp" 2>/dev/null | grep -oE 'KERNEL_AXIOM_COUNT=[0-9]+' | cut -d= -f2)
rm -f "$tmp"
[ -n "$N" ] || { echo "::error::could not compute kernel axiom count"; exit 2; }
echo "kernel axiom count: $N"

# 2. Canonical documented counts must all equal N.
chk(){ # label  number
  [ -n "$2" ] || { err "$1: count not found (regex drift?)"; return; }
  [ "$2" = "$N" ] || err "$1 = $2, but kernel = $N"
}
chk "AXIOM_AUDIT 'Active project axioms'" "$(grep -oE 'Active project axioms: [0-9]+' AXIOM_AUDIT.md | grep -oE '[0-9]+' | head -1)"
chk "AXIOM_AUDIT verification 'prints N'" "$(grep -oE 'prints [0-9]+ — the vendored' AXIOM_AUDIT.md | grep -oE '[0-9]+' | head -1)"
chk "AXIOM_AUDIT verification 'non-vendor): N'" "$(grep -oE 'non-vendor\): [0-9]+' AXIOM_AUDIT.md | grep -oE '[0-9]+' | head -1)"
chk "README at-a-glance Axioms" "$(grep -oE '\*\*Axioms\*\* \| [0-9]+' README.md | grep -oE '[0-9]+' | head -1)"

# 3. The AXIOM_AUDIT by-class breakdown table must SUM to the kernel count.
#    Catches the drift where a discharge updates the header but not the per-class
#    counts (e.g. #84 review: 2c still counted 2 discharged affine-form axioms).
#    Parses the `| Class | Count | Nature | Trust |` table; sums column 2 (Count).
breakdown=$(awk -F'|' '
  /Class.*Count.*Nature.*Trust/ { f=1; next }
  f && $0 ~ /^\|[-: ]+\|/        { next }
  f && /^\|/                     { c=$3; gsub(/[^0-9]/,"",c); if (c!="") s+=c; next }
  f && $0 !~ /^\|/               { f=0 }
  END { print s+0 }
' AXIOM_AUDIT.md)
chk "AXIOM_AUDIT by-class breakdown sum" "$breakdown"

if [ "$fail" = 0 ]; then echo "✓ axiom count consistent across docs + breakdown (= $N)"; else
  echo "✗ axiom-count drift — reconcile AXIOM_AUDIT.md (header + by-class breakdown) + README.md to the kernel count $N"; fi
exit $fail
