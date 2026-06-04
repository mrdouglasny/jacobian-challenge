#!/usr/bin/env python3
"""Definition inventory + degeneracy red-flag scanner for jacobian-challenge.

Walks the `Jacobians/` Lean library and emits, for every `def` / `abbrev` /
`structure` / named `instance`, a row: file, line, kind, name, body-head, and a
set of *red-flag* heuristics that hint a definition might be a degenerate /
placeholder / vacuous stub (the "faithfulness wall" — the kernel checks proofs
but never that a `def` matches intent).

This does NOT decide a definition is wrong; it surfaces candidates for human /
witness-lemma review. Output is a TSV (machine) + a console summary (human).

Usage:
    python3 scripts/definition_inventory.py            # writes docs/definition-inventory.tsv
    python3 scripts/definition_inventory.py --flags     # console: only flagged rows

Red-flag heuristics (each is a hint, not a verdict):
    trivial-body   RHS is a single trivial token (0, 1, True, ⊥, ∅, (), rfl,
                   trivial, default, Classical.arbitrary, fun _ => <trivial>)
    sorry-body     body contains `sorry`/`admit` (tracked elsewhere too)
    const-fun      body is `fun _ ... => <constant>` ignoring all args
    wrapper        body is a bare identifier (possible thin pass-through;
                   benign for `abbrev`, worth noting for `def`)
"""
from __future__ import annotations
import os, re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = ROOT / "Jacobians"

DECL_RE = re.compile(
    r'^(?P<kind>noncomputable def|def|abbrev|structure|noncomputable instance|instance)\s+'
    r'(?P<name>[^\s(){:\[]+)'
)
TRIVIAL_TOKENS = {
    "0", "1", "True", "False", "⊥", "⊤", "∅", "()", "rfl", "trivial",
    "default", "Classical.arbitrary", "PUnit.unit", "Unit.unit", "0)", "1)",
}

def body_head(lines, i):
    """Return the RHS text starting at `:=` for the decl at line i (joined, capped)."""
    # gather up to the next blank line or next top-level decl, cap ~6 lines
    chunk = []
    for j in range(i, min(i + 8, len(lines))):
        chunk.append(lines[j].rstrip("\n"))
        if j > i and re.match(r'^\S', lines[j]) and DECL_RE.match(lines[j]):
            chunk.pop()
            break
    text = " ".join(chunk)
    m = re.search(r':=\s*(.*)', text)
    return (m.group(1).strip() if m else "").strip()

def flags_for(kind, name, rhs):
    fl = set()
    if not rhs:
        return fl
    first = rhs.split("--")[0].strip()
    # strip a trailing comment / where
    if "sorry" in rhs or re.search(r'\badmit\b', rhs):
        fl.add("sorry-body")
    if first in TRIVIAL_TOKENS:
        fl.add("trivial-body")
    # fun _ => <trivial>  (ignores args, constant result)
    mfun = re.match(r'^fun\s+(_\s*)+=>\s*(?P<r>\S+)', first)
    if mfun and mfun.group("r").rstrip(")") in TRIVIAL_TOKENS:
        fl.add("const-fun")
    elif re.match(r'^fun\s+(_\s*)+=>', first):
        fl.add("const-fun?")
    # bare identifier wrapper (single token, alphanumeric/dotted, not trivial)
    if re.match(r'^[A-Za-z_][A-Za-z0-9_.]*$', first) and first not in TRIVIAL_TOKENS:
        fl.add("wrapper" if kind != "abbrev" else "abbrev-wrapper")
    return fl

def vetting_class(rel, kind, name, uses, fl):
    """Coarse 'how is this vetted' bucket (heuristic, for the master list).

    vendored   — under Vendor/; verified upstream + #print axioms checked on import
    instance   — typeclass instance; vetted by being synthesised into proofs that use it
    witness    — terminal existence/concrete witness (Witnesses.lean, *CycleBasis, *Loop, *Arc)
    orphan     — referenced nowhere; dead-or-forward-scaffolding (manual disposition needed)
    sorry      — body still contains sorry
    used       — referenced elsewhere; pinned transitively by its call sites
    """
    if "/Vendor/" in rel:
        return "vendored"
    if "sorry-body" in fl:
        return "sorry"
    if "instance" in kind:
        return "instance"
    if "Witnesses.lean" in rel or name.endswith(("CycleBasis", "Loop", "Arc")):
        return "witness"
    if "orphan" in fl:
        return "orphan"
    return "used"


def main():
    flags_only = "--flags" in sys.argv
    # First pass: collect all source text once, for usage counting.
    files = {}
    for path in sorted(LIB.rglob("*.lean")):
        files[path] = path.read_text(encoding="utf-8", errors="replace")
    full_text = "\n".join(files.values())

    rows = []
    for path in sorted(files):
        rel = path.relative_to(ROOT)
        lines = files[path].splitlines(keepends=True)
        for i, line in enumerate(lines):
            m = DECL_RE.match(line)
            if not m:
                continue
            kind = m.group("kind").replace("noncomputable ", "nc-")
            name = m.group("name")
            rhs = "" if "structure" in kind else body_head(lines, i)
            fl = flags_for(kind, name, rhs)
            # usage: occurrences of the (possibly dotted) leaf name across the lib,
            # minus the declaration itself. Use the leaf after the last '.' since
            # most call sites use the short name (open namespace) or projection.
            leaf = name.split(".")[-1]
            # Count both bare (`leaf`) and qualified (`Ns.leaf`) references: the
            # lookbehind excludes only an identifier char, NOT a dot, so
            # `Bridge.bridgeFormEquiv` is counted. Minus 1 for the decl itself.
            uses = len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(leaf) + r'(?![A-Za-z0-9_])', full_text)) - 1
            # Typeclass instances are resolved by synthesis, not by name, so a
            # name-usage count is meaningless for them — never flag as orphan.
            is_instance = "instance" in kind
            if uses <= 1 and "structure" not in kind and kind != "abbrev" and not is_instance:
                fl.add("orphan" if uses <= 0 else "near-orphan")
            vet = vetting_class(str(rel), kind, name, uses, fl)
            rows.append((str(rel), i + 1, kind, name, max(uses, 0), vet, rhs[:60], ",".join(sorted(fl))))

    out = ROOT / "docs" / "definition-inventory.tsv"
    with out.open("w", encoding="utf-8") as f:
        f.write("file\tline\tkind\tname\tuses\tvetting\tbody_head\tred_flags\n")
        for r in rows:
            f.write("\t".join(str(x) for x in r) + "\n")

    flagged = [r for r in rows if r[7]]
    print(f"total declarations: {len(rows)}  (def/abbrev/structure/instance)")
    print(f"wrote {out.relative_to(ROOT)}")
    by_kind = {}
    for r in rows:
        by_kind[r[2]] = by_kind.get(r[2], 0) + 1
    print("by kind:", ", ".join(f"{k}={v}" for k, v in sorted(by_kind.items())))
    by_vet = {}
    for r in rows:
        by_vet[r[5]] = by_vet.get(r[5], 0) + 1
    print("by vetting:", ", ".join(f"{k}={v}" for k, v in sorted(by_vet.items())))
    print(f"flagged (any heuristic): {len(flagged)}")
    fl_counts = {}
    for r in flagged:
        for fl in r[7].split(","):
            fl_counts[fl] = fl_counts.get(fl, 0) + 1
    print("flag breakdown:", ", ".join(f"{k}={v}" for k, v in sorted(fl_counts.items())))
    # The interesting risk set: orphans / trivial / sorry / const-fun (NOT plain wrappers).
    risk = {"orphan", "near-orphan", "trivial-body", "sorry-body", "const-fun"}
    show = [r for r in rows if set(r[7].split(",")) & risk]
    print(f"\n--- risk set (orphan/trivial/sorry/const-fun), non-vendor first ---")
    for r in sorted(show, key=lambda x: ("/Vendor/" in x[0], x[7], x[0])):
        vend = " [VENDOR]" if "/Vendor/" in r[0] else ""
        print(f"  uses={r[4]:<3} {r[7]:22} {r[2]:9} {r[3]:40} {r[0]}:{r[1]}{vend}")

if __name__ == "__main__":
    main()
