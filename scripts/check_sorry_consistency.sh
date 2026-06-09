#!/usr/bin/env bash
# Sorry-count consistency guard + robust sorry-bearing-file detector.
#
# The file-level guard in `.github/workflows/lean.yml` proves the *core* stays
# sorry-free, but its grep used a restricted shape (`:= sorry`, `by sorry`, …)
# that MISSED valid term placements like `exact sorry`, `refine sorry`,
# `simpa using sorry` — so a core-file `exact sorry` could bypass it (PR #122
# review). It also asserted no total, so the README's per-declaration counts
# drifted silently (the adelic `RiemannRochAnchor` 3 went uncounted from #105).
#
# This script is the single robust detector for both problems. It counts REAL
# sorrys after stripping Lean comments (block `/- … -/`, incl. `/-- … -/`
# docstrings, and line `--`), matching a broad `\bsorry\b` so every term/tactic
# placement is caught while prose and `sorryAx` are not.
#
# Modes:
#   --list-files   print one sorry-bearing file per line (consumed by the
#                  blocking core guard in lean.yml). Exit 0.
#   (default)      print per-file counts; assert (1) every sorry-bearing file is
#                  in the lean.yml allowlist, (2) the README "At a glance" total
#                  (gap + anchor) equals the real count. Exit non-zero on drift.
#
# NOTE: this is a fast static approximation; the ultimate authority is the Lean
# kernel ("declaration uses 'sorry'" at build time). It is intentionally broad.
set -uo pipefail
cd "$(dirname "$0")/.."

# Robust per-file real-sorry counts (comments stripped, broad `\bsorry\b`).
report="$(python3 - <<'PY'
import re, glob
pat = re.compile(r'\bsorry\b')
def strip(s):
    out=[]; i=0; depth=0; n=len(s)
    while i < n:
        two = s[i:i+2]
        if two == '/-': depth += 1; i += 2; continue
        if two == '-/' and depth > 0: depth -= 1; i += 2; continue
        if depth > 0: i += 1; continue
        if two == '--':
            j = s.find('\n', i); i = (n if j < 0 else j); continue
        out.append(s[i]); i += 1
    return ''.join(out)
total = 0
for f in sorted(glob.glob('Jacobians/**/*.lean', recursive=True)):
    if '/Vendor/' in f: continue
    c = len(pat.findall(strip(open(f, encoding='utf-8').read())))
    if c: print(f"{c}\t{f}"); total += c
print(f"TOTAL\t{total}")
PY
)"
sorry_files="$(awk -F'\t' '$1!="TOTAL"{print $2}' <<<"$report")"

# --list-files: emit the robust file list for the blocking core guard, nothing else.
if [ "${1:-}" = "--list-files" ]; then
  printf '%s\n' "$sorry_files"
  exit 0
fi

real_total="$(awk -F'\t' '$1=="TOTAL"{print $2}' <<<"$report")"
fail=0
err() { echo "::error::$1"; fail=1; }

echo "Real sorry-bearing files (comments stripped, \\bsorry\\b):"
awk -F'\t' '$1!="TOTAL"{printf "  %2d  %s\n",$1,$2}' <<<"$report"
echo "  -> real total: $real_total"

# (1) Every sorry-bearing file must be allowlisted in lean.yml (single source).
allow="$(sed -n '/allow="/,/"/p' .github/workflows/lean.yml \
        | sed 's/allow="//; s/"$//; s/^[[:space:]]*//' \
        | grep -E '\.lean$')"
while IFS= read -r f; do
  [ -z "$f" ] && continue
  grep -qxF "$f" <<<"$allow" || err "$f carries a sorry but is NOT in the lean.yml allowlist"
done <<<"$sorry_files"

# (2) README "At a glance" total must equal the real count.
line="$(grep -E '^\| \*\*`sorry`s\*\*' README.md | head -1)"
gap="$(grep -oE '[0-9]+ (in )?out-of-scope' <<<"$line" | grep -oE '^[0-9]+')"
anc="$(grep -oE '[0-9]+ anchor' <<<"$line" | grep -oE '^[0-9]+')"
if [ -z "$gap" ] || [ -z "$anc" ]; then
  err "could not parse the README 'At a glance' sorry line (format drift?): $line"
else
  claimed=$((gap + anc))
  echo "README claims: $gap gap-layer + $anc anchor-layer = $claimed"
  [ "$claimed" = "$real_total" ] || \
    err "README sorry total ($claimed) != real count ($real_total) — reconcile README.md"
fi

if [ "$fail" = 0 ]; then
  echo "✓ sorry counts consistent (real = README = $real_total; all in allowlist)"
else
  echo "✗ sorry-count drift — see errors above"
fi
exit $fail
