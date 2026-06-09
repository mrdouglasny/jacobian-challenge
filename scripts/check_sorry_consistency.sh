#!/usr/bin/env bash
# Sorry-count consistency guard.
#
# The file-level guard in `.github/workflows/lean.yml` proves the *core* stays
# sorry-free (every sorry-bearing file is an allowlisted scaffold) but, by its
# own note, does NOT assert a total — "a cheap grep over-counts proof-sketch
# lines". That left the README's per-declaration sorry counts unchecked, and
# they drifted (e.g. the adelic `RiemannRochAnchor` 3 went uncounted from #105
# until they were reconciled).
#
# This script closes that hole. It counts REAL sorrys (Lean comments — including
# `/-- … := by sorry … -/` docstring examples — stripped first, so the count is
# not inflated by prose), and checks:
#   (1) every sorry-bearing file is in the lean.yml allowlist (single source of
#       truth — parsed from the workflow, not duplicated here);
#   (2) the README "At a glance" sorry total (gap-layer + anchor-layer) equals
#       the real kernel-style count.
#
# Run from anywhere; exits non-zero on any drift.
set -uo pipefail
cd "$(dirname "$0")/.."

fail=0
err() { echo "::error::$1"; fail=1; }

# --- 1. Real per-file sorry counts (comment-stripped) -----------------------
counter() {
python3 - "$@" <<'PY'
import re, glob, sys
# A real sorry: `:= sorry`, `by sorry`, `=> sorry`, `; sorry`, `<;> sorry`, or a
# bare `sorry` line — but only in CODE, after stripping block/line comments.
pat = re.compile(r'(?:(?::=|\bby|=>|;|<;>)\s*sorry\b|^\s*sorry\s*$)', re.M)
def strip_comments(s):
    out=[]; i=0; depth=0; n=len(s)
    while i<n:
        two=s[i:i+2]
        if two=='/-': depth+=1; i+=2; continue
        if two=='-/' and depth>0: depth-=1; i+=2; continue
        if depth>0: i+=1; continue
        if two=='--':
            j=s.find('\n',i); i=(n if j<0 else j); continue
        out.append(s[i]); i+=1
    return ''.join(out)
total=0
for f in sorted(glob.glob('Jacobians/**/*.lean', recursive=True)):
    if '/Vendor/' in f: continue
    c=len(pat.findall(strip_comments(open(f).read())))
    if c: print(f"{c}\t{f}"); total+=c
print(f"TOTAL\t{total}")
PY
}
report="$(counter)"
real_total="$(awk -F'\t' '$1=="TOTAL"{print $2}' <<<"$report")"
sorry_files="$(awk -F'\t' '$1!="TOTAL"{print $2}' <<<"$report")"

echo "Real sorry-bearing files (comments stripped):"
awk -F'\t' '$1!="TOTAL"{printf "  %2d  %s\n",$1,$2}' <<<"$report"
echo "  -> real total: $real_total"

# --- 2. Every sorry-bearing file must be allowlisted in lean.yml -------------
# Parse the `allow="..."` heredoc block from the workflow (single source).
allow="$(sed -n '/allow="/,/"/p' .github/workflows/lean.yml \
        | sed 's/allow="//; s/"$//; s/^[[:space:]]*//' \
        | grep -E '\.lean$')"
while IFS= read -r f; do
  [ -z "$f" ] && continue
  grep -qxF "$f" <<<"$allow" || err "$f carries a sorry but is NOT in the lean.yml allowlist"
done <<<"$sorry_files"

# --- 3. README "At a glance" total must equal the real count ----------------
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
