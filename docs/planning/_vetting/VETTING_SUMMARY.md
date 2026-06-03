# Gemini 3.1 Pro vetting — strategic subset (12 of 90 plans)

Critiques produced by `gemini-3.1-pro-preview` with extended thinking enabled,
2026-06-03. Each critique is in this directory as `<slug>.md`; tally in
`_RESULTS.json`. Full critiques average ~3.5K chars each (~150 lines).

## Tally

| Verdict | Count | Plans |
|---|---|---|
| `accept`  | **1**  | `Divisor-deg` |
| `revise`  | **6**  | `AX_RiemannBilinear`, `AX_BranchLocus`, `AX_H1_ProjectiveLine_trivial`, `PlaneCurve-instCompactSpace`, `AX_AbelTheorem`, `AX_HyperellipticOneForm_eq_form` |
| `reject`  | **5**  | `AX_SerreDuality`, `AX_RiemannRoch`, `AX_HyperellipticForm_polynomial_decomposition`, `AX_genus_eq_zero_iff_homeo`, `AX_pushforward_pullback` |
| **Total** | 12   | |

## One-line verdicts

| Plan | V | Gemini's headline issue |
|---|---|---|
| `AX_RiemannRoch` | **reject** | Plan claims `genuine-textbook` but explicitly relies on `AX_SerreDuality` ⇒ really `provable-from-other-axioms` + 2 separate `needs-infra` for Čech LES & Serre finiteness. 2–4K LOC est "laughably naive" (real ~15K+). Čech LES across short exact seq is *not* exact in general without Leray. |
| `AX_SerreDuality` | **reject** | Should be `needs-infra` effort 10, not `mathlib-now`. Massive missing functional analysis + differential form integration. |
| `AX_HyperellipticForm_polynomial_decomposition` (L2) | **reject** | Recipe decomposes the wrong function ⇒ false polynomial claim. Function-field route bloats effort; an elementary pointwise-symmetry argument exists. |
| `AX_genus_eq_zero_iff_homeo` | **reject** | False mathematical premise — RHS is a **topological** ≃ₜ S² but the proof needs **biholomorphism** to ℂℙ¹ to pull back holomorphic invariants. The two are not interchangeable. |
| `AX_pushforward_pullback` | **reject** | Plan "unfolds an axiom's docstring" and introduces a new helper axiom — that's can-kicking, not discharge. |
| `AX_HyperellipticOneForm_eq_form` (L3 demo) | revise | The pointwise cocycle argument fails at branch/infinity chart origins `z = 0` because those points lie outside the chart overlap; needs a continuity-extension step. Step 4 is redundant. |
| `AX_AbelTheorem` | revise | Math errors: "purely imaginary" vs $2πi\mathbb{Z}$; "real periods" vs A-periods; basepoint may hit a pole; "50 LOC residue theorem" radically wrong. |
| `AX_RiemannBilinear` | revise | Logical cycle: Step 3 (A-matrix inversion) requires Step 4 (general bilinear identity). |
| `AX_BranchLocus` | revise | Gemini says route should *actually be* `mathlib-now` (contra my [review] flag, which guessed needs-infra). Step 6 has a point-set error — fails to cover unramified points before invoking compactness. |
| `AX_H1_ProjectiveLine_trivial` | revise | Confirms my [review] flag. Effort/LOC underestimated — `FundamentalGroupoid.vanKampen` extraction is hundreds of lines of category boilerplate. |
| `PlaneCurve-instCompactSpace` | revise | Confirms my [review] flag — should be `provable-from-other-axioms` not `mathlib-now`, effort 6 not 3. Logical gap in Step 2B (need max-modulus coordinate to guarantee cover). |
| `Divisor-deg` | **accept** | Effort-1 `FreeAbelianGroup.sum` instance. The one trivial case. |

## Patterns Gemini caught (likely apply to the un-vetted 78)

1. **Route inflation upward** — "mathlib-now" gets stamped on things that
   actually need infrastructure (SerreDuality, RiemannBilinear, H1_ProjectiveLine,
   PlaneCurve-instCompactSpace). Three of my five `[review]` flags were
   confirmed; one (`BranchLocus`) flipped the other way.
2. **Effort underestimation by ~3–10× on textbook-level plans** — the
   classifier agents anchored on "given the right infra, this is short"
   without budgeting the infra itself.
3. **Can-kicking via helper axioms** — `AX_pushforward_pullback` introduces
   a new axiom while claiming to discharge the old one. Need a hard rule
   against any plan whose Step N is "axiomatize <X>".
4. **Math errors hiding in clean prose** — the L2 plan decomposes the wrong
   function; L3 fails at chart origins; AbelTheorem confuses period normalizations.
   Surface plausibility ≠ correctness.
5. **Missing exactness/coverage hypotheses** — Čech LES, Step 6 of BranchLocus,
   Step 2B of PlaneCurve-instCompactSpace all have the same shape: a
   covering / exactness step asserted without justification.

## Cost

- 12 calls, sum 745.6s wall (~12.4 min)
- Total output: ~42K chars across 12 critiques
- Model: `gemini-3.1-pro-preview` with `thinking_budget=-1`
- Single one took 170s (L2 — the deepest math) — extended thinking ran where
  needed without being told.

## Recommended next steps

1. **Treat the vetting outputs as authoritative on these 12 plans.** Patch
   `ROADMAP.md`'s route + effort columns for the 11 non-accepts; rewrite
   each flagged recipe per Gemini's specific guidance (each critique gives
   a concrete revise/reject prescription).
2. **Extend the vetting**. If 11/12 of the strategic subset need work, the
   un-vetted 78 almost certainly contain similar errors. A full sweep is
   ~12 min × (78/12) ≈ 80 min and ~5–10× the cost. Worth it before any
   worker starts discharging.
3. **Add a hard rule to the recipe template**: a recipe whose Step N is
   "axiomatize ⟨X⟩" or "unfold the docstring" is automatically rejected.
4. **Consider a second model** for adversarial check — codex-rescue or
   GPT-5.4 — once located. Two strong models that *agree* a plan is sound
   gives a much better signal than one.
