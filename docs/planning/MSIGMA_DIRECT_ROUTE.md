# Mσ — direct two-sheet route to σ-anti-invariance (Gemini-deep-think-vetted)

*2026-06-07. REPLACES the `pullbackInvolution`-form route (Mσ.3→.5 in the
original roadmap/handoff). The pullback route hit a real obstruction:
obligation (1) analyticity of `(σ*ω).coeff q` on `(extChartAt q).target` needs
`σ` to map a whole chart source at `q` into the chart source at `σq`, which is
FALSE on the coarse atlas (`extChartAt` uses `Quotient.out` — arbitrary rep,
possibly the ∞ rep; chart sources are local "square" homeo sources). Gemini
deep-think (2026-06-07, 1m35s) decisively recommended this direct route instead
— "the pullback atlas-transfer boilerplate is agonizing; do not do this."*

## The idea
Prove the P1 anti-invariance identity **directly**, bypassing any global form
construction. On the clean affine projX charts only, define the base-space
scalar
```
s(z) := ω.coeff qSame z + ω.coeff qOpp z      (the σ-INVARIANT combination)
```
(qSame, qOpp = the two sheets over a non-branch z = q and σq) and prove `s ≡ 0`.
That is exactly anti-invariance: `ω.coeff qOpp z = − ω.coeff qSame z` (= the P1
goal / the sheet-swap helper's remaining obligation `coeff qSame = −coeff qOpp`).

## Why the SUM (not the difference) is the right object
At a simple branch point z₀ (`f z₀=0`, `f' z₀≠0`), local surface coord `w=y`,
projection `z(w) = z₀ + w²·u(w)`, `u(0)≠0`. By the cotangent cocycle the
projX coeff on the two sheets ±w is `φ₁(z)=H(w)·(dw/dz)`, `φ₂(z)=−H(−w)·(dw/dz)`
where `H(w):=ω.coeff_w(w)` is the projY-chart coeff. So
```
s(z) = φ₁+φ₂ = (H(w)−H(−w))·(dw/dz) = (H(w)−H(−w)) / z'(w).
```
`z'(w)=2w·u+w²u'` has a SIMPLE ZERO at w=0; `H(w)−H(−w)` is ODD ⇒ also zero at
w=0 ⇒ the `1/w` blow-ups CANCEL ⇒ `s` is bounded, limit `H'(0)/u(0)`. (The
difference `φ₁−φ₂ ∝ H(w)+H(−w) ≈ 2H(0)` does NOT cancel ⇒ blows up like
1/√(z−z₀). So the SUM is the removable/entire one.)

## Execution (reuses this session's banked lemmas)
- **Step A — single-valued.** For z ∉ branchPoints the fibre is `{q, σq}`; `s(z)`
  is symmetric in the two sheets (commutativity of `+`) ⇒ well-defined holomorphic
  on `ℂ \ branchPoints`. Analytic there: each `ω.coeff` analytic on its projX
  target (`liouvilleProjXNumerator`-style / `form.coeff_analyticOn`).
- **Step B — entire.** `s` extends across each branch point (removable, limit
  above). Engine: **`differentiable_of_analyticAt_off_roots`** (BANKED, e3d407f)
  — needs `s` analytic off `{f=0}` (Step A) + `s` continuous everywhere (the
  branch limit). The branch continuity is the one genuine analytic lemma to
  prove: `Tendsto s (𝓝[≠] z₀) (𝓝 (H'(0)/u(0)))`, via the `w`-coordinate odd-zero
  cancellation. **This is the hard kernel of the direct route** (replaces the old
  P3; same flavour, but now on the well-behaved `s`).
- **Step C — decay at ∞.** Even degree ⇒ two ∞ points, NOT branch points, local
  coord `t=1/z`, `dz=−dt/t²` ⇒ both `φ_i = O(1/z²)` ⇒ `s = O(1/z²) → 0` along
  `cocompact ℂ`.
- **Step D — Liouville.** entire (B) + →0 at ∞ (C) ⇒ `s ≡ 0` via
  **`eq_zero_of_differentiable_tendsto_zero_cocompact`** (BANKED, cd7ae6c).
- **Conclusion.** `s≡0` ⇒ `ω.coeff qOpp z = −ω.coeff qSame z` ⇒ feeds the P1
  sheet-swap (`liouvilleProjXNumerator_eq_of_neg_coeff_neg_branch`, 4a02267) ⇒
  L2 Differentiable-G P1 closes ⇒ P3/P4 per `L2_DIFFERENTIABLE_G_BLUEPRINT.md` ⇒
  flip `AX_HyperellipticForm_polynomial_decomposition` ⇒ L3 ⇒ 58→56.

## Status of the abandoned pullback pieces
Codex's green Mσ.3 helpers (`pullbackInvolutionChartRep/DerivFactor/Coeff`,
`…_isZeroOffChartTarget`, `…_projX`) stay in `AntiInvariance.lean` — harmless,
sorry-free, and `…DerivFactor`/`…ChartRep` encode the σ chart-derivative facts
(B_q, A_q) the Step-B `w`-coordinate computation may reuse. No need to delete.

## Open sub-tasks (in order)
1. **DR-A** ✅ DONE (Codex 70b5c9e, green): `liouvilleTwoSheetSum` (global `s`),
   `liouvilleChosenAffinePoint`, `liouvilleLocalSheetSum`,
   `liouvilleTwoSheetSum_of_eval_ne_zero`,
   `liouvilleLocalSheetSum_analyticAt_inter_affineProjX` (s analytic off {f=0}),
   and the payoff bridge `chosen_coeff_eq_neg_of_liouvilleTwoSheetSum_eq_zero`
   (s≡0 ⇒ anti-invariance). Quotient.out rep issue worked around.
2. **DR-B/C/D scaffolding** ✅ DONE (Codex a53b64a/bec6e4a, green, sorry-free):
   `liouvilleTwoSheetSumRemovable` (`s̃`, branch value = `Filter.limUnder` per the
   blueprint), `…_differentiable_of_analyticAt_off_roots_and_branch_tendsto`
   (∃-limit, NOT =0 — non-circular), `…_eq_zero_of_…_branch_tendsto_cocompact`,
   and `chosen_coeff_eq_neg_of_liouvilleTwoSheetSumRemovable_eq_zero`. The
   capstone `liouvilleTwoSheetSumRemovable_eq_zero_of_analyticAt_off_roots_branch_tendsto_cocompact`
   reduces anti-invariance to THREE analytic hypotheses, now the only open work:
   - **hAna** `∀ z, f z≠0 → AnalyticAt s z` (DR-A largely has it — wire in).
   - **hBranch** `∀ branch z, ∃ L, Tendsto s (𝓝[≠] z) (𝓝 L)` (THE HARD KERNEL —
     `DR_B_BRANCH_CONTINUITY_BLUEPRINT.md` w-cancellation).
   - **h0** `Tendsto s̃ cocompact (𝓝 0)` (DR-C ∞-decay).
   IN PROGRESS: Codex afd7ddaa8cd055d1c discharging the three.
