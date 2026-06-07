# DR-B — branch continuity of the two-sheet sum `s` (Gemini-3.1-pro-vetted)

*2026-06-07. The hard kernel of the direct two-sheet route. Fixes a real flaw in
the DR-A definition and gives the clean Lean path.*

## The flaw to fix first
DR-A (70b5c9e) defined the global `s = liouvilleTwoSheetSum` with **`s z := 0` at
branch points** (`@[simp] liouvilleTwoSheetSum_of_eval_eq_zero`). But the true
removable limit of `s` at a branch point z₀ is `H'(0)/u(0)`, **generically ≠ 0**
(it only becomes 0 after we conclude `s≡0`). So this `s` is DISCONTINUOUS at
branch points and `Continuous s` is unprovable without presupposing the
conclusion. **The `=0`-at-branch value must be replaced by the limit.**

## The fix — define the branch value as `Filter.lim` (value supplied automatically)
```lean
noncomputable def s̃ (form) (z : ℂ) : ℂ :=
  if H.f.eval z = 0 then Filter.lim (𝓝[≠] z) (liouvilleTwoSheetSum form)
  else liouvilleTwoSheetSum form z
```
Using `Filter.lim` means we NEVER name `H'(0)/u(0)` — we only prove *a limit
exists*, and `lim` extracts it. (Equivalently keep `liouvilleTwoSheetSum`'s
off-branch values and only the branch values change; the downstream consumer
needs `s≡0` OFF branch points, which is what we get.)

## `Differentiable ℂ s̃` — pointwise
- **Off root** (`f z ≠ 0`): `s̃ =ᶠ[𝓝 z] liouvilleTwoSheetSum form` ⇒ differentiable
  via DR-A's off-root analyticity + `Filter.EventuallyEq.differentiableAt`.
- **At root** (`f z₀ = 0`): removable singularity. Real Mathlib lemma (Gemini
  re-hallucinated `…differentiableAt_of_continuousAt_of_differentiableOn_compl_singleton`
  — DOES NOT EXIST):
  `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  `(hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z) (hc : ContinuousAt f c) : AnalyticAt ℂ f c`.
  `hd` from DR-A off-root analyticity + `eventually_eval_ne_zero_nhdsWithin` (P2).
  `hc` = `ContinuousAt s̃ z₀`: since `s̃ z₀ = lim (𝓝[≠] z₀) (twoSheetSum)`, this
  reduces to **`∃ L, Tendsto (liouvilleTwoSheetSum form) (𝓝[≠] z₀) (𝓝 L)`**
  (then `lim = L` and `s̃` is continuous: `Tendsto.lim_eq` + the cases agree).
  Equivalently package via the banked `differentiable_of_analyticAt_off_roots`
  applied to `s̃` once `Continuous s̃` is shown.

## The limit-exists crux (the only genuinely-local work) — inside the `w` chart
Goal: `∃ L, Tendsto (liouvilleTwoSheetSum form) (𝓝[≠] z₀) (𝓝 L)`.
Local model at a simple branch point: coord `w=y`, `z(w)=z₀+w²u(w)`, `u(0)≠0`,
`z'(w)=w·(2u(w)+w u'(w))`. With `H(w)` the projY-chart coeff,
`liouvilleTwoSheetSum (z(w)) = (H(w)−H(−w)) / z'(w)` for `w≠0`.
1. `N(w):=H(w)−H(−w)` analytic, `N(0)=0` ⇒ factor `N w = w·A w`, `A` analytic at 0
   (Mathlib: analytic + vanishes at 0 ⇒ divisible by `id`; via order / `AnalyticAt`
   `(z-z₀)`-factorization API).
2. `z'(w)=w·B w`, `B w = 2u(w)+w u'(w)` analytic, `B 0 = 2u(0) ≠ 0`.
3. Cancel `w` on `𝓝[≠] 0`: `twoSheetSum(z(w)) = A w / B w` (`Filter.EventuallyEq`).
4. `A/B` continuous at 0 (`B 0 ≠ 0`) ⇒ `Tendsto (A·/B·) (𝓝 0) (𝓝 (A 0/B 0))`.
5. Push to the base via the local homeo `w ↦ z(w)` (punctured nhds):
   `Tendsto twoSheetSum (𝓝[≠] z₀) (𝓝 (A 0/B 0))`. ⇒ `∃ L`.
   Reuse Codex's `pullbackInvolutionDerivFactor`/`…ChartRep` (B_q, A_q) +
   `polynomialLocalHomeomorph_symm_sq_derivative_div_two_analyticOn` for the
   `z'(w)`/`u` analyticity, and the projY chart API (`affineChartProjY`,
   `polynomialLocalHomeomorph.symm`).

## Then
`s̃` entire (above) + `s̃ → 0` at ∞ (DR-C, `s̃=twoSheetSum` off-branch, both sheet
coeffs `O(1/z²)`) ⇒ `s̃ ≡ 0` via banked `eq_zero_of_differentiable_tendsto_zero_cocompact`
⇒ `liouvilleTwoSheetSum form z = 0` for non-branch z ⇒
`chosen_coeff_eq_neg_of_liouvilleTwoSheetSum_eq_zero` ⇒ anti-invariance ⇒ P1.
