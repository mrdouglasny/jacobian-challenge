# h0 + hBranch — the last two analytic hypotheses (Gemini-3.1-pro-vetted)

*2026-06-07. The final inputs to unconditional σ-anti-invariance. `hAna` done.
After these two, the capstone `liouvilleTwoSheetSumRemovable_eq_zero_of_…` fires.*

## h0 — `Tendsto (liouvilleTwoSheetSumRemovable form) (cocompact ℂ) (𝓝 0)`
Decay at ∞. Only TWO ∞ points → use FIXED ∞-charts, no dynamic cover.
- `tendsto_inv_cocompact_zero : Tendsto (·⁻¹) (cocompact ℂ) (𝓝 0)`
  (via `tendsto_norm_cocompact_atTop` + `tendsto_inv_atTop_zero`).
- **EventuallyEq** (the work): `s =ᶠ[cocompact ℂ] fun z => -(z⁻¹)^2 * (g₁ (z⁻¹) + g₂ (z⁻¹))`,
  where `g₁,g₂` are the form's coeffs in the two FIXED ∞-charts (the points over ∞).
  For large |z|, `1/z` is in the ∞-chart target and the chosen point's `Quotient.out`
  is the ∞ rep, so each `affCoeff = form.coeff⟦inl·⟧(1/z)·(-1/z²)`; replace the moving
  center by the fixed ∞-chart via `affCoeff_eq_of_overlap`.
- `g₁,g₂` `ContinuousAt 0` (they're `AnalyticAt 0` = form.coeff on the ∞ chart target).
- Limit arithmetic: `(z⁻¹)^2 → 0` (`Tendsto.pow`,`.neg`), `g₁(z⁻¹)+g₂(z⁻¹) → g₁ 0+g₂ 0`
  (`ContinuousAt.tendsto.comp tendsto_inv_cocompact_zero`), `Tendsto.mul` ⇒ `0·(…)=0`.
- `Filter.EventuallyEq.tendsto` + `simpa`. (Reconcile `liouvilleTwoSheetSumRemovable`
  with `liouvilleTwoSheetSum` off-roots via the existing `…Removable_eventuallyEq_…`.)

## hBranch — `∀ z₀, f z₀=0 → ∃ L, Tendsto (liouvilleTwoSheetSum form) (𝓝[≠] z₀) (𝓝 L)`
Removable limit at branch points. KEY TOOLS: `dslope` + `Filter.map_map`.
- Local coord `w=y`, `z_map w = z(w) = z₀ + w²u(w)` (the projY local homeo image).
- `s(z_map w) = N(w)/D(w)` for w≠0, where `N(w)=H(w)−H(−w)` (H=projY coeff, odd ⇒ N 0=0),
  `D(w)=z_map w − z₀` (= w²u(w), D 0=0). [Establish this `h_cancel` EventuallyEq from the
  affCoeff/projY-chart formula — the real chart work.]
- **Factor out w via `dslope`** (`Mathlib.Analysis.Calculus.Dslope`):
  `A := dslope N 0`, `B := dslope D 0`; `w * dslope f 0 w = f w - f 0` (so `w·A w = N w`,
  `w·B w = D w`); `DifferentiableAt.continuousAt_dslope` ⇒ `A,B ContinuousAt 0`.
  `B 0 ≠ 0` (the branch derivative is nonzero — squarefree f ⇒ f'≠0 at roots; `D = w²u`,
  `dslope D 0 = w·u`, hmm — actually `D 0=0,D'0=0` since D~w²; recheck: want
  `s(z(w))=(H(w)−H(−w))/z'(w)`, z'(w)=D'(w); use the ODD/EVEN structure so the SINGLE w
  cancels — N odd ⇒ N=w·A, z'(w)=2wu+… = w·B' with B'(0)=2u(0)≠0. Use dslope on N and on
  `w↦z'(w)` appropriately so one w cancels, leaving `A(w)/B'(w)`, B'(0)≠0.]
- `s∘z_map =ᶠ[𝓝[≠]0] A/B'`, continuous at 0 (`ContinuousAt.div`, B'(0)≠0) ⇒
  `Tendsto (s∘z_map) (𝓝[≠]0) (𝓝 (A 0/B' 0))`.
- **Push through the 2:1 map** (NOT a homeo — don't invert): prove
  `Filter.map z_map (𝓝[≠] 0) = 𝓝[≠] z₀` (z_map continuous + open (`AnalyticAt.isOpenMap`/
  nonconstant) + locally `z_map w = z₀ ↔ w=0`), then `Filter.map_map` + `tendsto_def`
  transfers `Tendsto (s∘z_map)(𝓝[≠]0)` to `Tendsto s (𝓝[≠] z₀)`. `use (A 0/B' 0)`.

## Then (assembly — already-green capstone)
`liouvilleTwoSheetSumRemovable_eq_zero_of_analyticAt_off_roots_branch_tendsto_cocompact`
  hAna(=`liouvilleTwoSheetSum_analyticAt_off_roots`) hBranch h0 ⇒ `∀z, s̃ z = 0` ⇒
`chosen_coeff_eq_neg_of_liouvilleTwoSheetSumRemovable_eq_zero` = affCoeff anti-invariance.
Then numerator G=affCoeff·√f sheet-independent ⇒ entire+poly-growth ⇒ polynomial g ⇒
flip `AX_HyperellipticForm` (readout via `affCoeff_of_inl` at hQ points) → L3 → 55→53.
