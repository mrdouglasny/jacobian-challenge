# L2 flip — decomposed plan (post-anti-invariance)

*2026-06-07. σ-anti-invariance is PROVEN (`affCoeff_chosen_anti_invariance`,
d6a471a). Remaining: flip `AX_HyperellipticForm_polynomial_decomposition` (L2,
#35) + `AX_HyperellipticOneForm_eq_form` (L3, #36). Codex failed 3× on the
monolithic version (recon/hang). NEW APPROACH: small commit-each lemmas, mirrors
done by hand (Opus), growth gets a dedicated blueprint. Each step build-gated +
committed + pushed so a hang costs one lemma, not the session.*

## The wrapper target (LiouvilleSupport.lean:3576)
`polynomial_decomposition_of_entire_growth (form) (G) (hGdiff : Differentiable ℂ G)
(C) (hC : ∀z, ‖G z‖ ≤ C(1+‖z‖)^(N/2−2)) (hReadout) → L2 axiom`. Provide G + 4 args.

## Decomposed steps (each its own commit)
- **L2.1a** `affCoeff_mul_sqrt_invol` (numerator sheet-independence):
  `affCoeff form a z · √f_a(z) = affCoeff form a.invol z · √f_{a.invol}(z)`, from
  `affCoeff_chosen_anti_invariance` (affCoeff flips) + the √f sheet-sign-flip
  (`(squareLocalHomeomorph a.invol).symm (f z) = −(squareLocalHomeomorph a).symm (f z)`
  — may need proving from `squareLocalHomeomorph_symm_at_basepoint` / `_eq_of_mem`).
- **L2.1b** `def liouvilleNumeratorGRemovable` — global numerator; off-branch
  `affCoeff (chosen z)·√f`, at branch `Filter.limUnder (𝓝[≠] z) (off-branch)`
  (mirror `liouvilleTwoSheetSumRemovable`).
- **L2.1c** `liouvilleChosenNumeratorG_analyticAt` (fixed-chart): `AnalyticAt
  (fun z => affCoeff a₀ z · √f_{a₀} z) z₀` — TRIVIAL mirror of
  `liouvilleChosenTwoSheetSum_analyticAt` (:2785): `affCoeff_analyticAt_basepoint`
  × `squareLocalHomeomorph_symm_eval_analyticOn`, `.mul`.
- **L2.2** `liouvilleNumeratorG_analyticAt_off_roots` — MIRROR
  `liouvilleTwoSheetSum_analyticAt_of_eval_ne_zero` (:2809–2940): same fixed-chart
  a₀ + overlap (`affCoeff_eq_of_projX_symm`) EventuallyEq + the sheet case-split,
  but ONE term `affCoeff·√f`; the cross-sheet case uses L2.1a (instead of add_comm).
  `.congr` with `liouvilleChosenNumeratorG_analyticAt`.
- **L2.3** `liouvilleNumeratorG_branch_tendsto` — `∀ z₀, f z₀=0 → ∃L Tendsto G (𝓝[≠]z₀)(𝓝 L)`.
  SIMPLER than hBranch: G in the projY w-chart = `liouvilleProjYNumerator` directly
  (NO odd-part cancellation — one sheet), analytic at w=0
  (`liouvilleBranchPoint_numerator_analyticAt_zero`); push via `Filter.map_map` (reuse
  the `liouvilleTwoSheetSum_branch_tendsto` map-pushforward lemmas).
- **L2.4** `Differentiable ℂ liouvilleNumeratorGRemovable` — `differentiable_of_analyticAt_off_roots`
  + Continuous (from L2.2 off-root + L2.3 branch limits, mirror `…Removable_differentiable_…`).
- **L2.5 GROWTH — Gemini-3.1-pro-vetted route (b): work in the ∞-chart, NO √f branch-selection.**
  KEY IDENTITY (powers of `u=1/z` cancel algebraically): `G(z)/z^(N/2−2) =ᶠ[cocompact ℂ] −H(1/z)·v(1/z)`,
  where `H = form.coeff` in the ∞-chart (analytic at u=0, value `c₀`) and `v(u)` = the ∞-chart
  `√(reverse f)(u)` branch (`v² = (reverse f)(u)` via the gluing `mem_of_affine` Even.lean:291;
  `√f(z) = v(1/z)·z^(N/2)`). Both analytic at 0 ⇒ `−H·v` ContinuousAt 0 ⇒
  `Tendsto (G·/z^(N/2−2)) cocompact (𝓝 (−H 0·v 0))` via `tendsto_inv_cocompact_zero` (ALREADY proven)
  + `EventuallyEq.tendsto` + `ContinuousAt.mul/.neg` + `Tendsto.comp`. The EventuallyEq REUSES the
  ∞-chart machinery from `h0` (`liouvilleTwoSheetSumRemovable_tendsto_zero_cocompact` did the same
  `s =ᶠ[cocompact] -(z⁻¹)²·(g₁+g₂)` reduction — copy its fixed-∞-chart EventuallyEq, single term × v).
  Then `polynomial_growth_bound_of_tendsto_div_pow G (N/2−2) (−H 0·v 0) (G continuous) (the Tendsto)`
  (:3502) ⇒ `∃C, ‖G z‖≤C(1+‖z‖)^(N/2−2)`.
- **L2.5-OLD** GROWTH `‖G z‖ ≤ C(1+‖z‖)^(N/2−2)` — the ONE genuinely new piece (∞-chart).
  `polynomial_growth_bound_of_tendsto_div_pow G (N/2−2) c (cont) (hLim)`,
  `hLim : Tendsto (G z/z^(N/2−2)) cocompact (𝓝 c)`. At ∞ chosen-rep is `inr`:
  `G z = form.coeff⟦inl⟧(1/z)·(−1/z²)·√f(z)`, `√f~z^(N/2)`. ⇒ get its own Gemini-3.1-pro
  blueprint (the √f-at-∞ growth is the fiddly bit) BEFORE coding.
- **L2.6/7** hReadout (`affCoeff_of_inl` + `form_coeff_eq_liouvilleProjXNumerator_div`) +
  `exact polynomial_decomposition_of_entire_growth …` ⇒ FLIP L2.
- **L3** `AX_HyperellipticOneForm_eq_form`: ω'=hyperellipticForm H g; coeff agree on
  projX (L2) + projY (cocycle `hyperellipticEvenCoeff_cocycle_inr_inl` real) ⇒
  `HolomorphicOneForm.ext_of_coeff`. FLIP.

## Discipline
One lemma → `lake env lean` → commit → `git push`. No monolithic dispatches.
Growth (L2.5) is the only real risk; everything else is mirror/assembly of PROVEN lemmas.
