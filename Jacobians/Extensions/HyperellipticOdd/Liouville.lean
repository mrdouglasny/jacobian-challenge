/-
# Liouville argument for odd-degree hyperelliptic curves

Proves that every holomorphic 1-form on `HyperellipticOdd H` equals
`hyperellipticOddForm H g` for a unique polynomial `g` with
`g.natDegree < (H.f.natDegree - 1) / 2`.

This is the odd-degree counterpart of
`Jacobians.Axioms.HyperellipticLiouville.AX_HyperellipticOneForm_eq_form`.

**Proof strategy (mirroring the even case):**
1. Define raw numerator `G(z) = form.coeff(coe a)(z) · a.val.2`
2. Show `G` extends to an entire function (removable singularities at roots)
3. Show `G` has polynomial growth at infinity
4. Extract polynomial `g` via `differentiable_eq_polynomial_of_growth`
5. Show `form = hyperellipticOddForm H g`

**Key simplification vs even case:** `HyperellipticOdd` is `OnePoint`
(no quotient), so there is no `Quotient.out` case-splitting. The single
infinity point also simplifies the growth bound.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.OddForm
import Jacobians.Extensions.InvolutionPullback
import Jacobians.Axioms.HyperellipticLiouville
import Jacobians.ProjectiveCurve.Hyperelliptic.LiouvilleSupport
import Jacobians.GeneralResults.EntireGrowth
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Jacobians.Axioms.AbelJacobiMap

namespace Jacobians.Extensions.HyperellipticOdd

open scoped Manifold ContDiff Topology
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticOdd

variable {H : HyperellipticData} [Fact (Odd H.f.natDegree)]

/-! ## Definitions -/

/-- The raw single-sheet numerator: `form.coeff(coe a)(z) · y` where
`a` is an arbitrary affine lift of `z` (chosen via `liouvilleChosenAffinePoint`). -/
noncomputable def liouvilleRawNumerator
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) (z : ℂ) : ℂ :=
  let a := liouvilleChosenAffinePoint (H := H) z
  form.coeff (coe a : HyperellipticOdd H Fact.out) z * a.val.2

/-- The removable global numerator for the odd-degree curve.
At roots of `f`, we take the punctured limit; elsewhere we use the raw value. -/
noncomputable def liouvilleRemovableNumerator
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) (z : ℂ) : ℂ :=
  if H.f.eval z = 0 then
    Filter.limUnder (nhdsWithin z {z}ᶜ) (liouvilleRawNumerator form)
  else
    liouvilleRawNumerator form z

@[simp] theorem liouvilleRemovableNumerator_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) {z : ℂ}
    (hz : H.f.eval z ≠ 0) :
    liouvilleRemovableNumerator form z = liouvilleRawNumerator form z := by
  simp [liouvilleRemovableNumerator, hz]

/-- The global two-sheet sum of chart coefficients. -/
noncomputable def liouvilleTwoSheetSum
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) (z : ℂ) : ℂ :=
  if H.f.eval z = 0 then
    0
  else
    let a := liouvilleChosenAffinePoint (H := H) z
    form.coeff (coe a : HyperellipticOdd H Fact.out) z +
      form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z

/-- The removable version of the two-sheet sum. -/
noncomputable def liouvilleTwoSheetSumRemovable
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) (z : ℂ) : ℂ :=
  if H.f.eval z = 0 then
    Filter.limUnder (nhdsWithin z {z}ᶜ) (liouvilleTwoSheetSum form)
  else
    liouvilleTwoSheetSum form z

/-! ## Part A: Anti-invariance of the raw numerator

The product `form.coeff(coe a)(z) · a.val.2` is invariant under sheet
switching `a ↦ a.invol`. This is because the chart transition between the
`affineLiftChart` at `coe a` and at `coe a.invol` (through the overlap
with the infinity chart or a branch-point chart) introduces a sign flip
in the coefficient that cancels the sign flip in `y`.

Concretely: `form.coeff(coe a)(z) = −form.coeff(coe a.invol)(z)` for
`a ∈ smoothLocusY`, so `coeff · y = (−coeff) · (−y)`.
-/

/-- Anti-invariance: the chart coefficient negates when switching sheets.
For `a ∈ smoothLocusY H`, `form.coeff (coe a) z = −form.coeff (coe a.invol) z`. -/
theorem form_coeff_anti_invariance
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z =
      -form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z := by
  have hz_ext : z ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
      Set.range_id, Set.inter_univ]
    change z ∈ (affineLiftChart a).target
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    change z ∈ (HyperellipticAffine.affineChartAt a).target
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a haY]
    exact hz
  have h_src : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source :=
    PartialEquiv.map_target _ hz_ext
  rw [extChartAt_source] at h_src
  change (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z ∈ (affineLiftChart a).source at h_src
  rw [affineLiftChart_source] at h_src
  rcases h_src with ⟨q_aff, hq_src, hq_eq⟩
  have hq_Y : q_aff ∈ HyperellipticAffine.smoothLocusY H := by
    have h_src' : q_aff.val.2 ∈ (HyperellipticAffine.squareLocalHomeomorph a haY).source := by
      change q_aff ∈ (HyperellipticAffine.affineChartAt a).source at hq_src
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a haY] at hq_src
      exact hq_src
    have h_ne : q_aff.val.2 ≠ 0 := by
      intro hc
      have h0 : (0 : ℂ) ∈ (HyperellipticAffine.squareLocalHomeomorph a haY).source := hc ▸ h_src'
      exact HyperellipticAffine.squareLocalHomeomorph_zero_notMem_source a haY h0
    exact h_ne
  have hq_invol_Y : q_aff.invol ∈ HyperellipticAffine.smoothLocusY H := by
    change q_aff.invol.val.2 ≠ 0
    simp only [HyperellipticAffine.invol_val, neg_ne_zero]
    exact hq_Y
  have ha_invol_Y : a.invol ∈ smoothLocusY H := by
    change a.invol.val.2 ≠ 0
    rw [HyperellipticAffine.invol_val]
    simp only [neg_ne_zero]
    exact haY
  have hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z) ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source := sorry
  have hRel := Axioms.pullbackOneForm_isPullbackCoeffRel
    (hyperellipticInvolution H Fact.out)
    (hyperellipticInvolution_contMDiff H Fact.out)
    form
  have h_eq := hRel (coe a) (coe a.invol) z hz_ext hy_src
  have h_pullback : (Axioms.pullbackOneForm (hyperellipticInvolution H Fact.out)
      (hyperellipticInvolution_contMDiff H Fact.out) form).coeff (coe a) z =
      - form.coeff (coe a) z := by
    have h_map := congr_arg (fun f : HolomorphicOneForm (HyperellipticOdd H Fact.out) => f.coeff (coe a) z) (LinearMap.congr_fun (_root_.pullback_hyperellipticInvolution_eq_neg_proof H) form)
    exact h_map
  rw [h_pullback] at h_eq
  have h_z_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z) = z :=
    PartialEquiv.right_inv _ hz_ext
  have h_q_val_1 : q_aff.val.1 = z := by
    rw [← hq_eq] at h_z_eq
    change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some q_aff) = z at h_z_eq
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply] at h_z_eq
    rw [affineChartAt_of_mem_smoothLocusY a haY] at h_z_eq
    exact h_z_eq
  have h_eval_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)) (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z)) = z := by
    have hw_eq : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z) = coe q_aff.invol := by
      rw [← hq_eq]
      rfl
    rw [hw_eq]
    change ((HyperellipticAffine.affineChartAt a.invol).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some q_aff.invol) = z
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rw [affineChartAt_of_mem_smoothLocusY a.invol ha_invol_Y]
    change q_aff.invol.val.1 = z
    rw [HyperellipticAffine.invol_val]
    exact h_q_val_1
  have h_eq_on : ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)) ∘
      hyperellipticInvolution H Fact.out ∘
      ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm =ᶠ[nhds z]
      (fun w => w) := by
    have h_cont_symm : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z :=
      (continuousOn_extChartAt_symm (coe a : HyperellipticOdd H Fact.out)).continuousAt (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz_ext)
    have h_invol_cont : Continuous (hyperellipticInvolution H Fact.out) :=
      (hyperellipticInvolution_contMDiff H Fact.out).continuous
    have h_open_source : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source :=
      isOpen_extChartAt_source _
    have h_pre1 : IsOpen (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source) :=
      h_open_source.preimage h_invol_cont
    have h_pre2 : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹' (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source) ∈ nhds z :=
      h_cont_symm.preimage_mem_nhds (h_pre1.mem_nhds hy_src)
    have h_nhds : ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target ∩
        (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹' (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source)) ∈ nhds z :=
      Filter.inter_mem (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz_ext) h_pre2
    filter_upwards [h_nhds] with w hw
    obtain ⟨hw_target, hw_src⟩ := hw
    simp only [Function.comp_apply]
    have hp_w_src : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source :=
      PartialEquiv.map_target _ hw_target
    rw [extChartAt_source] at hp_w_src
    change _ ∈ (affineLiftChart a).source at hp_w_src
    rw [affineLiftChart_source] at hp_w_src
    rcases hp_w_src with ⟨q_w, hq_w_src, hq_w_eq⟩
    have h_LHS : (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)) (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w)) = q_w.invol.val.1 := by
      rw [← hq_w_eq]
      change ((HyperellipticAffine.affineChartAt a.invol).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w.invol) = q_w.invol.val.1
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      rw [affineChartAt_of_mem_smoothLocusY a.invol ha_invol_Y]
      rfl
    have h_RHS : w = q_w.val.1 := by
      have h_w_eq : w = (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w) := by
        rw [PartialEquiv.right_inv _ hw_target]
      rw [h_w_eq, ← hq_w_eq]
      change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w) = q_w.val.1
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      rw [affineChartAt_of_mem_smoothLocusY a haY]
      rfl
    rw [h_LHS, h_RHS]
    rw [HyperellipticAffine.invol_val]
  have h_fderiv : fderiv ℂ
      (⇑(extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)) ∘
       hyperellipticInvolution H Fact.out ∘
       ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm) z =
      fderiv ℂ (fun w => w) z :=
    h_eq_on.fderiv_eq
  have h_fderiv_id : (fderiv ℂ (fun w : ℂ => w) z) 1 = 1 := by
    have h_fderiv_at : HasFDerivAt (fun w : ℂ => w) (ContinuousLinearMap.id ℂ ℂ) z := by
      exact (ContinuousLinearMap.id ℂ ℂ).hasFDerivAt
    rw [h_fderiv_at.fderiv]
    rfl
  rw [h_eval_eq, h_fderiv, h_fderiv_id, mul_one] at h_eq
  exact neg_eq_iff_eq_neg.mp h_eq

/-- Consequence: the raw numerator is sheet-invariant. -/
theorem liouvilleRawNumerator_sheet_invariant
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z * a.val.2 =
      form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z *
        a.invol.val.2 := by
  rw [form_coeff_anti_invariance form a haY hz]
  simp only [HyperellipticAffine.invol_val]
  ring

/-! ## Part B: Analyticity of the raw numerator away from roots

For `z₀` with `H.f.eval z₀ ≠ 0`, the function `z ↦ liouvilleRawNumerator form z`
is analytic at `z₀`. The proof fixes a model branch using the chart's own
inverse and shows agreement with the raw numerator via anti-invariance.
-/

/-- The model function using a fixed branch: `form.coeff(coe a₀)(z) · y₀(z)`
where `y₀` is the continuous branch selected by `a₀`'s chart. -/
noncomputable def liouvilleModelNumerator
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a₀ : HyperellipticAffine H) (ha₀Y : a₀ ∈ smoothLocusY H)
    (z : ℂ) : ℂ :=
  form.coeff (coe a₀ : HyperellipticOdd H Fact.out) z *
    (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z)

/-- The raw numerator is analytic at every `z₀` where `f(z₀) ≠ 0`. -/
theorem liouvilleRawNumerator_analyticAt_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ (liouvilleRawNumerator form) z₀ := by
  sorry

/-! ## Part C: Removable numerator is analytic off roots -/

/-- The removable numerator is analytic at every non-root point. -/
theorem liouvilleRemovableNumerator_analyticAt_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    AnalyticAt ℂ (liouvilleRemovableNumerator form) z := by
  have hRaw := liouvilleRawNumerator_analyticAt_of_eval_ne_zero form hz
  apply hRaw.congr
  have hEval : ∀ᶠ w in nhds z, H.f.eval w ≠ 0 := by
    exact (Polynomial.continuous H.f).continuousAt.eventually_ne hz
  filter_upwards [hEval] with w hw
  exact (liouvilleRemovableNumerator_of_eval_ne_zero form hw).symm

/-! ## Part D: Branch-point limits

At each root `z₀` of `f`, the raw numerator has a removable singularity
with a finite limit. The argument: near a root, the coefficient
`form.coeff(coe a)(z)` is analytic and bounded, while `y(z) → 0`.
More precisely, the chart at a Weierstrass point uses the `y`-coordinate
(projY chart), and the form coefficient in that chart gives the limit. -/

/-- At each root of `f`, the raw numerator tends to a finite limit. -/
theorem liouvilleRawNumerator_tendsto_at_root
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ = 0) :
    ∃ L : ℂ, Filter.Tendsto (liouvilleRawNumerator form)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds L) := by
  sorry

/-! ## Part E: Continuity of the removable numerator -/

/-- The removable numerator is continuous on all of `ℂ`. -/
theorem liouvilleRemovableNumerator_continuous
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    Continuous (liouvilleRemovableNumerator form) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : H.f.eval z = 0
  · obtain ⟨L, hL⟩ := liouvilleRawNumerator_tendsto_at_root form hz
    rw [continuousAt_iff_punctured_nhds]
    have hValue : liouvilleRemovableNumerator form z =
        Filter.limUnder (nhdsWithin z {z}ᶜ) (liouvilleRawNumerator form) := by
      simp [liouvilleRemovableNumerator, hz]
    rw [hValue]
    have hToLim : Filter.Tendsto (liouvilleRawNumerator form)
        (nhdsWithin z {z}ᶜ)
        (nhds (Filter.limUnder (nhdsWithin z {z}ᶜ) (liouvilleRawNumerator form))) :=
      tendsto_nhds_limUnder ⟨L, hL⟩
    have hEq : liouvilleRemovableNumerator form =ᶠ[nhdsWithin z {z}ᶜ]
        liouvilleRawNumerator form := by
      filter_upwards [eventually_eval_ne_zero_nhdsWithin z] with w hw
      exact liouvilleRemovableNumerator_of_eval_ne_zero form hw
    exact hToLim.congr' hEq.symm
  · have hEq : liouvilleRemovableNumerator form =ᶠ[nhds z]
        liouvilleRawNumerator form := by
      have hEval : ∀ᶠ w in nhds z, H.f.eval w ≠ 0 :=
        (Polynomial.continuous H.f).continuousAt.eventually_ne hz
      filter_upwards [hEval] with w hw
      exact liouvilleRemovableNumerator_of_eval_ne_zero form hw
    exact (liouvilleRawNumerator_analyticAt_of_eval_ne_zero form hz).continuousAt.congr hEq.symm

/-! ## Part F: Differentiability of the removable numerator

Combines: analytic off finitely many roots + continuous everywhere
→ entire (differentiable on all of `ℂ`). -/

/-- The removable numerator is an entire function. -/
theorem liouvilleRemovableNumerator_differentiable
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    Differentiable ℂ (liouvilleRemovableNumerator form) := by
  refine differentiable_of_analyticAt_off_roots (liouvilleRemovableNumerator form) ?_ ?_
  · intro z hz
    have hEq : liouvilleRemovableNumerator form =ᶠ[nhds z]
        liouvilleRawNumerator form := by
      have hEval : ∀ᶠ w in nhds z, H.f.eval w ≠ 0 :=
        (Polynomial.continuous H.f).continuousAt.eventually_ne hz
      filter_upwards [hEval] with w hw
      exact liouvilleRemovableNumerator_of_eval_ne_zero form hw
    exact (liouvilleRawNumerator_analyticAt_of_eval_ne_zero form hz).congr hEq.symm
  · exact liouvilleRemovableNumerator_continuous form

/-! ## Part G: Polynomial growth bound at infinity

Using the infinity chart of `HyperellipticOdd`, we show
`‖liouvilleRemovableNumerator form z / z^n‖ ≤ R` for large `z`,
where `n = (H.f.natDegree - 1) / 2 - 1`.

The odd-degree curve has a single infinity point (unlike the even case
with two infinity sheets), which simplifies this argument.

**Key idea:** the form coefficient at infinity is bounded near `t = 0`
(holomorphicity). The chart transition from affine to infinity gives a
Jacobian factor that, combined with the `y`-factor in the numerator,
produces the growth bound. -/

/-- The removable numerator has polynomial growth of degree
at most `(H.f.natDegree - 1) / 2 - 1`. -/
theorem liouvilleRemovableNumerator_eventually_norm_div_pow_le
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ z : ℂ in Filter.cocompact ℂ,
        ‖liouvilleRemovableNumerator form z /
            z ^ ((H.f.natDegree - 1) / 2 - 1)‖ ≤ R := by
  sorry

/-! ## Part H: Readout — recover form coefficient from removable numerator

On every smooth-Y projX chart target, the form coefficient equals
the removable numerator divided by the local square root `y`. -/

/-- On smooth-Y chart targets, the form coefficient is the removable
numerator divided by the local `y`-function. -/
theorem liouvilleRemovableNumerator_readout
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z =
      liouvilleRemovableNumerator form z /
        (squareLocalHomeomorph (H := H) a haY).symm (H.f.eval z) := by
  sorry

/-! ## Part I: Main representation theorem

Every holomorphic 1-form on `HyperellipticOdd H` equals
`hyperellipticOddForm H g` for a polynomial `g` of bounded degree. -/

/-- **Level 3 for odd-degree curves.** Every holomorphic 1-form is a
canonical hyperelliptic form `hyperellipticOddForm H g`.

**Proof sketch (to be filled once Parts A–H are discharged):**
1. `liouvilleRemovableNumerator_eventually_norm_div_pow_le` (Part G)
   → growth bound on the removable numerator
2. `polynomial_growth_bound_of_eventually_norm_div_pow_le`
   → converts cocompact ratio bound to polynomial growth bound
3. `differentiable_eq_polynomial_of_growth` (from `EntireGrowth.lean`)
   → extracts polynomial `g` with `g.natDegree ≤ (d-1)/2 - 1`
4. Degree arithmetic: `≤ (d-1)/2 - 1` implies `< (d-1)/2`
5. Form equality via readout (Part H) + chart coverage -/
theorem AX_HyperellipticOddOneForm_eq_form_proof
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∃ g : Polynomial ℂ, g.natDegree < (H.f.natDegree - 1) / 2 ∧
      form = hyperellipticOddForm H g := by
  sorry

end Jacobians.Extensions.HyperellipticOdd

