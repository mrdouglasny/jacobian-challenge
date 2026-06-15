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
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target)
    (hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z) ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source) :
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
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target)
    (hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z) ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z * a.val.2 =
      form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z *
        a.invol.val.2 := by
  rw [form_coeff_anti_invariance form a haY hz hy_src]
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

/-- Helper lemma: local chart coefficients on smooth-Y are independent of center. -/
theorem coeff_eq_of_projX_symm
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z =
      form.coeff (coe ((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H) : HyperellipticOdd H Fact.out) z := by
  let p : HyperellipticAffine H := (affineChartProjX (H := H) a hpY).symm z
  have hz_ext : z ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
      Set.range_id, Set.inter_univ]
    change z ∈ (affineLiftChart a).target
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    change z ∈ (HyperellipticAffine.affineChartAt a).target
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a hpY]
    exact hz
  have hp_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z = coe p := by
    have h_symm : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) = (chartAt ℂ (coe a : HyperellipticOdd H Fact.out)).toPartialEquiv := by simp
    rw [h_symm]
    change (affineLiftChart a).symm z = coe p
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
    change coe ((HyperellipticAffine.affineChartAt a).symm z) = coe p
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a hpY]
  have hp_val_1 : p.val.1 = z := by
    exact affineChartProjX_symm_apply_fst a hpY hz
  have hpYp : p ∈ smoothLocusY H := by
    show p.val.2 ≠ 0
    have h_snd := affineChartProjX_symm_apply_snd a hpY hz
    rw [h_snd]
    exact HyperellipticAffine.squareLocalHomeomorph_symm_ne_zero a hpY hz
  have hy_src_p : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).source := by
    rw [hp_eq]
    exact mem_extChartAt_source (coe p)
  have hp_coord : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) (coe p) = z := by
    have h_symm : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) = (chartAt ℂ (coe p : HyperellipticOdd H Fact.out)).toPartialEquiv := by simp
    rw [h_symm]
    change (affineLiftChart p) (coe p) = z
    unfold affineLiftChart
    change ((ChartedSpace.chartAt p).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some p) = z
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    change (HyperellipticAffine.affineChartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) p = z
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY p hpYp]
    exact hp_val_1
  have h_eq_on : ⇑(extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) ∘
      ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm =ᶠ[nhds z]
      (fun w => w) := by
    have h_cont_symm : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z :=
      (continuousOn_extChartAt_symm (coe a : HyperellipticOdd H Fact.out)).continuousAt (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz_ext)
    have h_open_source : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).source :=
      isOpen_extChartAt_source _
    have h_pre2 : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).source ∈ nhds z :=
      h_cont_symm.preimage_mem_nhds (h_open_source.mem_nhds hy_src_p)
    have h_nhds : ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target ∩
        (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).source) ∈ nhds z :=
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
    have h_LHS : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w) = q_w.val.1 := by
      rw [← hq_w_eq]
      change ((HyperellipticAffine.affineChartAt p).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w) = q_w.val.1
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY p hpYp]
      rfl
    have h_RHS : w = q_w.val.1 := by
      have h_w_eq : w = (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w) := by
        rw [PartialEquiv.right_inv _ hw_target]
      rw [h_w_eq, ← hq_w_eq]
      change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w) = q_w.val.1
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a hpY]
      rfl
    rw [h_LHS, h_RHS]
  have h_fderiv : fderiv ℂ
      (⇑(extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) ∘
       ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm) z =
      fderiv ℂ (fun w => w) z :=
    h_eq_on.fderiv_eq
  have h_fderiv_id : (fderiv ℂ (fun w : ℂ => w) z) 1 = 1 := by
    have h_fderiv_at : HasFDerivAt (fun w : ℂ => w) (ContinuousLinearMap.id ℂ ℂ) z := by
      exact (ContinuousLinearMap.id ℂ ℂ).hasFDerivAt
    rw [h_fderiv_at.fderiv]
    rfl
  have hRel := form.2.2.1 (coe a) (coe p) z hz_ext hy_src_p
  rw [hp_eq, hp_coord, h_fderiv, h_fderiv_id, mul_one] at hRel
  exact hRel

/-- The raw numerator is analytic at every `z₀` where `f(z₀) ≠ 0`. -/
theorem liouvilleRawNumerator_analyticAt_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ (liouvilleRawNumerator form) z₀ := by
  classical
  let a₀ := liouvilleChosenAffinePoint (H := H) z₀
  have ha₀Y : a₀ ∈ smoothLocusY H := by
    simpa [a₀] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀
  let e₀ := affineChartProjX (H := H) a₀ ha₀Y
  have ha₀Src : a₀ ∈ e₀.source := by
    simpa [e₀] using affineChartProjX_mem_source (H := H) a₀ ha₀Y
  have hz₀Target : z₀ ∈ e₀.target := by
    have h := e₀.map_source ha₀Src
    simpa [e₀, a₀] using h
  have hSymm₀ : e₀.symm z₀ = a₀ := by
    have hMap : e₀ a₀ = a₀.val.1 := by rfl
    rw [show z₀ = a₀.val.1 by simp [a₀], ← hMap]
    exact e₀.left_inv ha₀Src
  have hEval : ∀ᶠ w in nhds z₀, H.f.eval w ≠ 0 :=
    (Polynomial.continuous H.f).continuousAt.eventually_ne hz₀
  have hAnaAff : AnalyticAt ℂ (fun z => form.coeff (coe a₀ : HyperellipticOdd H Fact.out) z) z₀ := by
    have hz₀_ext : z₀ ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).target := by
      rw [extChartAt_target]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
        Set.range_id, Set.inter_univ]
      change z₀ ∈ (affineLiftChart a₀).target
      unfold affineLiftChart
      rw [OpenPartialHomeomorph.lift_openEmbedding_target]
      change z₀ ∈ (HyperellipticAffine.affineChartAt a₀).target
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a₀ ha₀Y]
      exact hz₀Target
    have h_open : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).target := isOpen_extChartAt_target _
    exact (form.2.1 (coe a₀ : HyperellipticOdd H Fact.out)).analyticAt (h_open.mem_nhds hz₀_ext)
  have hAnaY : AnalyticAt ℂ
      (fun z : ℂ =>
        (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z)) z₀ := by
    exact AnalyticOn.analyticAt (e₀.open_target.mem_nhds hz₀Target)
      (by
        simpa [e₀] using
          squareLocalHomeomorph_symm_eval_analyticOn (H := H) a₀ ha₀Y)
  have hModelAna : AnalyticAt ℂ
      (fun z : ℂ =>
        form.coeff (coe a₀ : HyperellipticOdd H Fact.out) z *
          (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z)) z₀ :=
    hAnaAff.mul hAnaY
  have hEq : liouvilleRawNumerator form =ᶠ[nhds z₀]
      fun z : ℂ =>
        form.coeff (coe a₀ : HyperellipticOdd H Fact.out) z *
          (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z) := by
    filter_upwards [e₀.open_target.mem_nhds hz₀Target, hEval] with w hw h_ev_nz
    let p : HyperellipticAffine H := e₀.symm w
    have hp_val_1 : p.val.1 = w := by
      exact affineChartProjX_symm_apply_fst a₀ ha₀Y hw
    have hpYp : p ∈ smoothLocusY H := by
      show p.val.2 ≠ 0
      have hp_snd := affineChartProjX_symm_apply_snd a₀ ha₀Y hw
      rw [hp_snd]
      exact HyperellipticAffine.squareLocalHomeomorph_symm_ne_zero a₀ ha₀Y hw
    let ach := liouvilleChosenAffinePoint (H := H) w
    have hSq_eq : ach.val.2 ^ 2 = p.val.2 ^ 2 := by
      have h1 := liouvilleChosenAffinePoint_snd_sq (H := H) w
      have h2 : p.val.2 ^ 2 = H.f.eval w := by
        have hprop := p.property
        rw [hp_val_1] at hprop
        exact hprop
      rw [h1, h2]
    rcases eq_or_eq_neg_of_sq_eq_sq ach.val.2 p.val.2 hSq_eq with hSame | hOpp
    · have ha_eq : ach = p := by
        apply Subtype.ext
        apply Prod.ext
        · change w = p.val.1
          exact hp_val_1.symm
        · exact hSame
      unfold liouvilleRawNumerator
      change form.coeff (coe ach : HyperellipticOdd H Fact.out) w * ach.val.2 =
        form.coeff (coe a₀ : HyperellipticOdd H Fact.out) w *
          (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval w)
      rw [ha_eq]
      have hCoeffEq := coeff_eq_of_projX_symm form a₀ ha₀Y hw
      rw [hCoeffEq]
      have hp_snd := affineChartProjX_symm_apply_snd a₀ ha₀Y hw
      rw [← hp_snd]
    · have ha_eq : ach = p.invol := by
        apply Subtype.ext
        apply Prod.ext
        · change w = p.val.1
          exact hp_val_1.symm
        · exact hOpp
      unfold liouvilleRawNumerator
      change form.coeff (coe ach : HyperellipticOdd H Fact.out) w * ach.val.2 =
        form.coeff (coe a₀ : HyperellipticOdd H Fact.out) w *
          (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval w)
      rw [ha_eq]
      change form.coeff (coe p.invol : HyperellipticOdd H Fact.out) w * (-p.val.2) = _
      have hw_p : w ∈ (affineChartProjX p hpYp).target := by
        have hpSrc : p ∈ (affineChartProjX p hpYp).source :=
          affineChartProjX_mem_source p hpYp
        have h_img := OpenPartialHomeomorph.map_source (affineChartProjX p hpYp) hpSrc
        change p.val.1 ∈ _ at h_img
        rwa [hp_val_1] at h_img
      have hy_src_p : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).symm w) ∈
          (extChartAt 𝓘(ℂ, ℂ) (coe p.invol : HyperellipticOdd H Fact.out)).source := by
        have hw_ext : w ∈ (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).target := by
          rw [extChartAt_target]
          simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
            Set.range_id, Set.inter_univ]
          change w ∈ (affineLiftChart p).target
          unfold affineLiftChart
          rw [OpenPartialHomeomorph.lift_openEmbedding_target]
          change w ∈ (HyperellipticAffine.affineChartAt p).target
          rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY p hpYp]
          exact hw_p
        have h_symm_eq : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).symm w = coe p := by
          have h_symm : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) = (chartAt ℂ (coe p : HyperellipticOdd H Fact.out)).toPartialEquiv := by simp
          rw [h_symm]
          change (affineLiftChart p).symm w = coe p
          unfold affineLiftChart
          rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
          change coe ((HyperellipticAffine.affineChartAt p).symm w) = coe p
          rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY p hpYp]
          have h_symm_apply : (affineChartProjX p hpYp).symm w = p := by
            have hpSrc : p ∈ (affineChartProjX p hpYp).source :=
              affineChartProjX_mem_source p hpYp
            have h_left := OpenPartialHomeomorph.left_inv (affineChartProjX p hpYp) hpSrc
            change (affineChartProjX p hpYp).symm p.val.1 = p at h_left
            rw [hp_val_1] at h_left
            exact h_left
          rw [h_symm_apply]
        rw [h_symm_eq]
        change coe p.invol ∈ (extChartAt 𝓘(ℂ, ℂ) (coe p.invol : HyperellipticOdd H Fact.out)).source
        exact mem_extChartAt_source (coe p.invol)
      have hanti := form_coeff_anti_invariance form p hpYp hw_p hy_src_p
      have hCoeffEq := coeff_eq_of_projX_symm form a₀ ha₀Y hw
      have h_neg : form.coeff (coe p.invol : HyperellipticOdd H Fact.out) w = -form.coeff (coe p : HyperellipticOdd H Fact.out) w := by
        rw [hanti]
        simp
      rw [h_neg]
      rw [show -form.coeff (coe p : HyperellipticOdd H Fact.out) w * -p.val.2 =
        form.coeff (coe p : HyperellipticOdd H Fact.out) w * p.val.2 by ring]
      rw [hCoeffEq]
      have hp_snd := affineChartProjX_symm_apply_snd a₀ ha₀Y hw
      rw [← hp_snd]
  exact hModelAna.congr hEq.symm

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
  classical
  let p := liouvilleBranchPoint z₀ hz₀
  let hpX := liouvilleBranchPoint_mem_smoothLocusX (H := H) hz₀
  let hpYn := liouvilleBranchPoint_not_mem_smoothLocusY (H := H) hz₀
  let N : ℂ → ℂ := fun w =>
    form.coeff (coe p : HyperellipticOdd H Fact.out) w *
      (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2)) / 2)
  refine ⟨N 0, ?_⟩
  have hform : AnalyticOn ℂ (form.coeff (coe p : HyperellipticOdd H Fact.out)) (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).target :=
    form.2.1 (coe p : HyperellipticOdd H Fact.out)
  have hExt : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).target = (affineChartProjY (H := H) p hpX).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
      Set.range_id, Set.inter_univ]
    change (affineLiftChart p).target = _
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    change (HyperellipticAffine.affineChartAt p).target = _
    rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn]
  rw [hExt] at hform
  have hAna : AnalyticOn ℂ N (affineChartProjY (H := H) p hpX).target := by
    exact hform.mul (polynomialLocalHomeomorph_symm_sq_derivative_div_two_analyticOn (H := H) p hpX)
  have h0target : (0 : ℂ) ∈ (affineChartProjY (H := H) p hpX).target := by
    have hsrc : p ∈ (affineChartProjY (H := H) p hpX).source :=
      affineChartProjY_mem_source p hpX
    have htarget := (affineChartProjY (H := H) p hpX).map_source hsrc
    simpa [p, liouvilleBranchPoint] using htarget
  have hNcont : ContinuousAt N 0 := by
    have hAnaAt : AnalyticAt ℂ N 0 := AnalyticOn.analyticAt ((affineChartProjY (H := H) p hpX).open_target.mem_nhds h0target) hAna
    exact hAnaAt.continuousAt
  have hyTendsto : Filter.Tendsto
      (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) :=
    (liouvilleChosenAffinePoint_snd_tendsto_zero (H := H) hz₀).mono_left
      nhdsWithin_le_nhds
  have hModel : Filter.Tendsto
      (fun z : ℂ => N (liouvilleChosenAffinePoint (H := H) z).val.2)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds (N 0)) :=
    hNcont.tendsto.comp hyTendsto
  have hEq : liouvilleRawNumerator form =ᶠ[nhdsWithin z₀ {z₀}ᶜ]
      fun z : ℂ => N (liouvilleChosenAffinePoint (H := H) z).val.2 := by
    let e := polynomialLocalHomeomorph (H := H) p hpX
    have hz₀Src : z₀ ∈ e.source := by
      simpa [e, p, liouvilleBranchPoint] using
        polynomialLocalHomeomorph_mem_source (H := H) p hpX
    have hSrcEv : ∀ᶠ z in nhds z₀, z ∈ e.source :=
      e.open_source.mem_nhds hz₀Src
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hSrcEv,
      eventually_eval_ne_zero_nhdsWithin (H := H) z₀] with z hzSrc hzNZ
    let y := (liouvilleChosenAffinePoint (H := H) z).val.2
    have hySq : y ^ 2 = H.f.eval z := by
      simpa [y] using liouvilleChosenAffinePoint_snd_sq (H := H) z
    have hyNZ : y ≠ 0 := by
      intro hy0
      apply hzNZ
      simpa [hy0] using hySq.symm
    have hyTarget : y ∈ (affineChartProjY (H := H) p hpX).target := by
      have hmap : H.f.eval z ∈ e.target := by
        have heq : (e : ℂ → ℂ) z = H.f.eval z := by
          simp [e, polynomialLocalHomeomorph]
        simpa [heq] using e.map_source hzSrc
      change y ^ 2 ∈ e.target
      rwa [hySq]
    let a : HyperellipticAffine H := (affineChartProjY (H := H) p hpX).symm y
    have hfst := affineChartProjY_symm_apply_fst (H := H) p hpX hyTarget
    have hxSymm : a = liouvilleChosenAffinePoint (H := H) z := by
      apply Subtype.ext
      apply Prod.ext
      · have hleft : e.symm (H.f.eval z) = z := by
          have hleft' := e.left_inv hzSrc
          have heq : (e : ℂ → ℂ) z = H.f.eval z := by
            simp [e, polynomialLocalHomeomorph]
          simpa [heq] using hleft'
        change a.val.1 = _
        rw [hfst, hySq, hleft]
        rfl
      · have hsnd := affineChartProjY_symm_apply_snd (H := H) p hpX hyTarget
        change a.val.2 = _
        rw [hsnd]
    have haY : a ∈ smoothLocusY H := by
      show a.val.2 ≠ 0
      have hsnd := affineChartProjY_symm_apply_snd (H := H) p hpX hyTarget
      simpa [a, hsnd] using hyNZ
    let qA := (coe a : HyperellipticOdd H Fact.out)
    let q := (coe p : HyperellipticOdd H Fact.out)
    let c := affineLiftChart (h := Fact.out) p
    let cA := affineLiftChart (h := Fact.out) a
    have hqASrc : qA ∈ cA.source := mem_affineLiftChart_source a
    have hBranchSymm : c.symm y = qA := by
      have h_symm : c.symm = (affineLiftChart (h := Fact.out) p).symm := rfl
      rw [h_symm]
      unfold affineLiftChart
      rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
      change coe ((HyperellipticAffine.affineChartAt p).symm y) = qA
      rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn]
    have hChQ : (chartAt ℂ q).toPartialEquiv = c.toPartialEquiv := rfl
    have hChQA : (chartAt ℂ qA).toPartialEquiv = cA.toPartialEquiv := rfl
    have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target = (affineChartProjY (H := H) p hpX).target := hExt
    have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticOdd H Fact.out) = (c.symm : ℂ → HyperellipticOdd H Fact.out) := by
      ext x
      rfl
    have hExtCoeA : ((extChartAt 𝓘(ℂ, ℂ) qA) : HyperellipticOdd H Fact.out → ℂ) = (cA : HyperellipticOdd H Fact.out → ℂ) := by
      ext x
      rfl
    have hExtSrcA : (extChartAt 𝓘(ℂ, ℂ) qA).source = cA.source := by
      have h_ext : (extChartAt 𝓘(ℂ, ℂ) qA) = (chartAt ℂ qA).toPartialEquiv := by simp
      rw [h_ext, hChQA]
    have hwExt : y ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
      rwa [hExtTarget]
    have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm y ∈ (extChartAt 𝓘(ℂ, ℂ) qA).source := by
      rw [hExtSymm, hExtSrcA, hBranchSymm]
      exact hqASrc
    have hCoord : (extChartAt 𝓘(ℂ, ℂ) qA) ((extChartAt 𝓘(ℂ, ℂ) q).symm y) = a.val.1 := by
      rw [hExtCoeA, hExtSymm, hBranchSymm]
      change (affineLiftChart (h := Fact.out) a) qA = a.val.1
      unfold affineLiftChart
      change ((ChartedSpace.chartAt a).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some a) = a.val.1
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      change (HyperellipticAffine.affineChartAt a : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) a = a.val.1
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a haY]
      rfl
    have hOverlap : y ∈ (c.symm.trans cA).source := by
      refine ⟨?_, ?_⟩
      · change y ∈ (HyperellipticAffine.affineChartAt p).target
        rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn]
        exact hyTarget
      · change c.symm y ∈ cA.source
        rw [hBranchSymm]
        exact hqASrc
    have hEqOn : (fun t : ℂ => cA (c.symm t)) =ᶠ[nhds y]
        (fun t : ℂ => (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)) := by
      refine Filter.eventually_of_mem ((c.symm.trans cA).open_source.mem_nhds hOverlap) ?_
      intro t ht
      have htTarget : t ∈ (affineChartProjY (H := H) p hpX).target := by
        have h_t_mem : t ∈ (HyperellipticAffine.affineChartAt p).target := ht.1
        rwa [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn] at h_t_mem
      change (c.symm.trans cA) t =
        (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)
      change (((affineChartAt (H := H) p).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe)).symm.trans
          ((affineChartAt (H := H) a).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe))) t =
        (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
      rw [affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn]
      rw [affineChartAt_of_mem_smoothLocusY (H := H) a haY]
      change (((affineChartProjY (H := H) p hpX).symm t :
        HyperellipticAffine H).val.1) =
        (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)
      exact affineChartProjY_symm_apply_fst (H := H) p hpX htTarget
    have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) qA) ∘ (extChartAt 𝓘(ℂ, ℂ) q).symm) y 1 =
        2 * y / H.f.derivative.eval a.val.1 := by
      rw [hExtCoeA, hExtSymm]
      change fderiv ℂ (fun t : ℂ => cA (c.symm t)) y 1 =
        2 * y / H.f.derivative.eval a.val.1
      rw [Filter.EventuallyEq.fderiv_eq hEqOn]
      have htrans :=
        affineChartProjY_to_projX_transition_hasDerivAt (H := H) p hpX hyTarget
      change deriv (fun t : ℂ =>
        (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)) y =
        2 * y / H.f.derivative.eval a.val.1
      rw [htrans.deriv]
      rw [← hfst]
    have hRel := form.2.2.1 q qA y hwExt hSrcExt
    rw [hCoord] at hRel
    rw [hDeriv] at hRel
    have h_a_val_1 : a.val.1 = z := by
      have hleft' := e.left_inv hzSrc
      have heq : (e : ℂ → ℂ) z = H.f.eval z := by
        simp [e, polynomialLocalHomeomorph]
      have h_symm_apply := affineChartProjY_symm_apply_fst (H := H) p hpX hyTarget
      rw [h_symm_apply]
      rw [heq] at hleft'
      rw [← hySq] at hleft'
      exact hleft'
    have h_a_val_2 : a.val.2 = y := by
      rw [hxSymm]
    have hRel' : form.coeff q y = form.coeff qA z * (2 * y / H.f.derivative.eval z) := by
      rw [h_a_val_1] at hRel
      exact hRel
    unfold liouvilleRawNumerator
    change form.coeff (coe (liouvilleChosenAffinePoint (H := H) z) : HyperellipticOdd H Fact.out) z * (liouvilleChosenAffinePoint (H := H) z).val.2 = N (liouvilleChosenAffinePoint (H := H) z).val.2
    rw [← hxSymm]
    rw [h_a_val_2]
    unfold N
    have h_symm_apply := affineChartProjY_symm_apply_fst (H := H) p hpX hyTarget
    rw [h_symm_apply] at h_a_val_1
    rw [h_a_val_1]
    rw [hRel']
    have hDerivNe : H.f.derivative.eval z ≠ 0 := by
      have hFne := polynomialLocalHomeomorph_symm_eval_derivative_ne_zero (H := H) p hpX hyTarget
      rw [h_a_val_1] at hFne
      exact hFne
    have hyNZ' : y ≠ 0 := hyNZ
    field_simp
    ring
  exact hModel.congr' hEq.symm

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
  refine differentiable_of_analyticAt_off_roots (H := H) (liouvilleRemovableNumerator form) ?_ ?_
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
  classical
  set y := (squareLocalHomeomorph (H := H) a haY).symm (H.f.eval z) with hy_def
  let p : HyperellipticAffine H := (affineChartProjX (H := H) a haY).symm z
  have hp_source : p ∈ (affineChartProjX (H := H) a haY).source := by
    simpa [p] using (affineChartProjX (H := H) a haY).map_target hz
  have hp_fst : p.val.1 = z := by
    simpa [p] using affineChartProjX_symm_apply_fst (H := H) a haY hz
  have hp_snd : p.val.2 = y := by
    simpa [p, y, hy_def] using affineChartProjX_symm_apply_snd (H := H) a haY hz
  have hy_ne : y ≠ 0 := by
    simpa [y] using squareLocalHomeomorph_symm_ne_zero (H := H) a haY hz
  have hy_sq : y ^ 2 = H.f.eval z := by
    have hp := p.property
    simpa [hp_fst, hp_snd] using hp
  have hz_eval : H.f.eval z ≠ 0 := by
    intro hzero
    have hy_zero : y = 0 := sq_eq_zero_iff.mp (by simpa [hzero] using hy_sq)
    exact hy_ne hy_zero
  have hAff_a_p : form.coeff (coe a) z = form.coeff (coe p) z := by
    exact coeff_eq_of_projX_symm form a haY hz
  let ach := liouvilleChosenAffinePoint (H := H) z
  have hachY : ach ∈ smoothLocusY H := by
    simpa [ach] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz_eval
  have hach_sq : ach.val.2 ^ 2 = y ^ 2 := by
    rw [liouvilleChosenAffinePoint_snd_sq (H := H) z, hy_sq]
  have hRem : liouvilleRemovableNumerator form z =
      liouvilleRawNumerator form z :=
    liouvilleRemovableNumerator_of_eval_ne_zero form hz_eval
  have hNumerator : liouvilleRemovableNumerator form z =
      form.coeff (coe a) z * y := by
    rw [hRem]
    rcases eq_or_eq_neg_of_sq_eq_sq ach.val.2 y hach_sq with hsame | hneg
    · have hach_eq : ach = p := by
        apply Subtype.ext
        apply Prod.ext
        · simp [ach, p, hp_fst]
        · simpa [ach, hp_snd] using hsame
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) z = ach from rfl]
      rw [hach_eq]
      change form.coeff (coe p) z * p.val.2 = form.coeff (coe a) z * y
      rw [hp_snd, ← hAff_a_p]
    · have hach_eq : ach = p.invol := by
        apply Subtype.ext
        apply Prod.ext
        · simp [ach, p, hp_fst, HyperellipticAffine.invol]
        · simpa [ach, hp_snd, HyperellipticAffine.invol] using hneg
      have hpYp : p ∈ smoothLocusY H := by
        change p.val.2 ≠ 0
        rwa [hp_snd]
      have hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).symm z) ∈
          (extChartAt 𝓘(ℂ, ℂ) (coe p.invol : HyperellipticOdd H Fact.out)).source := by
        have h_symm_eq : ((extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).symm z : HyperellipticOdd H Fact.out) = coe p := by
          have h_symm : ((extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).symm : ℂ → HyperellipticOdd H Fact.out) = ((affineLiftChart p).symm : ℂ → HyperellipticOdd H Fact.out) := by
            ext x
            rfl
          rw [h_symm]
          change (affineLiftChart p).symm z = coe p
          unfold affineLiftChart
          rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
          change coe ((HyperellipticAffine.affineChartAt p).symm z) = coe p
          rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY p hpYp]
          have h_symm_apply : (affineChartProjX p hpYp).symm z = p := by
            have hpSrc : p ∈ (affineChartProjX p hpYp).source :=
              affineChartProjX_mem_source p hpYp
            have h_left := OpenPartialHomeomorph.left_inv (affineChartProjX p hpYp) hpSrc
            change (affineChartProjX p hpYp).symm p.val.1 = p at h_left
            rw [hp_fst] at h_left
            exact h_left
          rw [h_symm_apply]
        rw [h_symm_eq]
        change coe p.invol ∈ (extChartAt 𝓘(ℂ, ℂ) (coe p.invol : HyperellipticOdd H Fact.out)).source
        exact mem_extChartAt_source (coe p.invol)
      have hz_target : z ∈ (affineChartProjX p hpYp).target := by
        have hpSrc : p ∈ (affineChartProjX p hpYp).source :=
          affineChartProjX_mem_source p hpYp
        have hmap := (affineChartProjX p hpYp).map_source hpSrc
        have h_apply : (affineChartProjX p hpYp) p = z := by
          change p.val.1 = z
          exact hp_fst
        rwa [h_apply] at hmap
      have hsheet := liouvilleRawNumerator_sheet_invariant form p hpYp hz_target hy_src
      unfold liouvilleRawNumerator
      rw [show liouvilleChosenAffinePoint (H := H) z = ach from rfl]
      rw [hach_eq]
      change form.coeff (coe p.invol) z * p.invol.val.2 = form.coeff (coe a) z * y
      have hp_invol_snd : p.invol.val.2 = -y := by
        change -p.val.2 = -y
        rw [hp_snd]
      rw [hp_invol_snd]
      have hp_snd_y : p.val.2 = y := hp_snd
      have hsheet' : form.coeff (coe p) z * y = form.coeff (coe p.invol) z * -y := by
        have hsheet_raw := hsheet
        rw [hp_snd_y, hp_invol_snd] at hsheet_raw
        exact hsheet_raw
      rw [← hsheet']
      rw [← hAff_a_p]
  rw [hNumerator]
  field_simp [hy_ne]

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
theorem hyperellipticOddForm_coeff_projX_apply
    (g : Polynomial ℂ) (hDeg : g.natDegree < (H.f.natDegree - 1) / 2)
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX a hpY).target) :
    (hyperellipticOddForm H g).coeff (coe a : HyperellipticOdd H Fact.out) z =
      g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z) := by
  rw [hyperellipticOddForm_coeff_of_lt H hDeg]
  unfold hyperellipticOddCoeff
  change HyperellipticAffine.hyperellipticAffineCoeff g a z = _
  unfold HyperellipticAffine.hyperellipticAffineCoeff
  rw [dif_pos hpY]
  unfold affineProjXCoeff
  rw [if_pos hz]

theorem oneForm_eq_hyperellipticOddForm_of_eqOn_chartTarget
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (g : Polynomial ℂ)
    (hCoeff : ∀ q : HyperellipticOdd H Fact.out, ∀ z : ℂ,
      z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target →
        form.coeff q z = (hyperellipticOddForm H g).coeff q z) :
    form = hyperellipticOddForm H g := by
  apply HolomorphicOneForm.ext_of_coeff
  funext q z
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target
  · exact hCoeff q z hz
  · change (form : HyperellipticOdd H Fact.out → ℂ → ℂ) q z =
      (hyperellipticOddForm H g : HyperellipticOdd H Fact.out → ℂ → ℂ) q z
    rw [form.2.2.2 q z hz, (hyperellipticOddForm H g).2.2.2 q z hz]

theorem AX_HyperellipticOddOneForm_eq_form_proof
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∃ g : Polynomial ℂ, g.natDegree < (H.f.natDegree - 1) / 2 ∧
      form = hyperellipticOddForm H g := by
  classical
  obtain ⟨R, hR, hBound⟩ := liouvilleRemovableNumerator_eventually_norm_div_pow_le (H := H) form
  obtain ⟨C, hC⟩ :=
    Jacobians.Axioms.HyperellipticLiouville.polynomial_growth_bound_of_eventually_norm_div_pow_le
      (liouvilleRemovableNumerator form)
      ((H.f.natDegree - 1) / 2 - 1) R hR
      (liouvilleRemovableNumerator_differentiable form).continuous
      hBound
  obtain ⟨g, hgDeg, hgEval⟩ :=
    Jacobians.GeneralResults.differentiable_eq_polynomial_of_growth
      ((H.f.natDegree - 1) / 2 - 1)
      (liouvilleRemovableNumerator form)
      (liouvilleRemovableNumerator_differentiable form)
      C hC
  have hDeg : g.natDegree < (H.f.natDegree - 1) / 2 := by
    have h_deg_ge : 3 ≤ H.f.natDegree := H.h_degree
    omega
  refine ⟨g, hDeg, ?_⟩
  refine oneForm_eq_hyperellipticOddForm_of_eqOn_chartTarget form g ?_
  intro q z hz
  rcases q with _ | a
  · sorry
  · by_cases hpY : a ∈ smoothLocusY H
    · have hExt : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target =
          (affineChartProjX a hpY).target := by
        rw [extChartAt_target]
        simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
          Set.range_id, Set.inter_univ]
        rw [chartAt_coe a]
        unfold affineLiftChart
        rw [OpenPartialHomeomorph.lift_openEmbedding_target]
        change (HyperellipticAffine.affineChartAt a : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target = (affineChartProjX a hpY).target
        rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a hpY]
      have hzX : z ∈ (affineChartProjX a hpY).target := by
        rwa [← hExt]
      have hFormCoeff : form.coeff (coe a) z = g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z) := by
        rw [← hgEval z]
        exact liouvilleRemovableNumerator_readout form a hpY hzX
      have hCanCoeff : (hyperellipticOddForm H g).coeff (coe a) z = g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z) := by
        exact hyperellipticOddForm_coeff_projX_apply g hDeg a hpY hzX
      change form.coeff (coe a) z = (hyperellipticOddForm H g).coeff (coe a) z
      rw [hFormCoeff, hCanCoeff]
    · sorry

end Jacobians.Extensions.HyperellipticOdd

