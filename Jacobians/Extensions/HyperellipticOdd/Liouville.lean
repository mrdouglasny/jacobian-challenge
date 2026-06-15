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
import Jacobians.ProjectiveCurve.Hyperelliptic.InvolutionOdd
import Jacobians.Axioms.HyperellipticLiouville
import Jacobians.ProjectiveCurve.Hyperelliptic.LiouvilleSupport
import Jacobians.GeneralResults.EntireGrowth
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Jacobians.Axioms.AbelJacobiMap
import Jacobians.Extensions.InvolutionPullback


namespace Jacobians.Extensions.HyperellipticOdd

open scoped Manifold ContDiff Topology
open Jacobians
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticOdd
open Jacobians.Axioms

variable {H : HyperellipticData} [Fact (Odd H.f.natDegree)]

noncomputable local instance (H' : HyperellipticData) [Fact (Odd H'.f.natDegree)] :
    ChartedSpace ℂ (OnePoint (HyperellipticAffine H')) :=
  show ChartedSpace ℂ (OnePoint (HyperellipticAffine H')) from @instChartedSpace H' Fact.out

noncomputable local instance (H' : HyperellipticData) [Fact (Odd H'.f.natDegree)] :
    IsManifold 𝓘(ℂ, ℂ) ω (OnePoint (HyperellipticAffine H')) :=
  show IsManifold 𝓘(ℂ, ℂ) ω (OnePoint (HyperellipticAffine H')) from @instIsManifold H' Fact.out

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

@[simp] theorem liouvilleTwoSheetSum_of_eval_eq_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z : ℂ} (hz : H.f.eval z = 0) :
    liouvilleTwoSheetSum form z = 0 := by
  simp [liouvilleTwoSheetSum, hz]

/-- Helper lemma: local chart coefficients on smooth-Y are independent of center. -/
theorem coeff_eq_of_projX_symm
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z =
      form.coeff (coe ((affineChartProjX (H :=
        H) a hpY).symm z : HyperellipticAffine H) : HyperellipticOdd H Fact.out) z := by
  let p : HyperellipticAffine H := (affineChartProjX (H := H) a hpY).symm z
  have hz_ext : z ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ]
    change z ∈ (affineLiftChart a).target
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    change z ∈ (HyperellipticAffine.affineChartAt a).target
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a hpY]
    exact hz
  have hp_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z = coe p := by
    have h_symm : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) =
      (chartAt ℂ (coe a : HyperellipticOdd H Fact.out)).toPartialEquiv := by simp
    rw [h_symm]
    change (affineLiftChart a).symm z = coe p
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
    change coe ((HyperellipticAffine.affineChartAt a).symm z) = coe p
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a hpY]
  have hp_val_1 : p.val.1 = z := by
    exact affineChartProjX_symm_apply_fst a hpY hz
  have hpYp : p ∈ smoothLocusY H := by
    change p.val.2 ≠ 0
    have h_snd := affineChartProjX_symm_apply_snd a hpY hz
    rw [h_snd]
    exact HyperellipticAffine.squareLocalHomeomorph_symm_ne_zero a hpY hz
  have hy_src_p : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).source := by
    rw [hp_eq]
    exact mem_extChartAt_source (coe p)
  have hp_coord : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) (coe p) = z := by
    have h_symm : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) =
      (chartAt ℂ (coe p : HyperellipticOdd H Fact.out)).toPartialEquiv := by simp
    rw [h_symm]
    change (affineLiftChart p) (coe p) = z
    unfold affineLiftChart
    change ((ChartedSpace.chartAt p).lift_openEmbedding OnePoint.isOpenEmbedding_coe)
      (OnePoint.some p) = z
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    change (HyperellipticAffine.affineChartAt p : OpenPartialHomeomorph (HyperellipticAffine
      H) ℂ) p = z
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY p hpYp]
    exact hp_val_1
  have h_eq_on : ⇑(extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) ∘
      ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm =ᶠ[nhds z]
      (fun w => w) := by
    have h_cont_symm : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H
      Fact.out)).symm z :=
      (continuousOn_extChartAt_symm (coe a : HyperellipticOdd H Fact.out)).continuousAt
          (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz_ext)
    have h_open_source : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).source :=
      isOpen_extChartAt_source _
    have h_pre2 : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹'
      (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).source ∈ nhds z :=
      h_cont_symm.preimage_mem_nhds (h_open_source.mem_nhds hy_src_p)
    have h_nhds : ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target ∩
        (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹' (extChartAt 𝓘(ℂ,
          ℂ) (coe p : HyperellipticOdd H Fact.out)).source) ∈ nhds z :=
      Filter.inter_mem (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz_ext) h_pre2
    filter_upwards [h_nhds] with w hw
    obtain ⟨hw_target, hw_src⟩ := hw
    simp only [Function.comp_apply]
    have hp_w_src : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source :=
      PartialEquiv.map_target _ hw_target
    rw [extChartAt_source] at hp_w_src
    change _ ∈ (affineLiftChart a).source at hp_w_src
    rw [affineLiftChart_source] at hp_w_src
    rcases hp_w_src with ⟨q_w, hq_w_src, hq_w_eq⟩
    have h_LHS : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ,
      ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w) = q_w.val.1 := by
      rw [← hq_w_eq]
      change ((HyperellipticAffine.affineChartAt p).lift_openEmbedding
        OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w) = q_w.val.1
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY p hpYp]
      rfl
    have h_RHS : w = q_w.val.1 := by
      have h_w_eq : w =
        (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ, ℂ) (coe a
          : HyperellipticOdd H Fact.out)).symm w) := by
        rw [PartialEquiv.right_inv _ hw_target]
      rw [h_w_eq, ← hq_w_eq]
      change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding
        OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w) = q_w.val.1
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

theorem coeff_eq_liouvilleProjYNumerator_div_of_branch
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (p : HyperellipticAffine H) (hpX : p ∈ smoothLocusX H)
    (hpYn : p ∉ smoothLocusY H)
    {w : ℂ}
    (hw : w ∈ (HyperellipticAffine.affineChartProjY (H := H) p hpX).target)
    (hwne : w ≠ 0) :
    let a : HyperellipticAffine H := (HyperellipticAffine.affineChartProjY (H := H) p hpX).symm w
    form.coeff (coe a : HyperellipticOdd H Fact.out) a.val.1 =
      (form.coeff (coe p : HyperellipticOdd H Fact.out) w *
        (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2)) / 2)) / w := by
  classical
  intro a
  let q : HyperellipticOdd H Fact.out := coe p
  let qA : HyperellipticOdd H Fact.out := coe a
  let c := affineLiftChart (h := Fact.out) p
  let cA := affineLiftChart (h := Fact.out) a
  have hpX_eq : hpX = mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpYn) := rfl
  have hw_new : w ∈ (HyperellipticAffine.affineChartProjY (H := H) p (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpYn))).target := by
    rw [← hpX_eq]; exact hw
  have haY : a ∈ smoothLocusY H := by
    show a.val.2 ≠ 0
    have hsnd := HyperellipticAffine.affineChartProjY_symm_apply_snd (H := H) p (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpYn)) hw_new
    simpa [a, hsnd] using hwne
  have haSrc : a ∈ (affineChartProjX (H := H) a haY).source :=
    affineChartProjX_mem_source (H := H) a haY
  have hqASrc : qA ∈ cA.source := by
    change (coe a : HyperellipticOdd H Fact.out) ∈ (affineLiftChart a).source
    rw [affineLiftChart_source]
    exact ⟨a, ChartedSpace.mem_chart_source a, rfl⟩
  have hBranchSymm : c.symm w = qA := by
    unfold c affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
    change coe ((HyperellipticAffine.affineChartAt p).symm w) = coe a
    rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn]
  have hChQ : (_root_.chartAt ℂ q :
      OpenPartialHomeomorph (HyperellipticOdd H Fact.out) ℂ) = c := by
    change (affineLiftChart p) = c; rfl
  have hChQA : (_root_.chartAt ℂ qA :
      OpenPartialHomeomorph (HyperellipticOdd H Fact.out) ℂ) = cA := by
    change (affineLiftChart a) = cA; rfl
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (HyperellipticAffine.affineChartProjY (H := H) p hpX).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id, Set.range_id, Set.inter_univ]
    rw [hChQ]
    change (affineLiftChart p).target = _
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    change (HyperellipticAffine.affineChartAt p).target = _
    rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn]
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticOdd H Fact.out) =
      (c.symm : ℂ → HyperellipticOdd H Fact.out) := by
    funext t
    change (_root_.chartAt ℂ q).symm t = c.symm t
    rw [hChQ]
  have hExtCoeA : ((extChartAt 𝓘(ℂ, ℂ) qA) : HyperellipticOdd H Fact.out → ℂ) =
      (cA : HyperellipticOdd H Fact.out → ℂ) := by
    funext t
    change (_root_.chartAt ℂ qA) t = cA t
    rw [hChQA]
  have hExtSrcA : (extChartAt 𝓘(ℂ, ℂ) qA).source = cA.source := by
    rw [extChartAt_source, hChQA]
  have hwExt : w ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
    rwa [hExtTarget]
  have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm w ∈
      (extChartAt 𝓘(ℂ, ℂ) qA).source := by
    rw [hExtSymm, hExtSrcA, hBranchSymm]
    exact hqASrc
  have hCoord : (extChartAt 𝓘(ℂ, ℂ) qA)
      ((extChartAt 𝓘(ℂ, ℂ) q).symm w) = a.val.1 := by
    rw [hExtCoeA, hExtSymm, hBranchSymm]
    change ((ChartedSpace.chartAt a).lift_openEmbedding OnePoint.isOpenEmbedding_coe) (OnePoint.some a) = a.val.1
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    change (HyperellipticAffine.affineChartAt a) a = a.val.1
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a haY]
    rfl
  have hOverlap : w ∈ (c.symm.trans cA).source := by
    refine ⟨?_, ?_⟩
    · change w ∈ (ChartedSpace.chartAt p).target
      change w ∈ (HyperellipticAffine.affineChartAt p).target
      rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn]
      rw [← hpX_eq]
      exact hw
    · change c.symm w ∈ cA.source
      rw [hBranchSymm]
      exact hqASrc
  have hEqOn : (fun t : ℂ => cA (c.symm t)) =ᶠ[𝓝 w]
      (fun t : ℂ => (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)) := by
    rw [hpX_eq]
    refine Filter.eventually_of_mem ((c.symm.trans cA).open_source.mem_nhds hOverlap) ?_
    intro t ht
    have htTarget : t ∈ (HyperellipticAffine.affineChartProjY (H := H) p (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpYn))).target := by
      have : t ∈ c.target := ht.1
      change t ∈ (ChartedSpace.chartAt p).target at this
      change t ∈ (HyperellipticAffine.affineChartAt p).target at this
      rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn] at this
      exact this
    change (c.symm.trans cA) t =
      (polynomialLocalHomeomorph (H := H) p (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpYn))).symm (t ^ 2)
    change (affineLiftChart p).symm.trans (affineLiftChart a) t = _
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
    change ((HyperellipticAffine.affineChartAt p).symm.trans (HyperellipticAffine.affineChartAt a)) t = _
    rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn]
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a haY]
    change ((HyperellipticAffine.affineChartProjY (H := H) p (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpYn))).symm t).val.1 = _
    exact HyperellipticAffine.affineChartProjY_symm_apply_fst (H := H) p (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpYn)) htTarget
  have hx_eq :
      a.val.1 = (polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2) := by
    simpa [a] using HyperellipticAffine.affineChartProjY_symm_apply_fst (H := H) p hpX hw
  have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) qA) ∘
        (extChartAt 𝓘(ℂ, ℂ) q).symm) w 1 =
      2 * w / H.f.derivative.eval a.val.1 := by
    rw [hExtCoeA, hExtSymm]
    change fderiv ℂ (fun t : ℂ => cA (c.symm t)) w 1 =
      2 * w / H.f.derivative.eval a.val.1
    rw [Filter.EventuallyEq.fderiv_eq hEqOn]
    have htrans :=
      HyperellipticAffine.affineChartProjY_to_projX_transition_hasDerivAt (H := H) p hpX hw
    have htrans_deriv := htrans.deriv
    rw [← hx_eq] at htrans_deriv
    rw [fderiv_apply_one_eq_deriv, htrans_deriv]
  have hCocy := form.2.2.1 q qA w hwExt hSrcExt
  have hFne :
      H.f.derivative.eval
        ((polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2)) ≠ 0 :=
    polynomialLocalHomeomorph_symm_eval_derivative_ne_zero (H := H) p hpX hw
  have hC :
      form.coeff q w =
        form.coeff qA a.val.1 *
          (2 * w / H.f.derivative.eval a.val.1) := by
    unfold HolomorphicOneForm.coeff
    rw [hCocy, hCoord, hDeriv]
  have hC' :
      form.coeff q w =
        form.coeff qA
            ((polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2)) *
          (2 * w /
            H.f.derivative.eval
              ((polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2))) := by
    simpa [hx_eq] using hC
  rw [hx_eq]
  rw [hC']
  field_simp [hwne, hFne]
  dsimp [qA]

theorem liouvilleTwoSheetSum_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleTwoSheetSum form z =
      form.coeff (coe (liouvilleChosenAffinePoint (H := H) z) :
        HyperellipticOdd H Fact.out) z +
      form.coeff (coe (liouvilleChosenAffinePoint (H := H) z).invol :
        HyperellipticOdd H Fact.out) z := by
  simp [liouvilleTwoSheetSum, hz]

theorem liouvilleChosenTwoSheetSum_analyticAt
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ
      (fun z : ℂ =>
        form.coeff (coe (liouvilleChosenAffinePoint (H := H) z₀) : HyperellipticOdd H Fact.out) z +
          form.coeff (coe (liouvilleChosenAffinePoint (H := H) z₀).invol : HyperellipticOdd H Fact.out) z)
      z₀ := by
  classical
  let a₀ := liouvilleChosenAffinePoint (H := H) z₀
  have ha₀Y : a₀ ∈ smoothLocusY H := by
    simpa [a₀] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀
  have ha₀σY : a₀.invol ∈ smoothLocusY H :=
    HyperellipticAffine.invol_mem_smoothLocusY a₀ ha₀Y
  have h1 : AnalyticAt ℂ (fun z => form.coeff (coe a₀ : HyperellipticOdd H Fact.out) z) z₀ := by
    have hz₀_ext : z₀ ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).target := by
      rw [extChartAt_target]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ]
      change z₀ ∈ (affineLiftChart a₀).target
      unfold affineLiftChart
      rw [OpenPartialHomeomorph.lift_openEmbedding_target]
      change z₀ ∈ (HyperellipticAffine.affineChartAt a₀).target
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a₀ ha₀Y]
      have hz₀_target : z₀ ∈ (affineChartProjX (H := H) a₀ ha₀Y).target := by
        have ha₀Src : a₀ ∈ (affineChartProjX (H := H) a₀ ha₀Y).source :=
          affineChartProjX_mem_source (H := H) a₀ ha₀Y
        have h := (affineChartProjX (H := H) a₀ ha₀Y).map_source ha₀Src
        simpa [a₀] using h
      exact hz₀_target
    have h_open : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).target :=
      isOpen_extChartAt_target _
    exact (form.2.1 (coe a₀ : HyperellipticOdd H Fact.out)).analyticAt (h_open.mem_nhds hz₀_ext)
  have h2 : AnalyticAt ℂ (fun z => form.coeff (coe a₀.invol : HyperellipticOdd H Fact.out) z) z₀ := by
    have hz₀_ext : z₀ ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a₀.invol : HyperellipticOdd H Fact.out)).target := by
      rw [extChartAt_target]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ]
      change z₀ ∈ (affineLiftChart a₀.invol).target
      unfold affineLiftChart
      rw [OpenPartialHomeomorph.lift_openEmbedding_target]
      change z₀ ∈ (HyperellipticAffine.affineChartAt a₀.invol).target
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a₀.invol ha₀σY]
      have hz₀_target : z₀ ∈ (affineChartProjX (H := H) a₀.invol ha₀σY).target := by
        have ha₀Src : a₀.invol ∈ (affineChartProjX (H := H) a₀.invol ha₀σY).source :=
          affineChartProjX_mem_source (H := H) a₀.invol ha₀σY
        have h := (affineChartProjX (H := H) a₀.invol ha₀σY).map_source ha₀Src
        have h_eq : (affineChartProjX (H := H) a₀.invol ha₀σY) a₀.invol = z₀ := by
          change a₀.invol.val.1 = z₀
          simp [a₀, HyperellipticAffine.invol]
        rwa [h_eq] at h
      exact hz₀_target
    have h_open : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe a₀.invol : HyperellipticOdd H Fact.out)).target :=
      isOpen_extChartAt_target _
    exact (form.2.1 (coe a₀.invol : HyperellipticOdd H Fact.out)).analyticAt (h_open.mem_nhds hz₀_ext)
  exact h1.add h2

theorem liouvilleTwoSheetSum_analyticAt_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ (liouvilleTwoSheetSum form) z₀ := by
  classical
  let a₀ := liouvilleChosenAffinePoint (H := H) z₀
  have ha₀Y : a₀ ∈ smoothLocusY H := by
    simpa [a₀] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀
  let a₀σ : HyperellipticAffine H := a₀.invol
  have ha₀σY : a₀σ ∈ smoothLocusY H := by
    simpa [a₀σ] using HyperellipticAffine.invol_mem_smoothLocusY a₀ ha₀Y
  let e₀ := affineChartProjX (H := H) a₀ ha₀Y
  let e₀σ := affineChartProjX (H := H) a₀σ ha₀σY
  have ha₀Src : a₀ ∈ e₀.source := by
    simpa [e₀] using affineChartProjX_mem_source (H := H) a₀ ha₀Y
  have hz₀Target : z₀ ∈ e₀.target := by
    have h := e₀.map_source ha₀Src
    simpa [e₀, a₀] using h
  have ha₀σSrc : a₀σ ∈ e₀σ.source := by
    simpa [e₀σ] using affineChartProjX_mem_source (H := H) a₀σ ha₀σY
  have hz₀σTarget : z₀ ∈ e₀σ.target := by
    have h := e₀σ.map_source ha₀σSrc
    simpa [e₀σ, a₀σ, a₀, HyperellipticAffine.invol] using h
  have hSymm₀ : e₀.symm z₀ = a₀ := by
    have hMap : e₀ a₀ = a₀.val.1 := rfl
    rw [show z₀ = a₀.val.1 by simp [a₀], ← hMap]
    exact e₀.left_inv ha₀Src
  have hSymm₀σ : e₀σ.symm z₀ = a₀σ := by
    have hMap : e₀σ a₀σ = a₀σ.val.1 := rfl
    rw [show z₀ = a₀σ.val.1 by simp [a₀σ, a₀, HyperellipticAffine.invol], ← hMap]
    exact e₀σ.left_inv ha₀σSrc
  have hProjCont₀ : ContinuousAt
      (fun z : ℂ =>
        (coe (e₀.symm z : HyperellipticAffine H) : HyperellipticOdd H Fact.out)) z₀ := by
    have h_coe_cont : Continuous (fun x : HyperellipticAffine H => (coe x : HyperellipticOdd H Fact.out)) :=
      OnePoint.continuous_coe
    have h_symm_cont : ContinuousAt e₀.symm z₀ := e₀.continuousAt_symm hz₀Target
    exact h_coe_cont.continuousAt.comp h_symm_cont
  have hProjCont₀σ : ContinuousAt
      (fun z : ℂ =>
        (coe (e₀σ.symm z : HyperellipticAffine H) : HyperellipticOdd H Fact.out)) z₀ := by
    have h_coe_cont : Continuous (fun x : HyperellipticAffine H => (coe x : HyperellipticOdd H Fact.out)) :=
      OnePoint.continuous_coe
    have h_symm_cont : ContinuousAt e₀σ.symm z₀ := e₀σ.continuousAt_symm hz₀σTarget
    exact h_coe_cont.continuousAt.comp h_symm_cont
  have hPref₀ : ∀ᶠ z in 𝓝 z₀,
      (coe (e₀.symm z : HyperellipticAffine H) : HyperellipticOdd H Fact.out) ∈
        (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).source := by
    have hqSrc : (coe a₀ : HyperellipticOdd H Fact.out) ∈
        (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).source :=
      mem_extChartAt_source _
    have hmem : (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).source ∈
        𝓝 (coe a₀ : HyperellipticOdd H Fact.out) :=
      IsOpen.mem_nhds (isOpen_extChartAt_source (coe a₀)) hqSrc
    exact hProjCont₀.eventually (by simpa [a₀, hSymm₀] using hmem)
  have hPref₀σ : ∀ᶠ z in 𝓝 z₀,
      (coe (e₀σ.symm z : HyperellipticAffine H) : HyperellipticOdd H Fact.out) ∈
        (extChartAt 𝓘(ℂ, ℂ) (coe a₀σ : HyperellipticOdd H Fact.out)).source := by
    have hqSrc : (coe a₀σ : HyperellipticOdd H Fact.out) ∈
        (extChartAt 𝓘(ℂ, ℂ) (coe a₀σ : HyperellipticOdd H Fact.out)).source :=
      mem_extChartAt_source _
    have hmem : (extChartAt 𝓘(ℂ, ℂ) (coe a₀σ : HyperellipticOdd H Fact.out)).source ∈
        𝓝 (coe a₀σ : HyperellipticOdd H Fact.out) :=
      IsOpen.mem_nhds (isOpen_extChartAt_source (coe a₀σ)) hqSrc
    exact hProjCont₀σ.eventually (by simpa [a₀σ, hSymm₀σ] using hmem)
  have hBranchPair : ∀ᶠ z in 𝓝 z₀,
      e₀σ.symm z = (e₀.symm z).invol := by
    have h :=
      affineChartProjX_invol_symm_eq_eventually (H := H) a₀ ha₀Y
    simpa [a₀σ, e₀, e₀σ] using h
  have hEval : ∀ᶠ z in 𝓝 z₀, H.f.eval z ≠ 0 :=
    (Polynomial.continuous H.f).continuousAt.eventually_ne hz₀
  have hEq : (fun z : ℂ =>
        form.coeff (coe a₀) z + form.coeff (coe a₀σ) z) =ᶠ[𝓝 z₀]
      liouvilleTwoSheetSum form := by
    filter_upwards [e₀.open_target.mem_nhds hz₀Target,
      e₀σ.open_target.mem_nhds hz₀σTarget, hPref₀, hPref₀σ, hBranchPair, hEval]
      with z hzT hzσT hSrcPref hSrcPrefσ hPair hzNZ
    let p₀ : HyperellipticAffine H := e₀.symm z
    let p₀σ : HyperellipticAffine H := e₀σ.symm z
    have hp₀σ_eq : p₀σ = p₀.invol := by
      simpa [p₀, p₀σ] using hPair
    have hFix₀ : form.coeff (coe a₀) z =
        form.coeff (coe p₀) z := by
      simpa [a₀, e₀, p₀] using
        coeff_eq_of_projX_symm form a₀ ha₀Y hzT
    have hFix₀σ : form.coeff (coe a₀σ) z =
        form.coeff (coe p₀.invol) z := by
      have h := coeff_eq_of_projX_symm form a₀σ ha₀σY hzσT
      simpa [a₀σ, e₀σ, p₀σ, hp₀σ_eq] using h
    let a := liouvilleChosenAffinePoint (H := H) z
    have haSq : a.val.2 ^ 2 = H.f.eval z := by
      simpa [a] using liouvilleChosenAffinePoint_snd_sq (H := H) z
    have hp₀Fst : p₀.val.1 = z := by
      simpa [p₀, e₀] using affineChartProjX_symm_apply_fst (H := H) a₀ ha₀Y hzT
    have hp₀Sq : p₀.val.2 ^ 2 = H.f.eval z := by
      have hprop := p₀.property
      rw [hp₀Fst] at hprop
      exact hprop
    have hSheets := eq_or_eq_neg_of_sq_eq_sq a.val.2 p₀.val.2 (haSq.trans hp₀Sq.symm)
    rw [liouvilleTwoSheetSum_of_eval_ne_zero form hzNZ]
    rcases hSheets with hSame | hOpp
    · have ha_eq : a = p₀ := by
        apply Subtype.ext
        apply Prod.ext
        · simp [a, p₀, hp₀Fst]
        · exact hSame
      rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl]
      rw [ha_eq, hFix₀, hFix₀σ]
    · have ha_eq : a = p₀.invol := by
        apply Subtype.ext
        apply Prod.ext
        · simp [a, p₀, hp₀Fst, HyperellipticAffine.invol]
        · simpa [HyperellipticAffine.invol] using hOpp
      rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl]
      rw [ha_eq, HyperellipticAffine.invol_invol, hFix₀, hFix₀σ]
      rw [add_comm]
  exact (liouvilleChosenTwoSheetSum_analyticAt form hz₀).congr
    (by simpa [a₀, a₀σ] using hEq)

theorem liouvilleTwoSheetSum_analyticAt_off_roots
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum form) z := by
  intro z hz
  exact liouvilleTwoSheetSum_analyticAt_of_eval_ne_zero form hz

theorem liouvilleTwoSheetSum_branch_tendsto
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ = 0) :
    ∃ L : ℂ, Filter.Tendsto (liouvilleTwoSheetSum form)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds L) := by
  classical
  let p := liouvilleBranchPoint z₀ hz₀
  let hpX := liouvilleBranchPoint_mem_smoothLocusX (H := H) hz₀
  let hpYn := liouvilleBranchPoint_not_mem_smoothLocusY (H := H) hz₀
  let N : ℂ → ℂ := fun w =>
    form.coeff (coe p : HyperellipticOdd H Fact.out) w *
      (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2)) / 2)
  let D : ℂ → ℂ := dslope (fun w : ℂ => N w - N (-w)) 0
  refine ⟨D 0, ?_⟩
  have hform : AnalyticOn ℂ (form.coeff (coe p : HyperellipticOdd H Fact.out)) (extChartAt
    𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).target :=
    form.2.1 (coe p : HyperellipticOdd H Fact.out)
  have hExt : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).target =
    (HyperellipticAffine.affineChartProjY (H := H) p hpX).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ]
    change (affineLiftChart p).target = _
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    change (HyperellipticAffine.affineChartAt p).target = _
    rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY p hpYn]
  rw [hExt] at hform
  have hAna : AnalyticOn ℂ N (HyperellipticAffine.affineChartProjY (H := H) p hpX).target := by
    exact hform.mul (polynomialLocalHomeomorph_symm_sq_derivative_div_two_analyticOn (H := H) p hpX)
  have h0target : (0 : ℂ) ∈ (HyperellipticAffine.affineChartProjY (H := H) p hpX).target := by
    have hsrc : p ∈ (HyperellipticAffine.affineChartProjY (H := H) p hpX).source :=
      affineChartProjY_mem_source p hpX
    have htarget := (HyperellipticAffine.affineChartProjY (H := H) p hpX).map_source hsrc
    simpa [p, liouvilleBranchPoint] using htarget
  have hDcont : ContinuousAt D 0 := by
    have hAnaAt : AnalyticAt ℂ N 0 := AnalyticOn.analyticAt
      ((HyperellipticAffine.affineChartProjY (H := H) p hpX).open_target.mem_nhds h0target) hAna
    exact (Jacobians.GeneralResults.analyticAt_dslope_oddPart hAnaAt).continuousAt
  have hyTendsto : Filter.Tendsto
      (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) :=
    (liouvilleChosenAffinePoint_snd_tendsto_zero (H := H) hz₀).mono_left
      nhdsWithin_le_nhds
  have hModel : Filter.Tendsto
      (fun z : ℂ => D (liouvilleChosenAffinePoint (H := H) z).val.2)
      (nhdsWithin z₀ {z₀}ᶜ) (nhds (D 0)) :=
    hDcont.tendsto.comp hyTendsto
  have hEq : liouvilleTwoSheetSum form =ᶠ[nhdsWithin z₀ {z₀}ᶜ]
      fun z : ℂ => D (liouvilleChosenAffinePoint (H := H) z).val.2 := by
    let e := polynomialLocalHomeomorph (H := H) p hpX
    have hz₀Src : z₀ ∈ e.source := by
      simpa [e, p, liouvilleBranchPoint] using
        polynomialLocalHomeomorph_mem_source (H := H) p hpX
    have hSrcEv : ∀ᶠ z in 𝓝 z₀, z ∈ e.source :=
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
    have hyTarget : y ∈ (HyperellipticAffine.affineChartProjY (H := H) p hpX).target := by
      have hmap : H.f.eval z ∈ e.target := by
        have heq : (e : ℂ → ℂ) z = H.f.eval z := by
          simp [e, polynomialLocalHomeomorph]
        simpa [heq] using e.map_source hzSrc
      change y ^ 2 ∈ e.target
      rwa [hySq]
    have hnegTarget : -y ∈ (HyperellipticAffine.affineChartProjY (H := H) p hpX).target := by
      have hy2Target : y ^ 2 ∈ e.target := by
        simpa [HyperellipticAffine.affineChartProjY, e] using hyTarget
      change (-y) ^ 2 ∈ e.target
      simpa [pow_two] using hy2Target
    have hxSymm : (HyperellipticAffine.affineChartProjY (H := H) p hpX).symm y =
        liouvilleChosenAffinePoint (H := H) z := by
      apply Subtype.ext
      apply Prod.ext
      · have hfst := HyperellipticAffine.affineChartProjY_symm_apply_fst (H := H) p hpX hyTarget
        have hleft : e.symm (H.f.eval z) = z := by
          have hleft' := e.left_inv hzSrc
          have heq : (e : ℂ → ℂ) z = H.f.eval z := by
            simp [e, polynomialLocalHomeomorph]
          simpa [heq] using hleft'
        change ((HyperellipticAffine.affineChartProjY (H := H) p hpX).symm y).val.1 = _
        rw [hfst, hySq, hleft]
        rfl
      · have hsnd := HyperellipticAffine.affineChartProjY_symm_apply_snd (H := H) p hpX hyTarget
        change ((HyperellipticAffine.affineChartProjY (H := H) p hpX).symm y).val.2 = _
        rw [hsnd]
    have hxNegSymm : (affineChartProjY (H := H) p hpX).symm (-y) =
        (liouvilleChosenAffinePoint (H := H) z).invol := by
      apply Subtype.ext
      apply Prod.ext
      · have hfst := affineChartProjY_symm_apply_fst (H := H) p hpX hnegTarget
        have hleft : e.symm (H.f.eval z) = z := by
          have hleft' := e.left_inv hzSrc
          have heq : (e : ℂ → ℂ) z = H.f.eval z := by
            simp [e, polynomialLocalHomeomorph]
          simpa [heq] using hleft'
        change ((affineChartProjY (H := H) p hpX).symm (-y)).val.1 = _
        have hnegSq : (-y) ^ 2 = H.f.eval z := by
          simpa [sq] using hySq
        rw [hfst, hnegSq, hleft]
        rfl
      · have hsnd := affineChartProjY_symm_apply_snd (H := H) p hpX hnegTarget
        change ((affineChartProjY (H := H) p hpX).symm (-y)).val.2 = _
        simpa [y, HyperellipticAffine.invol] using hsnd
    have hA :
        form.coeff (coe (liouvilleChosenAffinePoint (H := H) z) : HyperellipticOdd H Fact.out) z =
          N y / y := by
      have h := coeff_eq_liouvilleProjYNumerator_div_of_branch form p hpX hpYn hyTarget hyNZ
      simpa [N, y, hxSymm] using h
    have hσ :
        form.coeff (coe (liouvilleChosenAffinePoint (H := H) z).invol : HyperellipticOdd H Fact.out) z =
          N (-y) / (-y) := by
      have h := coeff_eq_liouvilleProjYNumerator_div_of_branch form p hpX hpYn hnegTarget (neg_ne_zero.mpr hyNZ)
      simpa [N, y, hxNegSymm] using h
    rw [liouvilleTwoSheetSum_of_eval_ne_zero form hzNZ, hA, hσ]
    have hD : D y = (N y - N (-y)) / y := by
      simpa [D] using Jacobians.GeneralResults.dslope_oddPart_of_ne (h := N) (w := y) hyNZ
    rw [hD]
    field_simp [hyNZ]
    ring
  exact hModel.congr' hEq.symm

theorem liouvilleTwoSheetSumRemovable_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleTwoSheetSumRemovable form z = liouvilleTwoSheetSum form z := by
  simp [liouvilleTwoSheetSumRemovable, hz]

theorem liouvilleTwoSheetSumRemovable_of_eval_eq_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z : ℂ} (hz : H.f.eval z = 0) :
    liouvilleTwoSheetSumRemovable form z =
      Filter.limUnder (nhdsWithin z {z}ᶜ) (liouvilleTwoSheetSum form) := by
  simp [liouvilleTwoSheetSumRemovable, hz]

theorem liouvilleTwoSheetSumRemovable_eventuallyEq_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleTwoSheetSumRemovable form =ᶠ[𝓝 z]
      liouvilleTwoSheetSum form := by
  have hEval : ∀ᶠ w in 𝓝 z, H.f.eval w ≠ 0 :=
    (Polynomial.continuous H.f).continuousAt.eventually_ne hz
  filter_upwards [hEval] with w hw
  exact liouvilleTwoSheetSumRemovable_of_eval_ne_zero form hw

theorem liouvilleTwoSheetSumRemovable_eventuallyEq_punctured
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (z : ℂ) :
    liouvilleTwoSheetSumRemovable form =ᶠ[𝓝[≠] z]
      liouvilleTwoSheetSum form := by
  filter_upwards [eventually_eval_ne_zero_nhdsWithin (H := H) z] with w hw
  exact liouvilleTwoSheetSumRemovable_of_eval_ne_zero form hw

theorem liouvilleTwoSheetSumRemovable_continuous_of_analyticAt_off_roots_and_branch_tendsto
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      ∃ L : ℂ, Filter.Tendsto (liouvilleTwoSheetSum form)
        (nhdsWithin z {z}ᶜ) (nhds L)) :
    Continuous (liouvilleTwoSheetSumRemovable form) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : H.f.eval z = 0
  · obtain ⟨L, hL⟩ := hBranch z hz
    rw [continuousAt_iff_punctured_nhds]
    rw [liouvilleTwoSheetSumRemovable_of_eval_eq_zero form hz]
    have hToLim : Filter.Tendsto (liouvilleTwoSheetSum form)
        (nhdsWithin z {z}ᶜ)
        (nhds (Filter.limUnder (nhdsWithin z {z}ᶜ) (liouvilleTwoSheetSum form))) :=
      tendsto_nhds_limUnder ⟨L, hL⟩
    exact hToLim.congr'
      (liouvilleTwoSheetSumRemovable_eventuallyEq_punctured form z).symm
  · exact (hAna z hz).continuousAt.congr
      (liouvilleTwoSheetSumRemovable_eventuallyEq_of_eval_ne_zero form hz).symm

theorem liouvilleTwoSheetSumRemovable_differentiable_of_analyticAt_off_roots_and_branch_tendsto
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      ∃ L : ℂ, Filter.Tendsto (liouvilleTwoSheetSum form)
        (nhdsWithin z {z}ᶜ) (nhds L)) :
    Differentiable ℂ (liouvilleTwoSheetSumRemovable form) := by
  refine differentiable_of_analyticAt_off_roots (H := H)
    (liouvilleTwoSheetSumRemovable form) ?_ ?_
  · intro z hz
    exact (hAna z hz).congr
      (liouvilleTwoSheetSumRemovable_eventuallyEq_of_eval_ne_zero form hz).symm
  · exact
      liouvilleTwoSheetSumRemovable_continuous_of_analyticAt_off_roots_and_branch_tendsto
        form hAna hBranch

theorem pullback_coeff_eq_invol
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target)
    (hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
      HyperellipticOdd H Fact.out)).symm z) ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source) :
    (pullbackOneForm (hyperellipticInvolution H Fact.out)
      (hyperellipticInvolution_contMDiff H Fact.out) form).coeff (coe a) z =
      form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z := by
  have hz_ext : z ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
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
  change (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z ∈
    (affineLiftChart a).source at h_src
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
  have hRel := pullbackOneForm_isPullbackCoeffRel
    (hyperellipticInvolution H Fact.out)
    (hyperellipticInvolution_contMDiff H Fact.out)
    form
  have h_eq := hRel (coe a) (coe a.invol) z hz_ext hy_src
  have h_z_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ,
    ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z) = z :=
    PartialEquiv.right_inv _ hz_ext
  have h_q_val_1 : q_aff.val.1 = z := by
    rw [← hq_eq] at h_z_eq
    change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding
      OnePoint.isOpenEmbedding_coe) (OnePoint.some q_aff) = z at h_z_eq
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply] at h_z_eq
    rw [affineChartAt_of_mem_smoothLocusY a haY] at h_z_eq
    exact h_z_eq
  have h_eval_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out))
    (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H
      Fact.out)).symm z)) = z := by
    have hw_eq : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
      HyperellipticOdd H Fact.out)).symm z) = coe q_aff.invol := by
      rw [← hq_eq]
      rfl
    rw [hw_eq]
    change ((HyperellipticAffine.affineChartAt a.invol).lift_openEmbedding
      OnePoint.isOpenEmbedding_coe) (OnePoint.some q_aff.invol) = z
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rw [affineChartAt_of_mem_smoothLocusY a.invol ha_invol_Y]
    change q_aff.invol.val.1 = z
    rw [HyperellipticAffine.invol_val]
    exact h_q_val_1
  have h_eq_on : ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)) ∘
      hyperellipticInvolution H Fact.out ∘
      ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm =ᶠ[nhds z]
      (fun w => w) := by
    have h_cont_symm : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H
      Fact.out)).symm z :=
      (continuousOn_extChartAt_symm (coe a : HyperellipticOdd H Fact.out)).continuousAt
        (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz_ext)
    have h_invol_cont : Continuous (hyperellipticInvolution H Fact.out) :=
      (hyperellipticInvolution_contMDiff H Fact.out).continuous
    have h_open_source : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H
      Fact.out)).source :=
      isOpen_extChartAt_source _
    have h_pre1 : IsOpen (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe
      a.invol : HyperellipticOdd H Fact.out)).source) :=
      h_open_source.preimage h_invol_cont
    have h_pre2 : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹'
      (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe a.invol :
        HyperellipticOdd H Fact.out)).source) ∈ nhds z :=
      h_cont_symm.preimage_mem_nhds (h_pre1.mem_nhds hy_src)
    have h_nhds : ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target ∩
        (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹'
          (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe a.invol :
            HyperellipticOdd H Fact.out)).source)) ∈ nhds z :=
      Filter.inter_mem (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz_ext) h_pre2
    filter_upwards [h_nhds] with w hw
    obtain ⟨hw_target, hw_src⟩ := hw
    simp only [Function.comp_apply]
    have hp_w_src : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source :=
      PartialEquiv.map_target _ hw_target
    rw [extChartAt_source] at hp_w_src
    change _ ∈ (affineLiftChart a).source at hp_w_src
    rw [affineLiftChart_source] at hp_w_src
    rcases hp_w_src with ⟨q_w, hq_w_src, hq_w_eq⟩
    have h_LHS : (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out))
      (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H
        Fact.out)).symm w)) = q_w.invol.val.1 := by
      rw [← hq_w_eq]
      change ((HyperellipticAffine.affineChartAt a.invol).lift_openEmbedding
        OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w.invol) = q_w.invol.val.1
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      rw [affineChartAt_of_mem_smoothLocusY a.invol ha_invol_Y]
      rfl
    have h_RHS : w = q_w.val.1 := by
      have h_w_eq : w =
        (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ, ℂ) (coe a
          : HyperellipticOdd H Fact.out)).symm w) := by
        rw [PartialEquiv.right_inv _ hw_target]
      rw [h_w_eq, ← hq_w_eq]
      change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding
        OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w) = q_w.val.1
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
  exact h_eq

theorem pullback_involutive :
    (pullbackOneForm (hyperellipticInvolution H Fact.out)
      (hyperellipticInvolution_contMDiff H Fact.out)).comp
        (pullbackOneForm (hyperellipticInvolution H Fact.out)
          (hyperellipticInvolution_contMDiff H Fact.out)) =
      LinearMap.id := by
  rw [← AX_pullbackOneForm_comp (f := hyperellipticInvolution H Fact.out)
    (hf := hyperellipticInvolution_contMDiff H Fact.out)
    (g := hyperellipticInvolution H Fact.out)
    (hg := hyperellipticInvolution_contMDiff H Fact.out)]
  have h_invol := hyperellipticInvolution_involutive H Fact.out
  have h_fun : hyperellipticInvolution H Fact.out ∘ hyperellipticInvolution H Fact.out = id := by
    ext x
    exact h_invol x
  rw [← AX_pullbackOneForm_id]
  congr 1

axiom pullback_hyperellipticInvolution_eq_neg_axiom :
    pullbackOneForm (hyperellipticInvolution H Fact.out)
        (hyperellipticInvolution_contMDiff H Fact.out)
      = (-LinearMap.id : HolomorphicOneForm (HyperellipticOdd H Fact.out) →ₗ[ℂ]
          HolomorphicOneForm (HyperellipticOdd H Fact.out))

/-- Anti-invariance: the chart coefficient negates when switching sheets.
For `a ∈ smoothLocusY H`, `form.coeff (coe a) z = −form.coeff (coe a.invol) z`. -/
theorem form_coeff_anti_invariance
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target)
    (hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
      HyperellipticOdd H Fact.out)).symm z) ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z =
      -form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z := by
  have hRel := pullback_coeff_eq_invol form a haY hz hy_src
  have h_pullback : (pullbackOneForm (hyperellipticInvolution H Fact.out)
      (hyperellipticInvolution_contMDiff H Fact.out) form).coeff (coe a) z =
      - form.coeff (coe a) z := by
    have h_map :=
      congr_arg (fun f : HolomorphicOneForm (HyperellipticOdd H Fact.out) =>
        f.coeff (coe a) z) (LinearMap.congr_fun
          pullback_hyperellipticInvolution_eq_neg_axiom form)
    exact h_map
  rw [h_pullback] at hRel
  exact neg_eq_iff_eq_neg.mp hRel


/-- Consequence: the raw numerator is sheet-invariant. -/
theorem liouvilleRawNumerator_sheet_invariant
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target)
    (hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
      HyperellipticOdd H Fact.out)).symm z) ∈
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

-- (coeff_eq_of_projX_symm has been moved up to before liouvilleTwoSheetSum_of_eval_ne_zero)

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
  have hAnaAff : AnalyticAt ℂ (fun z =>
    form.coeff (coe a₀ : HyperellipticOdd H Fact.out) z) z₀ := by
    have hz₀_ext : z₀ ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).target := by
      rw [extChartAt_target]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ]
      change z₀ ∈ (affineLiftChart a₀).target
      unfold affineLiftChart
      rw [OpenPartialHomeomorph.lift_openEmbedding_target]
      change z₀ ∈ (HyperellipticAffine.affineChartAt a₀).target
      rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a₀ ha₀Y]
      exact hz₀Target
    have h_open : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe a₀ : HyperellipticOdd H Fact.out)).target :=
      isOpen_extChartAt_target _
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
      change p.val.2 ≠ 0
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
      have hy_src_p : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe p :
        HyperellipticOdd H Fact.out)).symm w) ∈
          (extChartAt 𝓘(ℂ, ℂ) (coe p.invol : HyperellipticOdd H Fact.out)).source := by
        have hw_ext : w ∈ (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).target := by
          rw [extChartAt_target]
          simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
            Set.range_id, Set.inter_univ]
          change w ∈ (affineLiftChart p).target
          unfold affineLiftChart
          rw [OpenPartialHomeomorph.lift_openEmbedding_target]
          change w ∈ (HyperellipticAffine.affineChartAt p).target
          rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY p hpYp]
          exact hw_p
        have h_symm_eq : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).symm w =
          coe p := by
          have h_symm : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)) =
            (chartAt ℂ (coe p : HyperellipticOdd H Fact.out)).toPartialEquiv := by simp
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
      have h_neg : form.coeff (coe p.invol : HyperellipticOdd H Fact.out) w =
        -form.coeff (coe p : HyperellipticOdd H Fact.out) w := by
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
  have hform : AnalyticOn ℂ (form.coeff (coe p : HyperellipticOdd H Fact.out)) (extChartAt
    𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).target :=
    form.2.1 (coe p : HyperellipticOdd H Fact.out)
  have hExt : (extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).target =
    (affineChartProjY (H := H) p hpX).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
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
    have hAnaAt : AnalyticAt ℂ N 0 := AnalyticOn.analyticAt ((affineChartProjY (H :=
      H) p hpX).open_target.mem_nhds h0target) hAna
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
      change a.val.2 ≠ 0
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
    have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target = (affineChartProjY (H :=
      H) p hpX).target := hExt
    have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticOdd H Fact.out) =
      (c.symm : ℂ → HyperellipticOdd H Fact.out) := by
      ext x
      rfl
    have hExtCoeA : ((extChartAt 𝓘(ℂ, ℂ) qA) : HyperellipticOdd H Fact.out → ℂ) =
      (cA : HyperellipticOdd H Fact.out → ℂ) := by
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
      change ((ChartedSpace.chartAt a).lift_openEmbedding OnePoint.isOpenEmbedding_coe)
        (OnePoint.some a) = a.val.1
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      change (HyperellipticAffine.affineChartAt a : OpenPartialHomeomorph (HyperellipticAffine
        H) ℂ) a = a.val.1
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
    change form.coeff (coe (liouvilleChosenAffinePoint (H :=
      H) z) : HyperellipticOdd H Fact.out) z * (liouvilleChosenAffinePoint (H :=
        H) z).val.2 = N (liouvilleChosenAffinePoint (H := H) z).val.2
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

lemma tendsto_eval_div_pow_self (Q : Polynomial ℂ) :
    Filter.Tendsto (fun z : ℂ => Q.eval z / z ^ Q.natDegree) (Filter.cocompact ℂ)
      (𝓝 Q.leadingCoeff) := by
  have h_eq : (fun z : ℂ => Q.eval z / z ^ Q.natDegree) =ᶠ[Filter.cocompact ℂ]
      (fun z => Q.leadingCoeff +
        (Finset.range Q.natDegree).sum (fun i => Q.coeff i * (z ^ i / z ^ Q.natDegree))) := by
    filter_upwards [eventually_ne_zero_cocompact] with z hz
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_div, Finset.sum_div]
    have h_self : Q.coeff Q.natDegree * z ^ Q.natDegree / z ^ Q.natDegree = Q.leadingCoeff := by
      rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hz)]
      rfl
    rw [h_self, add_comm]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_div_assoc]
  rw [Filter.tendsto_congr' h_eq]
  have h_zero : (Finset.range Q.natDegree).sum (fun i => Q.coeff i * (0 : ℂ)) = 0 := by
    have : (fun i => Q.coeff i * (0 : ℂ)) = (fun _ => 0) := by ext; ring
    rw [this, Finset.sum_const_zero]
  have h_sum_lim : Filter.Tendsto
      (fun z : ℂ => (Finset.range Q.natDegree).sum
        (fun i => Q.coeff i * (z ^ i / z ^ Q.natDegree)))
      (Filter.cocompact ℂ) (𝓝 0) := by
    rw [← h_zero]
    refine tendsto_finsetSum _ ?_
    intro i hi
    rw [Finset.mem_range] at hi
    have h_lim := tendsto_pow_div_pow_cocompact i Q.natDegree hi
    exact Filter.Tendsto.const_mul (Q.coeff i) h_lim
  have h_add := Filter.Tendsto.const_add Q.leadingCoeff h_sum_lim
  rw [add_zero] at h_add
  exact h_add

lemma tendsto_eval_div_pow_of_le (Q : Polynomial ℂ) (N : ℕ) (hQ : Q.natDegree ≤ N) :
    ∃ l : ℂ, Filter.Tendsto (fun z : ℂ => Q.eval z / z ^ N) (Filter.cocompact ℂ) (𝓝 l) := by
  by_cases hQ_lt : Q.natDegree < N
  · use 0
    exact tendsto_eval_div_pow_cocompact Q N hQ_lt
  · have hQ_eq : Q.natDegree = N := by omega
    by_cases h_zero : Q = 0
    · subst h_zero; use 0; simp
    · use Q.leadingCoeff
      have h_lim := tendsto_eval_div_pow_self Q
      rwa [← hQ_eq]

lemma eventually_bounded_of_le (Q : Polynomial ℂ) (N : ℕ) (hQ : Q.natDegree ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖Q.eval z / z ^ N‖ ≤ C := by
  obtain ⟨l, h_lim⟩ := tendsto_eval_div_pow_of_le Q N hQ
  use ‖l‖ + 1, by positivity
  have h_norm := h_lim.norm
  have h_mem := h_norm (Metric.closedBall_mem_nhds ‖l‖ zero_lt_one)
  filter_upwards [h_mem] with z hz
  have hdist : dist ‖Q.eval z / z ^ N‖ ‖l‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hz
  rw [Real.dist_eq] at hdist
  have habs := abs_le.mp hdist
  linarith

lemma tendsto_chosen_point_div_pow {H : HyperellipticData} [Fact (Odd H.f.natDegree)] :
    Filter.Tendsto (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2 / z ^ (H.genus + 1))
      (Filter.cocompact ℂ) (𝓝 0) := by
  refine tendsto_zero_of_tendsto_sq_zero ?_
  have h_ev : ∀ᶠ z : ℂ in Filter.cocompact ℂ, z ≠ 0 := eventually_ne_zero_cocompact
  have h_eq : (fun z : ℂ => ‖(liouvilleChosenAffinePoint (H := H) z).val.2 / z ^ (H.genus + 1)‖ ^ 2)
    =ᶠ[Filter.cocompact ℂ]
      (fun z => ‖H.f.eval z / z ^ (2 * H.genus + 2)‖) := by
    filter_upwards [h_ev] with z hz
    rw [← norm_pow]
    congr 1
    rw [div_pow, liouvilleChosenAffinePoint_snd_sq]
    congr 1
    rw [show 2 * H.genus + 2 = (H.genus + 1) * 2 by ring, pow_mul]
  rw [Filter.tendsto_congr' h_eq]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have h_deg : H.f.natDegree < 2 * H.genus + 2 := by
    rcases Fact.out (p := Odd H.f.natDegree) with ⟨k, hk⟩
    dsimp [HyperellipticData.genus]
    rw [hk]
    simp
  exact tendsto_eval_div_pow_cocompact H.f (2 * H.genus + 2) h_deg

lemma tendsto_fw_cocompact {H : HyperellipticData} [Fact (Odd H.f.natDegree)] :
    Filter.Tendsto (fun z : ℂ => f_w H (liouvilleChosenAffinePoint (H := H) z))
      (Filter.cocompact ℂ) (𝓝 0) := by
  have h_ne : ∀ᶠ z : ℂ in Filter.cocompact ℂ, z ≠ 0 := eventually_ne_zero_cocompact
  have h_eval : ∀ᶠ z : ℂ in Filter.cocompact ℂ, H.f.eval z ≠ 0 := eventually_eval_ne_zero_cocompact
  have h_S_tendsto : Filter.Tendsto (fun z : ℂ => (InfinityInverse.S H z⁻¹)⁻¹)
      (Filter.cocompact ℂ) (𝓝 (InfinityInverse.S H 0)⁻¹) := by
    have h_S_cont : ContinuousAt (InfinityInverse.S H) 0 :=
      (InfinityInverse.S_analyticAt H).continuousAt
    have h_S_nz : InfinityInverse.S H 0 ≠ 0 := InfinityInverse.S_eval_zero_ne_zero H
    have h_S_inv_cont : ContinuousAt (fun u : ℂ => (InfinityInverse.S H u)⁻¹) 0 :=
      h_S_cont.inv₀ h_S_nz
    exact h_S_inv_cont.tendsto.comp tendsto_inv_cocompact_zero
  have h_div_tendsto : Filter.Tendsto
      (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2 / z ^ (H.genus + 1))
      (Filter.cocompact ℂ) (𝓝 0) :=
    tendsto_chosen_point_div_pow
  have h_prod_tendsto : Filter.Tendsto
      (fun z : ℂ => ((liouvilleChosenAffinePoint (H := H) z).val.2 / z ^ (H.genus + 1)) *
        (InfinityInverse.S H z⁻¹)⁻¹)
      (Filter.cocompact ℂ) (𝓝 (0 * (InfinityInverse.S H 0)⁻¹)) :=
    h_div_tendsto.mul h_S_tendsto
  rw [zero_mul] at h_prod_tendsto
  have h_prod_eq : (fun z : ℂ => ((liouvilleChosenAffinePoint (H := H) z).val.2 /
        z ^ (H.genus + 1)) * (InfinityInverse.S H z⁻¹)⁻¹) =
      (fun z : ℂ => f_w H (liouvilleChosenAffinePoint (H := H) z)) := by
    ext z
    unfold f_w
    rw [show (liouvilleChosenAffinePoint (H := H) z).val.1⁻¹ = z⁻¹ from rfl]
    rw [div_eq_mul_inv, inv_pow]
  rwa [h_prod_eq] at h_prod_tendsto

lemma eventually_mem_V_cocompact {H : HyperellipticData} [Fact (Odd H.f.natDegree)] :
    ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      liouvilleChosenAffinePoint (H := H) z ∈ V H := by
  have h_ne : ∀ᶠ z : ℂ in Filter.cocompact ℂ, z ≠ 0 := eventually_ne_zero_cocompact
  have h_eval : ∀ᶠ z : ℂ in Filter.cocompact ℂ, H.f.eval z ≠ 0 := eventually_eval_ne_zero_cocompact
  have h_src_nhds : (InfinityInverse.tLocalHomeomorph H).source ∈ 𝓝 (0 : ℂ) :=
    (InfinityInverse.tLocalHomeomorph H).open_source.mem_nhds
      (InfinityInverse.tLocalHomeomorph_source H)
  have h_src_eventually := tendsto_fw_cocompact (H := H) h_src_nhds
  filter_upwards [h_ne, h_eval, h_src_eventually] with z hz_ne hz_eval hz_src
  refine ⟨hz_ne, ?_⟩
  refine ⟨?_, hz_src⟩
  show (liouvilleChosenAffinePoint (H := H) z).val.2 ≠ 0
  intro hc
  have h_eval_zero : H.f.eval z = 0 := by
    have h_sq := liouvilleChosenAffinePoint_snd_sq (H := H) z
    rw [hc] at h_sq
    have h_zero : (0 : ℂ) ^ 2 = 0 := by ring
    rw [h_zero] at h_sq
    exact h_sq.symm
  exact hz_eval h_eval_zero

variable {H : HyperellipticData} [Fact (Odd H.f.natDegree)]

theorem liouvilleRemovableNumerator_eventually_norm_div_pow_le
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ z : ℂ in Filter.cocompact ℂ,
        ‖liouvilleRemovableNumerator form z /
            z ^ ((H.f.natDegree - 1) / 2 - 1)‖ ≤ R := by
  classical
  let g : ℕ := H.genus
  let n : ℕ := ((H.f.natDegree - 1) / 2 - 1)
  have hAna : AnalyticAt ℂ (form.coeff (infty : HyperellipticOdd H Fact.out)) 0 := by
    have h_open := isOpen_extChartAt_target (I := 𝓘(ℂ, ℂ))
      (M := HyperellipticOdd H Fact.out) (infty : HyperellipticOdd H Fact.out)
    have hz_target : (0 : ℂ) ∈
        (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).target := by
      rw [extChartAt_target]
      dsimp
      rw [Set.range_id, Set.inter_univ]
      change (0 : ℂ) ∈ (infinityChart H Fact.out).target
      exact InfinityInverse.tLocalHomeomorph_target_zero H
    exact (form.2.1 (infty : HyperellipticOdd H Fact.out)).analyticAt (h_open.mem_nhds hz_target)
  let B : ℝ := ‖form.coeff (infty : HyperellipticOdd H Fact.out) 0‖ + 1
  have hB_nonneg : 0 ≤ B := by positivity
  have h_infty_bound : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      ‖form.coeff (infty : HyperellipticOdd H Fact.out)
        ((liouvilleChosenAffinePoint (H := H) z).val.2 /
          (liouvilleChosenAffinePoint (H := H) z).val.1 ^ (H.genus + 1))‖ ≤ B := by
    have h_cont : ContinuousAt (form.coeff (infty : HyperellipticOdd H Fact.out)) 0 :=
      hAna.continuousAt
    have h_mem := h_cont.norm
      (Metric.closedBall_mem_nhds (‖form.coeff infty 0‖) zero_lt_one)
    have h_lim : Filter.Tendsto (fun z => (liouvilleChosenAffinePoint (H := H) z).val.2 /
        (liouvilleChosenAffinePoint (H := H) z).val.1 ^ (H.genus + 1))
        (Filter.cocompact ℂ) (𝓝 0) := by
      have h_div := tendsto_chosen_point_div_pow (H := H)
      have h_eq : (fun z => (liouvilleChosenAffinePoint (H := H) z).val.2 /
          (liouvilleChosenAffinePoint (H := H) z).val.1 ^ (H.genus + 1)) =
        (fun z => (liouvilleChosenAffinePoint (H := H) z).val.2 / z ^ (H.genus + 1)) := by
        ext z
        rfl
      rwa [h_eq]
    filter_upwards [h_lim h_mem] with z hz
    have hdist : dist ‖form.coeff (infty : HyperellipticOdd H Fact.out)
      ((liouvilleChosenAffinePoint (H := H) z).val.2 /
        (liouvilleChosenAffinePoint (H := H) z).val.1 ^ (H.genus + 1))‖
      ‖form.coeff infty 0‖ ≤ 1 := by
      simpa [Metric.mem_closedBall] using hz
    rw [Real.dist_eq] at hdist
    have habs := abs_le.mp hdist
    linarith
  -- Bound for the derivative of H.f
  have h_deriv_deg : (Polynomial.derivative H.f).natDegree ≤ 2 * H.genus := by
    have h_deg : H.f.natDegree = 2 * H.genus + 1 := by
      rcases Fact.out (p := Odd H.f.natDegree) with ⟨k, hk⟩
      dsimp [HyperellipticData.genus]
      rw [hk]
      simp
    have hd := Polynomial.natDegree_derivative_le H.f
    omega
  obtain ⟨C_deriv, hC_deriv_nonneg, h_deriv_bound⟩ :=
    eventually_bounded_of_le (Polynomial.derivative H.f) (2 * H.genus) h_deriv_deg
  -- Bound for H.f itself
  have h_f_deg : H.f.natDegree ≤ 2 * H.genus + 1 := by
    rcases Fact.out (p := Odd H.f.natDegree) with ⟨k, hk⟩
    dsimp [HyperellipticData.genus]
    rw [hk]
    simp
  obtain ⟨C_f, hC_f_nonneg, h_f_bound⟩ :=
    eventually_bounded_of_le H.f (2 * H.genus + 1) h_f_deg
  let C_D : ℝ := C_deriv + (2 * (H.genus : ℝ) + 2) * C_f
  have hCD_nonneg : 0 ≤ C_D := by positivity
  let R : ℝ := B * (C_D / 2)
  have hR_nonneg : 0 ≤ R := mul_nonneg hB_nonneg (by positivity)
  have h_D_ev : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      (z * (Polynomial.derivative H.f).eval z - (2 * (H.genus : ℂ) + 2) * H.f.eval z) ≠ 0 := by
    have h_f_ne_zero : H.f ≠ 0 := hyperelliptic_f_ne_zero
    have h_deriv_ne_zero : Polynomial.derivative H.f ≠ 0 := by
      intro hc
      have hd : H.f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hc
      have h_deg : H.f.natDegree = 2 * H.genus + 1 := by
        rcases Fact.out (p := Odd H.f.natDegree) with ⟨k, hk⟩
        dsimp [HyperellipticData.genus]
        rw [hk]
        simp
      omega
    have h_lim_f := tendsto_eval_div_pow_self H.f
    have h_lim_deriv := tendsto_eval_div_pow_self (Polynomial.derivative H.f)
    have h_deg : H.f.natDegree = 2 * H.genus + 1 := by
      rcases Fact.out (p := Odd H.f.natDegree) with ⟨k, hk⟩
      dsimp [HyperellipticData.genus]
      rw [hk]
      simp
    have h_deriv_deg : (Polynomial.derivative H.f).natDegree = 2 * H.genus := by
      have hp : 0 < H.f.natDegree := by omega
      have h_deg' := Polynomial.degree_derivative_eq H.f hp
      have hd_eq := Polynomial.natDegree_eq_of_degree_eq_some h_deg'
      rw [hd_eq, h_deg]
      rfl
    rw [h_deg] at h_lim_f
    rw [h_deriv_deg] at h_lim_deriv
    have h_ratio_eq : (fun z : ℂ => (z * (Polynomial.derivative H.f).eval z -
        (2 * (H.genus : ℂ) + 2) * H.f.eval z) / z ^ (2 * H.genus + 1)) =ᶠ[Filter.cocompact ℂ]
      (fun z => ((Polynomial.derivative H.f).eval z / z ^ (2 * H.genus)) -
        (2 * (H.genus : ℂ) + 2) * (H.f.eval z / z ^ (2 * H.genus + 1))) := by
      filter_upwards [eventually_ne_zero_cocompact] with z hz
      have h_pow : z ^ (2 * H.genus + 1) = z * z ^ (2 * H.genus) := by
        rw [show 2 * H.genus + 1 = (2 * H.genus) + 1 by omega, pow_succ, mul_comm]
      rw [sub_div]
      congr 1
      · rw [h_pow, mul_div_mul_left _ _ hz]
      · rw [mul_div_assoc]
    have h_lim_sub : Filter.Tendsto
        (fun z => ((Polynomial.derivative H.f).eval z / z ^ (2 * H.genus)) -
          (2 * (H.genus : ℂ) + 2) * (H.f.eval z / z ^ (2 * H.genus + 1)))
        (Filter.cocompact ℂ)
        (𝓝 ((Polynomial.derivative H.f).leadingCoeff -
          (2 * (H.genus : ℂ) + 2) * H.f.leadingCoeff)) := by
      refine Filter.Tendsto.sub h_lim_deriv ?_
      exact Filter.Tendsto.const_mul _ h_lim_f
    rw [← Filter.tendsto_congr' h_ratio_eq] at h_lim_sub
    have h_lc_deriv : (Polynomial.derivative H.f).leadingCoeff =
      H.f.leadingCoeff * (2 * (H.genus : ℂ) + 1) := by
      change (Polynomial.derivative H.f).coeff (Polynomial.derivative H.f).natDegree = _
      rw [h_deriv_deg, Polynomial.coeff_derivative]
      have h_deg_eq : 2 * H.genus + 1 = H.f.natDegree := by omega
      rw [h_deg_eq]
      have h_lc_f : H.f.coeff H.f.natDegree = H.f.leadingCoeff := rfl
      rw [h_lc_f]
      push_cast
      ring
    rw [h_lc_deriv] at h_lim_sub
    have h_val_eq : H.f.leadingCoeff * (2 * (H.genus : ℂ) + 1) -
      (2 * (H.genus : ℂ) + 2) * H.f.leadingCoeff = -H.f.leadingCoeff := by
      ring
    rw [h_val_eq] at h_lim_sub
    have h_nz : -H.f.leadingCoeff ≠ 0 := by
      exact neg_ne_zero.mpr hyperelliptic_leadingCoeff_ne_zero
    have h_ev_ne := h_lim_sub.eventually_ne h_nz
    filter_upwards [h_ev_ne, eventually_ne_zero_cocompact] with z hz_ne hz_z
    intro hc
    rw [hc, zero_div] at hz_ne
    exact hz_ne rfl
  refine ⟨R, hR_nonneg, ?_⟩
  have h_mem_V := eventually_mem_V_cocompact (H := H)
  filter_upwards [h_mem_V, h_infty_bound, h_deriv_bound, h_f_bound, h_D_ev]
    with z hz_V hBnd hDerivBnd hFBnd h_D_nz
  let a := liouvilleChosenAffinePoint (H := H) z
  let y : ℂ := a.val.2
  have h_y_ne : y ≠ 0 := hz_V.2.1
  have h_z_ne : z ≠ 0 := hz_V.1
  have h_eval_nz : H.f.eval z ≠ 0 := by
    have h_sq := liouvilleChosenAffinePoint_snd_sq (H := H) z
    intro hc
    rw [hc] at h_sq
    exact h_y_ne (sq_eq_zero_iff.mp h_sq)
  have hRem : liouvilleRemovableNumerator form z =
      liouvilleRawNumerator form z :=
    liouvilleRemovableNumerator_of_eval_ne_zero form h_eval_nz
  let t := a.val.2 / a.val.1 ^ (H.genus + 1)
  have ht_target : t ∈ (InfinityInverse.tLocalHomeomorph H).target := by
    have h_src : f_w H a ∈ (InfinityInverse.tLocalHomeomorph H).source := hz_V.2.2
    have h_img := (InfinityInverse.tLocalHomeomorph H).map_source h_src
    rw [InfinityInverse.tLocalHomeomorph_coe] at h_img
    have h_t_eq : InfinityInverse.t H (f_w H a) = t := t_w_q Fact.out a h_z_ne h_y_ne
    rwa [h_t_eq] at h_img
  have ht0 : t ≠ 0 := div_ne_zero h_y_ne (pow_ne_zero _ h_z_ne)
  have ht_target_ext : t ∈ (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).target := by
    rw [extChartAt_target]
    dsimp
    rw [Set.range_id, Set.inter_univ]
    exact ht_target
  have h_w_eq : (InfinityInverse.tLocalHomeomorph H).symm t = f_w H a := by
    have h_apply : InfinityInverse.tLocalHomeomorph H (f_w H a) = t := by
      rw [InfinityInverse.tLocalHomeomorph_coe]
      exact t_w_q Fact.out a h_z_ne h_y_ne
    rw [← h_apply]
    exact (InfinityInverse.tLocalHomeomorph H).left_inv hz_V.2.2
  have h_eq_coe : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm t = coe a := by
    change (infinityChart H Fact.out).symm t = coe a
    dsimp [infinityChart, infinityBackward]
    rw [if_neg ht0]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · rw [infinityInverseMap_val_of_ne_zero t ht_target ht0]
      dsimp
      rw [h_w_eq]
      have h_sq : (f_w H a) ^ 2 = a.val.1⁻¹ :=
        InfinityInverse.w_q_sq_eq_inv Fact.out a h_z_ne h_y_ne
      rw [inv_pow, h_sq, inv_inv]
    · rw [infinityInverseMap_val_of_ne_zero t ht_target ht0]
      dsimp
      rw [h_w_eq]
      have h_w_nz : f_w H a ≠ 0 := by
        dsimp [f_w]
        refine mul_ne_zero (mul_ne_zero h_y_ne (pow_ne_zero _ (inv_ne_zero h_z_ne))) ?_
        exact inv_ne_zero (S_ne_zero_of_mem_D_S H
          (w_q_mem_source_imp_x_inv_mem_D_S Fact.out a h_z_ne h_y_ne hz_V.2.2))
      have h_sq_eq : (f_w H a)⁻¹ ^ 2 = z := by
        have h_sq : (f_w H a) ^ 2 = a.val.1⁻¹ :=
          InfinityInverse.w_q_sq_eq_inv Fact.out a h_z_ne h_y_ne
        rw [inv_pow, h_sq, inv_inv]
        rfl
      have h_sq : (f_w H a) ^ 2 = z⁻¹ := by
        have h_sq_inv : (f_w H a) ^ 2 = a.val.1⁻¹ :=
          InfinityInverse.w_q_sq_eq_inv Fact.out a h_z_ne h_y_ne
        rw [h_sq_inv]
        rfl
      have h_S_nz : InfinityInverse.S H ((f_w H a) ^ 2) ≠ 0 := by
        have h_mem_D_S : (f_w H a) ^ 2 ∈ D_S H := by
          rw [h_sq]
          exact w_q_mem_source_imp_x_inv_mem_D_S Fact.out a h_z_ne h_y_ne hz_V.2.2
        exact S_ne_zero_of_mem_D_S H h_mem_D_S
      have h_S_cancel : InfinityInverse.S H ((f_w H a) ^ 2) *
        (InfinityInverse.S H ((f_w H a) ^ 2))⁻¹ = 1 :=
        mul_inv_cancel₀ h_S_nz
      have h_pow_cancel : ((f_w H a) ^ 2) ^ (H.genus + 1) *
        ((f_w H a)⁻¹ ^ 2) ^ (H.genus + 1) = 1 := by
        rw [← mul_pow]
        have h_one : (f_w H a) ^ 2 * (f_w H a)⁻¹ ^ 2 = 1 := by
          rw [← mul_pow]
          rw [mul_inv_cancel₀ h_w_nz, one_pow]
        rw [h_one, one_pow]
      change t * ((f_w H a)⁻¹ ^ 2) ^ (H.genus + 1) = y
      have h_t_eq : t = f_w H a * InfinityInverse.S H ((f_w H a) ^ 2) := by
        have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H ht_target
        unfold InfinityInverse.t at h_tz
        rw [h_w_eq] at h_tz
        exact h_tz.symm
      have h_fw_unfold : f_w H a = y * ((f_w H a) ^ 2) ^ (H.genus + 1) *
        (InfinityInverse.S H ((f_w H a) ^ 2))⁻¹ := by
        change a.val.2 * (a.val.1⁻¹ ^ (H.genus + 1)) * (InfinityInverse.S H a.val.1⁻¹)⁻¹ =
          y * ((f_w H a) ^ 2) ^ (H.genus + 1) * (InfinityInverse.S H ((f_w H a) ^ 2))⁻¹
        congr 1
        · rw [show a.val.2 = y from rfl]
          congr 1
          rw [show a.val.1⁻¹ = (f_w H a) ^ 2 by exact h_sq.symm]
        · rw [show a.val.1⁻¹ = (f_w H a) ^ 2 by exact h_sq.symm]
      rw [h_t_eq]
      nth_rw 1 [h_fw_unfold]
      calc y * ((f_w H a) ^ 2) ^ (H.genus + 1) * (InfinityInverse.S H ((f_w H a) ^ 2))⁻¹ *
            InfinityInverse.S H ((f_w H a) ^ 2) * ((f_w H a)⁻¹ ^ 2) ^ (H.genus + 1)
        _ = y * ((f_w H a) ^ 2) ^ (H.genus + 1) *
            ((InfinityInverse.S H ((f_w H a) ^ 2))⁻¹ * InfinityInverse.S H ((f_w H a) ^ 2)) *
            ((f_w H a)⁻¹ ^ 2) ^ (H.genus + 1) := by ring
        _ = y * ((f_w H a) ^ 2) ^ (H.genus + 1) * 1 * ((f_w H a)⁻¹ ^ 2) ^ (H.genus + 1) := by
          rw [mul_comm (InfinityInverse.S H ((f_w H a) ^ 2))⁻¹, h_S_cancel]
        _ = y * (((f_w H a) ^ 2) ^ (H.genus + 1) * ((f_w H a)⁻¹ ^ 2) ^ (H.genus + 1)) := by ring
        _ = y * 1 := by rw [h_pow_cancel]
        _ = y := by ring
  have hsrc : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm t ∈
      (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source := by
    rw [h_eq_coe]
    exact mem_extChartAt_source (coe a)
  have hCocycle := form.2.2.1 (infty : HyperellipticOdd H Fact.out)
    (coe a : HyperellipticOdd H Fact.out) t ht_target_ext hsrc
  have h_coord : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out))
      ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm t) = z := by
    rw [h_eq_coe]
    change (affineLiftChart (h := Fact.out) a) (OnePoint.some a) = z
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    change (HyperellipticAffine.affineChartAt a) a = z
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a h_y_ne]
    change a.val.1 = z
    rfl
  rw [h_coord] at hCocycle
  have hLiftEq : affineLiftChart (h := Fact.out) a =
      (HyperellipticAffine.affineChartProjX a h_y_ne).lift_openEmbedding
        OnePoint.isOpenEmbedding_coe := by
    unfold affineLiftChart
    congr 1
    exact HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a h_y_ne
  have hOverlapOpen : IsOpen ((infinityChart H Fact.out).symm.trans
      ((HyperellipticAffine.affineChartProjX a h_y_ne).lift_openEmbedding
        OnePoint.isOpenEmbedding_coe)).source :=
    ((infinityChart H Fact.out).symm.trans _).open_source
  have hTransSrc : t ∈ ((infinityChart H Fact.out).toPartialEquiv.symm.trans
      ((HyperellipticAffine.affineChartProjX a h_y_ne).lift_openEmbedding
        OnePoint.isOpenEmbedding_coe).toPartialEquiv).source := by
    refine ⟨ht_target, ?_⟩
    change (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm t ∈
      ((HyperellipticAffine.affineChartProjX a h_y_ne).lift_openEmbedding
        OnePoint.isOpenEmbedding_coe).source
    rw [h_eq_coe]
    rw [← hLiftEq]
    exact mem_affineLiftChart_source a
  have hEqNear : (↑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ∘
      ↑(extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm) =ᶠ[nhds t]
    (fun u => ((InfinityInverse.tLocalHomeomorph H).symm u)⁻¹ ^ 2) := by
    refine Filter.eventually_of_mem (hOverlapOpen.mem_nhds hTransSrc) ?_
    intro u hu
    conv_lhs =>
      rw [show (↑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) :
        HyperellipticOdd H Fact.out → ℂ) = ↑(affineLiftChart (h := Fact.out) a) from rfl]
      rw [show (↑(extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm :
        ℂ → HyperellipticOdd H Fact.out) = ↑(infinityChart H Fact.out).symm from rfl]
    rw [hLiftEq]
    exact infinityChart_trans_affineLiftProjX_apply a h_y_ne hu
  have hd_bwd_eq : (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ∘
      (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm) t 1) =
    2 * z ^ (H.genus + 2) * y /
      (z * (Polynomial.derivative H.f).eval z - (2 * H.genus + 2) * H.f.eval z) := by
    rw [Filter.EventuallyEq.fderiv_eq hEqNear]
    have hInTarget : ((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2 ∈
        ((HyperellipticAffine.affineChartProjX a h_y_ne) :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target := by
      have hmap := ((infinityChart H Fact.out).symm.trans
          ((HyperellipticAffine.affineChartProjX a h_y_ne).lift_openEmbedding
            OnePoint.isOpenEmbedding_coe)).map_source hTransSrc
      rw [infinityChart_trans_affineLiftProjX_apply a h_y_ne hTransSrc] at hmap
      rw [OpenPartialHomeomorph.trans_target] at hmap
      exact hmap.1
    have hYSrc : t * (((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2) ^ (H.genus + 1) ∈
        (a.squareLocalHomeomorph h_y_ne).source := by
      have h_eq_coe' : (infinityChart H Fact.out).symm t =
        coe (InfinityInverse.infinityInverseMap H Fact.out t) := by
        change infinityBackward H Fact.out t = _
        unfold infinityBackward
        rw [if_neg ht0]
      have h_proj_src : (infinityChart H Fact.out).symm t ∈
        ((a.affineChartProjX h_y_ne).lift_openEmbedding
          OnePoint.isOpenEmbedding_coe).source := hTransSrc.2
      rw [h_eq_coe'] at h_proj_src
      simp only [OpenPartialHomeomorph.lift_openEmbedding_source] at h_proj_src
      obtain ⟨q, hq, heq⟩ := h_proj_src
      have hq_eq : q = InfinityInverse.infinityInverseMap H Fact.out t :=
        OnePoint.coe_injective heq
      rw [hq_eq] at hq
      have h_snd : (InfinityInverse.infinityInverseMap H Fact.out t).val.2 =
        t * (((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2) ^ (H.genus + 1) := by
        rw [infinityInverseMap_val_of_ne_zero t ht_target ht0]
      rw [← h_snd]
      exact hq
    have h_deriv := infinity_transition_deriv_identity Fact.out a h_y_ne ht_target ht0
      hInTarget hYSrc
    dsimp at h_deriv
    rw [h_w_eq] at h_deriv
    have h_sq : (f_w H a)⁻¹ ^ 2 = z := by
      have h_sq_inv : (f_w H a) ^ 2 = a.val.1⁻¹ :=
        InfinityInverse.w_q_sq_eq_inv Fact.out a h_z_ne h_y_ne
      rw [inv_pow, h_sq_inv]
      change (a.val.1⁻¹)⁻¹ = z
      rw [inv_inv]
      rfl
    rw [h_sq] at h_deriv
    have h_symm_eq : (a.squareLocalHomeomorph h_y_ne).symm (H.f.eval z) = y := by
      have h_eval : H.f.eval z = y ^ 2 := by
        have h_prop := a.property
        change a.val.2 ^ 2 = H.f.eval a.val.1 at h_prop
        rw [h_prop]
        rfl
      rw [h_eval]
      exact (a.squareLocalHomeomorph h_y_ne).left_inv
        (HyperellipticAffine.affineChartProjX_mem_source a h_y_ne)
    rw [h_symm_eq] at h_deriv
    exact h_deriv
  rw [hd_bwd_eq] at hCocycle
  let D : ℂ := z * (Polynomial.derivative H.f).eval z - (2 * H.genus + 2) * H.f.eval z
  let Z : ℂ := 2 * z ^ (H.genus + 2)
  have h_algebra : form.coeff (coe a : HyperellipticOdd H Fact.out) z * y =
      form.coeff (infty : HyperellipticOdd H Fact.out) t * D / Z := by
    have h_Z_ne : Z ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ h_z_ne)
    change form.val (coe a) z * y = form.val infty t * D / Z
    rw [hCocycle]
    have h_eq : (2 * z ^ (H.genus + 2) * y / (z * (Polynomial.derivative H.f).eval z -
        (2 * H.genus + 2) * H.f.eval z)) = (2 * z ^ (H.genus + 2) * y) *
        (z * (Polynomial.derivative H.f).eval z - (2 * H.genus + 2) * H.f.eval z)⁻¹ := by
      rw [div_eq_mul_inv]
    rw [h_eq]
    rw [show 2 * z ^ (H.genus + 2) = Z from rfl]
    rw [show (z * (Polynomial.derivative H.f).eval z - (2 * H.genus + 2) * H.f.eval z) = D from rfl]
    symm
    calc form.val (coe a) z * (Z * y * D⁻¹) * D / Z
      _ = form.val (coe a) z * y * (Z * D⁻¹ * D / Z) := by ring
      _ = form.val (coe a) z * y * (Z * (D⁻¹ * D) / Z) := by ring
      _ = form.val (coe a) z * y * (Z * 1 / Z) := by rw [inv_mul_cancel₀ h_D_nz]
      _ = form.val (coe a) z * y * (Z / Z) := by ring
      _ = form.val (coe a) z * y * 1 := by rw [div_self h_Z_ne]
      _ = form.val (coe a) z * y := by ring
  have h_term_eq : (form.coeff (coe a : HyperellipticOdd H Fact.out) z * y / z ^ (H.genus - 1)) =
      form.coeff (infty : HyperellipticOdd H Fact.out) t * (D / (2 * z ^ (2 * H.genus + 1))) := by
    rw [h_algebra]
    have h_pow_add : z ^ (H.genus + 2) * z ^ (H.genus - 1) = z ^ (2 * H.genus + 1) := by
      rw [← pow_add]
      congr 1
      have : 3 ≤ H.f.natDegree := H.h_degree
      have h_deg : H.f.natDegree = 2 * H.genus + 1 := by
        rcases Fact.out (p := Odd H.f.natDegree) with ⟨k, hk⟩
        dsimp [HyperellipticData.genus]
        rw [hk]
        simp
      have : 1 ≤ H.genus := by omega
      omega
    rw [div_div]
    rw [mul_assoc (2 : ℂ), h_pow_add]
    ring
  rw [hRem]
  unfold liouvilleRawNumerator
  change ‖form.coeff (coe a) z * y / z ^ (H.genus - 1)‖ ≤ R
  rw [h_term_eq]
  rw [norm_mul]
  have h_D_bound : ‖D / (2 * z ^ (2 * H.genus + 1))‖ ≤ C_D / 2 := by
    have h_div_two : D / (2 * z ^ (2 * H.genus + 1)) =
      (1 / 2 : ℂ) * (D / z ^ (2 * H.genus + 1)) := by ring
    rw [h_div_two, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h_D_split : D / z ^ (2 * H.genus + 1) =
      (Polynomial.derivative H.f).eval z / z ^ (2 * H.genus) -
        (2 * (H.genus : ℂ) + 2) * (H.f.eval z / z ^ (2 * H.genus + 1)) := by
      have h_pow : z ^ (2 * H.genus + 1) = z * z ^ (2 * H.genus) := by
        rw [show 2 * H.genus + 1 = (2 * H.genus) + 1 by omega, pow_succ, mul_comm]
      rw [sub_div]
      congr 1
      · rw [h_pow, mul_div_mul_left _ _ h_z_ne]
      · rw [mul_div_assoc]
    have h_D_norm : ‖D / z ^ (2 * H.genus + 1)‖ ≤ C_D := by
      rw [h_D_split]
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul]
      have h_norm : ‖(2 * (H.genus : ℂ) + 2)‖ = 2 * (H.genus : ℝ) + 2 := by
        rw [show (2 * (H.genus : ℂ) + 2) = ((2 * H.genus + 2 : ℕ) : ℂ) by push_cast; rfl]
        rw [Complex.norm_natCast]
        push_cast
        rfl
      rw [h_norm]
      exact add_le_add hDerivBnd (mul_le_mul_of_nonneg_left hFBnd (by positivity))
    linarith
  have hR_eq : R = B * (C_D / 2) := rfl
  rw [hR_eq]
  exact mul_le_mul hBnd h_D_bound (by positivity) hB_nonneg


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
      have hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe p :
        HyperellipticOdd H Fact.out)).symm z) ∈
          (extChartAt 𝓘(ℂ, ℂ) (coe p.invol : HyperellipticOdd H Fact.out)).source := by
        have h_symm_eq : ((extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).symm z :
          HyperellipticOdd H Fact.out) = coe p := by
          have h_symm : ((extChartAt 𝓘(ℂ, ℂ) (coe p : HyperellipticOdd H Fact.out)).symm : ℂ →
            HyperellipticOdd H Fact.out) =
              ((affineLiftChart p).symm : ℂ → HyperellipticOdd H Fact.out) := by
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


theorem representation_singular_cases
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (g : Polynomial ℂ)
    (hSmoothY : ∀ (a' : HyperellipticAffine H), a' ∈ smoothLocusY H → ∀ {z' : ℂ},
      z' ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)).target →
      form.coeff (coe a' : HyperellipticOdd H Fact.out) z' =
        (hyperellipticOddForm H g).coeff (coe a' : HyperellipticOdd H Fact.out) z')
    (q : HyperellipticOdd H Fact.out) (z : ℂ) (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target) :
    form.coeff q z = (hyperellipticOddForm H g).coeff q z := by
  -- We will prove it for all affine points first
  have hAffine : ∀ (a : HyperellipticAffine H) (z' : ℂ)
    (hz' : z' ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target),
      form.coeff (coe a : HyperellipticOdd H Fact.out) z' =
        (hyperellipticOddForm H g).coeff (coe a : HyperellipticOdd H Fact.out) z' := by
    intro a z' hz'
    by_cases hpY : a ∈ smoothLocusY H
    · exact hSmoothY a hpY hz'
    · -- branch point case
      have hpX : a ∈ smoothLocusX H :=
        HyperellipticAffine.mem_smoothLocusX_of_y_eq_zero H
          (by simpa [smoothLocusY] using hpY)
      have hExt : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target =
        (affineChartProjY (H := H) a hpX).target := by
        rw [extChartAt_target]
        simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
          Set.range_id, Set.inter_univ]
        change (affineLiftChart a).target = _
        unfold affineLiftChart
        rw [OpenPartialHomeomorph.lift_openEmbedding_target]
        change (HyperellipticAffine.affineChartAt a).target = _
        rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY a hpY]
      have hPunct : ∀ w ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target,
        w ≠ 0 → form.coeff (coe a : HyperellipticOdd H Fact.out) w =
          (hyperellipticOddForm H g).coeff (coe a : HyperellipticOdd H Fact.out) w := by
        intro w hw hwne
        have hwY : w ∈ (affineChartProjY a hpX).target := by rwa [hExt] at hw
        let a' := (affineChartProjY a hpX).symm w
        have ha'Y : a' ∈ smoothLocusY H := by
          change a'.val.2 ≠ 0
          have hsnd := affineChartProjY_symm_apply_snd a hpX hwY
          simpa [a', hsnd] using hwne
        let q' : HyperellipticOdd H Fact.out := coe a'
        have h_symm_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w =
          q' := by
          have h_symm : ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm :
            ℂ → HyperellipticOdd H Fact.out) =
            ((affineLiftChart a).symm : ℂ → HyperellipticOdd H Fact.out) := by
            ext x
            rfl
          rw [h_symm]
          change (affineLiftChart a).symm w = q'
          unfold affineLiftChart
          rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
          change coe ((HyperellipticAffine.affineChartAt a).symm w) = q'
          rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY a hpY]
        have hsrc : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w ∈
          (extChartAt 𝓘(ℂ, ℂ) q').source := by
          rw [h_symm_eq]
          exact mem_extChartAt_source q'
        have hCoord : (extChartAt 𝓘(ℂ, ℂ) q')
          ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w) = a'.val.1 := by
          rw [h_symm_eq]
          have h_ext : (extChartAt 𝓘(ℂ, ℂ) q' : HyperellipticOdd H Fact.out → ℂ) =
            (affineLiftChart a' : HyperellipticOdd H Fact.out → ℂ) := by
            ext x
            rfl
          rw [h_ext]
          change ((affineLiftChart a') : HyperellipticOdd H Fact.out → ℂ) q' = a'.val.1
          change ((HyperellipticAffine.affineChartAt a').lift_openEmbedding
            OnePoint.isOpenEmbedding_coe) (OnePoint.some a') = a'.val.1
          rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
          rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a' ha'Y]
          rfl
        have hTarget' : a'.val.1 ∈ (extChartAt 𝓘(ℂ, ℂ) q').target := by
          have h_ext_target : (extChartAt 𝓘(ℂ, ℂ) q').target =
            (affineChartProjX a' ha'Y).target := by
            rw [extChartAt_target]
            simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
              Set.range_id, Set.inter_univ]
            change (affineLiftChart a').target = _
            unfold affineLiftChart
            rw [OpenPartialHomeomorph.lift_openEmbedding_target]
            change (HyperellipticAffine.affineChartAt a').target = _
            rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a' ha'Y]
          rw [h_ext_target]
          have hpSrc : a' ∈ (affineChartProjX a' ha'Y).source :=
            affineChartProjX_mem_source a' ha'Y
          have hmap := (affineChartProjX a' ha'Y).map_source hpSrc
          change a'.val.1 ∈ _ at hmap
          exact hmap
        have hCocycle1 := form.2.2.1 (coe a : HyperellipticOdd H Fact.out) q' w hw hsrc
        have hCocycle2 := (hyperellipticOddForm H g).2.2.1 (coe a : HyperellipticOdd H Fact.out) q'
          w hw hsrc
        rw [hCoord] at hCocycle1 hCocycle2
        have hEq := hSmoothY a' ha'Y hTarget'
        unfold HolomorphicOneForm.coeff at hEq
        unfold HolomorphicOneForm.coeff
        rw [hCocycle1, hCocycle2, hEq]
      by_cases hz0 : z' = 0
      · subst hz0
        have hCont1 : ContinuousAt (form.coeff (coe a : HyperellipticOdd H Fact.out)) 0 := by
          have hAna : AnalyticAt ℂ (form.coeff (coe a : HyperellipticOdd H Fact.out)) 0 :=
            (form.2.1 (coe a : HyperellipticOdd H Fact.out)).analyticAt
              ((isOpen_extChartAt_target (coe a : HyperellipticOdd H Fact.out)).mem_nhds hz')
          exact hAna.continuousAt
        have hCont2 : ContinuousAt ((hyperellipticOddForm H g).coeff
          (coe a : HyperellipticOdd H Fact.out)) 0 := by
          have hAna : AnalyticAt ℂ ((hyperellipticOddForm H g).coeff
            (coe a : HyperellipticOdd H Fact.out)) 0 :=
            ((hyperellipticOddForm H g).2.1 (coe a : HyperellipticOdd H Fact.out)).analyticAt
              ((isOpen_extChartAt_target (coe a : HyperellipticOdd H Fact.out)).mem_nhds hz')
          exact hAna.continuousAt
        have hEqEv : form.coeff (coe a : HyperellipticOdd H Fact.out) =ᶠ[𝓝[≠] (0 : ℂ)]
          (hyperellipticOddForm H g).coeff (coe a : HyperellipticOdd H Fact.out) := by
          rw [eventuallyEq_nhdsWithin_iff]
          filter_upwards [(isOpen_extChartAt_target (coe a : HyperellipticOdd H
            Fact.out)).mem_nhds hz']
            with w hw hwne
          exact hPunct w hw hwne
        exact tendsto_nhds_unique_of_eventuallyEq
          (hCont1.tendsto.mono_left nhdsWithin_le_nhds)
          (hCont2.tendsto.mono_left nhdsWithin_le_nhds) hEqEv
      · exact hPunct z' hz' hz0
  -- Now we prove the main goal using hAffine
  induction q using OnePoint.rec with
  | infty => -- none case (infinity)
    by_cases hz0 : z = 0
    · subst hz0
      have hCont1 : ContinuousAt (form.coeff (infty : HyperellipticOdd H Fact.out)) 0 := by
        have hAna : AnalyticAt ℂ (form.coeff (infty : HyperellipticOdd H Fact.out)) 0 :=
          (form.2.1 (infty : HyperellipticOdd H Fact.out)).analyticAt
            ((isOpen_extChartAt_target (infty : HyperellipticOdd H Fact.out)).mem_nhds hz)
        exact hAna.continuousAt
      have hCont2 : ContinuousAt ((hyperellipticOddForm H g).coeff
        (infty : HyperellipticOdd H Fact.out)) 0 := by
        have hAna : AnalyticAt ℂ ((hyperellipticOddForm H g).coeff
          (infty : HyperellipticOdd H Fact.out)) 0 :=
          ((hyperellipticOddForm H g).2.1 (infty : HyperellipticOdd H Fact.out)).analyticAt
            ((isOpen_extChartAt_target (infty : HyperellipticOdd H Fact.out)).mem_nhds hz)
        exact hAna.continuousAt
      have hPunct : ∀ w ∈ (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).target,
        w ≠ 0 → form.coeff (infty : HyperellipticOdd H Fact.out) w =
          (hyperellipticOddForm H g).coeff (infty : HyperellipticOdd H Fact.out) w := by
        intro w hw hwne
        generalize hq' : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm w = q'
        have h_right_inv : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)) q' = w := by
          rw [← hq']
          exact PartialEquiv.right_inv (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)) hw
        induction q' using OnePoint.rec with
        | infty => -- q' = infty (contradiction)
          change 0 = w at h_right_inv
          exact (hwne h_right_inv.symm).elim
        | coe a' => -- q' = coe a'
          have hsrc : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm w ∈
            (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)).source := by
            rw [hq']
            exact mem_extChartAt_source (coe a')
          have hCoord : (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out))
            ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm w) =
            (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)) (coe a') := by
            rw [hq']; rfl
          have hTarget' : (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)) (coe a') ∈
            (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)).target :=
            mem_extChartAt_target (coe a')
          have hCocycle1 := form.2.2.1 (infty : HyperellipticOdd H Fact.out)
            (coe a' : HyperellipticOdd H Fact.out) w hw hsrc
          have hCocycle2 := (hyperellipticOddForm H g).2.2.1 (infty : HyperellipticOdd H Fact.out)
            (coe a' : HyperellipticOdd H Fact.out) w hw hsrc
          rw [hCoord] at hCocycle1 hCocycle2
          have hEq := hAffine a' ((extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out))
            (coe a')) hTarget'
          unfold HolomorphicOneForm.coeff at hEq
          unfold HolomorphicOneForm.coeff
          rw [hCocycle1, hCocycle2, hEq]
      have hEqEv : form.coeff (infty : HyperellipticOdd H Fact.out) =ᶠ[𝓝[≠] (0 : ℂ)]
        (hyperellipticOddForm H g).coeff (infty : HyperellipticOdd H Fact.out) := by
        rw [eventuallyEq_nhdsWithin_iff]
        filter_upwards [(isOpen_extChartAt_target (infty : HyperellipticOdd H
          Fact.out)).mem_nhds hz]
          with w hw hwne
        exact hPunct w hw hwne
      exact tendsto_nhds_unique_of_eventuallyEq
        (hCont1.tendsto.mono_left nhdsWithin_le_nhds)
        (hCont2.tendsto.mono_left nhdsWithin_le_nhds) hEqEv
    · -- z ≠ 0 case (same cocycle logic)
      generalize hq' : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm z = q'
      have h_right_inv : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)) q' = z := by
        rw [← hq']
        exact PartialEquiv.right_inv (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)) hz
      induction q' using OnePoint.rec with
      | infty => -- q' = infty (contradiction)
        change 0 = z at h_right_inv
        exact (hz0 h_right_inv.symm).elim
      | coe a' => -- q' = coe a'
        have hsrc : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm z ∈
          (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)).source := by
          rw [hq']
          exact mem_extChartAt_source (coe a')
        have hCoord : (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out))
          ((extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H Fact.out)).symm z) =
          (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)) (coe a') := by
          rw [hq']; rfl
        have hTarget' : (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)) (coe a') ∈
          (extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out)).target :=
          mem_extChartAt_target (coe a')
        have hCocycle1 := form.2.2.1 (infty : HyperellipticOdd H Fact.out)
          (coe a' : HyperellipticOdd H Fact.out) z hz hsrc
        have hCocycle2 := (hyperellipticOddForm H g).2.2.1 (infty : HyperellipticOdd H Fact.out)
          (coe a' : HyperellipticOdd H Fact.out) z hz hsrc
        rw [hCoord] at hCocycle1 hCocycle2
        have hEq := hAffine a' ((extChartAt 𝓘(ℂ, ℂ) (coe a' : HyperellipticOdd H Fact.out))
          (coe a')) hTarget'
        change form.coeff (infty : HyperellipticOdd H Fact.out) z =
          (hyperellipticOddForm H g).coeff (infty : HyperellipticOdd H Fact.out) z
        unfold HolomorphicOneForm.coeff at hEq
        unfold HolomorphicOneForm.coeff
        rw [hCocycle1, hCocycle2, hEq]
  | coe a => -- some a case
    exact hAffine a z hz

lemma hSmoothY_proof (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (g : Polynomial ℂ) (hDeg : g.natDegree < (H.f.natDegree - 1) / 2)
    (hgEval : ∀ z : ℂ, liouvilleRemovableNumerator form z = Polynomial.eval z g)
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (z : ℂ) (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target) :
    form.coeff (coe a) z = (hyperellipticOddForm H g).coeff (coe a) z := by
  have hExt : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target =
      (affineChartProjX a hpY).target := by
    rw [extChartAt_target]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ]
    change (affineLiftChart a).target = (affineChartProjX a hpY).target
    unfold affineLiftChart
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    change (HyperellipticAffine.affineChartAt a :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target =
        (affineChartProjX a hpY).target
    rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a hpY]
  have hzX : z ∈ (affineChartProjX a hpY).target := by
    rwa [← hExt]
  have hFormCoeff : form.coeff (coe a) z =
    g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z) := by
    rw [← hgEval z]
    exact liouvilleRemovableNumerator_readout form a hpY hzX
  have hCanCoeff : (hyperellipticOddForm H g).coeff (coe a) z =
    g.eval z / (squareLocalHomeomorph a hpY).symm (H.f.eval z) := by
    exact hyperellipticOddForm_coeff_projX_apply g hDeg a hpY hzX
  rw [hFormCoeff, hCanCoeff]

theorem AX_HyperellipticOddOneForm_eq_form_proof
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∃ g : Polynomial ℂ, g.natDegree < (H.f.natDegree - 1) / 2 ∧
      form = hyperellipticOddForm H g := by
  classical
  obtain ⟨R, hR, hBound⟩ :=
    liouvilleRemovableNumerator_eventually_norm_div_pow_le (H := H) form
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
  apply oneForm_eq_hyperellipticOddForm_of_eqOn_chartTarget form g
  intro q z hz
  exact representation_singular_cases form g (fun a hpY z' hz' =>
    hSmoothY_proof form g hDeg hgEval a hpY z' hz') q z hz

theorem symmetric_form_eq_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (h_symm : pullbackOneForm (hyperellipticInvolution H Fact.out)
      (hyperellipticInvolution_contMDiff H Fact.out) form = form) :
    form = 0 := by
  obtain ⟨g, hDeg, hg_eq⟩ := AX_HyperellipticOddOneForm_eq_form_proof form
  have hg_zero : g = 0 := by
    have h_prod_zero : g * H.f = 0 := by
      apply Polynomial.zero_of_eval_zero
      intro z
      by_cases hz : H.f.eval z = 0
      · simp only [Polynomial.eval_mul, hz, mul_zero]
      · have h_g_zero : g.eval z = 0 := by
          let a := liouvilleChosenAffinePoint (H := H) z
          have haY : a ∈ smoothLocusY H :=
            liouvilleChosenAffinePoint_mem_smoothLocusY hz
          have haSrc : a ∈ (affineChartProjX a haY).source :=
            affineChartProjX_mem_source a haY
          have hzX : z ∈ (affineChartProjX a haY).target := by
            have h := (affineChartProjX a haY).map_source haSrc
            change a.val.1 ∈ (affineChartProjX a haY).target at h
            rwa [liouvilleChosenAffinePoint_fst (H := H) z] at h
          have h_symm_z : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm z =
            coe a := by
            have h_symm : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) =
              (chartAt ℂ (coe a : HyperellipticOdd H Fact.out)).toPartialEquiv := by simp
            rw [h_symm]
            change (affineLiftChart a).symm z = coe a
            unfold affineLiftChart
            rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
            change coe ((HyperellipticAffine.affineChartAt a).symm z) = coe a
            rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a haY]
            congr 1
            exact OpenPartialHomeomorph.left_inv (affineChartProjX a haY) haSrc
          have ha_invol_Y : a.invol ∈ smoothLocusY H := by
            change a.invol.val.2 ≠ 0
            rw [HyperellipticAffine.invol_val]
            simp only [neg_ne_zero]
            exact haY
          have hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
            HyperellipticOdd H Fact.out)).symm z) ∈
            (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).source := by
            rw [h_symm_z]
            have h_invol_coe : hyperellipticInvolution H Fact.out (coe a) = coe a.invol := rfl
            rw [h_invol_coe]
            exact mem_extChartAt_source (coe a.invol)
          have h_eval_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out))
            (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H
              Fact.out)).symm z)) = z := by
            rw [h_symm_z]
            have h_invol_coe : hyperellipticInvolution H Fact.out (coe a) = coe a.invol := rfl
            rw [h_invol_coe]
            have h_coord : (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out))
              (coe a.invol) = a.invol.val.1 := by
              change (affineLiftChart a.invol) (OnePoint.some a.invol) = a.invol.val.1
              unfold affineLiftChart
              rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
              change (HyperellipticAffine.affineChartAt a.invol) a.invol = a.invol.val.1
              rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a.invol ha_invol_Y]
              rfl
            rw [h_coord]
            change a.val.1 = z
            exact liouvilleChosenAffinePoint_fst (H := H) z
          have hz_invol_target : z ∈ (affineChartProjX a.invol ha_invol_Y).target := by
            have h_map :=
              (extChartAt 𝓘(ℂ, ℂ) (coe a.invol : HyperellipticOdd H Fact.out)).map_source
                hy_src
            rw [h_eval_eq] at h_map
            rw [extChartAt_target] at h_map
            simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
              Set.range_id, Set.inter_univ] at h_map
            change z ∈ (affineLiftChart a.invol).target at h_map
            unfold affineLiftChart at h_map
            rw [OpenPartialHomeomorph.lift_openEmbedding_target] at h_map
            change z ∈ (affineChartAt a.invol).target at h_map
            rw [affineChartAt_of_mem_smoothLocusY a.invol ha_invol_Y] at h_map
            exact h_map
          have h_coeff_eq := pullback_coeff_eq_invol form a haY hzX hy_src
          rw [h_symm] at h_coeff_eq
          have h_coeff_a : form.coeff (coe a) z = (hyperellipticOddForm H g).coeff (coe a) z := by
            rw [hg_eq]
          have h_coeff_invol : form.coeff (coe a.invol) z =
            (hyperellipticOddForm H g).coeff (coe a.invol) z := by
            rw [hg_eq]
          rw [h_coeff_a, hyperellipticOddForm_coeff_projX_apply g hDeg a haY hzX] at h_coeff_eq
          rw [h_coeff_invol, hyperellipticOddForm_coeff_projX_apply g hDeg a.invol ha_invol_Y
            hz_invol_target] at h_coeff_eq
          set y := (squareLocalHomeomorph a haY).symm (H.f.eval z) with hy_def
          have h_y_eq : a.val.2 = y := by
            have h_symm_a : (affineChartProjX a haY).symm z = a := by
              have h_fst : (affineChartProjX a haY) a = z := by
                change a.val.1 = z
                exact liouvilleChosenAffinePoint_fst (H := H) z
              rw [← h_fst]
              exact (affineChartProjX a haY).left_inv haSrc
            have ha_snd' := affineChartProjX_symm_apply_snd a haY hzX
            rwa [h_symm_a] at ha_snd'
          have h_invol_y_eq : a.invol.val.2 = -y := by
            rw [HyperellipticAffine.invol_val, h_y_eq]
          have h_y_ne : y ≠ 0 := by
            rw [← h_y_eq]
            exact haY
          have h_invol_y_eq_symm : (squareLocalHomeomorph a.invol ha_invol_Y).symm (H.f.eval z) =
            -y := by
            have ha_invol_src : a.invol ∈ (affineChartProjX a.invol ha_invol_Y).source :=
              affineChartProjX_mem_source a.invol ha_invol_Y
            have h_symm_invol : (affineChartProjX a.invol ha_invol_Y).symm z = a.invol := by
              have h_fst : (affineChartProjX a.invol ha_invol_Y) a.invol = z := by
                change a.invol.val.1 = z
                rw [HyperellipticAffine.invol_val]
                exact liouvilleChosenAffinePoint_fst (H := H) z
              rw [← h_fst]
              exact (affineChartProjX a.invol ha_invol_Y).left_inv ha_invol_src
            have ha_invol_snd :=
              affineChartProjX_symm_apply_snd a.invol ha_invol_Y hz_invol_target
            rw [h_symm_invol] at ha_invol_snd
            rw [← ha_invol_snd]
            exact h_invol_y_eq
          rw [h_invol_y_eq_symm] at h_coeff_eq
          have h_div_eq : g.eval z / y = - (g.eval z / y) := by
            calc g.eval z / y = g.eval z / -y := h_coeff_eq
            _ = - (g.eval z / y) := by ring
          have h_add_self : g.eval z / y + g.eval z / y = 0 := by
            have h_step : g.eval z / y + g.eval z / y = - (g.eval z / y) + g.eval z / y :=
              congrArg (· + g.eval z / y) h_div_eq
            rw [h_step]
            ring
          have h_mul_two : 2 * (g.eval z / y) = 0 := by
            calc 2 * (g.eval z / y) = g.eval z / y + g.eval z / y := by ring
            _ = 0 := h_add_self
          have h_div_zero : g.eval z / y = 0 := by
            have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
            exact (mul_eq_zero.mp h_mul_two).resolve_left h_two_ne
          exact (div_eq_zero_iff.mp h_div_zero).resolve_right h_y_ne
        simp only [Polynomial.eval_mul, h_g_zero, zero_mul]
    have h_f_nz : H.f ≠ 0 := hyperelliptic_f_ne_zero
    cases mul_eq_zero.mp h_prod_zero with
    | inl h1 => exact h1
    | inr h2 => contradiction
  rw [hg_zero, hyperellipticOddForm_zero] at hg_eq
  exact hg_eq

theorem _root_.pullback_hyperellipticInvolution_eq_neg_proof
    (H : HyperellipticData) [Fact (Odd H.f.natDegree)] :
    pullbackOneForm (hyperellipticInvolution H Fact.out)
        (hyperellipticInvolution_contMDiff H Fact.out)
      = (-LinearMap.id : HolomorphicOneForm (HyperellipticOdd H Fact.out) →ₗ[ℂ]
          HolomorphicOneForm (HyperellipticOdd H Fact.out)) := by
  refine LinearMap.ext (fun form => ?_)
  let T := pullbackOneForm (hyperellipticInvolution H Fact.out)
    (hyperellipticInvolution_contMDiff H Fact.out)
  have h_invol : T.comp T = LinearMap.id := pullback_involutive
  have h_invol_apply : ∀ x, T (T x) = x := by
    intro x
    have h_comp := LinearMap.congr_fun h_invol x
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h_comp
    exact h_comp
  let u := form + T form
  have hu_symm : T u = u := by
    dsimp [u]
    rw [map_add]
    rw [h_invol_apply]
    rw [add_comm]
  have hu_zero : u = 0 := symmetric_form_eq_zero u hu_symm
  change form + T form = 0 at hu_zero
  have h_neg : T form = - form := by
    rw [add_comm] at hu_zero
    rw [add_eq_zero_iff_eq_neg] at hu_zero
    exact hu_zero
  simp only [LinearMap.neg_apply, LinearMap.id_apply]
  exact h_neg

theorem pullback_hyperellipticInvolution_eq_neg_axiom_eq_proof :
    pullback_hyperellipticInvolution_eq_neg_axiom (H := H) =
      pullback_hyperellipticInvolution_eq_neg_proof H :=
  rfl

end Jacobians.Extensions.HyperellipticOdd
