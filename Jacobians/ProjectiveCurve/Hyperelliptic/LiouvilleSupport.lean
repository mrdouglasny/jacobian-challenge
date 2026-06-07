/-
# Local support lemmas for Liouville L2

This file contains small, axiom-free pieces of the Liouville-L2 pipeline for
even-degree hyperelliptic curves. The global theorem still needs the hard
single-valued entire extension and infinity-growth arguments, but on any
smooth-`Y` projX chart the numerator `ω_x · y` is already a well-defined local
analytic function.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Form
import Jacobians.ProjectiveCurve.Hyperelliptic.Involution
import Jacobians.GeneralResults.EntireGrowth

namespace Jacobians.ProjectiveCurve

open scoped Manifold ContDiff Topology
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticAffineInfinity
open Jacobians.ProjectiveCurve.HyperellipticEvenProj

variable {H : HyperellipticData} [hf : Fact (¬ Odd H.f.natDegree)]

/-- The affine branch point over a root `x` of `H.f`: `(x, 0)`. -/
def liouvilleBranchPoint (x : ℂ) (hx : H.f.eval x = 0) : HyperellipticAffine H :=
  ⟨(x, 0), by simp [hx]⟩

omit hf in
/-- At a branch point, squarefreeness gives `f'(x) ≠ 0`, so the `w = y`
chart is valid. -/
theorem liouvilleBranchPoint_mem_smoothLocusX {x : ℂ} (hx : H.f.eval x = 0) :
    liouvilleBranchPoint (H := H) x hx ∈ smoothLocusX H := by
  unfold liouvilleBranchPoint smoothLocusX
  exact eval_derivative_ne_zero_of_eval_eq_zero H hx

omit hf in
/-- A branch point has `y = 0`, so it is not in the projX smooth-`Y` locus. -/
theorem liouvilleBranchPoint_not_mem_smoothLocusY {x : ℂ} (hx : H.f.eval x = 0) :
    liouvilleBranchPoint (H := H) x hx ∉ smoothLocusY H := by
  intro hY
  exact hY rfl

/-- The local Liouville numerator on a smooth-`Y` projX chart:
`form.coeff q z * y(z)`, where `y(z)` is the IFT branch of `sqrt (H.f.eval z)`.

The hard Liouville-L2 work is to show that these local numerators glue to a
single entire function of `z` and satisfy the infinity growth bound. -/
noncomputable def liouvilleProjXNumerator
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) : ℂ → ℂ :=
  fun z =>
    form.coeff q z *
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z)

/-- The coefficient of a one-form in the affine `x`-coordinate attached to `a`.

If the quotient representative of `mk (inl a)` is affine, this is the form's
own coefficient. If the representative is the infinity-side point, this pulls
the coefficient back through the elementary transition `u = 1 / x`,
`du = -dx / x^2`. -/
noncomputable def affCoeff
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) : ℂ → ℂ :=
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  match Quotient.out q with
  | Sum.inl _ => form.coeff q
  | Sum.inr _ => fun z => form.coeff q (1 / z) * (-1 / z ^ 2)

/-- When the preferred quotient representative of `mk (inl a)` is affine,
`affCoeff` reduces to the original chart coefficient. -/
theorem affCoeff_of_inl
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a a' : HyperellipticAffine H)
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inl a') :
    affCoeff (H := H) form a =
      form.coeff (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) := by
  simp [affCoeff, hQ]

/-- A form coefficient is analytic on the explicit smooth-`Y` projX target when
`q`'s chosen representative is the corresponding affine point. -/
theorem form_coeff_analyticOn_affineProjX_target
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a) :
    AnalyticOn ℂ (form.coeff q) (affineChartProjX (H := H) a hpY).target := by
  have hform : AnalyticOn ℂ (form.coeff q) (extChartAt 𝓘(ℂ, ℂ) q).target :=
    form.2.1 q
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((HyperellipticEvenProj.chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    change
      ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
          Set.range ↑𝓘(ℂ, ℂ) =
        (HyperellipticEvenProj.chartAt H hf.out q).target
    change _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt] at hform
  unfold HyperellipticEvenProj.chartAt at hform
  rw [hQ] at hform
  simp only [HyperellipticEvenProj.affineLiftChart,
    OpenPartialHomeomorph.lift_openEmbedding_target] at hform
  simpa [affineChartAt, hpY] using hform

/-- `affCoeff` is analytic on the affine `x`-chart target in the affine
representative branch. -/
theorem affCoeff_analyticOn_of_inl
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {a' : HyperellipticAffine H}
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inl a') :
    AnalyticOn ℂ (affCoeff (H := H) form a)
      ((affineChartProjX (H := H) a hpY).target ∩ {z | z ≠ 0}) := by
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  have hQq : Quotient.out q = Sum.inl a' := by
    simpa [q] using hQ
  have hOutEq : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a') = q := by
    rw [← hQq]
    exact Quotient.out_eq q
  have ha' : a' = a := by
    exact HyperellipticEvenProj.proj_inl_injective H (by
      simpa [q, HyperellipticEvenProj.proj, Function.comp_def] using hOutEq)
  have hQa : Quotient.out q = Sum.inl a := by
    simpa [q, ha'] using hQ
  have hEq : affCoeff (H := H) form a = form.coeff q := by
    simpa [q] using affCoeff_of_inl (H := H) form a a' hQ
  rw [hEq]
  exact (form_coeff_analyticOn_affineProjX_target form a hpY q hQa).mono
    Set.inter_subset_left

/-- If the preferred representative of `mk (inl a)` is on the infinity side,
then it is exactly the gluing image of `a`; in particular the affine
`x`-coordinate of `a` is nonzero and the infinity representative is in the
smooth-`Y` locus for the reversed curve. -/
theorem affCoeff_inr_out_eq_affineGluingImage
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {b : HyperellipticAffineInfinity H}
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inr b) :
    ∃ hx : a.val.1 ≠ 0,
      b = affineGluingImage a hx ∧
        b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  have hProj : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b) := by
    have hOut : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b) = q := by
      rw [← hQ]
      exact Quotient.out_eq q
    exact hOut.symm
  obtain ⟨hx, hb⟩ := proj_inl_eq_proj_inr_iff (H := H) hProj
  refine ⟨hx, hb, ?_⟩
  simpa [hb] using affineGluingImage_mem_smoothLocusY (H := H) a hpY hx

/-- In the infinity-representative branch, the basepoint inverse coordinate is
in the infinity lifted chart target. This is the basepoint version of the
chart-transfer domain mapping. -/
theorem affCoeff_inr_base_inv_mem_infinityLiftChart_target
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {b : HyperellipticAffineInfinity H}
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inr b) :
    a.val.1⁻¹ ∈ (infinityLiftChart H hf.out b).target := by
  obtain ⟨hx, hb, hbY⟩ :=
    affCoeff_inr_out_eq_affineGluingImage (H := H) a hpY hQ
  have hbSrc : b ∈
      (HyperellipticAffine.affineChartAt
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b).source := by
    rw [affineChartAt_of_mem_smoothLocusY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY]
    exact affineChartProjX_mem_source
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY
  have hbTarget := (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b).map_source hbSrc
  rw [affineChartAt_of_mem_smoothLocusY
    (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY] at hbTarget
  change b.val.1 ∈
    (affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).target at hbTarget
  have hbTarget' :
      a.val.1⁻¹ ∈ (affineChartProjX
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).target := by
    simpa [hb, affineGluingImage_val_fst] using hbTarget
  simpa [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
    affineChartAt_of_mem_smoothLocusY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY] using hbTarget'

/-- Conditional pointwise domain mapping for the `x ↦ 1/x` chart transfer.
Once the gluing image of the affine chart point is known to lie in the
infinity chart source at `b`, its infinity `u`-coordinate is `z⁻¹`, hence
`z⁻¹` is in the infinity lifted chart target. -/
theorem inv_mem_infinityLiftChart_target_of_gluing_source
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hbY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target)
    (hx : (((affineChartProjX (H := H) a hpY).symm z :
      HyperellipticAffine H).val.1) ≠ 0)
    (hSrc : affineGluingImage
        (((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H)) hx ∈
      (HyperellipticAffine.affineChartAt
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b).source) :
    z⁻¹ ∈ (infinityLiftChart H hf.out b).target := by
  have hTarget := (HyperellipticAffine.affineChartAt
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b).map_source hSrc
  rw [affineChartAt_of_mem_smoothLocusY
    (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY] at hTarget
  change ((affineGluingImage
        (((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H)) hx).val.1) ∈
      (affineChartProjX
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).target at hTarget
  have hTarget' :
      z⁻¹ ∈ (affineChartProjX
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).target := by
    rw [affineGluingImage_val_fst] at hTarget
    rw [affineChartProjX_symm_apply_fst (H := H) a hpY hz] at hTarget
    exact hTarget
  simpa [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
    affineChartAt_of_mem_smoothLocusY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY] using hTarget'

/-- Analyticity of the `affCoeff` infinity branch once the chart-transfer
domain map has been supplied. The remaining geometric obligation is exactly
`z ∈ affine target`, `z ≠ 0` implies `z⁻¹ ∈ infinity target`. -/
theorem affCoeff_analyticOn_of_inr_of_mapsTo
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {b : HyperellipticAffineInfinity H}
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inr b)
    (hMaps : Set.MapsTo (fun z : ℂ => z⁻¹)
      ((affineChartProjX (H := H) a hpY).target ∩ {z | z ≠ 0})
      (infinityLiftChart H hf.out b).target) :
    AnalyticOn ℂ (affCoeff (H := H) form a)
      ((affineChartProjX (H := H) a hpY).target ∩ {z | z ≠ 0}) := by
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let domain : Set ℂ :=
    (affineChartProjX (H := H) a hpY).target ∩ {z | z ≠ 0}
  have hQq : Quotient.out q = Sum.inr b := by
    simpa [q] using hQ
  have hform : AnalyticOn ℂ (form.coeff q) (extChartAt 𝓘(ℂ, ℂ) q).target :=
    form.2.1 q
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (infinityLiftChart H hf.out b).target := by
    rw [extChartAt_target]
    change
      ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
          Set.range ↑𝓘(ℂ, ℂ) =
        (infinityLiftChart H hf.out b).target
    change _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    change (HyperellipticEvenProj.chartAt H hf.out q).target =
      (infinityLiftChart H hf.out b).target
    unfold HyperellipticEvenProj.chartAt
    rw [hQq]
  rw [hExt] at hform
  have hInv : AnalyticOn ℂ (fun z : ℂ => z⁻¹) domain := by
    exact (analyticOn_id.mono (Set.subset_univ _)).inv (by
      intro z hz
      exact hz.2)
  have hInvOne : AnalyticOn ℂ (fun z : ℂ => 1 / z) domain := by
    simpa [one_div] using hInv
  have hMapsOne : Set.MapsTo (fun z : ℂ => 1 / z) domain
      (infinityLiftChart H hf.out b).target := by
    simpa [domain, one_div] using hMaps
  have hCoeffComp : AnalyticOn ℂ (fun z : ℂ => form.coeff q (1 / z)) domain := by
    simpa [Function.comp_def] using hform.comp hInvOne hMapsOne
  have hPow : AnalyticOn ℂ (fun z : ℂ => z ^ 2) domain :=
    (analyticOn_id.mono (Set.subset_univ _)).pow 2
  have hInvPow : AnalyticOn ℂ (fun z : ℂ => (z ^ 2)⁻¹) domain :=
    hPow.inv (by
      intro z hz
      exact pow_ne_zero 2 hz.2)
  have hFactor : AnalyticOn ℂ (fun z : ℂ => -1 / z ^ 2) domain := by
    simpa [div_eq_mul_inv] using hInvPow.neg
  have hProd : AnalyticOn ℂ
      (fun z : ℂ => form.coeff q (1 / z) * (-1 / z ^ 2)) domain :=
    hCoeffComp.mul hFactor
  have hEq : affCoeff (H := H) form a =
      fun z : ℂ => form.coeff q (1 / z) * (-1 / z ^ 2) := by
    funext z
    simp [affCoeff, q, hQq]
  simpa [domain, hEq]
    using hProd

/-- On an affine-to-infinity chart overlap, `affCoeff` is the same affine
`x`-coordinate coefficient read through the cotangent cocycle. This is the
`Quotient.out = inl` / `Quotient.out = inr` branch of the overlap comparison. -/
theorem affCoeff_eq_of_overlap_inl_inr
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a a' : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {b : HyperellipticAffineInfinity H}
    (hbY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inl a)
    (hQ' : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a')) = Sum.inr b)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target)
    (hSrc : (affineLiftChart H hf.out a).symm z ∈
      (infinityLiftChart H hf.out b).source) :
    affCoeff (H := H) form a z = affCoeff (H := H) form a' z := by
  classical
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let q' : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a')
  have hQq : Quotient.out q = Sum.inl a := by
    simpa [q] using hQ
  have hQq' : Quotient.out q' = Sum.inr b := by
    simpa [q'] using hQ'
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      affineLiftChart H hf.out a := by
    change HyperellipticEvenProj.chartAt H hf.out q = _
    unfold HyperellipticEvenProj.chartAt
    rw [hQq]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      infinityLiftChart H hf.out b := by
    change HyperellipticEvenProj.chartAt H hf.out q' = _
    unfold HyperellipticEvenProj.chartAt
    rw [hQq']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (affineChartProjX (H := H) a hpY).target := by
    rw [extChartAt_target]
    change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineChartProjX (H := H) a hpY).target
    rw [hChQ]
    change (affineLiftChart H hf.out a).target ∩ Set.range (id : ℂ → ℂ) =
      (affineChartProjX (H := H) a hpY).target
    rw [Set.range_id, Set.inter_univ]
    simp [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt, hpY]
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      ((affineLiftChart H hf.out a).symm : ℂ → HyperellipticEvenProj H) := by
    funext w
    change (_root_.chartAt ℂ q).symm w = (affineLiftChart H hf.out a).symm w
    rw [hChQ]
  have hExtCoe' : ((extChartAt 𝓘(ℂ, ℂ) q') : HyperellipticEvenProj H → ℂ) =
      ((infinityLiftChart H hf.out b) : HyperellipticEvenProj H → ℂ) := by
    funext w
    change (_root_.chartAt ℂ q') w = (infinityLiftChart H hf.out b) w
    rw [hChQ']
  have hExtSrc' : (extChartAt 𝓘(ℂ, ℂ) q').source =
      (infinityLiftChart H hf.out b).source := by
    rw [extChartAt_source, hChQ']
  have hzExt : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
    rwa [hExtTarget]
  have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈
      (extChartAt 𝓘(ℂ, ℂ) q').source := by
    rw [hExtSymm, hExtSrc']
    exact hSrc
  have hOverlap : z ∈ ((affineLiftChart H hf.out a).symm.trans
      (infinityLiftChart H hf.out b)).source := by
    refine ⟨?_, hSrc⟩
    simpa [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt, hpY] using hz
  have hCoord : (extChartAt 𝓘(ℂ, ℂ) q')
      ((extChartAt 𝓘(ℂ, ℂ) q).symm z) = z⁻¹ := by
    rw [hExtCoe', hExtSymm]
    exact HyperellipticEvenProj.chart_transition_eq_inv_X_U a hpY b hbY hOverlap
  have hzNZ : z ≠ 0 := by
    have hSrc_unwound : (affineLiftChart H hf.out a).symm z ∈
        (infinityLiftChart H hf.out b).source := hSrc
    simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm, affineLiftChart] at hSrc_unwound
    rw [affineChartAt_of_mem_smoothLocusY a hpY] at hSrc_unwound
    obtain ⟨bb, _hbb_src, hbb_eq⟩ := hSrc_unwound
    have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
        (Sum.inl ((affineChartProjX (H := H) a hpY).symm z)) =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := hbb_eq.symm
    obtain ⟨hxNZ, _hbb⟩ := proj_inl_eq_proj_inr_iff (H := H) hbb_eq'
    rwa [affineChartProjX_symm_apply_fst (H := H) a hpY hz] at hxNZ
  have hOverlapOpen : IsOpen ((affineLiftChart H hf.out a).symm.trans
      (infinityLiftChart H hf.out b)).source :=
    ((affineLiftChart H hf.out a).symm.trans (infinityLiftChart H hf.out b)).open_source
  have hEqOn : (fun w : ℂ => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) =ᶠ[nhds z] (fun w => w⁻¹) := by
    refine Filter.eventually_of_mem (hOverlapOpen.mem_nhds hOverlap) ?_
    intro w hw
    exact HyperellipticEvenProj.chart_transition_eq_inv_X_U a hpY b hbY hw
  have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘
        (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 = -1 / z ^ 2 := by
    rw [hExtCoe', hExtSymm]
    change fderiv ℂ (fun w : ℂ => (infinityLiftChart H hf.out b)
        ((affineLiftChart H hf.out a).symm w)) z 1 = -1 / z ^ 2
    rw [Filter.EventuallyEq.fderiv_eq hEqOn]
    rw [fderiv_inv_apply_one hzNZ]
    field_simp [pow_ne_zero 2 hzNZ]
  have hCocy := form.2.2.1 q q' z hzExt hSrcExt
  have hCoeff : form.coeff q z = form.coeff q' (1 / z) * (-1 / z ^ 2) := by
    unfold HolomorphicOneForm.coeff
    rw [hCocy, hCoord, hDeriv]
    simp [one_div]
  have hAff : affCoeff (H := H) form a z = form.coeff q z := by
    simp [affCoeff, q, hQq]
  have hAff' : affCoeff (H := H) form a' z =
      form.coeff q' (1 / z) * (-1 / z ^ 2) := by
    simp [affCoeff, q', hQq']
  rw [hAff, hAff', hCoeff]

/-- Basepoint analyticity of the affine `x`-coefficient attached to a
smooth-`Y` affine point.

This is the pointwise form needed by the Liouville two-sheet sum: in the
infinity-representative branch it uses only the fact that the basepoint inverse
lies in the local infinity chart target, not a global `MapsTo` statement. -/
theorem affCoeff_analyticAt_basepoint
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H) :
    AnalyticAt ℂ (affCoeff (H := H) form a) a.val.1 := by
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  cases hQ : Quotient.out q with
  | inl a' =>
      have hQq : Quotient.out q = Sum.inl a' := by
        simpa using hQ
      have hOutEq : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a') = q := by
        rw [← hQq]
        exact Quotient.out_eq q
      have ha' : a' = a := by
        exact HyperellipticEvenProj.proj_inl_injective H (by
          simpa [q, HyperellipticEvenProj.proj, Function.comp_def] using hOutEq)
      have hQa : Quotient.out q = Sum.inl a := by
        simpa [ha'] using hQq
      have hEq : affCoeff (H := H) form a = form.coeff q := by
        simpa [q] using affCoeff_of_inl (H := H) form a a' hQq
      have haSrc : a ∈ (affineChartProjX (H := H) a hpY).source :=
        affineChartProjX_mem_source a hpY
      have haTarget : a.val.1 ∈ (affineChartProjX (H := H) a hpY).target := by
        simpa using (affineChartProjX (H := H) a hpY).map_source haSrc
      rw [hEq]
      exact AnalyticOn.analyticAt
        ((affineChartProjX (H := H) a hpY).open_target.mem_nhds haTarget)
        (form_coeff_analyticOn_affineProjX_target form a hpY q hQa)
  | inr b =>
      have hQq : Quotient.out q = Sum.inr b := by
        simpa using hQ
      obtain ⟨hx, _hb, _hbY⟩ :=
        affCoeff_inr_out_eq_affineGluingImage (H := H) a hpY hQq
      have hform : AnalyticOn ℂ (form.coeff q) (extChartAt 𝓘(ℂ, ℂ) q).target :=
        form.2.1 q
      have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
          (infinityLiftChart H hf.out b).target := by
        rw [extChartAt_target]
        change
          ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
              Set.range ↑𝓘(ℂ, ℂ) =
            (infinityLiftChart H hf.out b).target
        change _ ∩ Set.range (id : ℂ → ℂ) = _
        rw [Set.range_id, Set.inter_univ]
        change (HyperellipticEvenProj.chartAt H hf.out q).target =
          (infinityLiftChart H hf.out b).target
        unfold HyperellipticEvenProj.chartAt
        rw [hQq]
      rw [hExt] at hform
      have hbaseInv : a.val.1⁻¹ ∈ (infinityLiftChart H hf.out b).target :=
        affCoeff_inr_base_inv_mem_infinityLiftChart_target (H := H) a hpY hQq
      have hbaseOne : 1 / a.val.1 ∈ (infinityLiftChart H hf.out b).target := by
        simpa [one_div] using hbaseInv
      have hCoeffAt : AnalyticAt ℂ (form.coeff q) (1 / a.val.1) :=
        AnalyticOn.analyticAt
          ((infinityLiftChart H hf.out b).open_target.mem_nhds hbaseOne)
          hform
      have hInv : AnalyticAt ℂ (fun z : ℂ => z⁻¹) a.val.1 :=
        (analyticAt_id (𝕜 := ℂ) (z := a.val.1)).inv hx
      have hInvOne : AnalyticAt ℂ (fun z : ℂ => 1 / z) a.val.1 := by
        simpa [one_div] using hInv
      have hCoeffComp :
          AnalyticAt ℂ (fun z : ℂ => form.coeff q (1 / z)) a.val.1 := by
        simpa [Function.comp_def] using hCoeffAt.comp hInvOne
      have hPow : AnalyticAt ℂ (fun z : ℂ => z ^ 2) a.val.1 :=
        (analyticAt_id (𝕜 := ℂ) (z := a.val.1)).pow 2
      have hInvPow : AnalyticAt ℂ (fun z : ℂ => (z ^ 2)⁻¹) a.val.1 :=
        hPow.inv (pow_ne_zero 2 hx)
      have hFactor : AnalyticAt ℂ (fun z : ℂ => -1 / z ^ 2) a.val.1 := by
        convert hInvPow.neg using 1
        ext z
        simp [div_eq_mul_inv]
      have hProd : AnalyticAt ℂ
          (fun z : ℂ => form.coeff q (1 / z) * (-1 / z ^ 2)) a.val.1 :=
        hCoeffComp.mul hFactor
      have hEq : affCoeff (H := H) form a =
          fun z : ℂ => form.coeff q (1 / z) * (-1 / z ^ 2) := by
        funext z
        simp [affCoeff, q, hQq]
      simpa [hEq] using hProd

/-- The local Liouville numerator is analytic on the smooth-`Y` projX target. -/
theorem liouvilleProjXNumerator_analyticOn
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a) :
    AnalyticOn ℂ (liouvilleProjXNumerator (H := H) form a hpY q)
      (affineChartProjX (H := H) a hpY).target := by
  exact (form_coeff_analyticOn_affineProjX_target form a hpY q hQ).mul
    (squareLocalHomeomorph_symm_eval_analyticOn (H := H) a hpY)

/-- Pointwise form of `liouvilleProjXNumerator_analyticOn`, convenient when
assembling a global numerator by local charts. -/
theorem liouvilleProjXNumerator_analyticAt
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    AnalyticAt ℂ (liouvilleProjXNumerator (H := H) form a hpY q) z :=
  AnalyticOn.analyticAt
    ((affineChartProjX (H := H) a hpY).open_target.mem_nhds hz)
    (liouvilleProjXNumerator_analyticOn form a hpY q hQ)

omit hf in
/-- The branch-chart factor `w ↦ f'(x(w)) / 2`, where
`x(w) = polynomialLocalHomeomorph.symm (w ^ 2)`, is analytic on a projY chart. -/
theorem polynomialLocalHomeomorph_symm_sq_derivative_div_two_analyticOn
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H) :
    AnalyticOn ℂ
      (fun w : ℂ =>
        H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) / 2)
      (affineChartProjY (H := H) a hpX).target := by
  set e := polynomialLocalHomeomorph (H := H) a hpX with he
  set chartTarget :=
    ((affineChartProjY (H := H) a hpX) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target with htarget
  have hSq : AnalyticOn ℂ (fun w : ℂ => w ^ 2) chartTarget :=
    (analyticOn_id.pow 2).mono (Set.subset_univ _)
  have hSymm : AnalyticOn ℂ e.symm e.target := by
    have hCD : ContDiffOn ℂ ω e.symm e.target :=
      polynomialLocalHomeomorph_contDiffOn_symm (H := H) a hpX
    rw [show (ω : WithTop ℕ∞) = ⊤ from rfl] at hCD
    exact (contDiffOn_omega_iff_analyticOn (𝕜 := ℂ) (E := ℂ) (F := ℂ)
      e.open_target.uniqueDiffOn).mp hCD
  have hMaps : Set.MapsTo (fun w : ℂ => w ^ 2) chartTarget e.target := by
    intro w hw
    change w ^ 2 ∈ e.target
    simpa [chartTarget, affineChartProjY, e] using hw
  have hX : AnalyticOn ℂ (fun w : ℂ => e.symm (w ^ 2)) chartTarget :=
    hSymm.comp hSq hMaps
  have hDer : AnalyticOn ℂ
      (fun w : ℂ => H.f.derivative.eval (e.symm (w ^ 2))) chartTarget :=
    hX.aeval_polynomial H.f.derivative
  have hTwo : AnalyticOn ℂ (fun _ : ℂ => (2 : ℂ)) chartTarget :=
    analyticOn_const
  have hTwo_ne : ∀ w ∈ chartTarget, (2 : ℂ) ≠ 0 := by
    intro _ _
    norm_num
  have hHalf : AnalyticOn ℂ
      (fun w : ℂ => H.f.derivative.eval (e.symm (w ^ 2)) / 2) chartTarget :=
    hDer.div hTwo hTwo_ne
  simpa [chartTarget, e] using hHalf

/-- A form coefficient is analytic on an explicit smooth-`X` projY target when
the preferred affine representative is a branch-chart point (`a ∉ smoothLocusY`). -/
theorem form_coeff_analyticOn_affineProjY_target
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a) :
    AnalyticOn ℂ (form.coeff q) (affineChartProjY (H := H) a hpX).target := by
  have hform : AnalyticOn ℂ (form.coeff q) (extChartAt 𝓘(ℂ, ℂ) q).target :=
    form.2.1 q
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((HyperellipticEvenProj.chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    change
      ↑𝓘(ℂ, ℂ).symm ⁻¹' (HyperellipticEvenProj.chartAt H hf.out q).target ∩
          Set.range ↑𝓘(ℂ, ℂ) =
        (HyperellipticEvenProj.chartAt H hf.out q).target
    change _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt] at hform
  unfold HyperellipticEvenProj.chartAt at hform
  rw [hQ] at hform
  simp only [HyperellipticEvenProj.affineLiftChart,
    OpenPartialHomeomorph.lift_openEmbedding_target] at hform
  simpa [affineChartAt, hpYn] using hform

/-- The local branch-chart Liouville numerator in the `w = y` coordinate:
`form.coeff · f'(x(w))/2`. This is the algebraic cancellation from
`dx = (2w/f'(x)) dw`, and is the bounded expression at branch points. -/
noncomputable def liouvilleProjYNumerator
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (q : HyperellipticEvenProj H) : ℂ → ℂ :=
  fun w =>
    form.coeff q w *
      (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) / 2)

/-- The branch-chart Liouville numerator is analytic in the `w = y` coordinate
at branch-chart points. This packages the blueprint's local cancellation:
there is no `1 / w` singularity left. -/
theorem liouvilleProjYNumerator_analyticOn
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a) :
    AnalyticOn ℂ (liouvilleProjYNumerator (H := H) form a hpX q)
      (affineChartProjY (H := H) a hpX).target := by
  exact (form_coeff_analyticOn_affineProjY_target form a hpX hpYn q hQ).mul
    (polynomialLocalHomeomorph_symm_sq_derivative_div_two_analyticOn (H := H) a hpX)

/-- Branch-point specialization of `liouvilleProjYNumerator_analyticOn`.
This is the local bounded/holomorphic expression supplied by the `w = y`
coordinate at a root of `H.f`. -/
theorem liouvilleBranchPoint_numerator_analyticOn
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {x : ℂ} (hx : H.f.eval x = 0)
    (q : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl (liouvilleBranchPoint (H := H) x hx)) :
    AnalyticOn ℂ
      (liouvilleProjYNumerator (H := H) form
        (liouvilleBranchPoint (H := H) x hx)
        (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx) q)
      (affineChartProjY (H := H) (liouvilleBranchPoint (H := H) x hx)
        (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx)).target := by
  exact liouvilleProjYNumerator_analyticOn form
    (liouvilleBranchPoint (H := H) x hx)
    (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx)
    (liouvilleBranchPoint_not_mem_smoothLocusY (H := H) hx) q hQ

/-- Pointwise branch-chart analyticity at the branch coordinate `w = 0`. -/
theorem liouvilleBranchPoint_numerator_analyticAt_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {x : ℂ} (hx : H.f.eval x = 0)
    (q : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl (liouvilleBranchPoint (H := H) x hx)) :
    AnalyticAt ℂ
      (liouvilleProjYNumerator (H := H) form
        (liouvilleBranchPoint (H := H) x hx)
        (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx) q)
      0 := by
  let p := liouvilleBranchPoint (H := H) x hx
  let hpX := liouvilleBranchPoint_mem_smoothLocusX (H := H) hx
  have h0target : (0 : ℂ) ∈ (affineChartProjY (H := H) p hpX).target := by
    have hsrc : p ∈ (affineChartProjY (H := H) p hpX).source :=
      affineChartProjY_mem_source p hpX
    have htarget := (affineChartProjY (H := H) p hpX).map_source hsrc
    simpa [p, liouvilleBranchPoint] using htarget
  exact AnalyticOn.analyticAt
    ((affineChartProjY (H := H) p hpX).open_target.mem_nhds h0target)
    (liouvilleBranchPoint_numerator_analyticOn form hx q hQ)

/-- Dividing the local numerator by the nonzero chart branch recovers the chart
coefficient. This is the local algebraic readout used in the final L2 assembly. -/
theorem form_coeff_eq_liouvilleProjXNumerator_div
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) {z : ℂ}
    (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    form.coeff q z =
      liouvilleProjXNumerator (H := H) form a hpY q z /
        (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) := by
  unfold liouvilleProjXNumerator
  have hYne := squareLocalHomeomorph_symm_ne_zero (H := H) a hpY hz
  rw [mul_div_cancel_right₀ _ hYne]

/-- On a same-sheet overlap of two smooth-`Y` affine `x`-charts, the local
Liouville numerator `coeff · y` is independent of the chosen chart centre.

This is the basic gluing fact available directly from the `HolomorphicOneForm`
cotangent cocycle: the `x`-to-`x` transition is locally the identity, so the
coefficient is unchanged, and the two local `y`-branches agree on the overlap. -/
theorem liouvilleProjXNumerator_eq_of_projX_overlap
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a a' : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (hpY' : a' ∈ smoothLocusY H)
    (q q' : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl a) (hQ' : Quotient.out q' = Sum.inl a')
    {z : ℂ}
    (hz : z ∈ (affineChartProjX (H := H) a hpY).target)
    (hSrc : ((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H) ∈
      (affineChartProjX (H := H) a' hpY').source) :
    liouvilleProjXNumerator (H := H) form a hpY q z =
      liouvilleProjXNumerator (H := H) form a' hpY' q' z := by
  classical
  set c := affineLiftChart H hf.out a with hc_def
  set c' := affineLiftChart H hf.out a' with hc'_def
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      c := by
    change HyperellipticEvenProj.chartAt H hf.out q = c
    rw [hc_def]
    unfold HyperellipticEvenProj.chartAt
    rw [hQ]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      c' := by
    change HyperellipticEvenProj.chartAt H hf.out q' = c'
    rw [hc'_def]
    unfold HyperellipticEvenProj.chartAt
    rw [hQ']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (affineChartProjX (H := H) a hpY).target := by
    rw [extChartAt_target]
    change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineChartProjX (H := H) a hpY).target
    rw [hChQ]
    rw [hc_def]
    change _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    simp [affineLiftChart, affineChartAt, hpY]
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      (c.symm : ℂ → HyperellipticEvenProj H) := by
    funext w
    change (_root_.chartAt ℂ q).symm w = c.symm w
    rw [hChQ]
  have hExtCoe' : ((extChartAt 𝓘(ℂ, ℂ) q') : HyperellipticEvenProj H → ℂ) =
      (c' : HyperellipticEvenProj H → ℂ) := by
    funext w
    change (_root_.chartAt ℂ q') w = c' w
    rw [hChQ']
  have hExtSrc' : (extChartAt 𝓘(ℂ, ℂ) q').source = c'.source := by
    rw [extChartAt_source, hChQ']
  have hzExt : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
    rwa [hExtTarget]
  have hSrcLift : c.symm z ∈ c'.source := by
    rw [hc_def, hc'_def]
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm]
    refine ⟨(affineChartProjX (H := H) a hpY).symm z, ?_, ?_⟩
    · simpa [affineChartAt, hpY, hpY'] using hSrc
    · simp [HyperellipticEvenProj.proj, affineChartAt, hpY]
  have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈
      (extChartAt 𝓘(ℂ, ℂ) q').source := by
    rw [hExtSymm, hExtSrc']
    exact hSrcLift
  have hCoord : (extChartAt 𝓘(ℂ, ℂ) q')
      ((extChartAt 𝓘(ℂ, ℂ) q).symm z) = z := by
    rw [hExtCoe', hExtSymm]
    change (c.symm.trans c') z = z
    rw [hc_def, hc'_def]
    change (((affineChartAt (H := H) a).lift_openEmbedding
        (isOpenEmbedding_proj_inl H hf.out)).symm.trans
        ((affineChartAt (H := H) a').lift_openEmbedding
          (isOpenEmbedding_proj_inl H hf.out))) z = z
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
    change (affineChartAt (H := H) a')
        ((affineChartAt (H := H) a).symm z) = z
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a hpY]
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a' hpY']
    change (((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H).val.1) = z
    exact affineChartProjX_symm_apply_fst (H := H) a hpY hz
  have hOverlap : z ∈ (c.symm.trans c').source := ⟨by
    rw [hc_def]
    simpa [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt, hpY] using hz, hSrcLift⟩
  have hOverlapOpen : IsOpen (c.symm.trans c').source := (c.symm.trans c').open_source
  have hEqId : (fun w : ℂ => c' (c.symm w)) =ᶠ[nhds z] (fun w : ℂ => w) := by
    refine Filter.eventually_of_mem (hOverlapOpen.mem_nhds hOverlap) ?_
    intro w hw
    have hwTarget : w ∈ (affineChartProjX (H := H) a hpY).target := by
      have : w ∈ c.target := hw.1
      rw [hc_def] at this
      simpa [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
        affineChartAt, hpY] using this
    change (c.symm.trans c') w = w
    rw [hc_def, hc'_def]
    change (((affineChartAt (H := H) a).lift_openEmbedding
        (isOpenEmbedding_proj_inl H hf.out)).symm.trans
        ((affineChartAt (H := H) a').lift_openEmbedding
          (isOpenEmbedding_proj_inl H hf.out))) w = w
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
    change (affineChartAt (H := H) a')
        ((affineChartAt (H := H) a).symm w) = w
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a hpY]
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a' hpY']
    change (((affineChartProjX (H := H) a hpY).symm w : HyperellipticAffine H).val.1) = w
    exact affineChartProjX_symm_apply_fst (H := H) a hpY hwTarget
  have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘
        (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 = 1 := by
    rw [hExtCoe', hExtSymm]
    change fderiv ℂ (fun w : ℂ => c' (c.symm w)) z 1 = 1
    rw [Filter.EventuallyEq.fderiv_eq hEqId]
    simp
  have hCocy := form.2.2.1 q q' z hzExt hSrcExt
  have hCoeff : form.coeff q z = form.coeff q' z := by
    unfold HolomorphicOneForm.coeff
    rw [hCocy, hCoord, hDeriv, mul_one]
  have hSymInY :
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) ∈
        (squareLocalHomeomorph (H := H) a' hpY').source := by
    have h2 := affineChartProjX_symm_apply_snd (H := H) a hpY hz
    rw [← h2]
    exact hSrc
  have hAgree :
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) =
        (squareLocalHomeomorph (H := H) a' hpY').symm (H.f.eval z) :=
    squareLocalHomeomorph_symm_eq_of_mem (H := H) a a' hpY hpY' hz hSymInY
  unfold liouvilleProjXNumerator
  rw [hCoeff, hAgree]

/-- Algebraic sheet-swap helper for the Liouville numerator.

If the form coefficient changes sign and the chosen square-root branch changes
sign, then the product `coeff · y` is unchanged. The missing P1 input is the
geometric coefficient anti-invariance hypothesis for arbitrary holomorphic
forms. -/
theorem liouvilleProjXNumerator_eq_of_neg_coeff_neg_branch
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a a' : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (hpY' : a' ∈ smoothLocusY H)
    (q q' : HyperellipticEvenProj H)
    {z : ℂ}
    (hCoeff : form.coeff q z = -form.coeff q' z)
    (hBranch :
      (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) =
        -(squareLocalHomeomorph (H := H) a' hpY').symm (H.f.eval z)) :
    liouvilleProjXNumerator (H := H) form a hpY q z =
      liouvilleProjXNumerator (H := H) form a' hpY' q' z := by
  unfold liouvilleProjXNumerator
  rw [hCoeff, hBranch]
  ring

/-! ## Direct two-sheet coefficient sum -/

omit hf in
/-- The affine point `(z, y)` on the curve, where `y` is the globally chosen
square root of `H.f.eval z`. This is only a sheet-choice device; all analytic
statements below are formulated so they do not depend on continuity of this
choice. -/
noncomputable def liouvilleChosenAffinePoint (z : ℂ) : HyperellipticAffine H :=
  ⟨(z, (exists_complex_sq_eq (H.f.eval z)).choose), by
    simpa using (exists_complex_sq_eq (H.f.eval z)).choose_spec⟩

omit hf in
@[simp] lemma liouvilleChosenAffinePoint_fst (z : ℂ) :
    (liouvilleChosenAffinePoint (H := H) z).val.1 = z := rfl

omit hf in
/-- The chosen affine point has square equal to the defining polynomial value. -/
lemma liouvilleChosenAffinePoint_snd_sq (z : ℂ) :
    (liouvilleChosenAffinePoint (H := H) z).val.2 ^ 2 = H.f.eval z := by
  simpa using (liouvilleChosenAffinePoint (H := H) z).property

omit hf in
/-- Away from branch points, the chosen affine point lies in the smooth-`Y`
locus. -/
theorem liouvilleChosenAffinePoint_mem_smoothLocusY {z : ℂ}
    (hz : H.f.eval z ≠ 0) :
    liouvilleChosenAffinePoint (H := H) z ∈ smoothLocusY H := by
  unfold smoothLocusY
  intro hy
  have hsq := liouvilleChosenAffinePoint_snd_sq (H := H) z
  rw [hy] at hsq
  exact hz (by simpa using hsq.symm)

omit hf in
/-- The base coordinate of the involuted chosen point is still `z`. -/
@[simp] lemma liouvilleChosenAffinePoint_invol_fst (z : ℂ) :
    ((liouvilleChosenAffinePoint (H := H) z).invol).val.1 = z := rfl

/-- The fixed two-sheet coefficient sum for a pair of projective points. This is
the local expression whose vanishing is exactly coefficient anti-invariance. -/
noncomputable def liouvilleLocalSheetSum
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (q q' : HyperellipticEvenProj H) : ℂ → ℂ :=
  fun z => form.coeff q z + form.coeff q' z

/-- The global direct-route sheet sum, with an arbitrary branch value. The hard
DR-B step is precisely to replace this arbitrary value by the removable limit
and prove continuity at each branch point. -/
noncomputable def liouvilleTwoSheetSum
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) : ℂ → ℂ := by
  classical
  exact fun z =>
    if H.f.eval z = 0 then
      0
    else
      let a := liouvilleChosenAffinePoint (H := H) z
      affCoeff (H := H) form a z + affCoeff (H := H) form a.invol z

@[simp] theorem liouvilleTwoSheetSum_of_eval_eq_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z = 0) :
    liouvilleTwoSheetSum (H := H) form z = 0 := by
  simp [liouvilleTwoSheetSum, hz]

theorem liouvilleTwoSheetSum_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleTwoSheetSum (H := H) form z =
      affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z +
        affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z).invol z := by
  simp [liouvilleTwoSheetSum, hz]

/-- On the common clean affine `x`-chart target for the two sheets, the fixed
two-sheet coefficient sum is analytic. This is the kernel-clean DR-A local
analyticity statement; global single-valuedness still requires the symmetric
sheet-choice comparison, and branch continuity is DR-B. -/
theorem liouvilleLocalSheetSum_analyticOn_inter_affineProjX
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q q' : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl a)
    (hQ' : Quotient.out q' = Sum.inl a.invol) :
    AnalyticOn ℂ (liouvilleLocalSheetSum (H := H) form q q')
      ((affineChartProjX (H := H) a hpY).target ∩
        (affineChartProjX (H := H) a.invol
          (HyperellipticAffine.invol_mem_smoothLocusY a hpY)).target) := by
  exact
    ((form_coeff_analyticOn_affineProjX_target form a hpY q hQ).mono
      Set.inter_subset_left).add
    ((form_coeff_analyticOn_affineProjX_target form a.invol
      (HyperellipticAffine.invol_mem_smoothLocusY a hpY) q' hQ').mono
      Set.inter_subset_right)

/-- Pointwise version of the local DR-A analyticity statement. -/
theorem liouvilleLocalSheetSum_analyticAt_inter_affineProjX
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q q' : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl a)
    (hQ' : Quotient.out q' = Sum.inl a.invol)
    {z : ℂ}
    (hz : z ∈ (affineChartProjX (H := H) a hpY).target ∩
      (affineChartProjX (H := H) a.invol
        (HyperellipticAffine.invol_mem_smoothLocusY a hpY)).target) :
    AnalyticAt ℂ (liouvilleLocalSheetSum (H := H) form q q') z := by
  have hOpen : IsOpen
      ((affineChartProjX (H := H) a hpY).target ∩
        (affineChartProjX (H := H) a.invol
          (HyperellipticAffine.invol_mem_smoothLocusY a hpY)).target) :=
    (affineChartProjX (H := H) a hpY).open_target.inter
      (affineChartProjX (H := H) a.invol
        (HyperellipticAffine.invol_mem_smoothLocusY a hpY)).open_target
  exact AnalyticOn.analyticAt (hOpen.mem_nhds hz)
    (liouvilleLocalSheetSum_analyticOn_inter_affineProjX form a hpY q q' hQ hQ')

/-- The direct-route payoff at the algebraic level: if the local sheet sum
vanishes at `z`, the two coefficients are negatives. -/
theorem coeff_eq_neg_of_liouvilleLocalSheetSum_eq_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (q q' : HyperellipticEvenProj H) {z : ℂ}
    (hzero : liouvilleLocalSheetSum (H := H) form q q' z = 0) :
    form.coeff q z = -form.coeff q' z := by
  simpa [liouvilleLocalSheetSum, add_eq_zero_iff_eq_neg] using hzero

/-- If the global direct-route scalar has been proved identically zero, then
the chosen two sheets satisfy coefficient anti-invariance away from branch
points. DR-B/DR-C/DR-D are the missing analytic inputs needed to produce
`hzero`. -/
theorem chosen_coeff_eq_neg_of_liouvilleTwoSheetSum_eq_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hzero : ∀ z, liouvilleTwoSheetSum (H := H) form z = 0)
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z =
      -affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z).invol z := by
  have hs := hzero z
  rw [liouvilleTwoSheetSum_of_eval_ne_zero (H := H) form hz] at hs
  simpa [add_eq_zero_iff_eq_neg] using hs

/-- Sanity check against the existing explicit basis constructor: for
`hyperellipticForm H g`, the local Liouville numerator is exactly `g.eval`. -/
theorem liouvilleProjXNumerator_hyperellipticForm_eq
    {g : Polynomial ℂ} (hDeg : g.natDegree < H.f.natDegree / 2 - 1)
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    liouvilleProjXNumerator (H := H) (hyperellipticForm H g) a hpY q z =
      g.eval z := by
  unfold liouvilleProjXNumerator
  rw [hyperellipticForm_coeff_projX (H := H) hDeg hpY hQ hz]
  have hYne := squareLocalHomeomorph_symm_ne_zero (H := H) a hpY hz
  rw [div_mul_cancel₀ _ hYne]

/-- Sanity check in the branch coordinate: for the canonical form
`hyperellipticForm H g`, the cancelled projY numerator is `g(x(w))`. -/
theorem liouvilleProjYNumerator_hyperellipticForm_eq
    {g : Polynomial ℂ} (hDeg : g.natDegree < H.f.natDegree / 2 - 1)
    (a : HyperellipticAffine H) (hpX : a ∈ smoothLocusX H)
    (hpYn : a ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
    {w : ℂ} (hw : w ∈ (affineChartProjY (H := H) a hpX).target) :
    liouvilleProjYNumerator (H := H) (hyperellipticForm H g) a hpX q w =
      g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) := by
  unfold liouvilleProjYNumerator
  rw [hyperellipticForm_coeff_of_lt H hDeg]
  change (hyperellipticEvenCoeff (H := H) g (infReverse H g)) q w *
      (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) / 2) =
    g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))
  change (match Quotient.out q with
    | Sum.inl a => hyperellipticAffineCoeff (H := H) g a
    | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) (infReverse H g) b) w *
      (H.f.derivative.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2)) / 2) =
    g.eval ((polynomialLocalHomeomorph (H := H) a hpX).symm (w ^ 2))
  rw [hQ]
  simp only [hyperellipticAffineCoeff, hpYn, dite_false]
  rw [affineProjYCoeff_eq_on_target g a hpX hw]
  have hFne := polynomialLocalHomeomorph_symm_eval_derivative_ne_zero (H := H) a hpX hw
  field_simp [hFne]

/-- In the even-degree case, `H.f.natDegree / 2 ≥ 2`. This is the arithmetic
fact needed to turn `natDegree ≤ N/2 - 2` into `natDegree < N/2 - 1`. -/
theorem even_natDegree_div_two_ge_two : 2 ≤ H.f.natDegree / 2 := by
  have hdeg4 : 4 ≤ H.f.natDegree := by
    have hdeg := H.h_degree
    have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hf.out
    obtain ⟨m, hm⟩ := heven
    omega
  omega

/-- If `G z / z^n` has a finite limit at infinity and `G` is continuous, then
`G` satisfies a global polynomial growth bound of degree `n`.

The compact set inserted in the proof includes `0`, so the division by `z^n`
is only used where `z ≠ 0`; the compact part is bounded by continuity. -/
theorem polynomial_growth_bound_of_tendsto_div_pow
    (G : ℂ → ℂ) (n : ℕ) (c : ℂ)
    (hGcont : Continuous G)
    (hlim : Filter.Tendsto (fun z : ℂ => G z / z ^ n) (Filter.cocompact ℂ) (𝓝 c)) :
    ∃ C : ℝ, ∀ z : ℂ, ‖G z‖ ≤ C * (1 + ‖z‖) ^ n := by
  classical
  let R : ℝ := ‖c‖ + 1
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hmem : (fun z : ℂ => G z / z ^ n) ⁻¹' Metric.closedBall c 1 ∈
      Filter.cocompact ℂ :=
    hlim (Metric.closedBall_mem_nhds c zero_lt_one)
  rw [Filter.mem_cocompact] at hmem
  obtain ⟨K₀, hK₀, hK₀sub⟩ := hmem
  let K : Set ℂ := K₀ ∪ {0}
  have hK : IsCompact K := hK₀.union isCompact_singleton
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hGcont.continuousOn
  let C : ℝ := max M R
  have hC_nonneg : 0 ≤ C := le_trans hR_nonneg (le_max_right M R)
  refine ⟨C, ?_⟩
  intro z
  have hpow_one : (1 : ℝ) ≤ (1 + ‖z‖) ^ n :=
    one_le_pow₀ (by linarith [norm_nonneg z])
  by_cases hzK : z ∈ K
  · calc
      ‖G z‖ ≤ M := hM z hzK
      _ ≤ C := le_max_left M R
      _ ≤ C * (1 + ‖z‖) ^ n := by
        have := mul_le_mul_of_nonneg_left hpow_one hC_nonneg
        simpa using this
  · have hzK₀ : z ∉ K₀ := fun hz => hzK (Or.inl hz)
    have hz0 : z ≠ 0 := by
      intro hz
      apply hzK
      right
      simp [hz]
    have hzratio_mem :
        G z / z ^ n ∈ Metric.closedBall c 1 := hK₀sub hzK₀
    have hdist : dist (G z / z ^ n) c ≤ 1 := by
      simpa [Metric.mem_closedBall] using hzratio_mem
    have hratio : ‖G z / z ^ n‖ ≤ R := by
      calc
        ‖G z / z ^ n‖ = dist (G z / z ^ n) 0 := by
          rw [dist_zero_right]
        _ ≤ dist (G z / z ^ n) c + dist c 0 := dist_triangle _ _ _
        _ ≤ 1 + ‖c‖ := by
          rw [dist_zero_right]
          linarith
        _ = R := by
          ring
    have hzpow_ne : z ^ n ≠ 0 := pow_ne_zero n hz0
    have hnorm_pow_le : ‖z‖ ^ n ≤ (1 + ‖z‖) ^ n :=
      pow_le_pow_left₀ (norm_nonneg z) (by linarith [norm_nonneg z]) n
    calc
      ‖G z‖ = ‖(G z / z ^ n) * z ^ n‖ := by
        rw [div_mul_cancel₀ _ hzpow_ne]
      _ = ‖G z / z ^ n‖ * ‖z ^ n‖ := norm_mul _ _
      _ ≤ R * ‖z ^ n‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
      _ = R * ‖z‖ ^ n := by
        rw [norm_pow]
      _ ≤ C * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right (le_max_right M R) (pow_nonneg (norm_nonneg z) n)
      _ ≤ C * (1 + ‖z‖) ^ n :=
        mul_le_mul_of_nonneg_left hnorm_pow_le hC_nonneg

/-- **Liouville L2 assembly from the two hard analytic inputs.**

If a global numerator `G : ℂ → ℂ` has already been constructed, is entire, has
the infinity growth bound `N/2 - 2`, and reads out the local coefficients as
`G(z) / y(z)` on every smooth-`Y` projX chart, then Step 4
(`differentiable_eq_polynomial_of_growth`) gives the exact polynomial
decomposition required by Liouville L2. -/
theorem polynomial_decomposition_of_entire_growth
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (G : ℂ → ℂ) (hGdiff : Differentiable ℂ G)
    (C : ℝ)
    (hC : ∀ z, ‖G z‖ ≤ C * (1 + ‖z‖) ^ (H.f.natDegree / 2 - 2))
    (hReadout : ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
      (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
      {z : ℂ} (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
      form.coeff q z =
        G z / (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.f.natDegree / 2 - 1 ∧
      ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
        (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
        {z : ℂ}
        (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
        form.coeff q z =
          g.eval z / (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) := by
  obtain ⟨g, hgDeg, hgEval⟩ :=
    Jacobians.GeneralResults.differentiable_eq_polynomial_of_growth
      (H.f.natDegree / 2 - 2) G hGdiff C hC
  refine ⟨g, ?_, ?_⟩
  · have htwo : 2 ≤ H.f.natDegree / 2 := even_natDegree_div_two_ge_two (H := H)
    omega
  · intro a hpY q hQ z hz
    rw [← hgEval z]
    exact hReadout a hpY q hQ hz

/-- The L2 chart-local decomposition matches the canonical
`hyperellipticForm` coefficient on every smooth-`Y` projX chart. -/
theorem coeff_eq_hyperellipticForm_on_projX_of_decomposition
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {g : Polynomial ℂ}
    (hDeg : g.natDegree < H.f.natDegree / 2 - 1)
    (hDecomp : ∀ (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
      (q : HyperellipticEvenProj H) (_hQ : Quotient.out q = Sum.inl a)
      {z : ℂ} (_hz : z ∈ (affineChartProjX (H := H) a hpY).target),
      form.coeff q z =
        g.eval z / (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl a)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a hpY).target) :
    form.coeff q z = (hyperellipticForm H g).coeff q z := by
  rw [hDecomp a hpY q hQ hz]
  rw [hyperellipticForm_coeff_projX (H := H) hDeg hpY hQ hz]

/-- If an arbitrary holomorphic form and a canonical hyperelliptic form agree
on every preferred chart target, the off-target normalization in
`HolomorphicOneForm` upgrades the chartwise equality to equality of forms. -/
theorem oneForm_eq_hyperellipticForm_of_eqOn_chartTarget
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (g : Polynomial ℂ)
    (hCoeff : ∀ q : HyperellipticEvenProj H, ∀ z : ℂ,
      z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target →
        form.coeff q z = (hyperellipticForm H g).coeff q z) :
    form = hyperellipticForm H g := by
  apply HolomorphicOneForm.ext_of_coeff
  funext q z
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target
  · exact hCoeff q z hz
  · change (form : HyperellipticEvenProj H → ℂ → ℂ) q z =
      (hyperellipticForm H g : HyperellipticEvenProj H → ℂ → ℂ) q z
    rw [form.2.2.2 q z hz, (hyperellipticForm H g).2.2.2 q z hz]

omit hf in
/-- `H.f` is a nonzero polynomial. -/
theorem hyperelliptic_f_ne_zero : H.f ≠ 0 := by
  intro h
  have hd := H.h_degree
  rw [h, Polynomial.natDegree_zero] at hd
  omega

omit hf in
/-- The roots of `H.f` are isolated: on a punctured neighbourhood of any point,
`H.f.eval` is nonzero. This is the isolated-zeros input to the branch-point
removable-singularity step of `liouvilleGlobalNumerator`'s differentiability
(L2a). -/
theorem eventually_eval_ne_zero_nhdsWithin (z₀ : ℂ) :
    ∀ᶠ z in 𝓝[≠] z₀, H.f.eval z ≠ 0 := by
  have hfin : {x : ℂ | H.f.IsRoot x}.Finite :=
    Polynomial.finite_setOf_isRoot (hyperelliptic_f_ne_zero (H := H))
  set R' : Set ℂ := {x : ℂ | H.f.IsRoot x} \ {z₀} with hR'
  have hR'closed : IsClosed R' := (hfin.subset Set.diff_subset).isClosed
  have hmem : R'ᶜ ∈ 𝓝 z₀ :=
    hR'closed.isOpen_compl.mem_nhds (by simp [hR'])
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with z hz hzc
  intro hzero
  exact hzc ⟨hzero, hz⟩

omit hf in
/-- **Shared removable-singularity engine.** A function analytic off the roots of
`H.f` and globally continuous on `ℂ` is entire. The branch points (roots of
`H.f`) are isolated (`eventually_eval_ne_zero_nhdsWithin`), so analyticity on the
punctured neighbourhood plus continuity at the point gives differentiability there
by Riemann's removable-singularity theorem.

Consumed by both the Mσ.4 single-valued-coefficient argument (`c` entire) and the
L2 Differentiable-`G` assembly (P4 in
`docs/planning/L2_DIFFERENTIABLE_G_BLUEPRINT.md`). The remaining content in each
caller is supplying the off-root analyticity and the global continuity (the
branch-point continuity being the genuine analytic work). -/
theorem differentiable_of_analyticAt_off_roots (g : ℂ → ℂ)
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 → AnalyticAt ℂ g z)
    (hCont : Continuous g) : Differentiable ℂ g := by
  intro z₀
  by_cases hz₀ : H.f.eval z₀ = 0
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ hCont.continuousAt).differentiableAt
    filter_upwards [eventually_eval_ne_zero_nhdsWithin (H := H) z₀] with z hz
    exact (hAna z hz).differentiableAt
  · exact (hAna z₀ hz₀).differentiableAt

/-- **Liouville endgame.** An entire function tending to `0` at infinity (along
the cocompact filter) is identically `0`. The closing step of the direct-Liouville
core (Mσ.4 step 4): once the single-valued coefficient is entire and decays at the
points over `∞`, it vanishes, hence the form does. Proved via the degree-`0`
growth bound (continuity + decay ⇒ boundedness) feeding
`differentiable_eq_polynomial_of_growth` (a bounded entire function is constant),
then uniqueness of the cocompact limit pins the constant to `0`. -/
theorem eq_zero_of_differentiable_tendsto_zero_cocompact (g : ℂ → ℂ)
    (hg : Differentiable ℂ g)
    (h0 : Filter.Tendsto g (Filter.cocompact ℂ) (𝓝 0)) :
    ∀ z, g z = 0 := by
  obtain ⟨C, hC⟩ := polynomial_growth_bound_of_tendsto_div_pow g 0 0 hg.continuous
    (by simpa using h0)
  obtain ⟨p, _hpdeg, hpeq⟩ :=
    Jacobians.GeneralResults.differentiable_eq_polynomial_of_growth 0 g hg C hC
  have hpc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero _hpdeg
  have hgc : ∀ z, g z = p.coeff 0 := fun z => by rw [hpeq z, hpc]; simp
  have hgconst : g = fun _ : ℂ => p.coeff 0 := funext hgc
  rw [hgconst] at h0
  have hzero : p.coeff 0 = 0 := tendsto_const_nhds_iff.mp h0
  exact fun z => by rw [hgc z, hzero]

/-! ## Direct two-sheet conditional assembly -/

/-- Continuity of the direct two-sheet sum from the exact branch-point
punctured-limit obligation.  This isolates the hard DR-B kernel: since
`liouvilleTwoSheetSum` is defined to be `0` at roots, the removable branch
limit must tend to `0`, not just to an arbitrary finite value. -/
theorem liouvilleTwoSheetSum_continuous_of_analyticAt_off_roots_and_branch_tendsto
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      Filter.Tendsto (liouvilleTwoSheetSum (H := H) form) (𝓝[≠] z) (𝓝 0)) :
    Continuous (liouvilleTwoSheetSum (H := H) form) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : H.f.eval z = 0
  · rw [continuousAt_iff_punctured_nhds]
    rw [liouvilleTwoSheetSum_of_eval_eq_zero (H := H) form hz]
    exact hBranch z hz
  · exact (hAna z hz).continuousAt

/-- DR-B payoff once off-root analyticity and continuity are supplied: the
banked removable-singularity engine makes the two-sheet sum entire. -/
theorem liouvilleTwoSheetSum_differentiable_of_analyticAt_off_roots_and_continuous
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z)
    (hCont : Continuous (liouvilleTwoSheetSum (H := H) form)) :
    Differentiable ℂ (liouvilleTwoSheetSum (H := H) form) :=
  differentiable_of_analyticAt_off_roots (H := H)
    (liouvilleTwoSheetSum (H := H) form) hAna hCont

/-- DR-B payoff packaged with the branch-limit obligation. -/
theorem liouvilleTwoSheetSum_differentiable_of_analyticAt_off_roots_and_branch_tendsto
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      Filter.Tendsto (liouvilleTwoSheetSum (H := H) form) (𝓝[≠] z) (𝓝 0)) :
    Differentiable ℂ (liouvilleTwoSheetSum (H := H) form) :=
  liouvilleTwoSheetSum_differentiable_of_analyticAt_off_roots_and_continuous
    (H := H) form hAna
    (liouvilleTwoSheetSum_continuous_of_analyticAt_off_roots_and_branch_tendsto
      (H := H) form hAna hBranch)

/-- DR-D: once DR-B gives differentiability and DR-C gives decay at infinity,
the banked Liouville endgame proves the direct two-sheet sum is identically
zero. -/
theorem liouvilleTwoSheetSum_eq_zero_of_differentiable_tendsto_zero_cocompact
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hdiff : Differentiable ℂ (liouvilleTwoSheetSum (H := H) form))
    (h0 : Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
      (Filter.cocompact ℂ) (𝓝 0)) :
    ∀ z, liouvilleTwoSheetSum (H := H) form z = 0 :=
  eq_zero_of_differentiable_tendsto_zero_cocompact
    (liouvilleTwoSheetSum (H := H) form) hdiff h0

/-- Fully conditional DR-B/C/D endgame: off-root analyticity, branch
punctured limits to the chosen root values, and cocompact decay imply
`liouvilleTwoSheetSum ≡ 0`. -/
theorem liouvilleTwoSheetSum_eq_zero_of_analyticAt_off_roots_branch_tendsto_cocompact
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      Filter.Tendsto (liouvilleTwoSheetSum (H := H) form) (𝓝[≠] z) (𝓝 0))
    (h0 : Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
      (Filter.cocompact ℂ) (𝓝 0)) :
    ∀ z, liouvilleTwoSheetSum (H := H) form z = 0 :=
  liouvilleTwoSheetSum_eq_zero_of_differentiable_tendsto_zero_cocompact
    (H := H) form
    (liouvilleTwoSheetSum_differentiable_of_analyticAt_off_roots_and_branch_tendsto
      (H := H) form hAna hBranch)
    h0

/-- Conditional anti-invariance payoff from the direct two-sheet route. -/
theorem chosen_coeff_eq_neg_of_analyticAt_off_roots_branch_tendsto_cocompact
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      Filter.Tendsto (liouvilleTwoSheetSum (H := H) form) (𝓝[≠] z) (𝓝 0))
    (h0 : Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
      (Filter.cocompact ℂ) (𝓝 0))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z =
      -affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z).invol z :=
  chosen_coeff_eq_neg_of_liouvilleTwoSheetSum_eq_zero (H := H) form
    (liouvilleTwoSheetSum_eq_zero_of_analyticAt_off_roots_branch_tendsto_cocompact
      (H := H) form hAna hBranch h0)
    hz

/-! ## Direct two-sheet removable extension -/

/-- The branch-removable extension of the direct two-sheet sum.  It agrees
with `liouvilleTwoSheetSum` away from the branch locus and fills each branch
point with the filter limit of the punctured two-sheet sum.  This is the
branch-value correction needed for DR-B: the original `liouvilleTwoSheetSum`
is intentionally kept unchanged for its off-branch payoff bridge. -/
noncomputable def liouvilleTwoSheetSumRemovable
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) : ℂ → ℂ :=
  fun z =>
    if H.f.eval z = 0 then
      Filter.limUnder (𝓝[≠] z) (liouvilleTwoSheetSum (H := H) form)
    else
      liouvilleTwoSheetSum (H := H) form z

@[simp] theorem liouvilleTwoSheetSumRemovable_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleTwoSheetSumRemovable (H := H) form z =
      liouvilleTwoSheetSum (H := H) form z := by
  simp [liouvilleTwoSheetSumRemovable, hz]

theorem liouvilleTwoSheetSumRemovable_of_eval_eq_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z = 0) :
    liouvilleTwoSheetSumRemovable (H := H) form z =
      Filter.limUnder (𝓝[≠] z) (liouvilleTwoSheetSum (H := H) form) := by
  simp [liouvilleTwoSheetSumRemovable, hz]

theorem liouvilleTwoSheetSumRemovable_eventuallyEq_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleTwoSheetSumRemovable (H := H) form =ᶠ[𝓝 z]
      liouvilleTwoSheetSum (H := H) form := by
  have hEval : ∀ᶠ w in 𝓝 z, H.f.eval w ≠ 0 :=
    (Polynomial.continuous H.f).continuousAt.eventually_ne hz
  filter_upwards [hEval] with w hw
  exact liouvilleTwoSheetSumRemovable_of_eval_ne_zero (H := H) form hw

theorem liouvilleTwoSheetSumRemovable_eventuallyEq_punctured
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (z : ℂ) :
    liouvilleTwoSheetSumRemovable (H := H) form =ᶠ[𝓝[≠] z]
      liouvilleTwoSheetSum (H := H) form := by
  filter_upwards [eventually_eval_ne_zero_nhdsWithin (H := H) z] with w hw
  exact liouvilleTwoSheetSumRemovable_of_eval_ne_zero (H := H) form hw

/-- Continuity of the corrected removable extension from the local existence
of each branch limit.  The hard DR-B kernel is exactly the `hBranch` input. -/
theorem liouvilleTwoSheetSumRemovable_continuous_of_analyticAt_off_roots_and_branch_tendsto
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      ∃ L : ℂ, Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
        (𝓝[≠] z) (𝓝 L)) :
    Continuous (liouvilleTwoSheetSumRemovable (H := H) form) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : H.f.eval z = 0
  · obtain ⟨L, hL⟩ := hBranch z hz
    rw [continuousAt_iff_punctured_nhds]
    rw [liouvilleTwoSheetSumRemovable_of_eval_eq_zero (H := H) form hz]
    have hToLim : Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
        (𝓝[≠] z)
        (𝓝 (Filter.limUnder (𝓝[≠] z) (liouvilleTwoSheetSum (H := H) form))) :=
      tendsto_nhds_limUnder ⟨L, hL⟩
    exact hToLim.congr'
      (liouvilleTwoSheetSumRemovable_eventuallyEq_punctured (H := H) form z).symm
  · exact (hAna z hz).continuousAt.congr
      (liouvilleTwoSheetSumRemovable_eventuallyEq_of_eval_ne_zero
        (H := H) form hz).symm

/-- Differentiability of the corrected removable extension from off-root
analyticity and branch limit existence, using the banked removable-singularity
engine. -/
theorem liouvilleTwoSheetSumRemovable_differentiable_of_analyticAt_off_roots_and_branch_tendsto
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      ∃ L : ℂ, Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
        (𝓝[≠] z) (𝓝 L)) :
    Differentiable ℂ (liouvilleTwoSheetSumRemovable (H := H) form) := by
  refine differentiable_of_analyticAt_off_roots (H := H)
    (liouvilleTwoSheetSumRemovable (H := H) form) ?_ ?_
  · intro z hz
    exact (hAna z hz).congr
      (liouvilleTwoSheetSumRemovable_eventuallyEq_of_eval_ne_zero
        (H := H) form hz).symm
  · exact
      liouvilleTwoSheetSumRemovable_continuous_of_analyticAt_off_roots_and_branch_tendsto
        (H := H) form hAna hBranch

/-- Liouville endgame for the corrected removable extension. -/
theorem liouvilleTwoSheetSumRemovable_eq_zero_of_analyticAt_off_roots_branch_tendsto_cocompact
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hAna : ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z)
    (hBranch : ∀ z : ℂ, H.f.eval z = 0 →
      ∃ L : ℂ, Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
        (𝓝[≠] z) (𝓝 L))
    (h0 : Filter.Tendsto (liouvilleTwoSheetSumRemovable (H := H) form)
      (Filter.cocompact ℂ) (𝓝 0)) :
    ∀ z, liouvilleTwoSheetSumRemovable (H := H) form z = 0 :=
  eq_zero_of_differentiable_tendsto_zero_cocompact
    (liouvilleTwoSheetSumRemovable (H := H) form)
    (liouvilleTwoSheetSumRemovable_differentiable_of_analyticAt_off_roots_and_branch_tendsto
      (H := H) form hAna hBranch)
    h0

theorem liouvilleTwoSheetSum_eq_zero_of_removable_eq_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hzero : ∀ z, liouvilleTwoSheetSumRemovable (H := H) form z = 0)
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleTwoSheetSum (H := H) form z = 0 := by
  have hz0 := hzero z
  rwa [liouvilleTwoSheetSumRemovable_of_eval_ne_zero (H := H) form hz] at hz0

/-- Conditional anti-invariance payoff from the corrected removable extension:
once `s̃ ≡ 0`, the original off-branch two-sheet sum vanishes and the existing
payoff bridge applies pointwise. -/
theorem chosen_coeff_eq_neg_of_liouvilleTwoSheetSumRemovable_eq_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (hzero : ∀ z, liouvilleTwoSheetSumRemovable (H := H) form z = 0)
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z =
      -affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z).invol z := by
  have hs : liouvilleTwoSheetSum (H := H) form z = 0 :=
    liouvilleTwoSheetSum_eq_zero_of_removable_eq_zero (H := H) form hzero hz
  rw [liouvilleTwoSheetSum_of_eval_ne_zero (H := H) form hz] at hs
  simpa [add_eq_zero_iff_eq_neg] using hs

end Jacobians.ProjectiveCurve
