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
import Jacobians.GeneralResults.OddPartDslope

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

omit hf in
/-- A chosen square root of the leading coefficient; it labels the two
infinity points in the even-degree compactification. -/
noncomputable def liouvilleInfinitySqrt (H : HyperellipticData) : ℂ :=
  (exists_complex_sq_eq H.f.leadingCoeff).choose

omit hf in
lemma liouvilleInfinitySqrt_sq (H : HyperellipticData) :
    liouvilleInfinitySqrt H ^ 2 = H.f.leadingCoeff :=
  (exists_complex_sq_eq H.f.leadingCoeff).choose_spec

omit hf in
lemma hyperelliptic_leadingCoeff_ne_zero : H.f.leadingCoeff ≠ 0 := by
  have hf0 : H.f ≠ 0 := by
    intro h
    have hd := H.h_degree
    rw [h, Polynomial.natDegree_zero] at hd
    omega
  exact Polynomial.leadingCoeff_ne_zero.mpr hf0

omit hf in
lemma liouvilleInfinitySqrt_ne_zero :
    liouvilleInfinitySqrt H ≠ 0 := by
  intro h
  have hs := liouvilleInfinitySqrt_sq H
  rw [h] at hs
  norm_num at hs
  exact hyperelliptic_leadingCoeff_ne_zero (H := H) hs.symm

omit hf in
lemma reverse_eval_zero_eq_leadingCoeff :
    (Polynomial.reverse H.f).eval 0 = H.f.leadingCoeff := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]

omit hf in
/-- The infinity point with positive chosen `u`-coordinate. -/
noncomputable def liouvilleInfinityPointPos (H : HyperellipticData) :
    HyperellipticAffineInfinity H :=
  ⟨(0, liouvilleInfinitySqrt H), by
    rw [reverse_eval_zero_eq_leadingCoeff (H := H)]
    exact liouvilleInfinitySqrt_sq H⟩

omit hf in
/-- The infinity point with negative chosen `u`-coordinate. -/
noncomputable def liouvilleInfinityPointNeg (H : HyperellipticData) :
    HyperellipticAffineInfinity H :=
  ⟨(0, -liouvilleInfinitySqrt H), by
    rw [reverse_eval_zero_eq_leadingCoeff (H := H)]
    simpa using liouvilleInfinitySqrt_sq H⟩

lemma liouvilleInfinityPointPos_mem_smoothLocusY :
    liouvilleInfinityPointPos H ∈
      smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
  show (liouvilleInfinityPointPos H).val.2 ≠ 0
  exact liouvilleInfinitySqrt_ne_zero (H := H)

lemma liouvilleInfinityPointNeg_mem_smoothLocusY :
    liouvilleInfinityPointNeg H ∈
      smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
  show (liouvilleInfinityPointNeg H).val.2 ≠ 0
  exact neg_ne_zero.mpr (liouvilleInfinitySqrt_ne_zero (H := H))

lemma quotient_out_eq_inr_of_infinity_fst_eq_zero
    (b : HyperellipticAffineInfinity H) (hb0 : b.val.1 = 0) :
    Quotient.out (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)) = Sum.inr b := by
  classical
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)
  have hOut : Quotient.mk (hyperellipticEvenSetoid H) (Quotient.out q) = q :=
    Quotient.out_eq q
  cases hQ : Quotient.out q with
  | inl a =>
      have hEq :
          Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) =
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b) := by
        simpa [q, hQ] using hOut
      obtain ⟨haNZ, hb⟩ := proj_inl_eq_proj_inr_iff (H := H) hEq
      have hbNZ : b.val.1 ≠ 0 := by
        rw [hb]
        exact inv_ne_zero haNZ
      exact False.elim (hbNZ hb0)
  | inr b' =>
      have hEq :
          Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b') =
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b) := by
        simpa [q, hQ] using hOut
      have hb' : b' = b := proj_inr_injective H hEq
      simp [hb']

lemma quotient_out_liouvilleInfinityPointPos :
    Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inr (liouvilleInfinityPointPos H))) =
      Sum.inr (liouvilleInfinityPointPos H) := by
  exact quotient_out_eq_inr_of_infinity_fst_eq_zero (H := H)
    (liouvilleInfinityPointPos H) rfl

lemma quotient_out_liouvilleInfinityPointNeg :
    Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inr (liouvilleInfinityPointNeg H))) =
      Sum.inr (liouvilleInfinityPointNeg H) := by
  exact quotient_out_eq_inr_of_infinity_fst_eq_zero (H := H)
    (liouvilleInfinityPointNeg H) rfl

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

/-- A form coefficient is analytic at the infinity coordinate `u = 0` for a
fixed smooth-`Y` infinity chart. -/
theorem form_coeff_analyticAt_infinity_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (b : HyperellipticAffineInfinity H)
    (hbY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (hb0 : b.val.1 = 0)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inr b) :
    AnalyticAt ℂ (form.coeff q) 0 := by
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
    rw [hQ]
  rw [hExt] at hform
  have hbSrc : b ∈
      (affineChartProjX
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).source :=
    affineChartProjX_mem_source
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY
  have h0target : (0 : ℂ) ∈ (infinityLiftChart H hf.out b).target := by
    have hmap := (affineChartProjX
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).map_source hbSrc
    have hbTarget : b.val.1 ∈
        (affineChartProjX
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).target := by
      change b.val.1 ∈
        (affineChartProjX
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).target at hmap
      exact hmap
    simpa [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt_of_mem_smoothLocusY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY, hb0]
      using hbTarget
  exact AnalyticOn.analyticAt
    ((infinityLiftChart H hf.out b).open_target.mem_nhds h0target) hform

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

/-- If the explicit affine-to-infinity gluing image lies in a fixed infinity
chart source, then the affine projective point lies in the lifted fixed
infinity chart source. -/
theorem quotient_mk_inl_mem_infinityLiftChart_source_of_gluing_mem
    (a : HyperellipticAffine H) (hx : a.val.1 ≠ 0)
    (b : HyperellipticAffineInfinity H)
    (hbY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (hmem : affineGluingImage a hx ∈
      (affineChartProjX
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY).source) :
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) ∈
      (infinityLiftChart H hf.out b).source := by
  simp only [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  refine ⟨affineGluingImage a hx, ?_, ?_⟩
  · simpa [affineChartAt_of_mem_smoothLocusY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY] using hmem
  · exact (proj_eq_affineGluingImage (H := H) a hx).symm

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

/-- On an affine-to-affine chart overlap, `affCoeff` is independent of the
smooth-`Y` chart centre. This is the `Quotient.out = inl` /
`Quotient.out = inl` branch of the overlap comparison: the coordinate
transition is the identity, so the cotangent cocycle has derivative `1`. -/
theorem affCoeff_eq_of_overlap_inl_inl
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a a' : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (hpY' : a' ∈ smoothLocusY H)
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inl a)
    (hQ' : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a')) = Sum.inl a')
    {z : ℂ}
    (hz : z ∈ (affineChartProjX (H := H) a hpY).target)
    (hSrc : ((affineChartProjX (H := H) a hpY).symm z :
        HyperellipticAffine H) ∈
      (affineChartProjX (H := H) a' hpY').source) :
    affCoeff (H := H) form a z = affCoeff (H := H) form a' z := by
  classical
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let q' : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a')
  let c := affineLiftChart H hf.out a
  let c' := affineLiftChart H hf.out a'
  have hQq : Quotient.out q = Sum.inl a := by
    simpa [q] using hQ
  have hQq' : Quotient.out q' = Sum.inl a' := by
    simpa [q'] using hQ'
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      c := by
    change HyperellipticEvenProj.chartAt H hf.out q = c
    unfold HyperellipticEvenProj.chartAt
    rw [hQq]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      c' := by
    change HyperellipticEvenProj.chartAt H hf.out q' = c'
    unfold HyperellipticEvenProj.chartAt
    rw [hQq']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (affineChartProjX (H := H) a hpY).target := by
    rw [extChartAt_target]
    change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineChartProjX (H := H) a hpY).target
    rw [hChQ]
    change c.target ∩ Set.range (id : ℂ → ℂ) =
      (affineChartProjX (H := H) a hpY).target
    rw [Set.range_id, Set.inter_univ]
    simp [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt, hpY]
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
    simp only [c, c', affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
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
    simp [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt, hpY, hz], hSrcLift⟩
  have hOverlapOpen : IsOpen (c.symm.trans c').source := (c.symm.trans c').open_source
  have hEqId : (fun w : ℂ => c' (c.symm w)) =ᶠ[nhds z] (fun w : ℂ => w) := by
    refine Filter.eventually_of_mem (hOverlapOpen.mem_nhds hOverlap) ?_
    intro w hw
    have hwTarget : w ∈ (affineChartProjX (H := H) a hpY).target := by
      have : w ∈ c.target := hw.1
      simpa [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
        affineChartAt, hpY] using this
    change (c.symm.trans c') w = w
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
  have hAff : affCoeff (H := H) form a z = form.coeff q z := by
    simp [affCoeff, q, hQq]
  have hAff' : affCoeff (H := H) form a' z = form.coeff q' z := by
    simp [affCoeff, q', hQq']
  rw [hAff, hAff', hCoeff]

/-- On an infinity-to-infinity chart overlap, `affCoeff` is independent of the
smooth-`Y` chart centre. Both sides unfold to the infinity-coordinate
coefficient at `1 / z`, multiplied by the same factor `-1 / z ^ 2`; the
infinity-coordinate transition itself is the identity. -/
theorem affCoeff_eq_of_overlap_inr_inr
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a a' : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (hpY' : a' ∈ smoothLocusY H)
    {b b' : HyperellipticAffineInfinity H}
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inr b)
    (hQ' : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a')) = Sum.inr b')
    {z : ℂ}
    (hu : 1 / z ∈ (infinityLiftChart H hf.out b).target)
    (hSrc : (infinityLiftChart H hf.out b).symm (1 / z) ∈
      (infinityLiftChart H hf.out b').source) :
    affCoeff (H := H) form a z = affCoeff (H := H) form a' z := by
  classical
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let q' : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a')
  let Hrev := HyperellipticAffineInfinity.reverseData H hf.out
  let c := infinityLiftChart H hf.out b
  let c' := infinityLiftChart H hf.out b'
  obtain ⟨_hx, _hb, hbY⟩ :=
    affCoeff_inr_out_eq_affineGluingImage (H := H) a hpY hQ
  obtain ⟨_hx', _hb', hbY'⟩ :=
    affCoeff_inr_out_eq_affineGluingImage (H := H) a' hpY' hQ'
  have hQq : Quotient.out q = Sum.inr b := by
    simpa [q] using hQ
  have hQq' : Quotient.out q' = Sum.inr b' := by
    simpa [q'] using hQ'
  have hChQ : (_root_.chartAt ℂ q : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      c := by
    change HyperellipticEvenProj.chartAt H hf.out q = c
    unfold HyperellipticEvenProj.chartAt
    rw [hQq]
  have hChQ' : (_root_.chartAt ℂ q' : OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) =
      c' := by
    change HyperellipticEvenProj.chartAt H hf.out q' = c'
    unfold HyperellipticEvenProj.chartAt
    rw [hQq']
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target = c.target := by
    rw [extChartAt_target]
    change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      c.target
    rw [hChQ]
    change c.target ∩ Set.range (id : ℂ → ℂ) = c.target
    rw [Set.range_id, Set.inter_univ]
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
  have huExt : 1 / z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
    rwa [hExtTarget]
  have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm (1 / z) ∈
      (extChartAt 𝓘(ℂ, ℂ) q').source := by
    rw [hExtSymm, hExtSrc']
    exact hSrc
  have huRev : 1 / z ∈ (affineChartProjX (H := Hrev) b hbY).target := by
    simpa [c, Hrev, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt_of_mem_smoothLocusY (H := Hrev) b hbY] using hu
  have hCoord : (extChartAt 𝓘(ℂ, ℂ) q')
      ((extChartAt 𝓘(ℂ, ℂ) q).symm (1 / z)) = 1 / z := by
    rw [hExtCoe', hExtSymm]
    change (c.symm.trans c') (1 / z) = 1 / z
    change (((affineChartAt (H := Hrev) b).lift_openEmbedding
        (isOpenEmbedding_proj_inr H hf.out)).symm.trans
        ((affineChartAt (H := Hrev) b').lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out))) (1 / z) = 1 / z
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
    change (affineChartAt (H := Hrev) b')
        ((affineChartAt (H := Hrev) b).symm (1 / z)) = 1 / z
    rw [affineChartAt_of_mem_smoothLocusY (H := Hrev) b hbY]
    rw [affineChartAt_of_mem_smoothLocusY (H := Hrev) b' hbY']
    change (((affineChartProjX (H := Hrev) b hbY).symm (1 / z) :
      HyperellipticAffine Hrev).val.1) = 1 / z
    exact affineChartProjX_symm_apply_fst (H := Hrev) b hbY huRev
  have hOverlap : 1 / z ∈ (c.symm.trans c').source := ⟨hu, hSrc⟩
  have hOverlapOpen : IsOpen (c.symm.trans c').source := (c.symm.trans c').open_source
  have hEqId : (fun w : ℂ => c' (c.symm w)) =ᶠ[nhds (1 / z)] (fun w : ℂ => w) := by
    refine Filter.eventually_of_mem (hOverlapOpen.mem_nhds hOverlap) ?_
    intro w hw
    have hwTarget : w ∈ (affineChartProjX (H := Hrev) b hbY).target := by
      have : w ∈ c.target := hw.1
      simpa [c, Hrev, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
        affineChartAt_of_mem_smoothLocusY (H := Hrev) b hbY] using this
    change (c.symm.trans c') w = w
    change (((affineChartAt (H := Hrev) b).lift_openEmbedding
        (isOpenEmbedding_proj_inr H hf.out)).symm.trans
        ((affineChartAt (H := Hrev) b').lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out))) w = w
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
    change (affineChartAt (H := Hrev) b')
        ((affineChartAt (H := Hrev) b).symm w) = w
    rw [affineChartAt_of_mem_smoothLocusY (H := Hrev) b hbY]
    rw [affineChartAt_of_mem_smoothLocusY (H := Hrev) b' hbY']
    change (((affineChartProjX (H := Hrev) b hbY).symm w :
      HyperellipticAffine Hrev).val.1) = w
    exact affineChartProjX_symm_apply_fst (H := Hrev) b hbY hwTarget
  have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) q') ∘
        (extChartAt 𝓘(ℂ, ℂ) q).symm) (1 / z) 1 = 1 := by
    rw [hExtCoe', hExtSymm]
    change fderiv ℂ (fun w : ℂ => c' (c.symm w)) (1 / z) 1 = 1
    rw [Filter.EventuallyEq.fderiv_eq hEqId]
    simp
  have hCocy := form.2.2.1 q q' (1 / z) huExt hSrcExt
  have hCoeff : form.coeff q (1 / z) = form.coeff q' (1 / z) := by
    unfold HolomorphicOneForm.coeff
    rw [hCocy, hCoord, hDeriv, mul_one]
  have hAff : affCoeff (H := H) form a z =
      form.coeff q (1 / z) * (-1 / z ^ 2) := by
    simp [affCoeff, q, hQq]
  have hAff' : affCoeff (H := H) form a' z =
      form.coeff q' (1 / z) * (-1 / z ^ 2) := by
    simp [affCoeff, q', hQq']
  rw [hAff, hAff', hCoeff]

/-- Compare `affCoeff` at a smooth-`Y` chart centre `a` with `affCoeff` at
the actual affine point reached by the `a`-chart at coordinate `z`.

The extra source hypothesis says that this reached point lies in the preferred
`Quotient.out` chart for `mk (inl a)`; near the basepoint it follows from
continuity and openness of that preferred chart source. -/
theorem affCoeff_eq_of_projX_symm
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ (affineChartProjX (H := H) a hpY).target)
    (hPrefSrc :
      Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl ((affineChartProjX (H := H) a hpY).symm z :
            HyperellipticAffine H)) ∈
        (_root_.chartAt ℂ
          (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) :
            OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source) :
    affCoeff (H := H) form a z =
      affCoeff (H := H) form
        ((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H) z := by
  classical
  let p : HyperellipticAffine H := (affineChartProjX (H := H) a hpY).symm z
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let q' : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p)
  have hpYp : p ∈ smoothLocusY H := by
    show p.val.2 ≠ 0
    have hne := squareLocalHomeomorph_symm_ne_zero (H := H) a hpY hz
    simpa [p, affineChartProjX_symm_apply_snd (H := H) a hpY hz] using hne
  have hpSrc : p ∈ (affineChartProjX (H := H) p hpYp).source :=
    affineChartProjX_mem_source (H := H) p hpYp
  have hpFst : p.val.1 = z := by
    simpa [p] using affineChartProjX_symm_apply_fst (H := H) a hpY hz
  have hzP : z ∈ (affineChartProjX (H := H) p hpYp).target := by
    have h : p.val.1 ∈ (affineChartProjX (H := H) p hpYp).target := by
      simpa using (affineChartProjX (H := H) p hpYp).map_source hpSrc
    simpa [hpFst] using h
  have hSymmP : (affineChartProjX (H := H) p hpYp).symm z = p := by
    have hMap : (affineChartProjX (H := H) p hpYp) p = p.val.1 := by
      change p.val.1 = p.val.1
      rfl
    rw [← hpFst, ← hMap]
    exact (affineChartProjX (H := H) p hpYp).left_inv hpSrc
  have hLiftA : (affineLiftChart H hf.out a).symm z = q' := by
    simp [q', p, affineLiftChart, affineChartAt_of_mem_smoothLocusY (H := H) a hpY,
      OpenPartialHomeomorph.lift_openEmbedding_symm, HyperellipticEvenProj.proj]
  have hLiftP : (affineLiftChart H hf.out p).symm z = q' := by
    simp [q', affineLiftChart, affineChartAt_of_mem_smoothLocusY (H := H) p hpYp,
      OpenPartialHomeomorph.lift_openEmbedding_symm, HyperellipticEvenProj.proj,
      hSymmP]
  have hPrefSrc' :
      q' ∈ (_root_.chartAt ℂ q' :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
    ChartedSpace.mem_chart_source q'
  have hPrefSrcQ : q' ∈ (_root_.chartAt ℂ q :
      OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source := by
    simpa [q, q', p] using hPrefSrc
  cases hQ : Quotient.out q with
  | inl a₁ =>
      have hQq : Quotient.out q = Sum.inl a₁ := by
        simpa using hQ
      have hOutEq : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a₁) = q := by
        rw [← hQq]
        exact Quotient.out_eq q
      have ha₁ : a₁ = a := by
        exact HyperellipticEvenProj.proj_inl_injective H (by
          simpa [q, HyperellipticEvenProj.proj, Function.comp_def] using hOutEq)
      have hQa : Quotient.out q = Sum.inl a := by
        simpa [ha₁] using hQq
      cases hQ' : Quotient.out q' with
      | inl p₁ =>
          have hQq' : Quotient.out q' = Sum.inl p₁ := by
            simpa using hQ'
          have hOutEq' :
              Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p₁) = q' := by
            rw [← hQq']
            exact Quotient.out_eq q'
          have hp₁ : p₁ = p := by
            exact HyperellipticEvenProj.proj_inl_injective H (by
              simpa [q', HyperellipticEvenProj.proj, Function.comp_def] using hOutEq')
          have hQp : Quotient.out q' = Sum.inl p := by
            simpa [hp₁] using hQq'
          have hSrc : ((affineChartProjX (H := H) a hpY).symm z :
              HyperellipticAffine H) ∈
              (affineChartProjX (H := H) p hpYp).source := by
            simpa [p] using hpSrc
          exact affCoeff_eq_of_overlap_inl_inl (H := H) form a p hpY hpYp
            hQa hQp hz hSrc
      | inr b' =>
          have hQq' : Quotient.out q' = Sum.inr b' := by
            simpa using hQ'
          obtain ⟨_hx', _hb', hbY'⟩ :=
            affCoeff_inr_out_eq_affineGluingImage (H := H) p hpYp hQq'
          have hSrcInf : q' ∈ (infinityLiftChart H hf.out b').source := by
            have h := hPrefSrc'
            change q' ∈ (HyperellipticEvenProj.chartAt H hf.out q').source at h
            unfold HyperellipticEvenProj.chartAt at h
            rw [hQq'] at h
            exact h
          have hSrc : (affineLiftChart H hf.out a).symm z ∈
              (infinityLiftChart H hf.out b').source := by
            rwa [hLiftA]
          exact affCoeff_eq_of_overlap_inl_inr (H := H) form a p hpY hbY'
            hQa hQq' hz hSrc
  | inr b =>
      have hQq : Quotient.out q = Sum.inr b := by
        simpa using hQ
      obtain ⟨_hx, _hb, hbY⟩ :=
        affCoeff_inr_out_eq_affineGluingImage (H := H) a hpY hQq
      have hSrcInf : q' ∈ (infinityLiftChart H hf.out b).source := by
        have h := hPrefSrcQ
        change q' ∈ (HyperellipticEvenProj.chartAt H hf.out q).source at h
        unfold HyperellipticEvenProj.chartAt at h
        rw [hQq] at h
        exact h
      have hOverlap : z ∈ ((affineLiftChart H hf.out a).symm.trans
          (infinityLiftChart H hf.out b)).source := by
        refine ⟨?_, ?_⟩
        · simpa [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt, hpY] using hz
        · change (affineLiftChart H hf.out a).symm z ∈
            (infinityLiftChart H hf.out b).source
          rw [hLiftA]
          exact hSrcInf
      have hCoordInv :
          (infinityLiftChart H hf.out b) q' = z⁻¹ := by
        rw [← hLiftA]
        exact HyperellipticEvenProj.chart_transition_eq_inv_X_U a hpY b hbY hOverlap
      have hCoordOne :
          (infinityLiftChart H hf.out b) q' = 1 / z := by
        simpa [one_div] using hCoordInv
      have hu : 1 / z ∈ (infinityLiftChart H hf.out b).target := by
        have hmap := (infinityLiftChart H hf.out b).map_source hSrcInf
        simpa [hCoordOne] using hmap
      have hSymmOne : (infinityLiftChart H hf.out b).symm (1 / z) = q' := by
        have hleft := (infinityLiftChart H hf.out b).left_inv hSrcInf
        simpa [hCoordOne] using hleft
      cases hQ' : Quotient.out q' with
      | inl p₁ =>
          have hQq' : Quotient.out q' = Sum.inl p₁ := by
            simpa using hQ'
          have hOutEq' :
              Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p₁) = q' := by
            rw [← hQq']
            exact Quotient.out_eq q'
          have hp₁ : p₁ = p := by
            exact HyperellipticEvenProj.proj_inl_injective H (by
              simpa [q', HyperellipticEvenProj.proj, Function.comp_def] using hOutEq')
          have hQp : Quotient.out q' = Sum.inl p := by
            simpa [hp₁] using hQq'
          have hSrc : (affineLiftChart H hf.out p).symm z ∈
              (infinityLiftChart H hf.out b).source := by
            rw [hLiftP]
            exact hSrcInf
          exact (affCoeff_eq_of_overlap_inl_inr (H := H) form p a hpYp hbY
            hQp hQq hzP hSrc).symm
      | inr b' =>
          have hQq' : Quotient.out q' = Sum.inr b' := by
            simpa using hQ'
          have hSrcInf' : q' ∈ (infinityLiftChart H hf.out b').source := by
            have h := hPrefSrc'
            change q' ∈ (HyperellipticEvenProj.chartAt H hf.out q').source at h
            unfold HyperellipticEvenProj.chartAt at h
            rw [hQq'] at h
            exact h
          have hSrc : (infinityLiftChart H hf.out b).symm (1 / z) ∈
              (infinityLiftChart H hf.out b').source := by
            rwa [hSymmOne]
          exact affCoeff_eq_of_overlap_inr_inr (H := H) form a p hpY hpYp
            hQq hQq' hu hSrc

/-- If an affine sheet lies in a fixed smooth infinity chart source, its
affine `x`-coefficient is the fixed infinity-chart coefficient pulled back by
`u = 1 / x`. -/
theorem affCoeff_eq_fixed_infinity_of_source
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (b : HyperellipticAffineInfinity H)
    (hbY : b ∈ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (hQInf : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)) = Sum.inr b)
    (hSrc :
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) ∈
        (infinityLiftChart H hf.out b).source) :
    affCoeff (H := H) form a a.val.1 =
      form.coeff (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)) (a.val.1⁻¹) *
        (-1 / a.val.1 ^ 2) := by
  classical
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let qInf : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)
  let z : ℂ := a.val.1
  let cA := affineLiftChart H hf.out a
  let cInf := infinityLiftChart H hf.out b
  have hzTarget : z ∈ (affineChartProjX (H := H) a hpY).target := by
    have haSrc : a ∈ (affineChartProjX (H := H) a hpY).source :=
      affineChartProjX_mem_source (H := H) a hpY
    have hmap := (affineChartProjX (H := H) a hpY).map_source haSrc
    change a.val.1 ∈ (affineChartProjX (H := H) a hpY).target at hmap
    simpa [z] using hmap
  have hzLiftTarget : z ∈ cA.target := by
    simpa [cA, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt_of_mem_smoothLocusY (H := H) a hpY] using hzTarget
  have hBaseSymm : cA.symm z = q := by
    have haSrc : a ∈ (affineChartProjX (H := H) a hpY).source :=
      affineChartProjX_mem_source (H := H) a hpY
    have hMap : (affineChartProjX (H := H) a hpY) a = a.val.1 := by
      rfl
    have hSymmA : (affineChartProjX (H := H) a hpY).symm z = a := by
      change (affineChartProjX (H := H) a hpY).symm a.val.1 = a
      rw [← hMap]
      exact (affineChartProjX (H := H) a hpY).left_inv haSrc
    simp [cA, q, z, affineLiftChart,
      affineChartAt_of_mem_smoothLocusY (H := H) a hpY,
      OpenPartialHomeomorph.lift_openEmbedding_symm, HyperellipticEvenProj.proj,
      hSymmA]
  have hxNZ : z ≠ 0 := by
    have hSrc_unwound : q ∈ cInf.source := by
      simpa [q, cInf] using hSrc
    simp only [cInf, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source]
      at hSrc_unwound
    obtain ⟨bb, _hbb_src, hbb_eq⟩ := hSrc_unwound
    have hbb_eq' :
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) =
          Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := by
      simpa [q] using hbb_eq.symm
    obtain ⟨hx, _⟩ := proj_inl_eq_proj_inr_iff (H := H) hbb_eq'
    simpa [z] using hx
  have hOverlapFixed : z ∈ (cA.symm.trans cInf).source := by
    refine ⟨hzLiftTarget, ?_⟩
    simpa [hBaseSymm, q, cInf] using hSrc
  have hCoordFixed : cInf q = z⁻¹ := by
    have h := HyperellipticEvenProj.chart_transition_eq_inv_X_U
      (H := H) a hpY b hbY hOverlapFixed
    simpa [cA, cInf, hBaseSymm] using h
  have hDerivFixed :
      fderiv ℂ (fun w : ℂ => cInf (cA.symm w)) z 1 = -1 / z ^ 2 := by
    have hOverlapOpen : IsOpen (cA.symm.trans cInf).source :=
      (cA.symm.trans cInf).open_source
    have hEqOn : (fun w : ℂ => cInf (cA.symm w)) =ᶠ[nhds z] (fun w => w⁻¹) := by
      refine Filter.eventually_of_mem (hOverlapOpen.mem_nhds hOverlapFixed) ?_
      intro w hw
      exact HyperellipticEvenProj.chart_transition_eq_inv_X_U
        (H := H) a hpY b hbY hw
    rw [Filter.EventuallyEq.fderiv_eq hEqOn]
    rw [fderiv_inv_apply_one hxNZ]
    field_simp [pow_ne_zero 2 hxNZ]
  cases hQ : Quotient.out q with
  | inl a' =>
      have hQq : Quotient.out q = Sum.inl a' := by simpa using hQ
      have hOutEq : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a') = q := by
        rw [← hQq]
        exact Quotient.out_eq q
      have ha' : a' = a := by
        exact HyperellipticEvenProj.proj_inl_injective H (by
          simpa [q, HyperellipticEvenProj.proj, Function.comp_def] using hOutEq)
      have hQa : Quotient.out q = Sum.inl a := by
        simpa [ha'] using hQq
      have hChQ : (_root_.chartAt ℂ q :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = cA := by
        change HyperellipticEvenProj.chartAt H hf.out q = cA
        unfold HyperellipticEvenProj.chartAt
        rw [hQa]
      have hChInf : (_root_.chartAt ℂ qInf :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = cInf := by
        change HyperellipticEvenProj.chartAt H hf.out qInf = cInf
        unfold HyperellipticEvenProj.chartAt
        rw [show Quotient.out qInf = Sum.inr b by simpa [qInf] using hQInf]
      have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
          (affineChartProjX (H := H) a hpY).target := by
        rw [extChartAt_target]
        change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
          (affineChartProjX (H := H) a hpY).target
        rw [hChQ]
        change cA.target ∩ Set.range (id : ℂ → ℂ) =
          (affineChartProjX (H := H) a hpY).target
        rw [Set.range_id, Set.inter_univ]
        simp [cA, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
          affineChartAt_of_mem_smoothLocusY (H := H) a hpY]
      have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
          (cA.symm : ℂ → HyperellipticEvenProj H) := by
        funext w
        change (_root_.chartAt ℂ q).symm w = cA.symm w
        rw [hChQ]
      have hExtCoeInf : ((extChartAt 𝓘(ℂ, ℂ) qInf) : HyperellipticEvenProj H → ℂ) =
          (cInf : HyperellipticEvenProj H → ℂ) := by
        funext w
        change (_root_.chartAt ℂ qInf) w = cInf w
        rw [hChInf]
      have hExtSrcInf : (extChartAt 𝓘(ℂ, ℂ) qInf).source = cInf.source := by
        rw [extChartAt_source, hChInf]
      have hzExt : z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
        rwa [hExtTarget]
      have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm z ∈
          (extChartAt 𝓘(ℂ, ℂ) qInf).source := by
        rw [hExtSymm, hExtSrcInf, hBaseSymm]
        simpa [q, cInf] using hSrc
      have hCoord : (extChartAt 𝓘(ℂ, ℂ) qInf)
          ((extChartAt 𝓘(ℂ, ℂ) q).symm z) = z⁻¹ := by
        rw [hExtCoeInf, hExtSymm, hBaseSymm]
        exact hCoordFixed
      have hDeriv :
          fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) qInf) ∘
            (extChartAt 𝓘(ℂ, ℂ) q).symm) z 1 = -1 / z ^ 2 := by
        rw [hExtCoeInf, hExtSymm]
        exact hDerivFixed
      have hCocy := form.2.2.1 q qInf z hzExt hSrcExt
      have hCoeff : form.coeff q z =
          form.coeff qInf (z⁻¹) * (-1 / z ^ 2) := by
        unfold HolomorphicOneForm.coeff
        rw [hCocy, hCoord, hDeriv]
      have hAff : affCoeff (H := H) form a z = form.coeff q z := by
        simp [affCoeff, q, hQa]
      simpa [qInf, z] using hAff.trans hCoeff
  | inr b' =>
      have hQq : Quotient.out q = Sum.inr b' := by simpa using hQ
      obtain ⟨_hx', _hb', hbY'⟩ :=
        affCoeff_inr_out_eq_affineGluingImage (H := H) a hpY hQq
      let c' := infinityLiftChart H hf.out b'
      have hChQ : (_root_.chartAt ℂ q :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = c' := by
        change HyperellipticEvenProj.chartAt H hf.out q = c'
        unfold HyperellipticEvenProj.chartAt
        rw [hQq]
      have hChInf : (_root_.chartAt ℂ qInf :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = cInf := by
        change HyperellipticEvenProj.chartAt H hf.out qInf = cInf
        unfold HyperellipticEvenProj.chartAt
        rw [show Quotient.out qInf = Sum.inr b by simpa [qInf] using hQInf]
      have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target = c'.target := by
        rw [extChartAt_target]
        change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
          c'.target
        rw [hChQ]
        change c'.target ∩ Set.range (id : ℂ → ℂ) = c'.target
        rw [Set.range_id, Set.inter_univ]
      have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
          (c'.symm : ℂ → HyperellipticEvenProj H) := by
        funext w
        change (_root_.chartAt ℂ q).symm w = c'.symm w
        rw [hChQ]
      have hExtCoeInf : ((extChartAt 𝓘(ℂ, ℂ) qInf) : HyperellipticEvenProj H → ℂ) =
          (cInf : HyperellipticEvenProj H → ℂ) := by
        funext w
        change (_root_.chartAt ℂ qInf) w = cInf w
        rw [hChInf]
      have hExtSrcInf : (extChartAt 𝓘(ℂ, ℂ) qInf).source = cInf.source := by
        rw [extChartAt_source, hChInf]
      have hu : 1 / z ∈ c'.target := by
        have hbase := affCoeff_inr_base_inv_mem_infinityLiftChart_target
          (H := H) a hpY hQq
        simpa [c', z, one_div] using hbase
      have huExt : 1 / z ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
        rwa [hExtTarget]
      have hSrcSelf : q ∈ c'.source := by
        have h : q ∈ (_root_.chartAt ℂ q :
            OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
          ChartedSpace.mem_chart_source q
        change q ∈ (HyperellipticEvenProj.chartAt H hf.out q).source at h
        unfold HyperellipticEvenProj.chartAt at h
        rw [hQq] at h
        exact h
      have hOverlapSelf : z ∈ (cA.symm.trans c').source := by
        refine ⟨hzLiftTarget, ?_⟩
        simpa [hBaseSymm] using hSrcSelf
      have hCoordSelf : c' q = z⁻¹ := by
        have h := HyperellipticEvenProj.chart_transition_eq_inv_X_U
          (H := H) a hpY b' hbY' hOverlapSelf
        simpa [cA, c', hBaseSymm] using h
      have hSymmOne : c'.symm (1 / z) = q := by
        have hleft := c'.left_inv hSrcSelf
        simpa [one_div, hCoordSelf] using hleft
      have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm (1 / z) ∈
          (extChartAt 𝓘(ℂ, ℂ) qInf).source := by
        rw [hExtSymm, hExtSrcInf, hSymmOne]
        simpa [q, cInf] using hSrc
      have hCoord : (extChartAt 𝓘(ℂ, ℂ) qInf)
          ((extChartAt 𝓘(ℂ, ℂ) q).symm (1 / z)) = 1 / z := by
        rw [hExtCoeInf, hExtSymm, hSymmOne]
        simpa [one_div] using hCoordFixed
      have huRev : 1 / z ∈ (affineChartProjX
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b' hbY').target := by
        simpa [c', infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
          affineChartAt_of_mem_smoothLocusY
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b' hbY'] using hu
      have hOverlapInf : 1 / z ∈ (c'.symm.trans cInf).source := by
        refine ⟨hu, ?_⟩
        change c'.symm (1 / z) ∈ cInf.source
        rw [hSymmOne]
        simpa [q, cInf] using hSrc
      have hEqId : (fun w : ℂ => cInf (c'.symm w)) =ᶠ[nhds (1 / z)] (fun w : ℂ => w) := by
        have hOverlapOpen : IsOpen (c'.symm.trans cInf).source :=
          (c'.symm.trans cInf).open_source
        refine Filter.eventually_of_mem (hOverlapOpen.mem_nhds hOverlapInf) ?_
        intro w hw
        have hwTarget : w ∈ (affineChartProjX
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b' hbY').target := by
          have : w ∈ c'.target := hw.1
          simpa [c', infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt_of_mem_smoothLocusY
              (H := HyperellipticAffineInfinity.reverseData H hf.out) b' hbY'] using this
        change (c'.symm.trans cInf) w = w
        change (((affineChartAt
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b').lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out)).symm.trans
          ((affineChartAt
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b).lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out))) w = w
        rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
        change (affineChartAt
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b)
          ((affineChartAt
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b').symm w) = w
        rw [affineChartAt_of_mem_smoothLocusY
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b' hbY']
        rw [affineChartAt_of_mem_smoothLocusY
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY]
        change (((affineChartProjX
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b' hbY').symm w :
          HyperellipticAffine (HyperellipticAffineInfinity.reverseData H hf.out)).val.1) = w
        exact affineChartProjX_symm_apply_fst
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b' hbY' hwTarget
      have hDeriv :
          fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) qInf) ∘
            (extChartAt 𝓘(ℂ, ℂ) q).symm) (1 / z) 1 = 1 := by
        rw [hExtCoeInf, hExtSymm]
        change fderiv ℂ (fun w : ℂ => cInf (c'.symm w)) (1 / z) 1 = 1
        rw [Filter.EventuallyEq.fderiv_eq hEqId]
        simp
      have hCocy := form.2.2.1 q qInf (1 / z) huExt hSrcExt
      have hCoeff : form.coeff q (1 / z) = form.coeff qInf (1 / z) := by
        unfold HolomorphicOneForm.coeff
        rw [hCocy, hCoord, hDeriv, mul_one]
      have hAff : affCoeff (H := H) form a z =
          form.coeff q (1 / z) * (-1 / z ^ 2) := by
        simp [affCoeff, q, hQq]
      rw [hAff, hCoeff]
      simp [qInf, z]

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

/-- The odd-part difference quotient of the branch-chart numerator is analytic
at the branch coordinate. This is the local cancellation used in the branch
limit proof. -/
theorem liouvilleBranchPoint_numerator_dslope_analyticAt_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {x : ℂ} (hx : H.f.eval x = 0)
    (q : HyperellipticEvenProj H)
    (hQ : Quotient.out q = Sum.inl (liouvilleBranchPoint (H := H) x hx)) :
    AnalyticAt ℂ
      (dslope
        (fun w : ℂ =>
          liouvilleProjYNumerator (H := H) form
              (liouvilleBranchPoint (H := H) x hx)
              (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx) q w -
            liouvilleProjYNumerator (H := H) form
              (liouvilleBranchPoint (H := H) x hx)
              (liouvilleBranchPoint_mem_smoothLocusX (H := H) hx) q (-w))
        0) 0 := by
  exact Jacobians.GeneralResults.analyticAt_dslope_oddPart
    (liouvilleBranchPoint_numerator_analyticAt_zero (H := H) form hx q hQ)

/-- The infinity-side branch numerator in the `v` coordinate of the reversed
curve. This is the same cancellation as `liouvilleProjYNumerator`, but for a
branch point whose preferred representative is on the infinity summand. -/
noncomputable def liouvilleInfinityProjYNumerator
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (b : HyperellipticAffineInfinity H)
    (hpX : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (q : HyperellipticEvenProj H) : ℂ → ℂ :=
  fun v =>
    form.coeff q v *
      ((Polynomial.reverse H.f).derivative.eval
          ((polynomialLocalHomeomorph
            (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX).symm (v ^ 2)) / 2)

/-- A form coefficient is analytic on an infinity branch `v`-chart when the
preferred representative is the corresponding infinity point. -/
theorem form_coeff_analyticOn_infinityProjY_target
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (b : HyperellipticAffineInfinity H)
    (hpX : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hpYn : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inr b) :
    AnalyticOn ℂ (form.coeff q)
      (affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX).target := by
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
    rw [hQ]
  rw [hExt] at hform
  simpa [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
    affineChartAt_of_not_mem_smoothLocusY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpYn]
    using hform

/-- The infinity-side branch numerator is analytic in the branch coordinate. -/
theorem liouvilleInfinityProjYNumerator_analyticOn
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (b : HyperellipticAffineInfinity H)
    (hpX : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hpYn : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inr b) :
    AnalyticOn ℂ (liouvilleInfinityProjYNumerator (H := H) form b hpX q)
      (affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX).target := by
  exact (form_coeff_analyticOn_infinityProjY_target form b hpX hpYn q hQ).mul
    (polynomialLocalHomeomorph_symm_sq_derivative_div_two_analyticOn
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX)

/-- Pointwise infinity-side branch numerator analyticity at `v = 0`. -/
theorem liouvilleInfinityBranchPoint_numerator_analyticAt_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (b : HyperellipticAffineInfinity H)
    (hpX : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hpYn : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (hb0 : b.val.2 = 0)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inr b) :
    AnalyticAt ℂ (liouvilleInfinityProjYNumerator (H := H) form b hpX q) 0 := by
  have h0target : (0 : ℂ) ∈
      (affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX).target := by
    have hsrc : b ∈
        (affineChartProjY
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX).source :=
      affineChartProjY_mem_source (H := HyperellipticAffineInfinity.reverseData H hf.out)
        b hpX
    have htarget :=
      (affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX).map_source hsrc
    change b.val.2 ∈
      (affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX).target at htarget
    simpa [hb0] using htarget
  exact AnalyticOn.analyticAt
    ((affineChartProjY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hpX).open_target.mem_nhds
        h0target)
    (liouvilleInfinityProjYNumerator_analyticOn form b hpX hpYn q hQ)

/-- The odd-part difference quotient of the infinity-side branch numerator is
analytic at the branch coordinate. -/
theorem liouvilleInfinityBranchPoint_numerator_dslope_analyticAt_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (b : HyperellipticAffineInfinity H)
    (hpX : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hpYn : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (hb0 : b.val.2 = 0)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inr b) :
    AnalyticAt ℂ
      (dslope
        (fun v : ℂ =>
          liouvilleInfinityProjYNumerator (H := H) form b hpX q v -
            liouvilleInfinityProjYNumerator (H := H) form b hpX q (-v))
        0) 0 := by
  exact Jacobians.GeneralResults.analyticAt_dslope_oddPart
    (liouvilleInfinityBranchPoint_numerator_analyticAt_zero
      (H := H) form b hpX hpYn hb0 q hQ)

/-- Data extracted when an affine branch point is represented on the infinity
summand by `Quotient.out`. -/
theorem liouvilleBranchPoint_out_inr_data
    {x : ℂ} (hx : H.f.eval x = 0)
    {b : HyperellipticAffineInfinity H}
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (liouvilleBranchPoint (H := H) x hx))) = Sum.inr b) :
    ∃ hxNZ : x ≠ 0,
      b = affineGluingImage (liouvilleBranchPoint (H := H) x hx) (by
          simpa [liouvilleBranchPoint] using hxNZ) ∧
        b.val.2 = 0 ∧
        b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out) ∧
        b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
  let p := liouvilleBranchPoint (H := H) x hx
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p)
  have hProj : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p) =
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b) := by
    have hOut : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b) = q := by
      rw [← show Quotient.out q = Sum.inr b by simpa [q, p] using hQ]
      exact Quotient.out_eq q
    exact hOut.symm
  obtain ⟨hpNZ, hb⟩ := proj_inl_eq_proj_inr_iff (H := H) hProj
  have hxNZ : x ≠ 0 := by
    simpa [p, liouvilleBranchPoint] using hpNZ
  refine ⟨hxNZ, ?_, ?_, ?_, ?_⟩
  · simpa [p] using hb
  · simp [hb, p, liouvilleBranchPoint, affineGluingImage_val_snd]
  · exact mem_smoothLocusX_of_y_eq_zero
      (HyperellipticAffineInfinity.reverseData H hf.out) (by
        simp [hb, p, liouvilleBranchPoint, affineGluingImage_val_snd])
  · intro hbY
    exact hbY (by
      simp [hb, p, liouvilleBranchPoint, affineGluingImage_val_snd])

/-- Infinity-branch cancellation for a moving off-branch affine point. In the
preferred infinity branch coordinate `v`, the affine `dx` coefficient is
`-u(v)^2` times the odd-branch numerator divided by `v`, where
`u(v) = x^{-1}` is the reverse affine coordinate. -/
theorem affCoeff_eq_liouvilleInfinityProjYNumerator_div_of_branch
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (b : HyperellipticAffineInfinity H)
    (hbX : b ∈ smoothLocusX (HyperellipticAffineInfinity.reverseData H hf.out))
    (hbYn : b ∉ smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out))
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inr b)
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    (hx : a.val.1 ≠ 0)
    {v : ℂ}
    (hv : v ∈
      (affineChartProjY
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).target)
    (hvne : v ≠ 0)
    (hBranchSymm :
      (infinityLiftChart H hf.out b).symm v =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a))
    (hu_eq : (polynomialLocalHomeomorph
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbX).symm (v ^ 2) =
      a.val.1⁻¹) :
    affCoeff (H := H) form a a.val.1 =
      - (a.val.1⁻¹) ^ 2 *
        (liouvilleInfinityProjYNumerator (H := H) form b hbX q v / v) := by
  classical
  let Hrev := HyperellipticAffineInfinity.reverseData H hf.out
  let qA : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let c := infinityLiftChart H hf.out b
  have hChQ : (_root_.chartAt ℂ q :
      OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = c := by
    change HyperellipticEvenProj.chartAt H hf.out q = c
    unfold HyperellipticEvenProj.chartAt
    rw [hQ]
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target = c.target := by
    rw [extChartAt_target]
    change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      c.target
    rw [hChQ]
    change c.target ∩ Set.range (id : ℂ → ℂ) = c.target
    rw [Set.range_id, Set.inter_univ]
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      (c.symm : ℂ → HyperellipticEvenProj H) := by
    funext t
    change (_root_.chartAt ℂ q).symm t = c.symm t
    rw [hChQ]
  have hvExt : v ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
    rw [hExtTarget]
    simpa [c, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn, Hrev] using hv
  cases hQa : Quotient.out qA with
  | inl a' =>
      have hQqA : Quotient.out qA = Sum.inl a' := by simpa using hQa
      have hOutEq : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a') = qA := by
        rw [← hQqA]
        exact Quotient.out_eq qA
      have ha' : a' = a := by
        exact HyperellipticEvenProj.proj_inl_injective H (by
          simpa [qA, HyperellipticEvenProj.proj, Function.comp_def] using hOutEq)
      have hQqAa : Quotient.out qA = Sum.inl a := by
        simpa [ha'] using hQqA
      let cA := affineLiftChart H hf.out a
      have hqASrc : qA ∈ cA.source := by
        change (HyperellipticEvenProj.proj H (Sum.inl a)) ∈
          ((affineChartAt (H := H) a).lift_openEmbedding
            (isOpenEmbedding_proj_inl H hf.out)).source
        rw [OpenPartialHomeomorph.lift_openEmbedding_source]
        refine ⟨a, ?_, rfl⟩
        simpa [affineChartAt_of_mem_smoothLocusY (H := H) a haY] using
          affineChartProjX_mem_source (H := H) a haY
      have hChQA : (_root_.chartAt ℂ qA :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = cA := by
        change HyperellipticEvenProj.chartAt H hf.out qA = cA
        unfold HyperellipticEvenProj.chartAt
        rw [hQqAa]
      have hExtCoeA : ((extChartAt 𝓘(ℂ, ℂ) qA) : HyperellipticEvenProj H → ℂ) =
          (cA : HyperellipticEvenProj H → ℂ) := by
        funext t
        change (_root_.chartAt ℂ qA) t = cA t
        rw [hChQA]
      have hExtSrcA : (extChartAt 𝓘(ℂ, ℂ) qA).source = cA.source := by
        rw [extChartAt_source, hChQA]
      have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm v ∈
          (extChartAt 𝓘(ℂ, ℂ) qA).source := by
        rw [hExtSymm, hExtSrcA, hBranchSymm]
        exact hqASrc
      have hCoord : (extChartAt 𝓘(ℂ, ℂ) qA)
          ((extChartAt 𝓘(ℂ, ℂ) q).symm v) = a.val.1 := by
        rw [hExtCoeA, hExtSymm, hBranchSymm]
        change ((affineChartAt (H := H) a).lift_openEmbedding
            (isOpenEmbedding_proj_inl H hf.out))
          ((HyperellipticEvenProj.proj H ∘
            (Sum.inl : HyperellipticAffine H → HyperellipticEvenPre H)) a) = a.val.1
        rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
        rw [affineChartAt_of_mem_smoothLocusY (H := H) a haY]
        rfl
      have hOverlap : v ∈ (c.symm.trans cA).source := by
        refine ⟨?_, ?_⟩
        · simpa [c, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn, Hrev] using hv
        · change c.symm v ∈ cA.source
          rw [hBranchSymm]
          exact hqASrc
      have hEqOn : (fun t : ℂ => cA (c.symm t)) =ᶠ[𝓝 v]
          (fun t : ℂ =>
            ((polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2))⁻¹) := by
        refine Filter.eventually_of_mem ((c.symm.trans cA).open_source.mem_nhds hOverlap) ?_
        intro t ht
        have htTarget : t ∈ (affineChartProjY (H := Hrev) b hbX).target := by
          have : t ∈ c.target := ht.1
          simpa [c, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn, Hrev] using this
        have hSrc_unwound : c.symm t ∈ cA.source := ht.2
        simp only [cA, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
          OpenPartialHomeomorph.lift_openEmbedding_symm, c, infinityLiftChart] at hSrc_unwound
        rw [affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn] at hSrc_unwound
        rw [affineChartAt_of_mem_smoothLocusY (H := H) a haY] at hSrc_unwound
        obtain ⟨aa, haa_src, haa_eq⟩ := hSrc_unwound
        have haa_eq' : Quotient.mk (hyperellipticEvenSetoid H)
            (Sum.inr ((affineChartProjY (H := Hrev) b hbX).symm t)) =
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl aa) := by
          simpa [c, infinityLiftChart, affineChartAt_of_not_mem_smoothLocusY
            (H := Hrev) b hbYn, OpenPartialHomeomorph.lift_openEmbedding_symm,
            HyperellipticEvenProj.proj, Hrev] using haa_eq.symm
        have haa_eq'' : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl aa) =
            Quotient.mk (hyperellipticEvenSetoid H)
              (Sum.inr ((affineChartProjY (H := Hrev) b hbX).symm t)) :=
          haa_eq'.symm
        obtain ⟨hx_t, haa_glue⟩ := proj_inl_eq_proj_inr_iff (H := H) haa_eq''
        change cA (c.symm t) =
          ((polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2))⁻¹
        have hcsymm_eq : c.symm t =
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl aa) := by
          simpa [c, infinityLiftChart, affineChartAt_of_not_mem_smoothLocusY
            (H := Hrev) b hbYn, OpenPartialHomeomorph.lift_openEmbedding_symm,
            HyperellipticEvenProj.proj, Hrev] using haa_eq.symm
        rw [hcsymm_eq]
        change ((affineChartAt (H := H) a).lift_openEmbedding
            (isOpenEmbedding_proj_inl H hf.out))
          ((HyperellipticEvenProj.proj H ∘
            (Sum.inl : HyperellipticAffine H → HyperellipticEvenPre H)) aa) =
          ((polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2))⁻¹
        rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
        rw [affineChartAt_of_mem_smoothLocusY (H := H) a haY]
        change aa.val.1 =
          ((polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2))⁻¹
        have hxrev :
            (polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2) =
              aa.val.1⁻¹ := by
          have hfst := congrArg (fun bb : HyperellipticAffineInfinity H => bb.val.1)
            haa_glue
          have hchart :=
            affineChartProjY_symm_apply_fst (H := Hrev) b hbX htTarget
          change (((affineChartProjY (H := Hrev) b hbX).symm t :
            HyperellipticAffine Hrev).val.1) = aa.val.1⁻¹ at hfst
          simpa [hchart, affineGluingImage_val_fst] using hfst
        rw [hxrev, inv_inv]
      have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) qA) ∘
            (extChartAt 𝓘(ℂ, ℂ) q).symm) v 1 =
          -(2 * v /
              (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹) /
            (a.val.1⁻¹) ^ 2 := by
        rw [hExtCoeA, hExtSymm]
        change fderiv ℂ (fun t : ℂ => cA (c.symm t)) v 1 =
          -(2 * v /
              (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹) /
            (a.val.1⁻¹) ^ 2
        rw [Filter.EventuallyEq.fderiv_eq hEqOn]
        have htrans :=
          affineChartProjY_to_projX_transition_hasDerivAt (H := Hrev) b hbX hv
        have hTHasDeriv :
            HasDerivAt
              (fun t : ℂ =>
                ((polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2))⁻¹)
              (-(2 * v /
                  (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹) /
                (a.val.1⁻¹) ^ 2) v := by
          have huNZ :
              (polynomialLocalHomeomorph (H := Hrev) b hbX).symm (v ^ 2) ≠ 0 := by
            simpa [hu_eq] using inv_ne_zero hx
          have h := htrans.fun_inv huNZ
          simpa [Hrev, hu_eq] using h
        change deriv
          (fun t : ℂ =>
            ((polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2))⁻¹) v = _
        exact hTHasDeriv.deriv
      have hCocy := form.2.2.1 q qA v hvExt hSrcExt
      have hCoeff :
          form.coeff qA a.val.1 =
            - (a.val.1⁻¹) ^ 2 *
              (liouvilleInfinityProjYNumerator (H := H) form b hbX q v / v) := by
        have hFne :
            (Polynomial.reverse H.f).derivative.eval
              ((polynomialLocalHomeomorph (H := Hrev) b hbX).symm (v ^ 2)) ≠ 0 :=
          polynomialLocalHomeomorph_symm_eval_derivative_ne_zero (H := Hrev) b hbX hv
        have hFneA :
            (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹ ≠ 0 := by
          simpa [hu_eq] using hFne
        have hC :
            form.coeff q v =
              form.coeff qA a.val.1 *
                (-(2 * v /
                    (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹) /
                  (a.val.1⁻¹) ^ 2) := by
          unfold HolomorphicOneForm.coeff
          rw [hCocy, hCoord, hDeriv]
        unfold liouvilleInfinityProjYNumerator
        rw [hu_eq, hC]
        field_simp [hvne, hFneA, inv_ne_zero hx]
      have hAff : affCoeff (H := H) form a a.val.1 = form.coeff qA a.val.1 := by
        simp [affCoeff, qA, hQqAa]
      exact hAff.trans hCoeff
  | inr bA =>
      have hQqA : Quotient.out qA = Sum.inr bA := by simpa using hQa
      obtain ⟨hxA, hbA, hbAY⟩ :=
        affCoeff_inr_out_eq_affineGluingImage (H := H) a haY hQqA
      let cA := infinityLiftChart H hf.out bA
      have hqASrc : qA ∈ cA.source := by
        have h : qA ∈ (_root_.chartAt ℂ qA :
            OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
          ChartedSpace.mem_chart_source qA
        change qA ∈ (HyperellipticEvenProj.chartAt H hf.out qA).source at h
        unfold HyperellipticEvenProj.chartAt at h
        rw [hQqA] at h
        exact h
      have hChQA : (_root_.chartAt ℂ qA :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = cA := by
        change HyperellipticEvenProj.chartAt H hf.out qA = cA
        unfold HyperellipticEvenProj.chartAt
        rw [hQqA]
      have hExtCoeA : ((extChartAt 𝓘(ℂ, ℂ) qA) : HyperellipticEvenProj H → ℂ) =
          (cA : HyperellipticEvenProj H → ℂ) := by
        funext t
        change (_root_.chartAt ℂ qA) t = cA t
        rw [hChQA]
      have hExtSrcA : (extChartAt 𝓘(ℂ, ℂ) qA).source = cA.source := by
        rw [extChartAt_source, hChQA]
      have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm v ∈
          (extChartAt 𝓘(ℂ, ℂ) qA).source := by
        rw [hExtSymm, hExtSrcA, hBranchSymm]
        exact hqASrc
      have hqA_eq_inr :
          Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bA) = qA := by
        rw [← hQqA]
        exact Quotient.out_eq qA
      have hCoord : (extChartAt 𝓘(ℂ, ℂ) qA)
          ((extChartAt 𝓘(ℂ, ℂ) q).symm v) = a.val.1⁻¹ := by
        rw [hExtCoeA, hExtSymm, hBranchSymm]
        have hInlEqInr :
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) =
              Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bA) := by
          rw [hbA]
          exact proj_eq_affineGluingImage (H := H) a hxA
        rw [hInlEqInr]
        change ((affineChartAt (H := Hrev) bA).lift_openEmbedding
            (isOpenEmbedding_proj_inr H hf.out))
          ((HyperellipticEvenProj.proj H ∘
            (Sum.inr : HyperellipticAffineInfinity H → HyperellipticEvenPre H)) bA) =
          a.val.1⁻¹
        rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
        rw [affineChartAt_of_mem_smoothLocusY (H := Hrev) bA hbAY]
        change bA.val.1 = a.val.1⁻¹
        simp [hbA, affineGluingImage_val_fst]
      have hOverlap : v ∈ (c.symm.trans cA).source := by
        refine ⟨?_, ?_⟩
        · simpa [c, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn, Hrev] using hv
        · change c.symm v ∈ cA.source
          rw [hBranchSymm]
          exact hqASrc
      have hEqOn : (fun t : ℂ => cA (c.symm t)) =ᶠ[𝓝 v]
          (fun t : ℂ => (polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2)) := by
        refine Filter.eventually_of_mem ((c.symm.trans cA).open_source.mem_nhds hOverlap) ?_
        intro t ht
        have htTarget : t ∈ (affineChartProjY (H := Hrev) b hbX).target := by
          have : t ∈ c.target := ht.1
          simpa [c, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
            affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn, Hrev] using this
        change (c.symm.trans cA) t =
          (polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2)
        change (((affineChartAt (H := Hrev) b).lift_openEmbedding
            (isOpenEmbedding_proj_inr H hf.out)).symm.trans
            ((affineChartAt (H := Hrev) bA).lift_openEmbedding
              (isOpenEmbedding_proj_inr H hf.out))) t =
          (polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2)
        rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
        rw [affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn]
        rw [affineChartAt_of_mem_smoothLocusY (H := Hrev) bA hbAY]
        change (((affineChartProjY (H := Hrev) b hbX).symm t :
          HyperellipticAffine Hrev).val.1) =
          (polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2)
        exact affineChartProjY_symm_apply_fst (H := Hrev) b hbX htTarget
      have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) qA) ∘
            (extChartAt 𝓘(ℂ, ℂ) q).symm) v 1 =
          2 * v / (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹ := by
        rw [hExtCoeA, hExtSymm]
        change fderiv ℂ (fun t : ℂ => cA (c.symm t)) v 1 =
          2 * v / (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹
        rw [Filter.EventuallyEq.fderiv_eq hEqOn]
        have htrans :=
          affineChartProjY_to_projX_transition_hasDerivAt (H := Hrev) b hbX hv
        change deriv (fun t : ℂ =>
          (polynomialLocalHomeomorph (H := Hrev) b hbX).symm (t ^ 2)) v =
          2 * v / (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹
        simpa [hu_eq] using htrans.deriv
      have hCocy := form.2.2.1 q qA v hvExt hSrcExt
      have hCoeff :
          form.coeff qA (a.val.1⁻¹) * (-(a.val.1⁻¹) ^ 2) =
            - (a.val.1⁻¹) ^ 2 *
              (liouvilleInfinityProjYNumerator (H := H) form b hbX q v / v) := by
        have hFne :
            (Polynomial.reverse H.f).derivative.eval
              ((polynomialLocalHomeomorph (H := Hrev) b hbX).symm (v ^ 2)) ≠ 0 :=
          polynomialLocalHomeomorph_symm_eval_derivative_ne_zero (H := Hrev) b hbX hv
        have hFneA :
            (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹ ≠ 0 := by
          simpa [hu_eq] using hFne
        have hC :
            form.coeff q v =
              form.coeff qA (a.val.1⁻¹) *
                (2 * v /
                  (Polynomial.reverse H.f).derivative.eval a.val.1⁻¹) := by
          unfold HolomorphicOneForm.coeff
          rw [hCocy, hCoord, hDeriv]
        unfold liouvilleInfinityProjYNumerator
        rw [hu_eq, hC]
        field_simp [hvne, hFneA]
      have hAff : affCoeff (H := H) form a a.val.1 =
          form.coeff qA (a.val.1⁻¹) * (-1 / a.val.1 ^ 2) := by
        simp [affCoeff, qA, hQqA]
      rw [hAff]
      convert hCoeff using 1
      field_simp [hx]

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

/-- Branch-chart cancellation, affine representative case. If the moving
off-branch sheet uses an affine `x`-chart as preferred representative, then
the affine `x`-coefficient is the branch-chart numerator divided by the branch
coordinate. This is the `projY -> projX` cotangent cocycle for a general
holomorphic one-form. -/
theorem affCoeff_eq_liouvilleProjYNumerator_div_of_branch_inl
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (p : HyperellipticAffine H) (hpX : p ∈ smoothLocusX H)
    (hpYn : p ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl p)
    {w : ℂ}
    (hw : w ∈ (affineChartProjY (H := H) p hpX).target)
    (hwne : w ≠ 0) :
    let a : HyperellipticAffine H := (affineChartProjY (H := H) p hpX).symm w
    Quotient.out (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inl a →
      affCoeff (H := H) form a a.val.1 =
        liouvilleProjYNumerator (H := H) form p hpX q w / w := by
  classical
  intro a hQa
  let qA : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let c := affineLiftChart H hf.out p
  let cA := affineLiftChart H hf.out a
  have haY : a ∈ smoothLocusY H := by
    show a.val.2 ≠ 0
    have hsnd := affineChartProjY_symm_apply_snd (H := H) p hpX hw
    simpa [a, hsnd] using hwne
  have haSrc : a ∈ (affineChartProjX (H := H) a haY).source :=
    affineChartProjX_mem_source (H := H) a haY
  have hqASrc : qA ∈ cA.source := by
    change (HyperellipticEvenProj.proj H (Sum.inl a)) ∈
      ((affineChartAt (H := H) a).lift_openEmbedding
        (isOpenEmbedding_proj_inl H hf.out)).source
    rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨a, ?_, rfl⟩
    simpa [affineChartAt_of_mem_smoothLocusY (H := H) a haY] using haSrc
  have hBranchSymm : c.symm w = qA := by
    simp [c, qA, a, affineLiftChart, affineChartAt_of_not_mem_smoothLocusY
      (H := H) p hpYn, OpenPartialHomeomorph.lift_openEmbedding_symm,
      HyperellipticEvenProj.proj]
  have hChQ : (_root_.chartAt ℂ q :
      OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = c := by
    change HyperellipticEvenProj.chartAt H hf.out q = c
    unfold HyperellipticEvenProj.chartAt
    rw [hQ]
  have hChQA : (_root_.chartAt ℂ qA :
      OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = cA := by
    change HyperellipticEvenProj.chartAt H hf.out qA = cA
    unfold HyperellipticEvenProj.chartAt
    rw [show Quotient.out qA = Sum.inl a by simpa [qA] using hQa]
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (affineChartProjY (H := H) p hpX).target := by
    rw [extChartAt_target]
    change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineChartProjY (H := H) p hpX).target
    rw [hChQ]
    change c.target ∩ Set.range (id : ℂ → ℂ) =
      (affineChartProjY (H := H) p hpX).target
    rw [Set.range_id, Set.inter_univ]
    simp [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn]
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      (c.symm : ℂ → HyperellipticEvenProj H) := by
    funext t
    change (_root_.chartAt ℂ q).symm t = c.symm t
    rw [hChQ]
  have hExtCoeA : ((extChartAt 𝓘(ℂ, ℂ) qA) : HyperellipticEvenProj H → ℂ) =
      (cA : HyperellipticEvenProj H → ℂ) := by
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
    change ((affineChartAt (H := H) a).lift_openEmbedding
        (isOpenEmbedding_proj_inl H hf.out))
      ((HyperellipticEvenProj.proj H ∘
        (Sum.inl : HyperellipticAffine H → HyperellipticEvenPre H)) a) = a.val.1
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a haY]
    rfl
  have hOverlap : w ∈ (c.symm.trans cA).source := by
    refine ⟨?_, ?_⟩
    · simpa [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
        affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn] using hw
    · change c.symm w ∈ cA.source
      rw [hBranchSymm]
      exact hqASrc
  have hEqOn : (fun t : ℂ => cA (c.symm t)) =ᶠ[𝓝 w]
      (fun t : ℂ => (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)) := by
    refine Filter.eventually_of_mem ((c.symm.trans cA).open_source.mem_nhds hOverlap) ?_
    intro t ht
    have htTarget : t ∈ (affineChartProjY (H := H) p hpX).target := by
      have : t ∈ c.target := ht.1
      simpa [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
        affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn] using this
    change (c.symm.trans cA) t =
      (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)
    change (((affineChartAt (H := H) p).lift_openEmbedding
        (isOpenEmbedding_proj_inl H hf.out)).symm.trans
        ((affineChartAt (H := H) a).lift_openEmbedding
          (isOpenEmbedding_proj_inl H hf.out))) t =
      (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)
    rw [OpenPartialHomeomorph.lift_openEmbedding_trans_apply]
    rw [affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn]
    rw [affineChartAt_of_mem_smoothLocusY (H := H) a haY]
    change (((affineChartProjY (H := H) p hpX).symm t :
      HyperellipticAffine H).val.1) =
      (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)
    exact affineChartProjY_symm_apply_fst (H := H) p hpX htTarget
  have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) qA) ∘
        (extChartAt 𝓘(ℂ, ℂ) q).symm) w 1 =
      2 * w / H.f.derivative.eval a.val.1 := by
    rw [hExtCoeA, hExtSymm]
    change fderiv ℂ (fun t : ℂ => cA (c.symm t)) w 1 =
      2 * w / H.f.derivative.eval a.val.1
    rw [Filter.EventuallyEq.fderiv_eq hEqOn]
    have htrans :=
      affineChartProjY_to_projX_transition_hasDerivAt (H := H) p hpX hw
    change deriv (fun t : ℂ =>
      (polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2)) w =
      2 * w / H.f.derivative.eval a.val.1
    have hfst := affineChartProjY_symm_apply_fst (H := H) p hpX hw
    simpa [a, hfst] using htrans.deriv
  have hCocy := form.2.2.1 q qA w hwExt hSrcExt
  have hCoeff : form.coeff qA a.val.1 =
      liouvilleProjYNumerator (H := H) form p hpX q w / w := by
    have hx_eq :
        a.val.1 = (polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2) := by
      simpa [a] using affineChartProjY_symm_apply_fst (H := H) p hpX hw
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
    unfold liouvilleProjYNumerator
    rw [hC']
    field_simp [hwne, hFne]
  have hAff : affCoeff (H := H) form a a.val.1 = form.coeff qA a.val.1 := by
    simp [affCoeff, qA, hQa]
  exact hAff.trans hCoeff

/-- Branch-chart cancellation, infinity representative case. If the moving
off-branch sheet's preferred representative is on the infinity side, the
`u = 1/x` derivative in the cotangent cocycle combines with the defining
`-1/x^2` factor in `affCoeff`, leaving the same branch numerator divided by
the branch coordinate. -/
theorem affCoeff_eq_liouvilleProjYNumerator_div_of_branch_inr
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (p : HyperellipticAffine H) (hpX : p ∈ smoothLocusX H)
    (hpYn : p ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl p)
    {w : ℂ}
    (hw : w ∈ (affineChartProjY (H := H) p hpX).target)
    (hwne : w ≠ 0)
    {b : HyperellipticAffineInfinity H} :
    let a : HyperellipticAffine H := (affineChartProjY (H := H) p hpX).symm w
    Quotient.out (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) = Sum.inr b →
      affCoeff (H := H) form a a.val.1 =
        liouvilleProjYNumerator (H := H) form p hpX q w / w := by
  classical
  intro a hQa
  let qA : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let c := affineLiftChart H hf.out p
  let cB := infinityLiftChart H hf.out b
  have haY : a ∈ smoothLocusY H := by
    show a.val.2 ≠ 0
    have hsnd := affineChartProjY_symm_apply_snd (H := H) p hpX hw
    simpa [a, hsnd] using hwne
  obtain ⟨hxNZ, hb, hbY⟩ :=
    affCoeff_inr_out_eq_affineGluingImage (H := H) a haY hQa
  have hqASrc : qA ∈ cB.source := by
    have h : qA ∈ (_root_.chartAt ℂ qA :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
      ChartedSpace.mem_chart_source qA
    change qA ∈ (HyperellipticEvenProj.chartAt H hf.out qA).source at h
    unfold HyperellipticEvenProj.chartAt at h
    rw [show Quotient.out qA = Sum.inr b by simpa [qA] using hQa] at h
    exact h
  have hBranchSymm : c.symm w = qA := by
    simp [c, qA, a, affineLiftChart, affineChartAt_of_not_mem_smoothLocusY
      (H := H) p hpYn, OpenPartialHomeomorph.lift_openEmbedding_symm,
      HyperellipticEvenProj.proj]
  have hChQ : (_root_.chartAt ℂ q :
      OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = c := by
    change HyperellipticEvenProj.chartAt H hf.out q = c
    unfold HyperellipticEvenProj.chartAt
    rw [hQ]
  have hChQA : (_root_.chartAt ℂ qA :
      OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ) = cB := by
    change HyperellipticEvenProj.chartAt H hf.out qA = cB
    unfold HyperellipticEvenProj.chartAt
    rw [show Quotient.out qA = Sum.inr b by simpa [qA] using hQa]
  have hExtTarget : (extChartAt 𝓘(ℂ, ℂ) q).target =
      (affineChartProjY (H := H) p hpX).target := by
    rw [extChartAt_target]
    change ↑𝓘(ℂ, ℂ).symm ⁻¹' (_root_.chartAt ℂ q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (affineChartProjY (H := H) p hpX).target
    rw [hChQ]
    change c.target ∩ Set.range (id : ℂ → ℂ) =
      (affineChartProjY (H := H) p hpX).target
    rw [Set.range_id, Set.inter_univ]
    simp [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
      affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn]
  have hExtSymm : ((extChartAt 𝓘(ℂ, ℂ) q).symm : ℂ → HyperellipticEvenProj H) =
      (c.symm : ℂ → HyperellipticEvenProj H) := by
    funext t
    change (_root_.chartAt ℂ q).symm t = c.symm t
    rw [hChQ]
  have hExtCoeA : ((extChartAt 𝓘(ℂ, ℂ) qA) : HyperellipticEvenProj H → ℂ) =
      (cB : HyperellipticEvenProj H → ℂ) := by
    funext t
    change (_root_.chartAt ℂ qA) t = cB t
    rw [hChQA]
  have hExtSrcA : (extChartAt 𝓘(ℂ, ℂ) qA).source = cB.source := by
    rw [extChartAt_source, hChQA]
  have hwExt : w ∈ (extChartAt 𝓘(ℂ, ℂ) q).target := by
    rwa [hExtTarget]
  have hSrcExt : (extChartAt 𝓘(ℂ, ℂ) q).symm w ∈
      (extChartAt 𝓘(ℂ, ℂ) qA).source := by
    rw [hExtSymm, hExtSrcA, hBranchSymm]
    exact hqASrc
  have hqA_eq_inr :
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b) = qA := by
    rw [← show Quotient.out qA = Sum.inr b by simpa [qA] using hQa]
    exact Quotient.out_eq qA
  have hCoord : (extChartAt 𝓘(ℂ, ℂ) qA)
      ((extChartAt 𝓘(ℂ, ℂ) q).symm w) = a.val.1⁻¹ := by
    rw [hExtCoeA, hExtSymm, hBranchSymm]
    rw [← hqA_eq_inr]
    change ((affineChartAt
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b).lift_openEmbedding
        (isOpenEmbedding_proj_inr H hf.out))
      ((HyperellipticEvenProj.proj H ∘
        (Sum.inr : HyperellipticAffineInfinity H → HyperellipticEvenPre H)) b) =
        a.val.1⁻¹
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rw [affineChartAt_of_mem_smoothLocusY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY]
    change b.val.1 = a.val.1⁻¹
    simp [hb, affineGluingImage]
  have hOverlap : w ∈ (c.symm.trans cB).source := by
    refine ⟨?_, ?_⟩
    · simpa [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
        affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn] using hw
    · change c.symm w ∈ cB.source
      rw [hBranchSymm]
      exact hqASrc
  have hEqOn : (fun t : ℂ => cB (c.symm t)) =ᶠ[𝓝 w]
      (fun t : ℂ => ((polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2))⁻¹) := by
    refine Filter.eventually_of_mem ((c.symm.trans cB).open_source.mem_nhds hOverlap) ?_
    intro t ht
    have htTarget : t ∈ (affineChartProjY (H := H) p hpX).target := by
      have : t ∈ c.target := ht.1
      simpa [c, affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target,
        affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn] using this
    have hSrc_unwound : c.symm t ∈ cB.source := ht.2
    simp only [cB, infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm, c, affineLiftChart] at hSrc_unwound
    rw [affineChartAt_of_not_mem_smoothLocusY (H := H) p hpYn] at hSrc_unwound
    rw [affineChartAt_of_mem_smoothLocusY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY] at hSrc_unwound
    obtain ⟨bb, hbb_src, hbb_eq⟩ := hSrc_unwound
    have hbb_eq' : Quotient.mk (hyperellipticEvenSetoid H)
        (Sum.inl ((affineChartProjY (H := H) p hpX).symm t)) =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := by
      simpa [c, affineLiftChart, affineChartAt_of_not_mem_smoothLocusY
        (H := H) p hpYn, OpenPartialHomeomorph.lift_openEmbedding_symm,
        HyperellipticEvenProj.proj] using hbb_eq.symm
    obtain ⟨hx_t, hbb⟩ := proj_inl_eq_proj_inr_iff (H := H) hbb_eq'
    change cB (c.symm t) =
      ((polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2))⁻¹
    have hcsymm_eq : c.symm t =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bb) := by
      simpa [c, affineLiftChart, affineChartAt_of_not_mem_smoothLocusY
        (H := H) p hpYn, OpenPartialHomeomorph.lift_openEmbedding_symm,
        HyperellipticEvenProj.proj] using hbb_eq.symm
    rw [hcsymm_eq]
    change ((affineChartAt
        (H := HyperellipticAffineInfinity.reverseData H hf.out) b).lift_openEmbedding
        (isOpenEmbedding_proj_inr H hf.out))
      ((HyperellipticEvenProj.proj H ∘
        (Sum.inr : HyperellipticAffineInfinity H → HyperellipticEvenPre H)) bb) =
        ((polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2))⁻¹
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rw [affineChartAt_of_mem_smoothLocusY
      (H := HyperellipticAffineInfinity.reverseData H hf.out) b hbY]
    rw [hbb]
    change (affineGluingImage
      ((affineChartProjY (H := H) p hpX).symm t) hx_t).val.1 =
      ((polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2))⁻¹
    simp [affineGluingImage, affineChartProjY_symm_apply_fst (H := H) p hpX htTarget]
  have hx_eq :
      a.val.1 = (polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2) := by
    simpa [a] using affineChartProjY_symm_apply_fst (H := H) p hpX hw
  have hDeriv : fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) qA) ∘
        (extChartAt 𝓘(ℂ, ℂ) q).symm) w 1 =
      -(2 * w / H.f.derivative.eval a.val.1) / a.val.1 ^ 2 := by
    rw [hExtCoeA, hExtSymm]
    change fderiv ℂ (fun t : ℂ => cB (c.symm t)) w 1 =
      -(2 * w / H.f.derivative.eval a.val.1) / a.val.1 ^ 2
    rw [Filter.EventuallyEq.fderiv_eq hEqOn]
    have htrans :=
      affineChartProjY_to_projX_transition_hasDerivAt (H := H) p hpX hw
    have hTHasDeriv :
        HasDerivAt
          (fun t : ℂ => ((polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2))⁻¹)
          (-(2 * w / H.f.derivative.eval a.val.1) / a.val.1 ^ 2) w := by
      have hxNZ' :
          (polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2) ≠ 0 := by
        simpa [← hx_eq] using hxNZ
      have h := htrans.fun_inv hxNZ'
      convert h using 1
      · rw [hx_eq]
    change deriv
      (fun t : ℂ => ((polynomialLocalHomeomorph (H := H) p hpX).symm (t ^ 2))⁻¹) w =
      -(2 * w / H.f.derivative.eval a.val.1) / a.val.1 ^ 2
    exact hTHasDeriv.deriv
  have hCocy := form.2.2.1 q qA w hwExt hSrcExt
  have hCoeff :
      form.coeff qA (a.val.1⁻¹) * (-1 / a.val.1 ^ 2) =
        liouvilleProjYNumerator (H := H) form p hpX q w / w := by
    have hFne :
        H.f.derivative.eval
          ((polynomialLocalHomeomorph (H := H) p hpX).symm (w ^ 2)) ≠ 0 :=
      polynomialLocalHomeomorph_symm_eval_derivative_ne_zero (H := H) p hpX hw
    have hFneA : H.f.derivative.eval a.val.1 ≠ 0 := by
      simpa [hx_eq] using hFne
    have hC :
        form.coeff q w =
          form.coeff qA (a.val.1⁻¹) *
            (-(2 * w / H.f.derivative.eval a.val.1) / a.val.1 ^ 2) := by
      unfold HolomorphicOneForm.coeff
      rw [hCocy, hCoord, hDeriv]
    unfold liouvilleProjYNumerator
    rw [← hx_eq]
    rw [hC]
    field_simp [hwne, hFneA, hxNZ]
  have hAff : affCoeff (H := H) form a a.val.1 =
      form.coeff qA (a.val.1⁻¹) * (-1 / a.val.1 ^ 2) := by
    simp [affCoeff, qA, hQa]
  exact hAff.trans hCoeff

/-- Branch-chart cancellation for a moving off-branch sheet, independent of
whether the preferred quotient representative of the moving sheet is affine or
infinity-side. -/
theorem affCoeff_eq_liouvilleProjYNumerator_div_of_branch
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    (p : HyperellipticAffine H) (hpX : p ∈ smoothLocusX H)
    (hpYn : p ∉ smoothLocusY H)
    (q : HyperellipticEvenProj H) (hQ : Quotient.out q = Sum.inl p)
    {w : ℂ}
    (hw : w ∈ (affineChartProjY (H := H) p hpX).target)
    (hwne : w ≠ 0) :
    let a : HyperellipticAffine H := (affineChartProjY (H := H) p hpX).symm w
    affCoeff (H := H) form a a.val.1 =
      liouvilleProjYNumerator (H := H) form p hpX q w / w := by
  classical
  intro a
  let qA : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  cases hQa : Quotient.out qA with
  | inl a' =>
      have hQqA : Quotient.out qA = Sum.inl a' := by simpa using hQa
      have hOutEq : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a') = qA := by
        rw [← hQqA]
        exact Quotient.out_eq qA
      have ha' : a' = a := by
        exact HyperellipticEvenProj.proj_inl_injective H (by
          simpa [qA, HyperellipticEvenProj.proj, Function.comp_def] using hOutEq)
      have hQaA : Quotient.out qA = Sum.inl a := by
        simpa [ha'] using hQqA
      exact
        affCoeff_eq_liouvilleProjYNumerator_div_of_branch_inl
          (H := H) form p hpX hpYn q hQ hw hwne hQaA
  | inr b =>
      exact
        affCoeff_eq_liouvilleProjYNumerator_div_of_branch_inr
          (H := H) form p hpX hpYn q hQ hw hwne (b := b) (by simpa [qA] using hQa)

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
/-- The arbitrary algebraic square-root coordinate chosen over `z` tends to
`0` as `z` approaches any branch point. -/
theorem liouvilleChosenAffinePoint_snd_tendsto_zero
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ = 0) :
    Filter.Tendsto (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2)
      (𝓝 z₀) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hεsq : 0 < ε ^ 2 := pow_pos hε 2
  have hf0 : Filter.Tendsto (fun z : ℂ => H.f.eval z) (𝓝 z₀) (𝓝 0) := by
    simpa [hz₀] using (Polynomial.continuous H.f).tendsto z₀
  have hnorm :
      Filter.Tendsto (fun z : ℂ => ‖H.f.eval z‖) (𝓝 z₀) (𝓝 0) :=
    by simpa using hf0.norm
  have hsmall : ∀ᶠ z in 𝓝 z₀, ‖H.f.eval z‖ < ε ^ 2 := by
    have hball := hnorm (Metric.ball_mem_nhds (0 : ℝ) hεsq)
    filter_upwards [hball] with z hz
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (norm_nonneg (H.f.eval z))]
      using hz
  filter_upwards [hsmall] with z hz
  have hsq :
      ‖(liouvilleChosenAffinePoint (H := H) z).val.2‖ ^ 2 < ε ^ 2 := by
    rw [← norm_pow, liouvilleChosenAffinePoint_snd_sq (H := H) z]
    exact hz
  have hnorm_lt : ‖(liouvilleChosenAffinePoint (H := H) z).val.2‖ < ε := by
    nlinarith [norm_nonneg ((liouvilleChosenAffinePoint (H := H) z).val.2), hε, hsq]
  simpa [Metric.mem_ball, Real.dist_eq,
    abs_of_nonneg (norm_nonneg ((liouvilleChosenAffinePoint (H := H) z).val.2))]
    using hnorm_lt

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

omit hf in
/-- Near a smooth-`Y` point, the local `x`-branch centered at the involuted
point is the pointwise involution of the local branch centered at the original
point. -/
theorem affineChartProjX_invol_symm_eq_eventually
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H) :
    ∀ᶠ z in 𝓝 a.val.1,
      ((affineChartProjX (H := H) a.invol
          (HyperellipticAffine.invol_mem_smoothLocusY a hpY)).symm z :
        HyperellipticAffine H) =
        ((affineChartProjX (H := H) a hpY).symm z).invol := by
  classical
  let hpYσ := HyperellipticAffine.invol_mem_smoothLocusY a hpY
  let e := affineChartProjX (H := H) a hpY
  let eσ := affineChartProjX (H := H) a.invol hpYσ
  change ∀ᶠ z in 𝓝 a.val.1, eσ.symm z = (e.symm z).invol
  have haSrc : a ∈ e.source := by
    simpa [e] using affineChartProjX_mem_source (H := H) a hpY
  have haTarget : a.val.1 ∈ e.target := by
    simpa [e] using e.map_source haSrc
  have haσSrc : a.invol ∈ eσ.source := by
    simpa [eσ, hpYσ] using affineChartProjX_mem_source (H := H) a.invol hpYσ
  have haσTarget : a.val.1 ∈ eσ.target := by
    have h := eσ.map_source haσSrc
    simpa [eσ, HyperellipticAffine.invol] using h
  have hYbase : ((e.symm a.val.1 : HyperellipticAffine H).val.2) = a.val.2 := by
    rw [show e = affineChartProjX (H := H) a hpY from rfl]
    rw [affineChartProjX_symm_apply_snd (H := H) a hpY haTarget]
    exact squareLocalHomeomorph_symm_at_basepoint (H := H) a hpY
  have hYσbase : ((eσ.symm a.val.1 : HyperellipticAffine H).val.2) = -a.val.2 := by
    rw [show eσ = affineChartProjX (H := H) a.invol hpYσ from rfl]
    rw [affineChartProjX_symm_apply_snd (H := H) a.invol hpYσ haσTarget]
    simpa [HyperellipticAffine.invol] using
      squareLocalHomeomorph_symm_at_basepoint (H := H) a.invol hpYσ
  have hContY : ContinuousAt
      (fun z : ℂ => ((e.symm z : HyperellipticAffine H).val.2)) a.val.1 :=
    (continuous_snd.comp continuous_subtype_val).continuousAt.comp
      (e.continuousAt_symm haTarget)
  have hContYσ : ContinuousAt
      (fun z : ℂ => ((eσ.symm z : HyperellipticAffine H).val.2)) a.val.1 :=
    (continuous_snd.comp continuous_subtype_val).continuousAt.comp
      (eσ.continuousAt_symm haσTarget)
  have hSepAt :
      ((eσ.symm a.val.1 : HyperellipticAffine H).val.2 -
        (e.symm a.val.1 : HyperellipticAffine H).val.2) ≠ 0 := by
    rw [hYσbase, hYbase]
    intro h
    have hmul : (2 : ℂ) * a.val.2 = 0 := by
      calc
        (2 : ℂ) * a.val.2 = -((-a.val.2) - a.val.2) := by ring
        _ = 0 := by rw [h]; ring
    exact hpY ((mul_eq_zero.mp hmul).resolve_left (by norm_num))
  have hSepEv : ∀ᶠ z in 𝓝 a.val.1,
      ((eσ.symm z : HyperellipticAffine H).val.2 -
        (e.symm z : HyperellipticAffine H).val.2) ≠ 0 :=
    (hContYσ.sub hContY).eventually_ne hSepAt
  filter_upwards [e.open_target.mem_nhds haTarget,
      eσ.open_target.mem_nhds haσTarget, hSepEv] with z hz hzσ hSep
  have hSq : ((eσ.symm z : HyperellipticAffine H).val.2) ^ 2 =
      ((e.symm z : HyperellipticAffine H).val.2) ^ 2 := by
    have hσ : ((eσ.symm z : HyperellipticAffine H).val.2) ^ 2 = H.f.eval z := by
      have hprop := (eσ.symm z : HyperellipticAffine H).property
      simpa [eσ, affineChartProjX_symm_apply_fst (H := H) a.invol hpYσ hzσ]
        using hprop
    have h0 : ((e.symm z : HyperellipticAffine H).val.2) ^ 2 = H.f.eval z := by
      have hprop := (e.symm z : HyperellipticAffine H).property
      simpa [e, affineChartProjX_symm_apply_fst (H := H) a hpY hz]
        using hprop
    exact hσ.trans h0.symm
  rcases eq_or_eq_neg_of_sq_eq_sq
      ((eσ.symm z : HyperellipticAffine H).val.2)
      ((e.symm z : HyperellipticAffine H).val.2) hSq with hSame | hNeg
  · exfalso
    exact hSep (by rw [hSame, sub_self])
  · apply Subtype.ext
    apply Prod.ext
    · change ((eσ.symm z : HyperellipticAffine H).val.1) =
        ((e.symm z : HyperellipticAffine H).invol).val.1
      rw [affineChartProjX_symm_apply_fst (H := H) a.invol hpYσ hzσ]
      rw [HyperellipticAffine.invol_val]
      exact (affineChartProjX_symm_apply_fst (H := H) a hpY hz).symm
    · change ((eσ.symm z : HyperellipticAffine H).val.2) =
        ((e.symm z : HyperellipticAffine H).invol).val.2
      simpa [HyperellipticAffine.invol] using hNeg

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

/-- The fixed two-sheet affine-coefficient expression determined by the chosen
point over a non-branch basepoint is analytic at that basepoint.

The remaining off-root analyticity step for `liouvilleTwoSheetSum` is to identify
the arbitrary chosen sheet near `z₀` with one of these two fixed local sheets; the
sum is symmetric, so the two cases give the same fixed expression. -/
theorem liouvilleChosenTwoSheetSum_analyticAt
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ
      (fun z : ℂ =>
        affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z₀) z +
          affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z₀).invol z)
      z₀ := by
  classical
  let a₀ := liouvilleChosenAffinePoint (H := H) z₀
  have ha₀Y : a₀ ∈ smoothLocusY H := by
    simpa [a₀] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀
  have ha₀σY : a₀.invol ∈ smoothLocusY H :=
    HyperellipticAffine.invol_mem_smoothLocusY a₀ ha₀Y
  have h1 : AnalyticAt ℂ (affCoeff (H := H) form a₀) z₀ := by
    simpa [a₀] using affCoeff_analyticAt_basepoint (H := H) form a₀ ha₀Y
  have h2 : AnalyticAt ℂ (affCoeff (H := H) form a₀.invol) z₀ := by
    simpa [a₀] using affCoeff_analyticAt_basepoint (H := H) form a₀.invol ha₀σY
  simpa [a₀] using h1.add h2

/-- The direct two-sheet sum is analytic away from branch points. Near a
non-branch basepoint, the arbitrary chosen sheet is one of the two fixed local
branches; the sum is symmetric, so it is eventually equal to the fixed analytic
two-branch expression. -/
theorem liouvilleTwoSheetSum_analyticAt_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z₀ := by
  classical
  let a₀ := liouvilleChosenAffinePoint (H := H) z₀
  have ha₀Y : a₀ ∈ smoothLocusY H := by
    simpa [a₀] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀
  let a₀σ : HyperellipticAffine H := a₀.invol
  have ha₀σY : a₀σ ∈ smoothLocusY H := by
    simpa [a₀σ] using HyperellipticAffine.invol_mem_smoothLocusY a₀ ha₀Y
  let e₀ := affineChartProjX (H := H) a₀ ha₀Y
  let e₀σ := affineChartProjX (H := H) a₀σ ha₀σY
  let q₀ : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a₀)
  let q₀σ : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a₀σ)
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
    have hMap : e₀ a₀ = a₀.val.1 := by
      change a₀.val.1 = a₀.val.1
      rfl
    rw [show z₀ = a₀.val.1 by simp [a₀], ← hMap]
    exact e₀.left_inv ha₀Src
  have hSymm₀σ : e₀σ.symm z₀ = a₀σ := by
    have hMap : e₀σ a₀σ = a₀σ.val.1 := by
      change a₀σ.val.1 = a₀σ.val.1
      rfl
    rw [show z₀ = a₀σ.val.1 by simp [a₀σ, a₀, HyperellipticAffine.invol], ← hMap]
    exact e₀σ.left_inv ha₀σSrc
  have hProjCont₀ : ContinuousAt
      (fun z : ℂ =>
        Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀.symm z : HyperellipticAffine H))) z₀ :=
    continuous_quotient_mk'.continuousAt.comp
      ((continuous_inl.continuousAt).comp (e₀.continuousAt_symm hz₀Target))
  have hProjCont₀σ : ContinuousAt
      (fun z : ℂ =>
        Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀σ.symm z : HyperellipticAffine H))) z₀ :=
    continuous_quotient_mk'.continuousAt.comp
      ((continuous_inl.continuousAt).comp (e₀σ.continuousAt_symm hz₀σTarget))
  have hPref₀ : ∀ᶠ z in 𝓝 z₀,
      Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀.symm z : HyperellipticAffine H)) ∈
        (_root_.chartAt ℂ q₀ :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source := by
    have hqSrc : q₀ ∈ (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
      ChartedSpace.mem_chart_source q₀
    have hmem : (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source ∈
        𝓝 q₀ :=
      (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).open_source.mem_nhds hqSrc
    exact hProjCont₀.eventually (by simpa [q₀, hSymm₀] using hmem)
  have hPref₀σ : ∀ᶠ z in 𝓝 z₀,
      Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀σ.symm z : HyperellipticAffine H)) ∈
        (_root_.chartAt ℂ q₀σ :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source := by
    have hqSrc : q₀σ ∈ (_root_.chartAt ℂ q₀σ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
      ChartedSpace.mem_chart_source q₀σ
    have hmem : (_root_.chartAt ℂ q₀σ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source ∈
        𝓝 q₀σ :=
      (_root_.chartAt ℂ q₀σ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).open_source.mem_nhds hqSrc
    exact hProjCont₀σ.eventually (by simpa [q₀σ, hSymm₀σ] using hmem)
  have hBranchPair : ∀ᶠ z in 𝓝 z₀,
      e₀σ.symm z = (e₀.symm z).invol := by
    have h :=
      affineChartProjX_invol_symm_eq_eventually (H := H) a₀ ha₀Y
    simpa [a₀σ, e₀, e₀σ] using h
  have hEval : ∀ᶠ z in 𝓝 z₀, H.f.eval z ≠ 0 :=
    (Polynomial.continuous H.f).continuousAt.eventually_ne hz₀
  have hEq : (fun z : ℂ =>
        affCoeff (H := H) form a₀ z + affCoeff (H := H) form a₀σ z) =ᶠ[𝓝 z₀]
      liouvilleTwoSheetSum (H := H) form := by
    filter_upwards [e₀.open_target.mem_nhds hz₀Target,
      e₀σ.open_target.mem_nhds hz₀σTarget, hPref₀, hPref₀σ, hBranchPair, hEval]
      with z hzT hzσT hSrcPref hSrcPrefσ hPair hzNZ
    let p₀ : HyperellipticAffine H := e₀.symm z
    let p₀σ : HyperellipticAffine H := e₀σ.symm z
    have hp₀σ_eq : p₀σ = p₀.invol := by
      simpa [p₀, p₀σ] using hPair
    have hFix₀ : affCoeff (H := H) form a₀ z =
        affCoeff (H := H) form p₀ z := by
      simpa [a₀, e₀, p₀, q₀] using
        affCoeff_eq_of_projX_symm (H := H) form a₀ ha₀Y hzT hSrcPref
    have hFix₀σ : affCoeff (H := H) form a₀σ z =
        affCoeff (H := H) form p₀.invol z := by
      have h := affCoeff_eq_of_projX_symm (H := H) form a₀σ ha₀σY hzσT hSrcPrefσ
      simpa [a₀σ, e₀σ, p₀σ, hp₀σ_eq, q₀σ] using h
    let a := liouvilleChosenAffinePoint (H := H) z
    have haSq : a.val.2 ^ 2 = H.f.eval z := by
      simpa [a] using liouvilleChosenAffinePoint_snd_sq (H := H) z
    have hp₀Fst : p₀.val.1 = z := by
      simpa [p₀, e₀] using affineChartProjX_symm_apply_fst (H := H) a₀ ha₀Y hzT
    have hp₀Sq : p₀.val.2 ^ 2 = H.f.eval z := by
      have hprop := p₀.property
      simpa [hp₀Fst] using hprop
    have hSheets := eq_or_eq_neg_of_sq_eq_sq a.val.2 p₀.val.2 (haSq.trans hp₀Sq.symm)
    rw [liouvilleTwoSheetSum_of_eval_ne_zero (H := H) form hzNZ]
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
  exact (liouvilleChosenTwoSheetSum_analyticAt (H := H) form hz₀).congr
    (by simpa [a₀, a₀σ] using hEq)

/-- Off-root analyticity of the direct two-sheet sum, packaged in the `hAna`
shape used by the Liouville scaffolding. -/
theorem liouvilleTwoSheetSum_analyticAt_off_roots
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∀ z : ℂ, H.f.eval z ≠ 0 →
      AnalyticAt ℂ (liouvilleTwoSheetSum (H := H) form) z := by
  intro z hz
  exact liouvilleTwoSheetSum_analyticAt_of_eval_ne_zero (H := H) form hz

/-- Branch punctured limit in the case where the projective branch point's
preferred chart is the affine `w = y` chart. The proof is the branch recipe:
on the punctured branch neighbourhood the two affine coefficients are
`N(w)/w` and `N(-w)/(-w)`, hence their sum is the odd-part difference quotient
of the analytic branch numerator `N`. -/
theorem liouvilleTwoSheetSum_branch_tendsto_of_branch_out_inl
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ = 0)
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (liouvilleBranchPoint (H := H) z₀ hz₀))) =
      Sum.inl (liouvilleBranchPoint (H := H) z₀ hz₀)) :
    ∃ L : ℂ, Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
      (𝓝[≠] z₀) (𝓝 L) := by
  classical
  let p := liouvilleBranchPoint (H := H) z₀ hz₀
  let hpX := liouvilleBranchPoint_mem_smoothLocusX (H := H) hz₀
  let hpYn := liouvilleBranchPoint_not_mem_smoothLocusY (H := H) hz₀
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p)
  let N : ℂ → ℂ := liouvilleProjYNumerator (H := H) form p hpX q
  let D : ℂ → ℂ := dslope (fun w : ℂ => N w - N (-w)) 0
  refine ⟨D 0, ?_⟩
  have hQq : Quotient.out q = Sum.inl p := by
    simpa [q, p] using hQ
  have hDcont : ContinuousAt D 0 := by
    have hAna : AnalyticAt ℂ D 0 := by
      simpa [D, N, p, hpX, q] using
        liouvilleBranchPoint_numerator_dslope_analyticAt_zero
          (H := H) form hz₀ q hQq
    exact hAna.continuousAt
  have hyTendsto : Filter.Tendsto
      (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2)
      (𝓝[≠] z₀) (𝓝 0) :=
    (liouvilleChosenAffinePoint_snd_tendsto_zero (H := H) hz₀).mono_left
      nhdsWithin_le_nhds
  have hModel : Filter.Tendsto
      (fun z : ℂ => D (liouvilleChosenAffinePoint (H := H) z).val.2)
      (𝓝[≠] z₀) (𝓝 (D 0)) :=
    hDcont.tendsto.comp hyTendsto
  have hEq : liouvilleTwoSheetSum (H := H) form =ᶠ[𝓝[≠] z₀]
      fun z : ℂ => D (liouvilleChosenAffinePoint (H := H) z).val.2 := by
    let e := polynomialLocalHomeomorph (H := H) p hpX
    have hz₀Src : z₀ ∈ e.source := by
      simpa [e, p, liouvilleBranchPoint] using
        polynomialLocalHomeomorph_mem_source (H := H) p hpX
    have hSrcEv : ∀ᶠ z in 𝓝 z₀, z ∈ e.source :=
      e.open_source.mem_nhds hz₀Src
    have hRootEv : ∀ᶠ z in 𝓝[≠] z₀, H.f.eval z ≠ 0 := by
      have hne : H.f ≠ 0 := by
        intro hzero
        have hd := H.h_degree
        rw [hzero, Polynomial.natDegree_zero] at hd
        omega
      have hfin : {x : ℂ | H.f.IsRoot x}.Finite :=
        Polynomial.finite_setOf_isRoot hne
      set R' : Set ℂ := {x : ℂ | H.f.IsRoot x} \ {z₀} with hR'
      have hR'closed : IsClosed R' := (hfin.subset Set.diff_subset).isClosed
      have hmem : R'ᶜ ∈ 𝓝 z₀ :=
        hR'closed.isOpen_compl.mem_nhds (by simp [hR'])
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with z hz hzc
      intro hzero
      exact hzc ⟨hzero, hz⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hSrcEv,
      hRootEv] with z hzSrc hzNZ
    let y : ℂ := (liouvilleChosenAffinePoint (H := H) z).val.2
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
    have hnegTarget : -y ∈ (affineChartProjY (H := H) p hpX).target := by
      have hy2Target : y ^ 2 ∈ e.target := by
        simpa [affineChartProjY, e] using hyTarget
      change (-y) ^ 2 ∈ e.target
      simpa [pow_two] using hy2Target
    have hxSymm : (affineChartProjY (H := H) p hpX).symm y =
        liouvilleChosenAffinePoint (H := H) z := by
      apply Subtype.ext
      apply Prod.ext
      · have hfst := affineChartProjY_symm_apply_fst (H := H) p hpX hyTarget
        have hleft : e.symm (H.f.eval z) = z := by
          have hleft' := e.left_inv hzSrc
          have heq : (e : ℂ → ℂ) z = H.f.eval z := by
            simp [e, polynomialLocalHomeomorph]
          simpa [heq] using hleft'
        change ((affineChartProjY (H := H) p hpX).symm y).val.1 =
          (liouvilleChosenAffinePoint (H := H) z).val.1
        rw [hfst, hySq, hleft]
        rfl
      · change ((affineChartProjY (H := H) p hpX).symm y).val.2 =
          (liouvilleChosenAffinePoint (H := H) z).val.2
        simpa [y] using affineChartProjY_symm_apply_snd (H := H) p hpX hyTarget
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
        change ((affineChartProjY (H := H) p hpX).symm (-y)).val.1 =
          ((liouvilleChosenAffinePoint (H := H) z).invol).val.1
        have hnegSq : (-y) ^ 2 = H.f.eval z := by
          simpa [sq] using hySq
        rw [hfst, hnegSq, hleft]
        rfl
      · change ((affineChartProjY (H := H) p hpX).symm (-y)).val.2 =
          ((liouvilleChosenAffinePoint (H := H) z).invol).val.2
        have hsnd := affineChartProjY_symm_apply_snd (H := H) p hpX hnegTarget
        simpa [y, HyperellipticAffine.invol] using hsnd
    have hA :
        affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z =
          N y / y := by
      have h := affCoeff_eq_liouvilleProjYNumerator_div_of_branch
        (H := H) form p hpX hpYn q hQq hyTarget hyNZ
      simpa [N, y, hxSymm] using h
    have hσ :
        affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z).invol z =
          N (-y) / (-y) := by
      have h := affCoeff_eq_liouvilleProjYNumerator_div_of_branch
        (H := H) form p hpX hpYn q hQq hnegTarget (neg_ne_zero.mpr hyNZ)
      simpa [N, y, hxNegSymm] using h
    rw [liouvilleTwoSheetSum_of_eval_ne_zero (H := H) form hzNZ, hA, hσ]
    have hD : D y = (N y - N (-y)) / y := by
      simpa [D] using Jacobians.GeneralResults.dslope_oddPart_of_ne (h := N) (w := y) hyNZ
    rw [hD]
    field_simp [hyNZ]
    ring
  exact hModel.congr' hEq.symm

/-- Branch punctured limit in the case where the projective branch point's
preferred chart is the infinity-side `v` branch chart. -/
theorem liouvilleTwoSheetSum_branch_tendsto_of_branch_out_inr
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ = 0)
    {b : HyperellipticAffineInfinity H}
    (hQ : Quotient.out
        (Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (liouvilleBranchPoint (H := H) z₀ hz₀))) =
      Sum.inr b) :
    ∃ L : ℂ, Filter.Tendsto (liouvilleTwoSheetSum (H := H) form)
      (𝓝[≠] z₀) (𝓝 L) := by
  classical
  let p := liouvilleBranchPoint (H := H) z₀ hz₀
  let hpX := liouvilleBranchPoint_mem_smoothLocusX (H := H) hz₀
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p)
  obtain ⟨hz₀NZ, hb, hb0, hbX, hbYn⟩ :=
    liouvilleBranchPoint_out_inr_data (H := H) hz₀ hQ
  let Hrev := HyperellipticAffineInfinity.reverseData H hf.out
  let M : ℂ → ℂ := liouvilleInfinityProjYNumerator (H := H) form b hbX q
  let D : ℂ → ℂ := dslope (fun v : ℂ => M v - M (-v)) 0
  refine ⟨- (z₀⁻¹) ^ 2 * D 0, ?_⟩
  have hQq : Quotient.out q = Sum.inr b := by
    simpa [q, p] using hQ
  have hDcont : ContinuousAt D 0 := by
    have hAna : AnalyticAt ℂ D 0 := by
      simpa [D, M, q, Hrev] using
        liouvilleInfinityBranchPoint_numerator_dslope_analyticAt_zero
          (H := H) form b hbX hbYn hb0 q hQq
    exact hAna.continuousAt
  have hyTendsto : Filter.Tendsto
      (fun z : ℂ => (liouvilleChosenAffinePoint (H := H) z).val.2)
      (𝓝[≠] z₀) (𝓝 0) :=
    (liouvilleChosenAffinePoint_snd_tendsto_zero (H := H) hz₀).mono_left
      nhdsWithin_le_nhds
  have hinvTendsto : Filter.Tendsto (fun z : ℂ => z⁻¹)
      (𝓝[≠] z₀) (𝓝 z₀⁻¹) :=
    (continuousAt_inv₀ hz₀NZ).tendsto.mono_left nhdsWithin_le_nhds
  have hvTendsto : Filter.Tendsto
      (fun z : ℂ =>
        (liouvilleChosenAffinePoint (H := H) z).val.2 *
          z⁻¹ ^ (H.f.natDegree / 2))
      (𝓝[≠] z₀) (𝓝 0) := by
    have hpow := hinvTendsto.pow (H.f.natDegree / 2)
    simpa using hyTendsto.mul hpow
  have hFactor : Filter.Tendsto (fun z : ℂ => - (z⁻¹) ^ 2)
      (𝓝[≠] z₀) (𝓝 (-(z₀⁻¹) ^ 2)) :=
    (hinvTendsto.pow 2).neg
  have hModel : Filter.Tendsto
      (fun z : ℂ =>
        - (z⁻¹) ^ 2 *
          D ((liouvilleChosenAffinePoint (H := H) z).val.2 *
            z⁻¹ ^ (H.f.natDegree / 2)))
      (𝓝[≠] z₀) (𝓝 (-(z₀⁻¹) ^ 2 * D 0)) := by
    exact hFactor.mul (hDcont.tendsto.comp hvTendsto)
  have hEq : liouvilleTwoSheetSum (H := H) form =ᶠ[𝓝[≠] z₀]
      fun z : ℂ =>
        - (z⁻¹) ^ 2 *
          D ((liouvilleChosenAffinePoint (H := H) z).val.2 *
            z⁻¹ ^ (H.f.natDegree / 2)) := by
    let e := polynomialLocalHomeomorph (H := H) p hpX
    let eInf := polynomialLocalHomeomorph (H := Hrev) b hbX
    have hz₀Src : z₀ ∈ e.source := by
      simpa [e, p, liouvilleBranchPoint] using
        polynomialLocalHomeomorph_mem_source (H := H) p hpX
    have hSrcEv : ∀ᶠ z in 𝓝 z₀, z ∈ e.source :=
      e.open_source.mem_nhds hz₀Src
    have hu₀Src : z₀⁻¹ ∈ eInf.source := by
      have hbSrc : b ∈ (affineChartProjY (H := Hrev) b hbX).source :=
        affineChartProjY_mem_source (H := Hrev) b hbX
      change b.val.1 ∈ eInf.source at hbSrc
      have hb1 : b.val.1 = z₀⁻¹ := by
        simp [hb, liouvilleBranchPoint, affineGluingImage_val_fst]
      simpa [hb1] using hbSrc
    have hInvSrcEv : ∀ᶠ z in 𝓝 z₀, z⁻¹ ∈ eInf.source :=
      (continuousAt_inv₀ hz₀NZ).eventually (eInf.open_source.mem_nhds hu₀Src)
    have hZneEv : ∀ᶠ z in 𝓝 z₀, z ≠ 0 :=
      (continuousAt_id.eventually_ne hz₀NZ)
    have hRootEv : ∀ᶠ z in 𝓝[≠] z₀, H.f.eval z ≠ 0 := by
      have hne : H.f ≠ 0 := by
        intro hzero
        have hd := H.h_degree
        rw [hzero, Polynomial.natDegree_zero] at hd
        omega
      have hfin : {x : ℂ | H.f.IsRoot x}.Finite :=
        Polynomial.finite_setOf_isRoot hne
      set R' : Set ℂ := {x : ℂ | H.f.IsRoot x} \ {z₀} with hR'
      have hR'closed : IsClosed R' := (hfin.subset Set.diff_subset).isClosed
      have hmem : R'ᶜ ∈ 𝓝 z₀ :=
        hR'closed.isOpen_compl.mem_nhds (by simp [hR'])
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with z hz hzc
      intro hzero
      exact hzc ⟨hzero, hz⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hSrcEv,
      eventually_nhdsWithin_of_eventually_nhds hInvSrcEv,
      eventually_nhdsWithin_of_eventually_nhds hZneEv, hRootEv] with z hzSrc hzInvSrc hzNZ hzEval
    let a : HyperellipticAffine H := liouvilleChosenAffinePoint (H := H) z
    let y : ℂ := a.val.2
    let v : ℂ := y * z⁻¹ ^ (H.f.natDegree / 2)
    have haY : a ∈ smoothLocusY H := by
      simpa [a] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hzEval
    have haσY : a.invol ∈ smoothLocusY H :=
      HyperellipticAffine.invol_mem_smoothLocusY a haY
    have hxA : a.val.1 ≠ 0 := by
      simpa [a] using hzNZ
    have hxAσ : a.invol.val.1 ≠ 0 := by
      simpa [HyperellipticAffine.invol] using hxA
    have hySq : y ^ 2 = H.f.eval z := by
      simpa [a, y] using liouvilleChosenAffinePoint_snd_sq (H := H) z
    have hyNZ : y ≠ 0 := by
      intro hy0
      apply hzEval
      simpa [hy0] using hySq.symm
    have hvNZ : v ≠ 0 := by
      exact mul_ne_zero hyNZ (pow_ne_zero _ (inv_ne_zero hzNZ))
    have hyTarget : y ∈ (affineChartProjY (H := H) p hpX).target := by
      have hmap : H.f.eval z ∈ e.target := by
        have heq : (e : ℂ → ℂ) z = H.f.eval z := by
          simp [e, polynomialLocalHomeomorph]
        simpa [heq] using e.map_source hzSrc
      change y ^ 2 ∈ e.target
      rwa [hySq]
    have hnegTarget : -y ∈ (affineChartProjY (H := H) p hpX).target := by
      have hy2Target : y ^ 2 ∈ e.target := by
        simpa [affineChartProjY, e] using hyTarget
      change (-y) ^ 2 ∈ e.target
      simpa [pow_two] using hy2Target
    have hxSymm : (affineChartProjY (H := H) p hpX).symm y = a := by
      apply Subtype.ext
      apply Prod.ext
      · have hfst := affineChartProjY_symm_apply_fst (H := H) p hpX hyTarget
        have hleft : e.symm (H.f.eval z) = z := by
          have hleft' := e.left_inv hzSrc
          have heq : (e : ℂ → ℂ) z = H.f.eval z := by
            simp [e, polynomialLocalHomeomorph]
          simpa [heq] using hleft'
        change ((affineChartProjY (H := H) p hpX).symm y).val.1 = a.val.1
        rw [hfst, hySq, hleft]
        rfl
      · change ((affineChartProjY (H := H) p hpX).symm y).val.2 = a.val.2
        simpa [a, y] using affineChartProjY_symm_apply_snd (H := H) p hpX hyTarget
    have hxNegSymm : (affineChartProjY (H := H) p hpX).symm (-y) = a.invol := by
      apply Subtype.ext
      apply Prod.ext
      · have hfst := affineChartProjY_symm_apply_fst (H := H) p hpX hnegTarget
        have hleft : e.symm (H.f.eval z) = z := by
          have hleft' := e.left_inv hzSrc
          have heq : (e : ℂ → ℂ) z = H.f.eval z := by
            simp [e, polynomialLocalHomeomorph]
          simpa [heq] using hleft'
        change ((affineChartProjY (H := H) p hpX).symm (-y)).val.1 = a.invol.val.1
        have hnegSq : (-y) ^ 2 = H.f.eval z := by
          simpa [sq] using hySq
        rw [hfst, hnegSq, hleft]
        rfl
      · change ((affineChartProjY (H := H) p hpX).symm (-y)).val.2 = a.invol.val.2
        have hsnd := affineChartProjY_symm_apply_snd (H := H) p hpX hnegTarget
        simpa [a, y, HyperellipticAffine.invol] using hsnd
    have hvSq : v ^ 2 = (Polynomial.reverse H.f).eval z⁻¹ := by
      show (y * z⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = _
      rw [mul_pow, hySq]
      have hpow_eq : (z⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = z⁻¹ ^ H.f.natDegree := by
        rw [← pow_mul]
        congr 1
        have heven : Even H.f.natDegree := Nat.not_odd_iff_even.mp hf.out
        obtain ⟨m, hm⟩ := heven
        omega
      rw [hpow_eq]
      exact (reverse_eval_inv_eq (H := H) z hzNZ).symm
    have hvTarget : v ∈ (affineChartProjY (H := Hrev) b hbX).target := by
      change v ^ 2 ∈ eInf.target
      rw [hvSq]
      have hmap : (eInf : ℂ → ℂ) z⁻¹ ∈ eInf.target := eInf.map_source hzInvSrc
      have hact : (eInf : ℂ → ℂ) z⁻¹ = (Polynomial.reverse H.f).eval z⁻¹ := by
        show Hrev.f.eval z⁻¹ = (Polynomial.reverse H.f).eval z⁻¹
        rfl
      simpa [hact] using hmap
    have hnegvTarget : -v ∈ (affineChartProjY (H := Hrev) b hbX).target := by
      have hv2Target : v ^ 2 ∈ eInf.target := by
        simpa [affineChartProjY, eInf] using hvTarget
      change (-v) ^ 2 ∈ eInf.target
      simpa [pow_two] using hv2Target
    have hu_eq : eInf.symm (v ^ 2) = z⁻¹ := by
      have hleft := eInf.left_inv hzInvSrc
      have hact : (eInf : ℂ → ℂ) z⁻¹ = (Polynomial.reverse H.f).eval z⁻¹ := by
        show Hrev.f.eval z⁻¹ = (Polynomial.reverse H.f).eval z⁻¹
        rfl
      rw [hact] at hleft
      simpa [hvSq] using hleft
    have huneg_eq : eInf.symm ((-v) ^ 2) = z⁻¹ := by
      simpa [pow_two] using hu_eq
    have hBranchSymm : (infinityLiftChart H hf.out b).symm v =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) := by
      have hbv_eq : ((affineChartProjY (H := Hrev) b hbX).symm v :
          HyperellipticAffine Hrev) = affineGluingImage a hxA := by
        apply Subtype.ext
        apply Prod.ext
        · change (((affineChartProjY (H := Hrev) b hbX).symm v :
            HyperellipticAffine Hrev).val.1) = (affineGluingImage a hxA).val.1
          rw [affineChartProjY_symm_apply_fst (H := Hrev) b hbX hvTarget, hu_eq]
          simp [affineGluingImage_val_fst, a]
        · change (((affineChartProjY (H := Hrev) b hbX).symm v :
            HyperellipticAffine Hrev).val.2) = (affineGluingImage a hxA).val.2
          rw [affineChartProjY_symm_apply_snd (H := Hrev) b hbX hvTarget]
          simp [affineGluingImage_val_snd, v, y, a]
      change ((affineChartAt (H := Hrev) b).lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out)).symm v =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
      rw [affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn]
      change Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inr ((affineChartProjY (H := Hrev) b hbX).symm v)) =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
      rw [hbv_eq]
      exact (proj_eq_affineGluingImage (H := H) a hxA).symm
    have hBranchNegSymm : (infinityLiftChart H hf.out b).symm (-v) =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a.invol) := by
      have hbv_eq : ((affineChartProjY (H := Hrev) b hbX).symm (-v) :
          HyperellipticAffine Hrev) = affineGluingImage a.invol hxAσ := by
        apply Subtype.ext
        apply Prod.ext
        · change (((affineChartProjY (H := Hrev) b hbX).symm (-v) :
            HyperellipticAffine Hrev).val.1) = (affineGluingImage a.invol hxAσ).val.1
          rw [affineChartProjY_symm_apply_fst (H := Hrev) b hbX hnegvTarget, huneg_eq]
          simp [affineGluingImage_val_fst, a, HyperellipticAffine.invol]
        · change (((affineChartProjY (H := Hrev) b hbX).symm (-v) :
            HyperellipticAffine Hrev).val.2) = (affineGluingImage a.invol hxAσ).val.2
          rw [affineChartProjY_symm_apply_snd (H := Hrev) b hbX hnegvTarget]
          simp [affineGluingImage_val_snd, v, y, a, HyperellipticAffine.invol, neg_mul]
      change ((affineChartAt (H := Hrev) b).lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out)).symm (-v) =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a.invol)
      rw [affineChartAt_of_not_mem_smoothLocusY (H := Hrev) b hbYn]
      change Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inr ((affineChartProjY (H := Hrev) b hbX).symm (-v))) =
        Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a.invol)
      rw [hbv_eq]
      exact (proj_eq_affineGluingImage (H := H) a.invol hxAσ).symm
    have hA :
        affCoeff (H := H) form a z =
          - (z⁻¹) ^ 2 * (M v / v) := by
      have h := affCoeff_eq_liouvilleInfinityProjYNumerator_div_of_branch
        (H := H) form b hbX hbYn q hQq a haY hxA hvTarget hvNZ hBranchSymm
        (by simpa [a] using hu_eq)
      simpa [M, a] using h
    have hσ :
        affCoeff (H := H) form a.invol z =
          - (z⁻¹) ^ 2 * (M (-v) / (-v)) := by
      have h := affCoeff_eq_liouvilleInfinityProjYNumerator_div_of_branch
        (H := H) form b hbX hbYn q hQq a.invol haσY hxAσ hnegvTarget
        (neg_ne_zero.mpr hvNZ) hBranchNegSymm
        (by simpa [a, HyperellipticAffine.invol] using huneg_eq)
      simpa [M, a, HyperellipticAffine.invol] using h
    rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl]
    rw [liouvilleTwoSheetSum_of_eval_ne_zero (H := H) form hzEval, hA, hσ]
    have hD : D v = (M v - M (-v)) / v := by
      simpa [D] using Jacobians.GeneralResults.dslope_oddPart_of_ne (h := M) (w := v) hvNZ
    rw [hD]
    field_simp [hvNZ]
    ring
  exact hModel.congr' hEq.symm

/-- Every affine branch point has a finite punctured limit for the direct
two-sheet sum, independent of whether `Quotient.out` chooses the affine branch
chart or the infinity branch chart. -/
theorem liouvilleTwoSheetSum_branch_tendsto
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    ∀ z₀, H.f.eval z₀ = 0 →
      ∃ L, Filter.Tendsto (liouvilleTwoSheetSum (H := H) form) (𝓝[≠] z₀) (𝓝 L) := by
  intro z₀ hz₀
  let p := liouvilleBranchPoint (H := H) z₀ hz₀
  let q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl p)
  cases hQ : Quotient.out q with
  | inl a =>
      have hOutEq : Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) = q := by
        rw [← hQ]
        exact Quotient.out_eq q
      have ha : a = p := by
        exact HyperellipticEvenProj.proj_inl_injective H (by
          simpa [q, HyperellipticEvenProj.proj, Function.comp_def] using hOutEq)
      have hQp : Quotient.out q = Sum.inl p := by
        simpa [ha] using hQ
      exact liouvilleTwoSheetSum_branch_tendsto_of_branch_out_inl
        (H := H) form hz₀ (by simpa [q, p] using hQp)
  | inr b =>
      exact liouvilleTwoSheetSum_branch_tendsto_of_branch_out_inr
        (H := H) form hz₀ (b := b) (by simpa [q, p] using hQ)

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
/-- The cocompact filter eventually avoids `0`. -/
theorem eventually_ne_zero_cocompact :
    ∀ᶠ z : ℂ in Filter.cocompact ℂ, z ≠ 0 := by
  rw [Filter.eventually_iff]
  rw [Filter.mem_cocompact]
  refine ⟨{0}, isCompact_singleton, ?_⟩
  intro z hz
  simpa using hz

omit hf in
/-- The cocompact filter eventually avoids the finite root set of `H.f`. -/
theorem eventually_eval_ne_zero_cocompact :
    ∀ᶠ z : ℂ in Filter.cocompact ℂ, H.f.eval z ≠ 0 := by
  have hfin : {x : ℂ | H.f.IsRoot x}.Finite :=
    Polynomial.finite_setOf_isRoot (hyperelliptic_f_ne_zero (H := H))
  rw [Filter.eventually_iff]
  rw [Filter.mem_cocompact]
  refine ⟨{x : ℂ | H.f.IsRoot x}, hfin.isCompact, ?_⟩
  intro z hz hzero
  exact hz hzero

omit hf in
/-- If `v²` is sufficiently close to `c²`, then `v` is close to one of the
two square roots `c` or `-c`. -/
lemma dist_sq_lt_or_dist_neg_lt {c v : ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : dist (v ^ 2) (c ^ 2) < ε * ε) :
    dist v c < ε ∨ dist v (-c) < ε := by
  by_cases hvc : dist v c < ε
  · exact Or.inl hvc
  · right
    by_contra hvm
    have h1 : ε ≤ ‖v - c‖ := by
      simpa [dist_eq_norm] using (le_of_not_gt hvc)
    have h2 : ε ≤ ‖v + c‖ := by
      have h2' : ε ≤ dist v (-c) := le_of_not_gt hvm
      simpa [dist_eq_norm, sub_neg_eq_add] using h2'
    have hdist : dist (v ^ 2) (c ^ 2) = ‖(v - c) * (v + c)‖ := by
      rw [dist_eq_norm]
      congr 1
      ring
    have hle : ε * ε ≤ ‖(v - c) * (v + c)‖ := by
      rw [norm_mul]
      exact mul_le_mul h1 h2 (le_of_lt hε) (norm_nonneg _)
    rw [hdist] at h
    linarith

omit hf in
/-- Inversion tends to `0` along the cocompact filter on `ℂ`. -/
theorem tendsto_inv_cocompact_zero :
    Filter.Tendsto (fun z : ℂ => z⁻¹) (Filter.cocompact ℂ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_inv] using (tendsto_norm_cocompact_atTop (E := ℂ)).inv_tendsto_atTop

theorem liouvilleChosenAffinePoint_infinity_sources_eventually_cocompact :
    ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      z ≠ 0 ∧ H.f.eval z ≠ 0 ∧
      ((Quotient.mk (hyperellipticEvenSetoid H)
            (Sum.inl (liouvilleChosenAffinePoint (H := H) z)) ∈
          (infinityLiftChart H hf.out (liouvilleInfinityPointPos H)).source ∧
        Quotient.mk (hyperellipticEvenSetoid H)
            (Sum.inl ((liouvilleChosenAffinePoint (H := H) z).invol)) ∈
          (infinityLiftChart H hf.out (liouvilleInfinityPointNeg H)).source) ∨
       (Quotient.mk (hyperellipticEvenSetoid H)
            (Sum.inl (liouvilleChosenAffinePoint (H := H) z)) ∈
          (infinityLiftChart H hf.out (liouvilleInfinityPointNeg H)).source ∧
        Quotient.mk (hyperellipticEvenSetoid H)
            (Sum.inl ((liouvilleChosenAffinePoint (H := H) z).invol)) ∈
          (infinityLiftChart H hf.out (liouvilleInfinityPointPos H)).source)) := by
  classical
  let c : ℂ := liouvilleInfinitySqrt H
  let Hrev := HyperellipticAffineInfinity.reverseData H hf.out
  let bPlus := liouvilleInfinityPointPos H
  let bMinus := liouvilleInfinityPointNeg H
  have hbPlusY : bPlus ∈ smoothLocusY Hrev := by
    simpa [bPlus, Hrev] using liouvilleInfinityPointPos_mem_smoothLocusY (H := H)
  have hbMinusY : bMinus ∈ smoothLocusY Hrev := by
    simpa [bMinus, Hrev] using liouvilleInfinityPointNeg_mem_smoothLocusY (H := H)
  let ePlus := squareLocalHomeomorph (H := Hrev) bPlus hbPlusY
  let eMinus := squareLocalHomeomorph (H := Hrev) bMinus hbMinusY
  have hcSrc : c ∈ ePlus.source := by
    have hbSrc : bPlus ∈ (affineChartProjX (H := Hrev) bPlus hbPlusY).source :=
      affineChartProjX_mem_source (H := Hrev) bPlus hbPlusY
    change bPlus.val.2 ∈ ePlus.source at hbSrc
    simpa [bPlus, c, ePlus, liouvilleInfinityPointPos] using hbSrc
  have hnegcSrc : -c ∈ eMinus.source := by
    have hbSrc : bMinus ∈ (affineChartProjX (H := Hrev) bMinus hbMinusY).source :=
      affineChartProjX_mem_source (H := Hrev) bMinus hbMinusY
    change bMinus.val.2 ∈ eMinus.source at hbSrc
    simpa [bMinus, c, eMinus, liouvilleInfinityPointNeg] using hbSrc
  obtain ⟨epsPlus, hepsPlus, hepsPlusSub⟩ := Metric.isOpen_iff.mp ePlus.open_source c hcSrc
  obtain ⟨epsMinus, hepsMinus, hepsMinusSub⟩ :=
    Metric.isOpen_iff.mp eMinus.open_source (-c) hnegcSrc
  let ε : ℝ := min epsPlus epsMinus
  have hε : 0 < ε := lt_min hepsPlus hepsMinus
  have hrev :
      Filter.Tendsto (fun z : ℂ => (Polynomial.reverse H.f).eval z⁻¹)
        (Filter.cocompact ℂ) (𝓝 (c ^ 2)) := by
    have hcont :
        Filter.Tendsto (fun u : ℂ => (Polynomial.reverse H.f).eval u)
          (𝓝 0) (𝓝 ((Polynomial.reverse H.f).eval 0)) :=
      (Polynomial.continuous (Polynomial.reverse H.f)).continuousAt
    have h := hcont.comp tendsto_inv_cocompact_zero
    simpa [c, reverse_eval_zero_eq_leadingCoeff (H := H),
      liouvilleInfinitySqrt_sq H] using h
  have hclose : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      dist ((Polynomial.reverse H.f).eval z⁻¹) (c ^ 2) < ε * ε :=
    hrev (Metric.ball_mem_nhds _ (mul_pos hε hε))
  filter_upwards [eventually_ne_zero_cocompact,
      eventually_eval_ne_zero_cocompact (H := H), hclose] with z hz0 hzEval hzClose
  let a := liouvilleChosenAffinePoint (H := H) z
  have haY : a ∈ smoothLocusY H := by
    simpa [a] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hzEval
  have hx : a.val.1 ≠ 0 := by
    simpa [a] using hz0
  have hxσ : a.invol.val.1 ≠ 0 := by
    simpa [HyperellipticAffine.invol] using hx
  let v : ℂ := a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2)
  have hv_sq : v ^ 2 = (Polynomial.reverse H.f).eval z⁻¹ := by
    have hmem :=
      HyperellipticAffineInfinity.mem_of_affine H hf.out a.val.1 a.val.2 a.property hx
    simpa [v, a] using hmem
  have hvClose : dist (v ^ 2) (c ^ 2) < ε * ε := by
    simpa [hv_sq] using hzClose
  have hvCases := dist_sq_lt_or_dist_neg_lt hε hvClose
  have hεPlusLe : ε ≤ epsPlus := min_le_left epsPlus epsMinus
  have hεMinusLe : ε ≤ epsMinus := min_le_right epsPlus epsMinus
  have hmk_source
      (b : HyperellipticAffineInfinity H)
      (hbY : b ∈ smoothLocusY Hrev)
      (hmem : affineGluingImage a hx ∈
        (affineChartProjX (H := Hrev) b hbY).source) :
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) ∈
        (infinityLiftChart H hf.out b).source :=
    quotient_mk_inl_mem_infinityLiftChart_source_of_gluing_mem
      (H := H) a hx b (by simpa [Hrev] using hbY) hmem
  have hmkσ_source
      (b : HyperellipticAffineInfinity H)
      (hbY : b ∈ smoothLocusY Hrev)
      (hmem : affineGluingImage a.invol hxσ ∈
        (affineChartProjX (H := Hrev) b hbY).source) :
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a.invol) ∈
        (infinityLiftChart H hf.out b).source :=
    quotient_mk_inl_mem_infinityLiftChart_source_of_gluing_mem
      (H := H) a.invol hxσ b (by simpa [Hrev] using hbY) hmem
  refine ⟨hz0, hzEval, ?_⟩
  rcases hvCases with hvNearPlus | hvNearMinus
  · left
    have hvSrcPlus : v ∈ ePlus.source :=
      hepsPlusSub (by
        rw [Metric.mem_ball]
        exact lt_of_lt_of_le hvNearPlus hεPlusLe)
    have hnegvSrcMinus : -v ∈ eMinus.source :=
      hepsMinusSub (by
        rw [Metric.mem_ball]
        have : dist (-v) (-c) = dist v c := by
          rw [dist_eq_norm, dist_eq_norm]
          rw [show -v - -c = -(v - c) by ring, norm_neg]
        rw [this]
        exact lt_of_lt_of_le hvNearPlus hεMinusLe)
    constructor
    · refine hmk_source bPlus hbPlusY ?_
      change (affineGluingImage a hx).val.2 ∈ ePlus.source
      simpa [v, ePlus, bPlus, Hrev] using hvSrcPlus
    · refine hmkσ_source bMinus hbMinusY ?_
      change (affineGluingImage a.invol hxσ).val.2 ∈ eMinus.source
      have hsnd : (affineGluingImage a.invol hxσ).val.2 = -v := by
        simp [v, inv_pow, HyperellipticAffine.invol, neg_mul]
      simpa [hsnd, v, inv_pow, eMinus, bMinus, Hrev] using hnegvSrcMinus
  · right
    have hvSrcMinus : v ∈ eMinus.source :=
      hepsMinusSub (by
        rw [Metric.mem_ball]
        exact lt_of_lt_of_le hvNearMinus hεMinusLe)
    have hnegvSrcPlus : -v ∈ ePlus.source :=
      hepsPlusSub (by
        rw [Metric.mem_ball]
        have : dist (-v) c = dist v (-c) := by
          rw [dist_eq_norm, dist_eq_norm]
          rw [show -v - c = -(v - -c) by ring, norm_neg]
        rw [this]
        exact lt_of_lt_of_le hvNearMinus hεPlusLe)
    constructor
    · refine hmk_source bMinus hbMinusY ?_
      change (affineGluingImage a hx).val.2 ∈ eMinus.source
      simpa [v, eMinus, bMinus, Hrev] using hvSrcMinus
    · refine hmkσ_source bPlus hbPlusY ?_
      change (affineGluingImage a.invol hxσ).val.2 ∈ ePlus.source
      have hsnd : (affineGluingImage a.invol hxσ).val.2 = -v := by
        simp [v, inv_pow, HyperellipticAffine.invol, neg_mul]
      simpa [hsnd, v, inv_pow, ePlus, bPlus, Hrev] using hnegvSrcPlus

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

/-- The removable two-sheet sum decays to zero at infinity. -/
theorem liouvilleTwoSheetSumRemovable_tendsto_zero_cocompact
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) :
    Filter.Tendsto (liouvilleTwoSheetSumRemovable (H := H) form)
      (Filter.cocompact ℂ) (𝓝 0) := by
  classical
  let bPlus := liouvilleInfinityPointPos H
  let bMinus := liouvilleInfinityPointNeg H
  let qPlus : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bPlus)
  let qMinus : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr bMinus)
  have hbPlusY : bPlus ∈
      smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
    simpa [bPlus] using liouvilleInfinityPointPos_mem_smoothLocusY (H := H)
  have hbMinusY : bMinus ∈
      smoothLocusY (HyperellipticAffineInfinity.reverseData H hf.out) := by
    simpa [bMinus] using liouvilleInfinityPointNeg_mem_smoothLocusY (H := H)
  have hQPlus : Quotient.out qPlus = Sum.inr bPlus := by
    simpa [qPlus, bPlus] using quotient_out_liouvilleInfinityPointPos (H := H)
  have hQMinus : Quotient.out qMinus = Sum.inr bMinus := by
    simpa [qMinus, bMinus] using quotient_out_liouvilleInfinityPointNeg (H := H)
  have hPlusAna : AnalyticAt ℂ (form.coeff qPlus) 0 := by
    simpa [qPlus, bPlus] using
      form_coeff_analyticAt_infinity_zero (H := H) form bPlus hbPlusY
        (by simp [bPlus, liouvilleInfinityPointPos]) qPlus hQPlus
  have hMinusAna : AnalyticAt ℂ (form.coeff qMinus) 0 := by
    simpa [qMinus, bMinus] using
      form_coeff_analyticAt_infinity_zero (H := H) form bMinus hbMinusY
        (by simp [bMinus, liouvilleInfinityPointNeg]) qMinus hQMinus
  have hPlus :
      Filter.Tendsto (fun z : ℂ => form.coeff qPlus (z⁻¹))
        (Filter.cocompact ℂ) (𝓝 (form.coeff qPlus 0)) :=
    hPlusAna.continuousAt.tendsto.comp tendsto_inv_cocompact_zero
  have hMinus :
      Filter.Tendsto (fun z : ℂ => form.coeff qMinus (z⁻¹))
        (Filter.cocompact ℂ) (𝓝 (form.coeff qMinus 0)) :=
    hMinusAna.continuousAt.tendsto.comp tendsto_inv_cocompact_zero
  have hFactor :
      Filter.Tendsto (fun z : ℂ => -1 / z ^ 2)
        (Filter.cocompact ℂ) (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_inv_cocompact_zero.pow 2).neg
  have hModel :
      Filter.Tendsto
        (fun z : ℂ =>
          (form.coeff qPlus (z⁻¹) + form.coeff qMinus (z⁻¹)) *
            (-1 / z ^ 2))
        (Filter.cocompact ℂ) (𝓝 0) := by
    have hsum := hPlus.add hMinus
    have hprod := hsum.mul hFactor
    simpa using hprod
  have hEq :
      liouvilleTwoSheetSumRemovable (H := H) form =ᶠ[Filter.cocompact ℂ]
        fun z : ℂ =>
          (form.coeff qPlus (z⁻¹) + form.coeff qMinus (z⁻¹)) *
            (-1 / z ^ 2) := by
    filter_upwards [liouvilleChosenAffinePoint_infinity_sources_eventually_cocompact
        (H := H)] with z hzPack
    rcases hzPack with ⟨_hz0, hzEval, hsrcCases⟩
    let a := liouvilleChosenAffinePoint (H := H) z
    have haY : a ∈ smoothLocusY H := by
      simpa [a] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hzEval
    have haσY : a.invol ∈ smoothLocusY H :=
      HyperellipticAffine.invol_mem_smoothLocusY a haY
    rw [liouvilleTwoSheetSumRemovable_of_eval_ne_zero (H := H) form hzEval]
    rw [liouvilleTwoSheetSum_of_eval_ne_zero (H := H) form hzEval]
    rcases hsrcCases with hPlusMinus | hMinusPlus
    · have hA : affCoeff (H := H) form a z =
          form.coeff qPlus (z⁻¹) * (-1 / z ^ 2) := by
        have h := affCoeff_eq_fixed_infinity_of_source
          (H := H) form a haY bPlus hbPlusY hQPlus hPlusMinus.1
        simpa [a, qPlus] using h
      have hσ : affCoeff (H := H) form a.invol z =
          form.coeff qMinus (z⁻¹) * (-1 / z ^ 2) := by
        have h := affCoeff_eq_fixed_infinity_of_source
          (H := H) form a.invol haσY bMinus hbMinusY hQMinus hPlusMinus.2
        simpa [a, qMinus, HyperellipticAffine.invol] using h
      rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl, hA, hσ]
      ring
    · have hA : affCoeff (H := H) form a z =
          form.coeff qMinus (z⁻¹) * (-1 / z ^ 2) := by
        have h := affCoeff_eq_fixed_infinity_of_source
          (H := H) form a haY bMinus hbMinusY hQMinus hMinusPlus.1
        simpa [a, qMinus] using h
      have hσ : affCoeff (H := H) form a.invol z =
          form.coeff qPlus (z⁻¹) * (-1 / z ^ 2) := by
        have h := affCoeff_eq_fixed_infinity_of_source
          (H := H) form a.invol haσY bPlus hbPlusY hQPlus hMinusPlus.2
        simpa [a, qPlus, HyperellipticAffine.invol] using h
      rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl, hA, hσ]
      ring
  exact hModel.congr' hEq.symm

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

/-- **σ-anti-invariance (unconditional).** For every holomorphic 1-form on the
even-degree hyperelliptic curve, the affine-`x` coefficients at the two sheets
over a non-branch point `z` are negatives of each other. This is the
direct-two-sheet-route conclusion (`s ≡ 0`): the three analytic inputs
`liouvilleTwoSheetSum_analyticAt_off_roots`, `liouvilleTwoSheetSum_branch_tendsto`,
and `liouvilleTwoSheetSumRemovable_tendsto_zero_cocompact` feed the
removable-extension Liouville capstone, forcing the two-sheet sum to vanish. -/
theorem affCoeff_chosen_anti_invariance
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z =
      -affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z).invol z :=
  chosen_coeff_eq_neg_of_liouvilleTwoSheetSumRemovable_eq_zero (H := H) form
    (liouvilleTwoSheetSumRemovable_eq_zero_of_analyticAt_off_roots_branch_tendsto_cocompact
      (H := H) form
      (liouvilleTwoSheetSum_analyticAt_off_roots (H := H) form)
      (liouvilleTwoSheetSum_branch_tendsto (H := H) form)
      (liouvilleTwoSheetSumRemovable_tendsto_zero_cocompact (H := H) form))
    hz

/-! ### L2: the single-sheet numerator `G = affCoeff·√f` is a polynomial -/

/-- **L2.1c** Fixed-chart analyticity of the single-sheet numerator. The numerator
in the chosen affine chart at `z₀`, `z ↦ affCoeff form a₀ z · √f(z)`, is analytic
at `z₀` — `affCoeff` analytic at the chart basepoint times the analytic `√f`
branch. (Mirror of `liouvilleChosenTwoSheetSum_analyticAt`, one term × √f.) -/
theorem liouvilleChosenNumeratorG_analyticAt
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ
      (fun z : ℂ =>
        affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z₀) z *
          (squareLocalHomeomorph (H := H) (liouvilleChosenAffinePoint (H := H) z₀)
              (liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀)).symm
            (H.f.eval z))
      z₀ := by
  classical
  set a₀ := liouvilleChosenAffinePoint (H := H) z₀ with ha₀def
  have ha₀Y : a₀ ∈ smoothLocusY H :=
    liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀
  have h1 : AnalyticAt ℂ (affCoeff (H := H) form a₀) z₀ :=
    affCoeff_analyticAt_basepoint (H := H) form a₀ ha₀Y
  have hz₀Target : z₀ ∈ (affineChartProjX (H := H) a₀ ha₀Y).target := by
    have ha₀Src : a₀ ∈ (affineChartProjX (H := H) a₀ ha₀Y).source :=
      affineChartProjX_mem_source (H := H) a₀ ha₀Y
    have h := (affineChartProjX (H := H) a₀ ha₀Y).map_source ha₀Src
    simpa [a₀] using h
  have h2 : AnalyticAt ℂ
      (fun z : ℂ => (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z)) z₀ :=
    AnalyticOn.analyticAt
      ((affineChartProjX (H := H) a₀ ha₀Y).open_target.mem_nhds hz₀Target)
      (squareLocalHomeomorph_symm_eval_analyticOn (H := H) a₀ ha₀Y)
  exact h1.mul h2

omit hf in
/-- **L2.1a** The `√f` branch flips sign between the two sheets: on the involuted
affine chart it is the negative of the branch on the original chart, at any `z`
where the two charts' inverse images are involutes. (Used in the cross-sheet case
of the single-sheet numerator's off-root analyticity.) -/
theorem squareLocalHomeomorph_symm_eval_invol_flip
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    (hpYσ : a.invol ∈ smoothLocusY H)
    {z : ℂ} (hzT : z ∈ (affineChartProjX (H := H) a hpY).target)
    (hzσT : z ∈ (affineChartProjX (H := H) a.invol hpYσ).target)
    (hpair : ((affineChartProjX (H := H) a.invol hpYσ).symm z : HyperellipticAffine H) =
      ((affineChartProjX (H := H) a hpY).symm z : HyperellipticAffine H).invol) :
    (squareLocalHomeomorph (H := H) a.invol hpYσ).symm (H.f.eval z) =
      -(squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) := by
  rw [← affineChartProjX_symm_apply_snd (H := H) a hpY hzT,
    ← affineChartProjX_symm_apply_snd (H := H) a.invol hpYσ hzσT, hpair]
  simp [HyperellipticAffine.invol]

/-- **L2.1b** The single-sheet numerator `G = affCoeff·√f` (raw form: `0` at
branch points). Off-branch it is the chosen-sheet `affCoeff` times the `√f`
branch; by σ-anti-invariance it is sheet-independent, hence well-defined. -/
noncomputable def liouvilleNumeratorGRaw
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) : ℂ → ℂ := by
  classical
  exact fun z =>
    if hz : H.f.eval z = 0 then
      0
    else
      affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z *
        (squareLocalHomeomorph (H := H) (liouvilleChosenAffinePoint (H := H) z)
            (liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz)).symm
          (H.f.eval z)

@[simp] theorem liouvilleNumeratorGRaw_of_eval_eq_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z = 0) :
    liouvilleNumeratorGRaw (H := H) form z = 0 := by
  simp [liouvilleNumeratorGRaw, hz]

theorem liouvilleNumeratorGRaw_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleNumeratorGRaw (H := H) form z =
      affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z *
        (squareLocalHomeomorph (H := H) (liouvilleChosenAffinePoint (H := H) z)
            (liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz)).symm
          (H.f.eval z) := by
  simp only [liouvilleNumeratorGRaw, dif_neg hz]

/-- **L2.1b** The removable extension of the single-sheet numerator: the branch
value is the punctured-neighbourhood limit (`Filter.limUnder`), making `G`
continuous (and ultimately entire). Off-branch it agrees with the raw numerator. -/
noncomputable def liouvilleNumeratorG
    (form : HolomorphicOneForm (HyperellipticEvenProj H)) : ℂ → ℂ :=
  fun z =>
    if H.f.eval z = 0 then
      Filter.limUnder (𝓝[≠] z) (liouvilleNumeratorGRaw (H := H) form)
    else
      liouvilleNumeratorGRaw (H := H) form z

theorem liouvilleNumeratorG_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    liouvilleNumeratorG (H := H) form z = liouvilleNumeratorGRaw (H := H) form z := by
  simp [liouvilleNumeratorG, hz]

/-- The raw single-sheet numerator is analytic away from branch points. Near a
non-branch basepoint, the arbitrary chosen sheet is one of the two fixed local
sheets; in the opposite-sheet case the coefficient and square-root signs both
flip, so the product agrees with the fixed analytic expression. -/
theorem liouvilleNumeratorGRaw_analyticAt_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticEvenProj H))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ (liouvilleNumeratorGRaw (H := H) form) z₀ := by
  classical
  let a₀ := liouvilleChosenAffinePoint (H := H) z₀
  have ha₀Y : a₀ ∈ smoothLocusY H := by
    simpa [a₀] using liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hz₀
  let a₀σ : HyperellipticAffine H := a₀.invol
  have ha₀σY : a₀σ ∈ smoothLocusY H := by
    simpa [a₀σ] using HyperellipticAffine.invol_mem_smoothLocusY a₀ ha₀Y
  let e₀ := affineChartProjX (H := H) a₀ ha₀Y
  let e₀σ := affineChartProjX (H := H) a₀σ ha₀σY
  let q₀ : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a₀)
  let q₀σ : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a₀σ)
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
    have hMap : e₀ a₀ = a₀.val.1 := by
      change a₀.val.1 = a₀.val.1
      rfl
    rw [show z₀ = a₀.val.1 by simp [a₀], ← hMap]
    exact e₀.left_inv ha₀Src
  have hSymm₀σ : e₀σ.symm z₀ = a₀σ := by
    have hMap : e₀σ a₀σ = a₀σ.val.1 := by
      change a₀σ.val.1 = a₀σ.val.1
      rfl
    rw [show z₀ = a₀σ.val.1 by simp [a₀σ, a₀, HyperellipticAffine.invol], ← hMap]
    exact e₀σ.left_inv ha₀σSrc
  have hProjCont₀ : ContinuousAt
      (fun z : ℂ =>
        Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀.symm z : HyperellipticAffine H))) z₀ :=
    continuous_quotient_mk'.continuousAt.comp
      ((continuous_inl.continuousAt).comp (e₀.continuousAt_symm hz₀Target))
  have hProjCont₀σ : ContinuousAt
      (fun z : ℂ =>
        Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀σ.symm z : HyperellipticAffine H))) z₀ :=
    continuous_quotient_mk'.continuousAt.comp
      ((continuous_inl.continuousAt).comp (e₀σ.continuousAt_symm hz₀σTarget))
  have hPref₀ : ∀ᶠ z in 𝓝 z₀,
      Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀.symm z : HyperellipticAffine H)) ∈
        (_root_.chartAt ℂ q₀ :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source := by
    have hqSrc : q₀ ∈ (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
      ChartedSpace.mem_chart_source q₀
    have hmem : (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source ∈
        𝓝 q₀ :=
      (_root_.chartAt ℂ q₀ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).open_source.mem_nhds hqSrc
    exact hProjCont₀.eventually (by simpa [q₀, hSymm₀] using hmem)
  have hPref₀σ : ∀ᶠ z in 𝓝 z₀,
      Quotient.mk (hyperellipticEvenSetoid H)
          (Sum.inl (e₀σ.symm z : HyperellipticAffine H)) ∈
        (_root_.chartAt ℂ q₀σ :
          OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source := by
    have hqSrc : q₀σ ∈ (_root_.chartAt ℂ q₀σ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source :=
      ChartedSpace.mem_chart_source q₀σ
    have hmem : (_root_.chartAt ℂ q₀σ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).source ∈
        𝓝 q₀σ :=
      (_root_.chartAt ℂ q₀σ :
        OpenPartialHomeomorph (HyperellipticEvenProj H) ℂ).open_source.mem_nhds hqSrc
    exact hProjCont₀σ.eventually (by simpa [q₀σ, hSymm₀σ] using hmem)
  have hBranchPair : ∀ᶠ z in 𝓝 z₀,
      e₀σ.symm z = (e₀.symm z).invol := by
    have h :=
      affineChartProjX_invol_symm_eq_eventually (H := H) a₀ ha₀Y
    simpa [a₀σ, e₀, e₀σ] using h
  have hEval : ∀ᶠ z in 𝓝 z₀, H.f.eval z ≠ 0 :=
    (Polynomial.continuous H.f).continuousAt.eventually_ne hz₀
  have hEq : (fun z : ℂ =>
        affCoeff (H := H) form a₀ z *
          (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z)) =ᶠ[𝓝 z₀]
      liouvilleNumeratorGRaw (H := H) form := by
    filter_upwards [e₀.open_target.mem_nhds hz₀Target,
      e₀σ.open_target.mem_nhds hz₀σTarget, hPref₀, hPref₀σ, hBranchPair, hEval]
      with z hzT hzσT hSrcPref hSrcPrefσ hPair hzNZ
    let p₀ : HyperellipticAffine H := e₀.symm z
    let p₀σ : HyperellipticAffine H := e₀σ.symm z
    have hp₀σ_eq : p₀σ = p₀.invol := by
      simpa [p₀, p₀σ] using hPair
    have hp₀Y : p₀ ∈ smoothLocusY H := by
      show p₀.val.2 ≠ 0
      have hne := squareLocalHomeomorph_symm_ne_zero (H := H) a₀ ha₀Y hzT
      simpa [p₀, e₀, affineChartProjX_symm_apply_snd (H := H) a₀ ha₀Y hzT]
        using hne
    have hp₀σY : p₀.invol ∈ smoothLocusY H :=
      HyperellipticAffine.invol_mem_smoothLocusY p₀ hp₀Y
    have hp₀Src : p₀ ∈ (affineChartProjX (H := H) p₀ hp₀Y).source :=
      affineChartProjX_mem_source (H := H) p₀ hp₀Y
    have hp₀σSrc : p₀.invol ∈
        (affineChartProjX (H := H) p₀.invol hp₀σY).source :=
      affineChartProjX_mem_source (H := H) p₀.invol hp₀σY
    have hp₀Fst : p₀.val.1 = z := by
      simpa [p₀, e₀] using affineChartProjX_symm_apply_fst (H := H) a₀ ha₀Y hzT
    have hzP : z ∈ (affineChartProjX (H := H) p₀ hp₀Y).target := by
      have h : p₀.val.1 ∈ (affineChartProjX (H := H) p₀ hp₀Y).target := by
        simpa using (affineChartProjX (H := H) p₀ hp₀Y).map_source hp₀Src
      simpa [hp₀Fst] using h
    have hzPσ : z ∈ (affineChartProjX (H := H) p₀.invol hp₀σY).target := by
      have h : p₀.invol.val.1 ∈
          (affineChartProjX (H := H) p₀.invol hp₀σY).target := by
        simpa using (affineChartProjX (H := H) p₀.invol hp₀σY).map_source hp₀σSrc
      simpa [HyperellipticAffine.invol, hp₀Fst] using h
    have hSymmP : (affineChartProjX (H := H) p₀ hp₀Y).symm z = p₀ := by
      have hMap : (affineChartProjX (H := H) p₀ hp₀Y) p₀ = p₀.val.1 := by
        change p₀.val.1 = p₀.val.1
        rfl
      rw [← hp₀Fst, ← hMap]
      exact (affineChartProjX (H := H) p₀ hp₀Y).left_inv hp₀Src
    have hSymmPσ :
        (affineChartProjX (H := H) p₀.invol hp₀σY).symm z = p₀.invol := by
      have hMap : (affineChartProjX (H := H) p₀.invol hp₀σY) p₀.invol =
          p₀.invol.val.1 := by
        change p₀.invol.val.1 = p₀.invol.val.1
        rfl
      rw [show z = p₀.invol.val.1 by simp [HyperellipticAffine.invol, hp₀Fst], ← hMap]
      exact (affineChartProjX (H := H) p₀.invol hp₀σY).left_inv hp₀σSrc
    have hPairP :
        (affineChartProjX (H := H) p₀.invol hp₀σY).symm z =
          ((affineChartProjX (H := H) p₀ hp₀Y).symm z).invol := by
      rw [hSymmPσ, hSymmP]
    have hFix₀ : affCoeff (H := H) form a₀ z =
        affCoeff (H := H) form p₀ z := by
      simpa [a₀, e₀, p₀, q₀] using
        affCoeff_eq_of_projX_symm (H := H) form a₀ ha₀Y hzT hSrcPref
    have hBranchAgree :
        (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z) =
          (squareLocalHomeomorph (H := H) p₀ hp₀Y).symm (H.f.eval z) := by
      have hSymInY :
          (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z) ∈
            (squareLocalHomeomorph (H := H) p₀ hp₀Y).source := by
        have h2 := affineChartProjX_symm_apply_snd (H := H) a₀ ha₀Y hzT
        rw [← h2]
        exact hp₀Src
      exact squareLocalHomeomorph_symm_eq_of_mem (H := H) a₀ p₀ ha₀Y hp₀Y hzT hSymInY
    let a := liouvilleChosenAffinePoint (H := H) z
    have haSq : a.val.2 ^ 2 = H.f.eval z := by
      simpa [a] using liouvilleChosenAffinePoint_snd_sq (H := H) z
    have hp₀Sq : p₀.val.2 ^ 2 = H.f.eval z := by
      have hprop := p₀.property
      simpa [hp₀Fst] using hprop
    have hSheets := eq_or_eq_neg_of_sq_eq_sq a.val.2 p₀.val.2 (haSq.trans hp₀Sq.symm)
    rw [liouvilleNumeratorGRaw_of_eval_ne_zero (H := H) form hzNZ]
    rcases hSheets with hSame | hOpp
    · have ha_eq : a = p₀ := by
        apply Subtype.ext
        apply Prod.ext
        · simp [a, p₀, hp₀Fst]
        · exact hSame
      calc
        affCoeff (H := H) form a₀ z *
            (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z) =
          affCoeff (H := H) form p₀ z *
            (squareLocalHomeomorph (H := H) p₀ hp₀Y).symm (H.f.eval z) := by
            rw [hFix₀, hBranchAgree]
        _ = affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z *
            (squareLocalHomeomorph (H := H) (liouvilleChosenAffinePoint (H := H) z)
              (liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hzNZ)).symm
              (H.f.eval z) := by
            simp [a, ha_eq]
    · have ha_eq : a = p₀.invol := by
        apply Subtype.ext
        apply Prod.ext
        · simp [a, p₀, hp₀Fst, HyperellipticAffine.invol]
        · simpa [HyperellipticAffine.invol] using hOpp
      have hCoeffFlip : affCoeff (H := H) form p₀.invol z =
          -affCoeff (H := H) form p₀ z := by
        have hAnti := affCoeff_chosen_anti_invariance (H := H) form hzNZ
        rw [show liouvilleChosenAffinePoint (H := H) z = a from rfl] at hAnti
        rw [ha_eq, HyperellipticAffine.invol_invol] at hAnti
        exact hAnti
      have hBranchFlip :
          (squareLocalHomeomorph (H := H) p₀.invol hp₀σY).symm (H.f.eval z) =
            -(squareLocalHomeomorph (H := H) p₀ hp₀Y).symm (H.f.eval z) :=
        squareLocalHomeomorph_symm_eval_invol_flip (H := H) p₀ hp₀Y hp₀σY
          hzP hzPσ hPairP
      calc
        affCoeff (H := H) form a₀ z *
            (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z) =
          affCoeff (H := H) form p₀ z *
            (squareLocalHomeomorph (H := H) p₀ hp₀Y).symm (H.f.eval z) := by
            rw [hFix₀, hBranchAgree]
        _ = (-affCoeff (H := H) form p₀ z) *
            (-(squareLocalHomeomorph (H := H) p₀ hp₀Y).symm (H.f.eval z)) := by
            ring
        _ = affCoeff (H := H) form p₀.invol z *
            (squareLocalHomeomorph (H := H) p₀.invol hp₀σY).symm (H.f.eval z) := by
            rw [hCoeffFlip, hBranchFlip]
        _ = affCoeff (H := H) form (liouvilleChosenAffinePoint (H := H) z) z *
            (squareLocalHomeomorph (H := H) (liouvilleChosenAffinePoint (H := H) z)
              (liouvilleChosenAffinePoint_mem_smoothLocusY (H := H) hzNZ)).symm
              (H.f.eval z) := by
            simp [a, ha_eq]
  exact (liouvilleChosenNumeratorG_analyticAt (H := H) form hz₀).congr
    (by simpa [a₀] using hEq)

end Jacobians.ProjectiveCurve
