import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff
open Jacobians.RiemannSurface
open Polynomial

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- Custom induction principle for `HyperellipticOdd H h` to avoid unfolding it to
`OnePoint (HyperellipticAffine H)` during proofs. This ensures typeclass search
can find the `ChartedSpace` and `IsManifold` instances. -/
@[elab_as_elim]
protected theorem rec {C : HyperellipticOdd H h → Prop}
    (infty_val : C infty)
    (coe_val : ∀ (a : HyperellipticAffine H), C (a : HyperellipticOdd H h)) :
    ∀ (p : HyperellipticOdd H h), C p := by
  intro p
  change OnePoint (HyperellipticAffine H) at p
  induction p with
  | infty =>
    change C infty
    exact infty_val
  | coe a =>
    change C (coe a)
    exact coe_val a

/-- The unified coefficient family for `g(x) dx / y` on the odd curve `HyperellipticOdd H h`. -/
noncomputable def hyperellipticOddCoeff (g : Polynomial ℂ) (p : HyperellipticOdd H h) :
    ℂ → ℂ := fun z => by
  classical
  let p' : OnePoint (HyperellipticAffine H) := p
  exact p'.elim
    (if hz : z ∈ (infinityChart H h).target then
       if z = 0 then
         -2 * g.coeff (H.genus - 1) / H.f.leadingCoeff
       else
         let x := (infinityInverseMap H h z).val.1
         2 * g.eval x * x ^ (H.genus + 2) /
           (x * (Polynomial.derivative H.f).eval x - (2 * H.genus + 2) * H.f.eval x)
     else 0)
    (fun a => HyperellipticAffine.hyperellipticAffineCoeff g a z)

theorem hyperellipticOddCoeff_zero :
    hyperellipticOddCoeff (H := H) (h := h) 0 = 0 := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [mul_zero, zero_div]
    · simp only [Polynomial.eval_zero, mul_zero, zero_mul, zero_div]
    · rfl
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_zero]
    rfl

theorem hyperellipticOddCoeff_add (g g' : Polynomial ℂ) :
    hyperellipticOddCoeff (H := H) (h := h) (g + g') =
      hyperellipticOddCoeff g + hyperellipticOddCoeff g' := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    simp only [Pi.add_apply]
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [Polynomial.coeff_add]
      ring
    · simp only [Polynomial.eval_add]
      ring
    · ring
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_add g g']
    rfl

theorem hyperellipticOddCoeff_smul (c : ℂ) (g : Polynomial ℂ) :
    hyperellipticOddCoeff (H := H) (h := h) (c • g) =
      c • hyperellipticOddCoeff g := by
  funext p z
  unfold hyperellipticOddCoeff
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    simp only [Pi.smul_apply, smul_eq_mul]
    dsimp [infty]
    split_ifs with hz hz0
    · simp only [Polynomial.coeff_smul, smul_eq_mul]
      ring
    · simp only [Polynomial.eval_smul, smul_eq_mul]
      ring
    · ring
  | coe_val a =>
    rw [HyperellipticAffine.hyperellipticAffineCoeff_smul c g]
    rfl

/-- The coefficient family is zero off each chart target. -/
theorem hyperellipticOddCoeff_isZeroOffChartTarget (g : Polynomial ℂ) :
    IsZeroOffChartTarget (HyperellipticOdd H h)
      (hyperellipticOddCoeff (H := H) (h := h) g) := by
  intro p z hz
  induction p using HyperellipticOdd.rec with
  | infty_val =>
    unfold hyperellipticOddCoeff
    have hExt : (extChartAt 𝓘(ℂ, ℂ) (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target := by
      change Set.univ ∩ (chartAt (infty : HyperellipticOdd H h)).target =
        (infinityChart H h).target
      rw [Set.univ_inter]
      rfl
    rw [hExt] at hz
    dsimp [infty] at *
    split_ifs
    rfl
  | coe_val a =>
    unfold hyperellipticOddCoeff
    have hExt_lift : (extChartAt 𝓘(ℂ, ℂ) (a : HyperellipticOdd H h)).target =
        (extChartAt 𝓘(ℂ, ℂ) a).target := by
      change Set.univ ∩ (chartAt (a : HyperellipticOdd H h)).target =
        Set.univ ∩ (ChartedSpace.chartAt a).target
      dsimp [coe, HyperellipticOdd.coe]
      rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hExt_lift] at hz
    dsimp [coe] at *
    exact HyperellipticAffine.hyperellipticAffineCoeff_isZeroOffChartTarget g a z hz

/-- The coefficient family is analytic on the affine charts. -/
theorem hyperellipticOddCoeff_analyticOn_affineLift
    (g : Polynomial ℂ) (a : HyperellipticAffine H) :
    AnalyticOn ℂ (hyperellipticOddCoeff (h := h) g (coe a))
      (affineLiftChart (h := h) a).target := by
  have hCoeff : hyperellipticOddCoeff (h := h) g (coe a) =
      HyperellipticAffine.hyperellipticAffineCoeff g a := rfl
  rw [hCoeff]
  have hLift : (affineLiftChart (h := h) a).target = (extChartAt 𝓘(ℂ, ℂ) a).target := by
    change (affineLiftChart (h := h) a).target = Set.univ ∩ (ChartedSpace.chartAt a).target
    rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [Set.univ_inter]
  rw [hLift]
  exact HyperellipticAffine.hyperellipticAffineCoeff_isHolomorphicOneFormCoeff g a

/-- Same-summand cocycle equation holds on overlaps of affine charts. -/
theorem hyperellipticOddCoeff_cocycle_coe_coe (g : Polynomial ℂ) (p q : HyperellipticAffine H)
    {z : ℂ} (hz : z ∈ (affineLiftChart (h := h) p).target)
    (hsrc : (affineLiftChart (h := h) p).symm z ∈ (affineLiftChart (h := h) q).source) :
    hyperellipticOddCoeff (h := h) g (coe p) z =
      hyperellipticOddCoeff (h := h) g (coe q) ((affineLiftChart (h := h) q)
        ((affineLiftChart (h := h) p).symm z)) *
        (fderiv ℂ ((affineLiftChart (h := h) q) ∘ (affineLiftChart (h := h) p).symm) z 1) := by
  have hp : hyperellipticOddCoeff (h := h) g (coe p) =
      HyperellipticAffine.hyperellipticAffineCoeff g p := rfl
  have hq : hyperellipticOddCoeff (h := h) g (coe q) =
      HyperellipticAffine.hyperellipticAffineCoeff g q := rfl
  rw [hp, hq]
  have hExt_target : (extChartAt 𝓘(ℂ, ℂ) p).target = (affineLiftChart (h := h) p).target := by
    change Set.univ ∩ (ChartedSpace.chartAt p).target = (affineLiftChart (h := h) p).target
    rw [Set.univ_inter]
    rw [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
  have hz_aff : z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target := by
    rw [hExt_target]; exact hz
  have hsrc_aff : (extChartAt 𝓘(ℂ, ℂ) p).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) q).source := by
    rw [extChartAt_source 𝓘(ℂ, ℂ) q]
    have hSymm : (extChartAt 𝓘(ℂ, ℂ) p).symm z =
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm z := rfl
    rw [hSymm]
    have hsrc' := hsrc
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
      OpenPartialHomeomorph.lift_openEmbedding_source] at hsrc'
    obtain ⟨w, hw, heq⟩ := hsrc'
    have heq' : w = (ChartedSpace.chartAt p : OpenPartialHomeomorph
      (HyperellipticAffine H) ℂ).symm z := by
      exact OnePoint.coe_injective heq
    rw [← heq']
    exact hw
  have hLift_apply : (affineLiftChart (h := h) q) ((affineLiftChart (h := h) p).symm z) =
      (ChartedSpace.chartAt q : OpenPartialHomeomorph (HyperellipticAffine H) ℂ)
        ((ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm z) := by
    simp only [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_symm,
      Function.comp_apply, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [hLift_apply]
  have hFderiv : fderiv ℂ ((affineLiftChart (h := h) q) ∘ (affineLiftChart (h := h) p).symm) z =
      fderiv ℂ ((ChartedSpace.chartAt q : OpenPartialHomeomorph (HyperellipticAffine H) ℂ) ∘
        (ChartedSpace.chartAt p : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).symm) z := by
    refine Filter.EventuallyEq.fderiv_eq
      (Filter.eventuallyEq_of_mem (s := (affineLiftChart (h := h) p).target) ?_ ?_)
    · exact (affineLiftChart (h := h) p).open_target.mem_nhds hz
    · intro w hw
      simp only [Function.comp_apply, affineLiftChart,
        OpenPartialHomeomorph.lift_openEmbedding_symm,
        OpenPartialHomeomorph.lift_openEmbedding_apply]
  rw [hFderiv]
  exact HyperellipticAffine.hyperellipticAffineCoeff_satisfiesCotangentCocycle
    g p q z hz_aff hsrc_aff

end Jacobians.ProjectiveCurve.HyperellipticOdd
