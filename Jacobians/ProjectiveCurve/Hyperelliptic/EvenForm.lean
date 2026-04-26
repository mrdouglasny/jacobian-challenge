/-
# Unified coefficient family on `HyperellipticEvenProj H`

Combines the affine bundle (`AffineForm.lean`) and the affine-infinity
bundle (`AffineInfinityForm.lean`) into a coefficient family on the
quotient `HyperellipticEvenProj H`. Two of the three submodule
predicates -- `IsHolomorphicOneFormCoeff` and `IsZeroOffChartTarget` --
follow directly from the summand bundles via case-split on
`Quotient.out`.

The third predicate -- `SatisfiesCotangentCocycle` -- splits into:
* same-summand cases: handled by the within-summand cocycle bundles
  from S3/S4.
* cross-summand cases (`Sum.inl × Sum.inr` and symmetric): the
  Möbius-transition gluing region. Currently axiomatized at the
  smoothness level (in `EvenAtlas.lean`); the cocycle equation will
  follow once those smoothness axioms are discharged with explicit
  chain-rule computations on `x ↦ 1/x` and the polynomial-root
  corrections.

The coefficient is parametrized by **two** polynomials `g_aff` and
`g_inf` -- one for each summand. For the form to be globally well-
defined (i.e. the cross-summand cocycle to close), `g_aff` and `g_inf`
must be related by the Möbius transformation
`g_inf(u) du/v = g_aff(1/u) (-du/u²) (u^(g+1)/v)`. This relation is
encoded in S5; here we set up the framework before assembling it.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.ProjectiveCurve.Hyperelliptic.AffineInfinityForm
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas

namespace Jacobians.ProjectiveCurve.HyperellipticEvenProj

open scoped Manifold ContDiff Topology
open Polynomial
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticAffineInfinity

variable {H : HyperellipticData}

/-- Unified coefficient family on `HyperellipticEvenProj H`: dispatch
to the affine or affine-infinity coefficient by case-splitting on
`Quotient.out q`. -/
noncomputable def hyperellipticEvenCoeff
    [hf : Fact (¬ Odd H.f.natDegree)]
    (g_aff g_inf : Polynomial ℂ) :
    HyperellipticEvenProj H → ℂ → ℂ := fun q =>
  match Quotient.out q with
  | Sum.inl a => hyperellipticAffineCoeff (H := H) g_aff a
  | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) g_inf b

/-- The unified coefficient is analytic on each chart target. -/
theorem hyperellipticEvenCoeff_isHolomorphicOneFormCoeff
    [hf : Fact (¬ Odd H.f.natDegree)] (g_aff g_inf : Polynomial ℂ) :
    IsHolomorphicOneFormCoeff (HyperellipticEvenProj H)
      (hyperellipticEvenCoeff (H := H) g_aff g_inf) := by
  intro q
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (chartAt H hf.out q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (chartAt H hf.out q).target
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt]
  unfold chartAt
  rcases hQ : Quotient.out q with a | b
  · simp only [hQ]
    show AnalyticOn ℂ _
      (((HyperellipticAffine.affineChartAt (H := H) a)
        : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).lift_openEmbedding
          (isOpenEmbedding_proj_inl H hf.out)).target
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineCoeff (H := H) g_aff a := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have h := hyperellipticAffineCoeff_isHolomorphicOneFormCoeff
      (H := H) g_aff a
    have hExtA : (extChartAt 𝓘(ℂ, ℂ) a).target =
        ((HyperellipticAffine.affineChartAt (H := H) a)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    rw [hExtA] at h
    exact h
  · simp only [hQ]
    show AnalyticOn ℂ _
      (((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)
        : OpenPartialHomeomorph (HyperellipticAffineInfinity H) ℂ).lift_openEmbedding
          (isOpenEmbedding_proj_inr H hf.out)).target
    rw [OpenPartialHomeomorph.lift_openEmbedding_target]
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineInfinityCoeff (H := H) g_inf b := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have h := hyperellipticAffineInfinityCoeff_isHolomorphicOneFormCoeff
      (H := H) g_inf b
    have hExtB : (extChartAt 𝓘(ℂ, ℂ) b).target =
        ((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    rw [hExtB] at h
    convert h using 1

/-- The unified coefficient vanishes off each chart target. -/
theorem hyperellipticEvenCoeff_isZeroOffChartTarget
    [hf : Fact (¬ Odd H.f.natDegree)] (g_aff g_inf : Polynomial ℂ) :
    IsZeroOffChartTarget (HyperellipticEvenProj H)
      (hyperellipticEvenCoeff (H := H) g_aff g_inf) := by
  intro q z hz
  have hExt : (extChartAt 𝓘(ℂ, ℂ) q).target =
      ((chartAt H hf.out q)).target := by
    rw [extChartAt_target]
    show ↑𝓘(ℂ, ℂ).symm ⁻¹' (chartAt H hf.out q).target ∩ Set.range ↑𝓘(ℂ, ℂ) =
      (chartAt H hf.out q).target
    show _ ∩ Set.range (id : ℂ → ℂ) = _
    rw [Set.range_id, Set.inter_univ]
    rfl
  rw [hExt] at hz
  unfold chartAt at hz
  rcases hQ : Quotient.out q with a | b
  · simp only [hQ] at hz
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineCoeff (H := H) g_aff a := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have hLift : (affineLiftChart H hf.out a).target =
        (HyperellipticAffine.affineChartAt (H := H) a).target := by
      simp [affineLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hLift] at hz
    have h := hyperellipticAffineCoeff_isZeroOffChartTarget (H := H) g_aff a
    have hExtA : (extChartAt 𝓘(ℂ, ℂ) a).target =
        ((HyperellipticAffine.affineChartAt (H := H) a)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    apply h
    rw [hExtA]; exact hz
  · simp only [hQ] at hz
    have hCoeff : hyperellipticEvenCoeff (H := H) g_aff g_inf q =
        hyperellipticAffineInfinityCoeff (H := H) g_inf b := by
      unfold hyperellipticEvenCoeff
      rw [hQ]
    rw [hCoeff]
    have hLift : (infinityLiftChart H hf.out b).target =
        (HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b).target := by
      simp [infinityLiftChart, OpenPartialHomeomorph.lift_openEmbedding_target]
    rw [hLift] at hz
    have h := hyperellipticAffineInfinityCoeff_isZeroOffChartTarget
      (H := H) g_inf b
    have hExtB : (extChartAt 𝓘(ℂ, ℂ) b).target =
        ((HyperellipticAffine.affineChartAt
          (H := HyperellipticAffineInfinity.reverseData H hf.out) b)).target := by
      rw [extChartAt_target]
      show _ ∩ Set.range (id : ℂ → ℂ) = _
      rw [Set.range_id, Set.inter_univ]
      rfl
    apply h
    rw [hExtB]; exact hz

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
