/-
Canonical period integral of a holomorphic 1-form along an analytic arc.
-/
import Submission.Jacobians.RiemannSurface.PartitionIndependence

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The canonical moving-chart integral of a holomorphic 1-form along an
analytic arc. -/
noncomputable def canonicalArcIntegral (γ : AnalyticArc X)
    (form : HolomorphicOneForm X) : ℂ :=
  ∫ r in (0 : ℝ)..1, canonicalIntegrand γ form r

/-- The canonical moving-chart integrand is additive in the holomorphic
1-form. -/
theorem canonicalIntegrand_add (γ : AnalyticArc X)
    (form₁ form₂ : HolomorphicOneForm X) (r : ℝ) :
    canonicalIntegrand γ (form₁ + form₂) r =
      canonicalIntegrand γ form₁ r + canonicalIntegrand γ form₂ r := by
  simp [canonicalIntegrand, HolomorphicOneForm.coeff_add, add_mul]

/-- The canonical moving-chart integrand is homogeneous in the holomorphic
1-form. -/
theorem canonicalIntegrand_smul (γ : AnalyticArc X) (c : ℂ)
    (form : HolomorphicOneForm X) (r : ℝ) :
    canonicalIntegrand γ (c • form) r = c * canonicalIntegrand γ form r := by
  simp [canonicalIntegrand, HolomorphicOneForm.coeff_smul, mul_assoc]

/-- The canonical arc integral is additive in the holomorphic 1-form, assuming
the two summand integrands are interval-integrable. -/
theorem canonicalArcIntegral_add (γ : AnalyticArc X)
    (form₁ form₂ : HolomorphicOneForm X)
    (h₁ : IntervalIntegrable (canonicalIntegrand γ form₁) MeasureTheory.volume 0 1)
    (h₂ : IntervalIntegrable (canonicalIntegrand γ form₂) MeasureTheory.volume 0 1) :
    canonicalArcIntegral γ (form₁ + form₂) =
      canonicalArcIntegral γ form₁ + canonicalArcIntegral γ form₂ := by
  unfold canonicalArcIntegral
  simp_rw [canonicalIntegrand_add γ form₁ form₂]
  exact intervalIntegral.integral_add h₁ h₂

/-- The canonical arc integral is homogeneous in the holomorphic 1-form. -/
theorem canonicalArcIntegral_smul (γ : AnalyticArc X) (c : ℂ)
    (form : HolomorphicOneForm X) :
    canonicalArcIntegral γ (c • form) = c * canonicalArcIntegral γ form := by
  unfold canonicalArcIntegral
  simp_rw [canonicalIntegrand_smul γ c form]
  exact intervalIntegral.integral_const_mul c (canonicalIntegrand γ form)

end Jacobians.RiemannSurface
