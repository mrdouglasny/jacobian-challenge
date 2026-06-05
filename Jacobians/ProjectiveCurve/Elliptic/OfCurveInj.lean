import Jacobians.ProjectiveCurve.Elliptic.Periods
import Jacobians.Axioms.AbelJacobiMap

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Jacobians.RiemannSurface
open Jacobians.AbelianVariety
open Jacobians.Axioms

variable {ω₁ ω₂ : ℂ} {h : LinearIndependent ℝ ![ω₁, ω₂]}

namespace EllipticOfCurveInj

/-- The invariant differential `dz` has coefficient `1` at every chart center. -/
theorem ellipticDz_coeff_chart_center (P : Elliptic ω₁ ω₂ h) :
    (ellipticDz ω₁ ω₂ h).coeff P ((extChartAt 𝓘(ℂ, ℂ) P) P) = 1 := by
  change Set.indicator _ (fun _ => (1 : ℂ)) _ = 1
  exact Set.indicator_of_mem (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) P) _

/-- Along a bridge path on an elliptic curve, the canonical `dz` integrand is
the derivative of any differentiable universal-cover lift supplied by
`ComplexTorus.exists_lift_of_chart_path`. -/
theorem bridgePath_canonicalIntegrand_ellipticDz_eq_lift_deriv
    (P₀ Q : Elliptic ω₁ ω₂ h) (liftBP : ℝ → ℂ)
    (hlift_deriv : ∀ t : ℝ,
      deriv liftBP t =
        deriv ((extChartAt 𝓘(ℂ, ℂ)
          (Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q t)) ∘
            Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q) t)
    (t : ℝ) :
    canonicalIntegrand (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
        (ellipticDz ω₁ ω₂ h) t =
      deriv liftBP t := by
  rw [canonicalIntegrand]
  rw [ellipticDz_coeff_chart_center]
  rw [one_mul]
  rw [hlift_deriv]
  rfl

/-- The canonical `dz` integrand along a bridge path is interval-integrable. -/
theorem bridgePath_canonicalIntegrand_ellipticDz_intervalIntegrable
    (P₀ Q : Elliptic ω₁ ω₂ h) :
    IntervalIntegrable
      (canonicalIntegrand
        (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
        (ellipticDz ω₁ ω₂ h)) MeasureTheory.volume 0 1 := by
  let f : ℝ → ℂ := fun t =>
    (Jacobians.Bridge.bridgeForm (ellipticDz ω₁ ω₂ h)).toFun
      (Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q t)
      (Jacobians.Vendor.Kirov.pathSpeed
        (Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q) t)
  have hf : IntervalIntegrable f MeasureTheory.volume 0 1 :=
    Jacobians.Bridge.bridgePath_lineIntegrable
      (X := Elliptic ω₁ ω₂ h) P₀ Q (ellipticDz ω₁ ω₂ h)
  refine hf.congr ?_
  intro t _ht
  exact Jacobians.Bridge.bridge_kirov_integrand_eq_canonicalIntegrand
    (X := Elliptic ω₁ ω₂ h) P₀ Q (ellipticDz ω₁ ω₂ h) t

/-- Lift-based computation of the bridge integral of `dz`: it is the endpoint
difference of the universal-cover lift of the bridge path. -/
theorem bridgePath_canonicalArcIntegral_ellipticDz_eq_lift_sub
    (P₀ Q : Elliptic ω₁ ω₂ h) :
    ∃ liftBP : ℝ → ℂ,
      (∀ t : ℝ,
        (QuotientAddGroup.mk' (ellipticLattice ω₁ ω₂ h).toAddSubgroup
          (liftBP t) : Elliptic ω₁ ω₂ h) =
          Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q t) ∧
      (∀ t : ℝ, DifferentiableAt ℝ liftBP t) ∧
      canonicalArcIntegral
          (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
          (ellipticDz ω₁ ω₂ h) =
        liftBP 1 - liftBP 0 := by
  rcases ComplexTorus.exists_lift_of_chart_path
      (L := ellipticLattice ω₁ ω₂ h)
      (g := Jacobians.Bridge.bridgePath (X := Elliptic ω₁ ω₂ h) P₀ Q)
      (Jacobians.Bridge.bridgePath_continuous (X := Elliptic ω₁ ω₂ h) P₀ Q)
      (Jacobians.Bridge.bridgePath_chart_differentiable (X := Elliptic ω₁ ω₂ h) P₀ Q) with
    ⟨liftBP, hlift_mk, hlift_diff, hlift_deriv⟩
  refine ⟨liftBP, hlift_mk, hlift_diff, ?_⟩
  have hderiv_eq :
      (fun t : ℝ =>
        canonicalIntegrand
          (Jacobians.Bridge.bridgePathArc (X := Elliptic ω₁ ω₂ h) P₀ Q)
          (ellipticDz ω₁ ω₂ h) t) =
        deriv liftBP := by
    funext t
    exact bridgePath_canonicalIntegrand_ellipticDz_eq_lift_deriv
      (P₀ := P₀) (Q := Q) liftBP hlift_deriv t
  have hint_deriv : IntervalIntegrable (deriv liftBP) MeasureTheory.volume 0 1 := by
    rw [← hderiv_eq]
    exact bridgePath_canonicalIntegrand_ellipticDz_intervalIntegrable (P₀ := P₀) (Q := Q)
  unfold canonicalArcIntegral
  rw [hderiv_eq]
  exact intervalIntegral.integral_deriv_eq_sub
    (a := (0 : ℝ)) (b := 1) (f := liftBP)
    (fun x _hx => hlift_diff x) hint_deriv

end EllipticOfCurveInj

end Jacobians.ProjectiveCurve
