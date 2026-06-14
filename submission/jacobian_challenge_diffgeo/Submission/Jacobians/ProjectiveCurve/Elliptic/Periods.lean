import Submission.Jacobians.ProjectiveCurve.Elliptic.OneForm
import Submission.Jacobians.ProjectiveCurve.Elliptic.Witnesses
import Submission.Jacobians.RiemannSurface.CanonicalArcIntegral

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Jacobians.RiemannSurface
open Jacobians.AbelianVariety

variable (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])

/-- The moving-chart integrand of `dz` along the A-cycle is constantly `ω₁`. -/
theorem aLoop_canonicalIntegrand_eq (r : ℝ) :
    canonicalIntegrand (aArc ω₁ ω₂ h) (ellipticDz ω₁ ω₂ h) r = ω₁ := by
  rw [canonicalIntegrand]
  have hcoeff :
      (ellipticDz ω₁ ω₂ h).coeff ((aArc ω₁ ω₂ h).extend r)
        ((extChartAt 𝓘(ℂ, ℂ) ((aArc ω₁ ω₂ h).extend r))
          ((aArc ω₁ ω₂ h).extend r)) = 1 := by
    change Set.indicator _ (fun _ => (1 : ℂ)) _ = 1
    exact Set.indicator_of_mem
      (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) ((aArc ω₁ ω₂ h).extend r)) _
  have hderiv :
      deriv (fun u : ℝ =>
        (extChartAt 𝓘(ℂ, ℂ) ((aArc ω₁ ω₂ h).extend r))
          ((aArc ω₁ ω₂ h).extend u)) r = ω₁ := by
    simpa [aArc, aLoopExtend, Elliptic] using
      (ComplexTorus.extChartAt_quotient_mk_line_deriv
        (L := ellipticLattice ω₁ ω₂ h)
        ((aArc ω₁ ω₂ h).extend r) ω₁ r
        (by simp [aArc, aLoopExtend, Elliptic]))
  rw [hcoeff, hderiv]
  simp

/-- The moving-chart integrand of `dz` along the B-cycle is constantly `ω₂`. -/
theorem bLoop_canonicalIntegrand_eq (r : ℝ) :
    canonicalIntegrand (bArc ω₁ ω₂ h) (ellipticDz ω₁ ω₂ h) r = ω₂ := by
  rw [canonicalIntegrand]
  have hcoeff :
      (ellipticDz ω₁ ω₂ h).coeff ((bArc ω₁ ω₂ h).extend r)
        ((extChartAt 𝓘(ℂ, ℂ) ((bArc ω₁ ω₂ h).extend r))
          ((bArc ω₁ ω₂ h).extend r)) = 1 := by
    change Set.indicator _ (fun _ => (1 : ℂ)) _ = 1
    exact Set.indicator_of_mem
      (mem_extChartAt_target (I := 𝓘(ℂ, ℂ)) ((bArc ω₁ ω₂ h).extend r)) _
  have hderiv :
      deriv (fun u : ℝ =>
        (extChartAt 𝓘(ℂ, ℂ) ((bArc ω₁ ω₂ h).extend r))
          ((bArc ω₁ ω₂ h).extend u)) r = ω₂ := by
    simpa [bArc, bLoopExtend, Elliptic] using
      (ComplexTorus.extChartAt_quotient_mk_line_deriv
        (L := ellipticLattice ω₁ ω₂ h)
        ((bArc ω₁ ω₂ h).extend r) ω₂ r
        (by simp [bArc, bLoopExtend, Elliptic]))
  rw [hcoeff, hderiv]
  simp

/-- The period of `dz` along the A-cycle is the lattice generator `ω₁`. -/
theorem aLoop_period_eq :
    canonicalArcIntegral (aLoop ω₁ ω₂ h).arc (ellipticDz ω₁ ω₂ h) = ω₁ := by
  unfold canonicalArcIntegral
  have hconst : ∀ r : ℝ,
      canonicalIntegrand (aLoop ω₁ ω₂ h).arc (ellipticDz ω₁ ω₂ h) r = ω₁ := by
    intro r
    simpa [aLoop] using aLoop_canonicalIntegrand_eq ω₁ ω₂ h r
  simp_rw [hconst]
  simp

/-- The period of `dz` along the B-cycle is the lattice generator `ω₂`. -/
theorem bLoop_period_eq :
    canonicalArcIntegral (bLoop ω₁ ω₂ h).arc (ellipticDz ω₁ ω₂ h) = ω₂ := by
  unfold canonicalArcIntegral
  have hconst : ∀ r : ℝ,
      canonicalIntegrand (bLoop ω₁ ω₂ h).arc (ellipticDz ω₁ ω₂ h) r = ω₂ := by
    intro r
    simpa [bLoop] using bLoop_canonicalIntegrand_eq ω₁ ω₂ h r
  simp_rw [hconst]
  simp

end Jacobians.ProjectiveCurve
