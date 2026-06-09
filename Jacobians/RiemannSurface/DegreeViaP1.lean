/-
# The degree theorem via `ℙ¹` — global fiber-sum constancy (issue #120)

Toward `deg(div f) = 0`. The map `toP1 f : X → ℙ¹` (from `MeromorphicToP1.lean`)
has a globally constant weighted fiber sum (the degree of the branched cover):
`weightedFiberConservation` gives local constancy, and `ℙ¹` is connected, so the
weighted fiber sum is the same over every value — in particular over `0` (zeros)
and over `∞` (poles).
-/

import Jacobians.RiemannSurface.MeromorphicToP1

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open Filter OnePoint
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.ProjectiveLine
open Jacobians.Vendor.Wallace.HolomorphicForms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

namespace MeromorphicFunctionField

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- Every fiber of `toP1 f` (a non-constant map) is finite. -/
theorem toP1_fiber_finite {f : MeromorphicFunctionField X} (hf : Nonconstant f)
    (y : ProjectiveLine) : (toP1 f ⁻¹' {y}).Finite :=
  isHolomorphic_finite_fiber
    (isHolomorphic_of_contMDiff (toP1_contMDiff f)
      (hasLocalKfoldRamification_of_contMDiff (toP1_contMDiff f))) hf y

/-- **Global fiber-sum constancy.** The weighted fiber sum of `toP1 f` is the same
over every value (the degree of the branched cover). -/
theorem toP1_weightedFiberSum_const {f : MeromorphicFunctionField X} (hf : Nonconstant f)
    (y : ProjectiveLine) :
    (toP1_fiber_finite hf y).toFinset.sum (mapAnalyticOrderAt (toP1 f))
      = (toP1_fiber_finite hf ∞).toFinset.sum (mapAnalyticOrderAt (toP1 f)) := by
  have hlc : IsLocallyConstant
      (fun y => (toP1_fiber_finite hf y).toFinset.sum (mapAnalyticOrderAt (toP1 f))) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    exact weightedFiberConservation_of_contMDiff (toP1_contMDiff f) hf
      (fun y => toP1_fiber_finite hf y) y₀
  exact congrFun (hlc.eq_const ∞) y

end MeromorphicFunctionField

end Jacobians.RiemannSurface
