/-
# Backward leg of `AX_genus_eq_zero_iff_homeo`, closed

Composes the G2-lane reduction `genus_eq_zero_of_homeo_sphere`
(`Jacobians/RiemannSurface/GenusZeroBackward.lean`, PR #199: backward
uniformization with `π₁(S²) = 1` as its single hypothesis) with the S2-lane
theorem `Jacobians.Topology.simplyConnectedSpace_sphere` (π₁(S²) = 1, via the
ported Kirov two-open van Kampen development), yielding the **unconditional**
backward direction: a compact Riemann surface homeomorphic to the 2-sphere
has genus zero.

S2 lane (`docs/planning/HANDOVER_PARALLEL_ACCOUNT.md` Package 1 Goal A);
bridge file per the repo's `Jacobians/Bridge/` pattern.
-/
import Submission.Jacobians.RiemannSurface.GenusZeroBackward
import Submission.Jacobians.Topology.SphereSimplyConnected

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **Backward direction of `AX_genus_eq_zero_iff_homeo`, unconditional.**
A compact Riemann surface homeomorphic to the 2-sphere has genus zero. -/
theorem genus_eq_zero_of_homeo_sphere_unconditional [T2Space X] [CompactSpace X]
    [ConnectedSpace X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    genus X = 0 :=
  genus_eq_zero_of_homeo_sphere Jacobians.Topology.simplyConnectedSpace_sphere h

end Jacobians.RiemannSurface
