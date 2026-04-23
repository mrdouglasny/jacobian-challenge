/-
`genus ProjectiveLine = 0`.

**Direct proof via uniformization.** Since we have `stereographic :
ProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` from
`Jacobians/ProjectiveCurve/Line.lean`, we just apply the ⇐ direction
of `AX_genus_eq_zero_iff_homeo`:

    genus X = 0 ↔ Nonempty (X ≃ₜ S²)

to discharge.

This routes `genus ProjectiveLine = 0` through the uniformization
axiom. An alternative direct proof via Liouville + chart cocycle on
`HolomorphicOneForm ProjectiveLine` exists but is substantially more
Lean work; deferred until we need a non-axiom-based route.

See `docs/completion-plan.md` workstream B1.
-/
import Jacobians.ProjectiveCurve.Line
import Jacobians.Axioms.Uniformization0

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- The genus of `ProjectiveLine` is zero.

Proof: use the `stereographic` homeomorphism `ProjectiveLine ≃ₜ S²`
and apply the uniformization axiom `AX_genus_eq_zero_iff_homeo`. -/
theorem genus_projectiveLine_eq_zero :
    Jacobians.RiemannSurface.genus ProjectiveLine = 0 := by
  rw [Jacobians.Axioms.AX_genus_eq_zero_iff_homeo]
  exact ⟨ProjectiveLine.stereographic⟩

end Jacobians.ProjectiveCurve
