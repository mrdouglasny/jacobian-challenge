/-
`periodMapInBasis` / `periodLatticeInBasis` — the period map and its image
in coordinates, extracted from `Axioms/PeriodLattice.lean` so the Layer-3
discharge (`Layer3/Periods.lean`) can consume the definitions without an
import cycle (`Axioms/PeriodLattice.lean` imports the discharge to convert
its axioms into theorems). Same maneuver as `RiemannRochBase` for the
RR/Serre discharge. Namespace unchanged (`Jacobians.Axioms`), so all
existing callers keep working.
-/
import Submission.Jacobians.RiemannSurface.Genus
import Submission.Jacobians.RiemannSurface.Periods

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- The period map written in coordinates with respect to a chosen basis of
holomorphic one-forms. The original `periodMap` is only additive; we view
it as a `ℤ`-linear map via `AddMonoidHom.toIntLinearMap`, then compose with
the coordinate map on the dual basis. -/
noncomputable def periodMapInBasis (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    H1 X x₀ →ₗ[ℤ] (Fin (genus X) → ℂ) :=
  (b.dualBasis.equivFun.toLinearMap.restrictScalars ℤ).comp (periodMap X x₀).toIntLinearMap

/-- The period lattice in basis coordinates, defined as the range of
`periodMapInBasis`. This is the `Submodule ℤ` consumed by
`AbelianVariety.ComplexTorus`. -/
noncomputable def periodLatticeInBasis (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Submodule ℤ (Fin (genus X) → ℂ) :=
  LinearMap.range (periodMapInBasis X x₀ b)

end Jacobians.Axioms
