/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.Axioms.AbelJacobiMap
import Jacobians.RiemannSurface.Divisor

/-!
# The Abel-Jacobi map on divisors (base definition)

`abelJacobiDiv`, split out of `Jacobians/Axioms/AbelTheorem.lean` (the
Phase-C base-file pattern) so that the engine-side plumbing
(`Jacobians/RiemannSurface/AbelPlumbing.lean`) and the E6 adapter
(`Jacobians/Bridge/AbelEngineAdapter.lean`) can consume the definition
without importing the Abel-theorem statement file — which now imports
THEM to prove the ⊆ direction.
-/

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- The Abel-Jacobi map extended linearly from
points to divisors. On a formal combination `∑ n_P · P`, evaluates to
`∑ n_P · ofCurveImpl P₀ P - (∑ n_P) · ofCurveImpl P₀ P₀`; basepoint
`P₀` is chosen via `Classical.arbitrary`. -/
noncomputable def abelJacobiDiv (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Divisor X →+ Jacobian X :=
  FreeAbelianGroup.lift (fun P => ofCurveImpl X (Classical.arbitrary X) P)

end Jacobians.Axioms
