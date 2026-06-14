/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Submission.Jacobians.RiemannSurface.Cohomology.H1

/-!
# Riemann-Roch and Serre duality anchors for adelic cohomology

These are the first theorem statements for the Weil/Serre repartition model of
`H¹`.  The proofs are the new challenge: finite dimensionality of the quotient,
the adelic Riemann-Roch dimension formula, and Serre duality via the residue
pairing.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- Adelic Riemann-Roch for Weil repartition cohomology on a compact Riemann
surface:
`h⁰(D) - h¹(D) = deg(D) + 1 - g`. -/
theorem riemannRoch_anchor (D : Divisor X) :
    (Module.finrank ℂ (riemannRochSpace D) : ℤ) -
        (Module.finrank ℂ (adeleH1 D) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ) := by
  sorry

/-- The Weil repartition quotient computing `H¹(X, O(D))` is finite
dimensional over `ℂ`. -/
theorem adeleH1_finiteDim (D : Divisor X) :
    FiniteDimensional ℂ (adeleH1 D) := by
  sorry

/-- Serre duality for the adelic cohomology anchor: there exists a canonical
divisor `K` such that, for every `D`, `H¹(O(D)) ≅ H⁰(O(K − D))^*`. The `∃ K`
captures "there is a dualizing/canonical divisor" — duality holds for that
distinguished `K`, **not** for an arbitrary divisor. Future work replaces the
existential with an explicit canonical-divisor construction (`div(ω)`) and proves
the isomorphism via the residue pairing on Weil repartitions. -/
theorem serre_anchor :
    ∃ K : Divisor X, ∀ D : Divisor X,
      Nonempty (adeleH1 D ≃ₗ[ℂ] Module.Dual ℂ (riemannRochSpace (K - D))) := by
  sorry

end Jacobians.RiemannSurface

