/-
# Finiteness of Riemann–Roch spaces (`dim L(D) < ∞`) — elementary route

Discharge of the `riemannRochSpace_finiteDimensional` pin (issue #116) via the
elementary upper bound `ℓ(D) ≤ 1 + deg D⁺` (Forster §16 / Miranda Ch. VI), the
"easy half" of Riemann's inequality — Montel-free. See
`docs/planning/riemannRochSpace_finiteDimensional.md`.

Build order: monotonicity → reduce to effective → local coefficient functional
+ kernel → `Multiset` induction → assemble.
-/

import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace

namespace Jacobians.RiemannSurface

open scoped Manifold ContDiff
open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- **Monotonicity of `L(D)` in the divisor.** If `D ≤ D'` coefficientwise
(`coeff p D ≤ coeff p D'` for all `p`) then `L(D) ⊆ L(D')`: a larger pole
allowance is a weaker constraint. -/
theorem riemannRochSpace_mono {D D' : Divisor X}
    (h : ∀ p, FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)
            ≤ FreeAbelianGroup.coeff p (D' : FreeAbelianGroup X)) :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro F hF p
  have hp := hF p
  refine le_trans ?_ hp
  have hle : (-(FreeAbelianGroup.coeff p (D' : FreeAbelianGroup X)))
            ≤ (-(FreeAbelianGroup.coeff p (D : FreeAbelianGroup X))) :=
    neg_le_neg (h p)
  exact_mod_cast hle

/-- Transport finite-dimensionality **down** a divisor inequality: if `L(D')` is
finite-dimensional and `L(D) ⊆ L(D')`, then `L(D)` is finite-dimensional. The
inclusion `L(D) ↪ L(D')` is injective ℂ-linear, so finiteness pulls back. -/
theorem finiteDimensional_of_riemannRochSpace_le {D D' : Divisor X}
    (h : riemannRochSpace D ≤ riemannRochSpace D')
    [FiniteDimensional ℂ (riemannRochSpace D')] :
    FiniteDimensional ℂ (riemannRochSpace D) :=
  Module.Finite.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

end Jacobians.RiemannSurface
