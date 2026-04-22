/-
`AX_H1FreeRank2g`: first homology of a compact Riemann surface is free
abelian of rank twice the genus.

**Statement.** For `X` a compact connected T2 complex 1-manifold of
genus `g`, `H1 X x₀` (≅ `Abelianization (π₁ X x₀)`) is a free ℤ-module
of rank `2 * genus X`.

**Why true.** Classical CW-topology / simplicial homology. The
standard presentation of a compact oriented genus-`g` surface has
generators `α_1, β_1, …, α_g, β_g` with a single relation
`∏ [α_i, β_i] = 1`. Abelianizing makes the commutator trivial and
leaves a free ℤ-module of rank `2g`.

**Why axiomatized.** Proving this from scratch requires formalizing
the classification of compact oriented surfaces (or a CW/simplicial
structure on each Riemann surface), which is a major project
independent of this formalization.

See `docs/formalization-plan.md` §7; discharge priority #3.
-/
import Mathlib
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.Genus

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Axiom.** For a compact Riemann surface `X`, `H1 X x₀` is free
abelian of rank `2 * genus X`. Provided as a `Nonempty` statement
supplying an explicit ℤ-basis of the right cardinality. -/
axiom AX_H1FreeRank2g {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Nonempty (Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀))

end Jacobians.Axioms
