/-
`AX_FiniteDimOneForms`: the ℂ-vector space of holomorphic 1-forms on a
compact Riemann surface is finite-dimensional.

**Statement.** For any `X` satisfying Buzzard's typeclass constraints
(compact, connected, T2, `ChartedSpace ℂ`, `IsManifold 𝓘(ℂ) ω`),
`HolomorphicOneForm X` is a finite-dimensional ℂ-vector space.

**Why this is true.** Classical. Two standard routes:

1. Normal families + mean value: the space of holomorphic 1-forms has a
   norm (via the sup of chart coefficients over a finite cover of
   compact `X`). Uniformly bounded families are normal, hence the unit
   ball in this norm is compact, forcing finite-dim.

2. Serre duality applied to `ω_X` (the canonical sheaf): `dim H⁰(X, ω_X)
   = dim H¹(X, 𝒪_X)` and both are finite because `X` is compact.

**Why axiomatized.** Proving (1) requires a ChartedSpace-level sup-norm
theory that isn't in Mathlib at the pin. Proving (2) requires full
sheaf cohomology on complex manifolds, which is also absent. Both are
projects in their own right, independent of the rest of this formalization.

**Installed as an instance.** Per `docs/codex-review.md` and
`docs/claude-review.md`: if `FiniteDimensional ℂ (HolomorphicOneForm X)`
is only a theorem (not a global instance), then `Module.finrank` returns 0
on the infinite-dim codomain and `Fin (genus X) → ℂ` silently collapses
to `Unit`, making the `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)`
instance type-correct but semantically dead. This axiom **must** be a
global instance for downstream modules (`Genus.lean`, `Construction.lean`)
to be well-behaved.

See `docs/formalization-plan.md` §7 and §4.6.
-/
import Jacobians.RiemannSurface.OneForm

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Axiom.** The ℂ-vector space of holomorphic 1-forms on a compact
(connected, T2) complex 1-manifold is finite-dimensional. -/
axiom AX_FiniteDimOneForms {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    FiniteDimensional ℂ (HolomorphicOneForm X)

/-- Install `AX_FiniteDimOneForms` as a global instance. Without this,
`Module.finrank ℂ (HolomorphicOneForm X)` returns 0 on spaces where the
axiom is not directly invoked, silently collapsing downstream `genus`
and `ChartedSpace` constructions. -/
instance instFiniteDimOneForms {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    FiniteDimensional ℂ (HolomorphicOneForm X) :=
  AX_FiniteDimOneForms

end Jacobians.Axioms
