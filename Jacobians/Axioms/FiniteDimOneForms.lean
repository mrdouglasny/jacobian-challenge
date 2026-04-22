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

/-- Install finite-dimensionality of `HolomorphicOneForm X` as a global
instance. At the current `⊥`-submodule stub this follows from
`Submodule.finiteDimensional_bot` *without* invoking the axiom. When the
predicates `IsHolomorphicOneFormCoeff` / `SatisfiesCotangentCocycle` are
refined, the instance will delegate to `AX_FiniteDimOneForms`.

**Soundness note.** A previous iteration defined this instance as
`instFiniteDimOneForms := AX_FiniteDimOneForms` on top of the
`{ f | True ∧ True }` stub carrier (≅ full function space `X → ℂ → ℂ`).
Combined with `rank_fun_infinite` + surjection onto `ℂ → ℂ`, that scaffold
let us derive `False` — any `exfalso` could have discharged the 24
Challenge sorries. The fix: `HolomorphicOneForm X = ⊥.restrict` at the
stub, which is trivially 0-dim, and the axiom only bites after the
predicates land. -/
instance instFiniteDimOneForms {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    FiniteDimensional ℂ (HolomorphicOneForm X) := by
  -- HolomorphicOneForm X = ↥(⊥ : Submodule ℂ (X → ℂ → ℂ)) at the stub.
  -- The zero submodule is trivially finite-dimensional.
  change FiniteDimensional ℂ ↥(holomorphicOneFormSubmodule X)
  unfold holomorphicOneFormSubmodule
  infer_instance

end Jacobians.Axioms
