/- 
Bridge from the Riemann-surface scaffolding to `AbelianVariety.ComplexTorus`.

## Design

Buzzard's challenge wants `Jacobian X` charted over `Fin (genus X) → ℂ`,
not over the dual space `(HolomorphicOneForm X →ₗ[ℂ] ℂ)`. To avoid having
two competing `ChartedSpace` instances on the same quotient, this module
bakes a chosen basis of `HolomorphicOneForm X` into the construction:

1. pick `jacobianBasis X : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`;
2. transport `periodMap` into basis coordinates via
   `Axioms.periodMapInBasis`;
3. take the quotient torus
   `ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis ...)`.

The basepoint is handled by `Classical.choice` from `[Nonempty X]`; this
matches the current bridge attempt policy. Basepoint-independence is not
proved here.

## Scope

This file intentionally does **not** touch `Jacobians/Challenge.lean`.
It packages the Jacobian construction and the seven inherited typeclass
instances so the challenge file can swap to them later in one step.

## Universe note

The ambient `Fin (genus X) → ℂ` lives in `Type`, so this bridge currently
defines `Jacobian` without forcing Buzzard's exact `: Type u` codomain
annotation. The quotient/typeclass architecture is in place; a later
universe-lift wrapper can be added if we insist on a literally
universe-polymorphic replacement.
-/
import Jacobians.AbelianVariety.ComplexTorus
import Jacobians.Axioms.PeriodLattice

namespace Jacobians

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface
open Jacobians.Axioms
open Jacobians.AbelianVariety

/-- The chosen basis used to write the Jacobian ambient space in the
concrete coordinates `Fin (genus X) → ℂ`. This is `Module.finBasis`, so the
index type is definitionally `Fin (genus X)`. -/
noncomputable def jacobianBasis (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X) :=
  Module.finBasis ℂ (HolomorphicOneForm X)

/-- The Jacobian of `X`, defined as the complex torus obtained by quotienting
`Fin (genus X) → ℂ` by the period lattice written in the chosen basis
`jacobianBasis X`.

The present bridge picks a basepoint using `Classical.choice` from
`[Nonempty X]`; later work can replace this with a proof that the resulting
lattice is independent of the choice. -/
noncomputable def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :=
  ComplexTorus (Fin (genus X) → ℂ)
    (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X))

namespace Jacobian

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The Jacobian of a compact Riemann surface is an additive commutative
group. This is inherited from the quotient-additive-group structure on
`ComplexTorus`. -/
noncomputable instance : AddCommGroup (Jacobian X) := by
  change AddCommGroup (ComplexTorus (Fin (genus X) → ℂ)
    (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X)))
  infer_instance

/-- The Jacobian carries the quotient topology from its ambient complex
torus presentation. -/
noncomputable instance : TopologicalSpace (Jacobian X) := by
  change TopologicalSpace (ComplexTorus (Fin (genus X) → ℂ)
    (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X)))
  infer_instance

noncomputable instance : T2Space (Jacobian X) := by
  change T2Space (ComplexTorus (Fin (genus X) → ℂ)
    (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X)))
  infer_instance

noncomputable instance : CompactSpace (Jacobian X) := by
  change CompactSpace (ComplexTorus (Fin (genus X) → ℂ)
    (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X)))
  infer_instance

/-- The Jacobian is charted over `Fin (genus X) → ℂ` by construction. -/
noncomputable instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := by
  change ChartedSpace (Fin (genus X) → ℂ) (ComplexTorus (Fin (genus X) → ℂ)
    (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X)))
  infer_instance

noncomputable instance :
    IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := by
  change IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
    (ComplexTorus (Fin (genus X) → ℂ)
      (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X)))
  infer_instance

noncomputable instance :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := by
  change LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
    (ComplexTorus (Fin (genus X) → ℂ)
      (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X)))
  infer_instance

end Jacobian

end Jacobians
