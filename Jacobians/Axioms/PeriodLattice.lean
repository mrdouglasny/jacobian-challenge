/- 
`AX_PeriodLattice`: the period image in basis coordinates is a full
`ℤ`-lattice in `ℂ^g`.

## Construction-level setup

`periodMap X x₀` currently lands in `(HolomorphicOneForm X →ₗ[ℂ] ℂ)`. The
Jacobian bridge in `Jacobians/Jacobian/Construction.lean` needs a lattice
inside the concrete ambient `Fin (genus X) → ℂ`, because
`ComplexTorus.lean` is already built over explicit finite-dimensional
normed complex vector spaces.

So this file fixes a basis

* `b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)`

and transports the period map into coordinates:

* `periodMapInBasis X x₀ b : H1 X x₀ →ₗ[ℤ] (Fin (genus X) → ℂ)`.

Its range `periodLatticeInBasis X x₀ b` is the lattice used by the
bridge construction.

## Why axiomatized

The classical theorem is that the period image is discrete of full real
rank. Equivalently, in any holomorphic-one-form basis it is a full
`ℤ`-lattice in `ℂ^g`. This follows from the Riemann bilinear relations;
see Mumford, *Tata Lectures on Theta I*, Ch. II §2, and Griffiths-Harris,
Ch. 2 §2.

At the current project stage the actual proof depends on path integrals,
the intersection form, and the positive-definiteness statement packaged in
`AX_RiemannBilinear`, so we expose the lattice property here as a named
axiom for the Jacobian bridge.\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\) -- not-an-axiom (doc text, ignore in counts)

Both axioms below are **NOT VERIFIED** and should be retired once the
Riemann-bilinear infrastructure lands.
-/
import Jacobians.RiemannSurface.Genus
import Jacobians.RiemannSurface.Periods

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

/-- **Axiom (NOT VERIFIED).** In basis coordinates, the period image carries
the discrete topology.

This is one half of the data required by Mathlib's `IsZLattice`-based
`ComplexTorus` API. It should eventually be derived from
`AX_RiemannBilinear`, since a full lattice in a finite-dimensional real
vector space is automatically discrete. -/
axiom instPeriodLatticeDiscrete (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (periodLatticeInBasis X x₀ b)

attribute [instance] instPeriodLatticeDiscrete

/-- **Axiom (NOT VERIFIED).** In basis coordinates, the image of the period
map is a full `ℤ`-lattice in `Fin (genus X) → ℂ`.

Mathematical source: the classical period-lattice theorem, equivalently the
combination of Riemann's bilinear relations with the rank computation
`rank H₁(X, ℤ) = 2g`. This is the exact hypothesis needed to feed the
period image into `AbelianVariety.ComplexTorus`. -/
axiom AX_PeriodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    IsZLattice ℝ (periodLatticeInBasis X x₀ b)

attribute [instance] AX_PeriodLattice

end Jacobians.Axioms
