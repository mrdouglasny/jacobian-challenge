/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.Genus

/-!
# Divisors on a compact Riemann surface

This file contains the real divisor layer shared by the line-bundle stubs and
the meromorphic-function infrastructure.  Divisors are formal integer
combinations of points, implemented as `FreeAbelianGroup X`; their degree is
the sum of coefficients.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace Jacobians.Axioms

/-- The group of divisors on a compact Riemann surface `X`: formal
`ℤ`-combinations of points of `X`, i.e. the free abelian group on the
underlying set (Forster, *Lectures on Riemann Surfaces*, Ch. I §8). The
geometric typeclasses are unused by the encoding but kept on the signature so
downstream consumers elaborate unchanged. -/
abbrev Divisor (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Type u := FreeAbelianGroup X

/-- Divisors form an additive commutative group, inherited from
`FreeAbelianGroup`. -/
instance Divisor.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : AddCommGroup (Divisor X) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup X))

/-- The degree of a divisor: for a formal combination `D = ∑ n_P · P`,
`deg D := ∑ n_P`. An `AddMonoidHom` `Divisor X →+ ℤ`. -/
noncomputable def Divisor.deg (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] : Divisor X →+ ℤ :=
  FreeAbelianGroup.lift (fun _ : X => (1 : ℤ))

end Jacobians.Axioms

