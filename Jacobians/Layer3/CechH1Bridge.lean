/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.Divisor
import KirovDolbeault.Dolbeault.CechFinitenessWiring
import KirovDolbeault.Dolbeault.LerayCoverExists

/-!
# Čech `H¹` bridge: `H1coh` as the Kirov-Dolbeault Čech cohomology

Phase-D bridge file (docs/planning/PHASE_D_BRIDGE_PLAN.md, A4 step (i);
type alignment in docs/planning/PHASE_D_TYPE_ALIGNMENT.md §3). The former
Layer-3 axioms `H1coh`, `H1coh.instAddCommGroup`, `H1coh.instModule`, and
`H1coh.instFiniteDimensional` become real definitions here, backed by the
Kirov Dolbeault port (Lake dependency `KirovDolbeault`, declarations under
`Jacobians.Dolbeault`):

* `H1coh D` is the genuine germ-class Čech cohomology
  `H¹(𝔘, 𝒪_D) = Z¹/B¹` of the canonical chart-disk cover
  `Jacobians.Dolbeault.chartDiskCover`, with the divisor translated across
  `FreeAbelianGroup.equivFinsupp : FreeAbelianGroup X ≃+ (X →₀ ℤ)`
  (our `Divisor X` vs the port's).
* The group/module instances are the `Submodule.Quotient` instances.
* Finite-dimensionality is the port's Forster §14 finiteness theorem
  `Jacobians.Dolbeault.finiteDimensional_cechH1_wired` (Montel compactness +
  Leray disk acyclicity; sorry-free, standard-3 axioms only).

This file consumes only sorry-free port results; the headline declarations
are `#print axioms`-checked to `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Manifold Topology ContDiff

namespace Jacobians.Layer3

universe u

/- Name-resolution shim. The port declares `Jacobians.Divisor` (a `Finsupp`
divisor), which — once the port is imported — shadows the opened
`Jacobians.Axioms.Divisor` inside `namespace Jacobians.Layer3` (enclosing
namespaces beat `open`). Re-exporting pins the bare names `Divisor` and
`Divisor.deg` in this namespace to our `FreeAbelianGroup` divisor layer, so
downstream Layer-3 files keep elaborating unchanged. -/
export Jacobians.Axioms (Divisor Divisor.deg)

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- The first cohomology vector space `H¹(X, O(D))` of the divisor sheaf
`O(D)`, realized as the germ-class Čech cohomology `H¹(𝔘, 𝒪_D)` of the
canonical chart-disk cover `𝔘 = chartDiskCover X` from the Kirov Dolbeault
port, with our `FreeAbelianGroup` divisor translated to the port's `Finsupp`
divisor along `FreeAbelianGroup.equivFinsupp`.

Only the vector-space structure and finite-dimensionality are exposed at
Layer 3; the cover choice never leaks because every Layer-3 cohomological
fact flows through the companion bridge results for the same cover.

Reference: Forster, *Lectures on Riemann Surfaces*, §§12-14. -/
def H1coh (D : Divisor X) : Type u :=
  (Jacobians.Dolbeault.chartDiskCover (X := X)).toFiniteCover.cechH1
    (FreeAbelianGroup.equivFinsupp X D)

/-- Additive group structure on `H¹(X, O(D))`, inherited from the Čech
cocycles-modulo-coboundaries quotient. -/
instance H1coh.instAddCommGroup (D : Divisor X) : AddCommGroup (H1coh D) :=
  inferInstanceAs
    (AddCommGroup
      ((Jacobians.Dolbeault.chartDiskCover (X := X)).toFiniteCover.cechH1
        (FreeAbelianGroup.equivFinsupp X D)))

/-- Complex vector-space structure on `H¹(X, O(D))`, inherited from the Čech
cocycles-modulo-coboundaries quotient. -/
instance H1coh.instModule (D : Divisor X) : Module ℂ (H1coh D) :=
  inferInstanceAs
    (Module ℂ
      ((Jacobians.Dolbeault.chartDiskCover (X := X)).toFiniteCover.cechH1
        (FreeAbelianGroup.equivFinsupp X D)))

/-- Serre finiteness for the first cohomology of `O(D)`: the port's Forster
§14 theorem (`finiteDimensional_cechH1_wired`, sup-norm Čech model + Montel
compactness + Leray disk acyclicity), applied to the chart-disk cover. -/
instance H1coh.instFiniteDimensional (D : Divisor X) :
    FiniteDimensional ℂ (H1coh D) :=
  Jacobians.Dolbeault.finiteDimensional_cechH1_wired
    (Jacobians.Dolbeault.chartDiskCover (X := X)).toFiniteCover
    (FreeAbelianGroup.equivFinsupp X D)

end Jacobians.Layer3
