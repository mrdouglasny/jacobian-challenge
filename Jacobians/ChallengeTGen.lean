/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Jacobians.Challenge
import Jacobians.RiemannSurface.OfCurveInjOfTGen

/-!
# Buzzard headlines under T-GEN (`AX_PeriodCycleBasis`-free wiring)

This file states the Buzzard challenge headlines as `_of_tgen` implications:
each is the public headline conjoined with the explicit hypothesis
`hgen : AnalyticLoopsGenerateH1 (Classical.arbitrary X)` (T-GEN). The point
is the **wiring**: when T-GEN becomes an unconditional theorem (the PL lane),
these implications discharge `hgen` mechanically.

## What is `AX_PeriodCycleBasis`-free under T-GEN at the consumer level

* `Jacobian.ofCurve_inj_of_tgen` — positive-genus injectivity of the
  Abel-Jacobi map. `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`. The statement is a pure proposition about the *group/type*
  structure of `Jacobian X` (`ofCurveImpl` and `AddCommGroup (Jacobian X)`
  are already standard-3), so re-routing the proof through the basis-free
  Abel-⊆ engine `abel_subset_basis_free` removes the axiom entirely. This is
  the `ofCurveImpl_inj_of_tgen` content under the public `ofCurve` name
  (`ofCurve` is definitionally `ofCurveImpl`).

## What is NOT `AX_PeriodCycleBasis`-free at the consumer level (the residual)

The `ContMDiff`-on-`Jacobian X` headlines —
`Jacobian.pushforward_contMDiff`, `Jacobian.pullback_contMDiff`,
`Jacobian.pushforward_pullback`, `Jacobian.ofCurve_contMDiff` — and the
Abel ⊇ Liouville step `fiberAJConstancy` **cannot** be made
`AX_PeriodCycleBasis`-free by a consumer-side `hgen`. Their *statements*
synthesize the `ChartedSpace`/`IsManifold` instances on `Jacobian X`, which
are built from the GLOBAL period-lattice instances
`Jacobians.Axioms.instPeriodLatticeDiscrete` /
`Jacobians.Axioms.AX_PeriodLattice` — and those carry `AX_PeriodCycleBasis`
in their *bodies*. Instance synthesis during statement elaboration does not
see a local `hgen`, and a `letI`/`haveI` in the proof body cannot change the
instance term already fixed in the elaborated type (confirmed: `#print
axioms` on the `IsManifold (Jacobian X)` instance itself lists
`AX_PeriodCycleBasis`).

These headlines therefore drop `AX_PeriodCycleBasis` **the instant the
global instances are reproven axiom-free** — which is exactly what making
T-GEN an unconditional theorem accomplishes (the PL lane discharges
`instPeriodLatticeDiscrete` / `AX_PeriodLattice` from T-GEN-now-theorem via
`Jacobians.RiemannSurface.periodLatticeInBasis_discreteTopology_of_tgen` /
`periodLatticeInBasis_isZLattice_of_tgen`). It is a property of the global
instance declarations, not of any consumer hypothesis. See the report and
`Jacobians.RiemannSurface.OfCurveInjOfTGen`.
-/

universe u

namespace Jacobian

open scoped Manifold Topology ContDiff
open Jacobians Jacobians.RiemannSurface

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Buzzard headline `ofCurve_inj`, `AX_PeriodCycleBasis`-free under T-GEN.**
For positive genus, the Abel-Jacobi map `ofCurve P : X → Jacobian X` is
injective. Same statement as `Jacobian.ofCurve_inj`, but proven from the
explicit T-GEN hypothesis through the basis-free Abel-⊆ engine, so its kernel
closure is standard-3 + T-GEN. `ofCurve` is definitionally `ofCurveImpl`, so
this is `ofCurveImpl_inj_of_tgen` repackaged under the public name. -/
theorem ofCurve_inj_of_tgen
    (hgen : AnalyticLoopsGenerateH1 (Classical.arbitrary X))
    (P : X) (h : 0 < Jacobians.RiemannSurface.genus X) :
    Function.Injective (ofCurve P) :=
  ofCurveImpl_inj_of_tgen hgen P h

end Jacobian
