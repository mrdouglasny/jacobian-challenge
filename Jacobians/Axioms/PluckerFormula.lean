/-
`AX_PluckerFormula`: genus of a smooth plane curve.

**Statement (Lean, refined 2026-04-23).** For `H : PlaneCurveData` with
degree `d ≥ 3`, the smooth projective plane curve `PlaneCurve H` has
genus

    genus (PlaneCurve H) = (d - 1)(d - 2) / 2.

Degrees 1 and 2 give genus 0 (lines and smooth conics are ≃ ℙ¹).

**Why true.** Adjunction formula on `ℙ²`: `ω_X = 𝒪_X(d - 3)` for a
smooth degree-`d` plane curve. Counting global sections:

    dim H⁰(X, ω_X) = dim H⁰(ℙ², 𝒪(d-3)) = (d-3+2)(d-3+1)/2 = (d-1)(d-2)/2.

By our `genus X = Module.finrank ℂ (HolomorphicOneForm X)` and the
identification `HolomorphicOneForm X = H⁰(X, ω_X)`, this gives the
formula.

**Why axiomatized.** The classical proof goes through adjunction on
`ℙ²`, which in turn needs sheaf cohomology of line bundles on
projective space (same story as `AX_RiemannRoch`). Not in Mathlib at
this pin.

**Scope.** Track 2 only. For `ProjectiveLine`, `Elliptic`,
`Hyperelliptic`: the genus is directly given by construction or
derivable from other axioms.

## History

- 2026-04-23 (A2 + E1 in completion plan): promoted from doc-only
  using the `PlaneCurve` type stubs from E1.

See `docs/formalization-plan.md` §7, discharge priority #9;
`docs/completion-plan.md` workstreams E1 + A2. Reference:
Griffiths-Harris Ch. 2.4; Mumford's Red Book Ch. III §8.
-/
import Jacobians.RiemannSurface.Genus
import Jacobians.ProjectiveCurve.PlaneCurve

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface Jacobians.ProjectiveCurve

/-- **Axiom (Plücker formula).** The genus of the smooth projective
plane curve `PlaneCurve H` of degree `d` is `(d - 1)(d - 2) / 2`
(with the convention that for `d ∈ {1, 2}`, the formula gives `0`).

Note `H.d ≥ 1` by `PlaneCurveData.h_deg`; for `d = 1` (line) or
`d = 2` (smooth conic), both sides are 0. For `d ≥ 3`, both sides give
the positive genus. -/
axiom AX_PluckerFormula (H : PlaneCurveData) :
    genus (PlaneCurve H) = (H.d - 1) * (H.d - 2) / 2

end Jacobians.Axioms
