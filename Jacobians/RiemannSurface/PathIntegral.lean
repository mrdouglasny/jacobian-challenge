/-
Path integrals of holomorphic 1-forms along piecewise-real-analytic
arcs on a complex 1-manifold.

## Purpose

Retire `periodMap` from axiom-stub to a real `def`. The period map is
classically defined as `[γ] ↦ (ω ↦ ∫_γ ω)`, where the integral ranges
over a loop representative of a homology class. Well-definedness on
`H_1 = π_1^{ab}` rests on homotopy invariance of the path integral.

## Design

Following the design decision recorded in
`Jacobians/Axioms/AnalyticCycleBasis.lean` (and the user-driven
discussion in `docs/history.md` 2026-04-22 "PathIntegral design
conversation"), we restrict to **piecewise-real-analytic** arcs and
reuse Mathlib's `curveIntegral` / `intervalIntegral` chart-locally.

Three levels of integration:

1. **`pathIntegralOnChart`** — single chart. For an arc `γ` whose image
   lies in a single chart's source, the integral reduces to
   `intervalIntegral` of `coeff_p(chart ∘ γ(t)) · (chart ∘ γ)'(t)` over
   `[0, 1]`.

2. **`pathIntegralAnalyticArc`** — general arc. Partition `[0, 1]`
   subordinate to a chart cover of `γ`'s image; sum chart-local pieces.
   Independence of the chart cover / partition is a theorem via the
   cotangent cocycle on `ω` (now part of `SatisfiesCotangentCocycle`).

3. **Homotopy invariance**. `pathIntegralAnalyticArc` descends to
   `H_1 X x₀` — for `γ ∼ γ'` smoothly homotopic, the integrals agree.
   Classical proof: Cauchy's theorem on chart disks + Stokes on the
   rectangle.

## Status (2026-04-23)

This module defines the **chart-local** integration (step 1) as a real
Lean `def` using `intervalIntegral`. Steps 2 and 3 are TODOs — they
require partition refinement machinery and Cauchy's theorem on
chart-disks respectively. Once those land, `periodMap` retires from
axiom-stub to a real def here.

## References

* Mumford, *Tata Lectures on Theta I*, §II.2.
* Forster, *Lectures on Riemann Surfaces*, Ch. I §10–13.
* Griffiths-Harris, *Principles of Algebraic Geometry*, Ch. 0.2.
* Mathlib: `MeasureTheory.Integral.CurveIntegral.Basic` — `curveIntegral`
  on normed spaces is the chart-local primitive.
-/
import Jacobians.RiemannSurface.AnalyticArc
import Jacobians.RiemannSurface.OneForm

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Chart-local path integral.** Given a reference point `p : X`
(taken as the chart center) and an analytic arc `γ`, compute the
integral of a holomorphic 1-form `ω` by pulling back to `ℝ → ℂ` via the
chart at `p` and doing an interval integral.

**Formula.** `∫_γ ω ≈ ∫₀¹ coeff_p(φ_p(γ(t))) · (φ_p ∘ γ)'(t) dt`.

This is correct **only when `γ`'s image lies entirely within
`(extChartAt p).source`**. For general arcs, see
`pathIntegralAnalyticArc` (TODO) which partitions subordinate to a chart
cover. -/
noncomputable def pathIntegralOnChart
    (γ : AnalyticArc X) (p : X) (form : HolomorphicOneForm X) : ℂ :=
  ∫ r in (0 : ℝ)..1,
    form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
      derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
        (Set.Ioo (0 : ℝ) 1) r

-- TODO (pathIntegralAnalyticArc): for a general `AnalyticArc`, define
-- `∫_γ ω` by:
--   1. Pick a finite chart cover `{U_i}` of `γ`'s image `γ([0, 1])`
--      (exists by compactness).
--   2. Refine `γ.partition` to a partition `0 = t_0 < t_1 < … < t_n = 1`
--      such that `γ([t_i, t_{i+1}]) ⊆ U_{σ(i)}` for some assignment σ.
--   3. Compute `∑_i pathIntegralOnChart (γ.restrict [t_i, t_{i+1}])
--      (chart center of U_{σ(i)}) ω`.
-- Independence of the chart cover / partition choice is a theorem
-- provable via the cotangent cocycle on `form` (see
-- `SatisfiesCotangentCocycle`).

-- TODO (pathIntegral_homotopy_invariant): for smoothly homotopic
-- analytic arcs `γ ∼ γ'`, `pathIntegralAnalyticArc γ ω =
-- pathIntegralAnalyticArc γ' ω`. Proof: Cauchy on chart disks + Stokes.

-- TODO (periodMap retirement): once the above two TODOs land:
--   noncomputable def periodMap (X) [...] (x₀ : X) :
--       H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
--     -- factor through `Abelianization` universal property + homotopy
--     -- invariance
-- and the axiom `periodMap` in `Periods.lean` is retired.

end Jacobians.RiemannSurface
