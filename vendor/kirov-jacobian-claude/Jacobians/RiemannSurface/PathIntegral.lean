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
   rectangle. The current homology-level period pairing is constructed
   separately in `Jacobians.RiemannSurface.LoopIntegral` to avoid an
   import cycle through canonical multi-chart integration.

## Status (2026-04-23)

This module defines the **chart-local** integration (step 1) as a real
Lean `def` using `intervalIntegral`.

## References

* Mumford, *Tata Lectures on Theta I*, §II.2.
* Forster, *Lectures on Riemann Surfaces*, Ch. I §10–13.
* Griffiths-Harris, *Principles of Algebraic Geometry*, Ch. 0.2.
* Mathlib: `MeasureTheory.Integral.CurveIntegral.Basic` — `curveIntegral`
  on normed spaces is the chart-local primitive.
-/
import Jacobians.RiemannSurface.AnalyticArc
import Jacobians.RiemannSurface.OneForm
import Jacobians.RiemannSurface.Homology

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
`pathIntegralAnalyticLoop` which uses an analogous chart-local formula
with the basepoint `x₀` — correct for loops that stay near `x₀`.
A proper multi-chart `pathIntegralAnalyticArc` is a TODO. -/
noncomputable def pathIntegralOnChart
    (γ : AnalyticArc X) (p : X) (form : HolomorphicOneForm X) : ℂ :=
  ∫ r in (0 : ℝ)..1,
    form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
      derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend s))
        (Set.Ioo (0 : ℝ) 1) r

-- `loopIntegralToH1` lives in `Jacobians.RiemannSurface.LoopIntegral`.
-- Keeping it out of this file avoids the import cycle through
-- `CanonicalArcIntegral` and `MultiChartIntegral`.

end Jacobians.RiemannSurface
