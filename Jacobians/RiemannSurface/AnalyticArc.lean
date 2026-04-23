/-
Piecewise-real-analytic arcs and loops on a complex 1-manifold.

## Why this exists

The period map `H_1(X, ℤ) → (HolomorphicOneForm X)^*` is classically
defined by contour integration `[γ] ↦ (ω ↦ ∫_γ ω)`. Formalizing the
integral for a *general* smooth path requires substantial infrastructure
(chart-additivity, Cauchy + Stokes on chart disks, homotopy invariance).
By restricting to **piecewise-real-analytic** paths we can reuse
Mathlib's `curveIntegral` (on normed spaces) chart-locally and appeal to
analytic continuation for homotopy arguments.

**Classical fact (axiomatized as `AX_AnalyticCycleBasis`):** every
homology class `[γ] ∈ H_1(X, ℤ)` has a piecewise-real-analytic
representative, and there exists a ℤ-basis of `H_1` consisting of such
representatives.

## Design (refined 2026-04-23)

`AnalyticArc X` carries:
  - `extend : ℝ → X` — the arc as a function of a real parameter,
    defined for all `r : ℝ` but only meaningful on `[0, 1]`.
  - `continuous'` — continuity of `extend`.
  - `partition : Finset ℝ` — partition points in `[0, 1]` including
    `0` and `1`.
  - `is_analytic` — a real predicate (no longer `True`): on the
    open interior of each partition interval, the chart-pullback
    `(extChartAt p) ∘ extend` is real-analytic, where `p` is the
    image point.

Using `extend : ℝ → X` (as opposed to `toFun : unitInterval → X`) lets
us state analyticity via Mathlib's `AnalyticAt ℝ` on ordinary
`ℝ → ℂ` functions without subtype gymnastics.

Compatibility: `toFun : unitInterval → X` is provided as
`fun t => extend t.val`, with a coe via `AnalyticArc.toPath`-style
helpers (TODO as needed).
-/
import Mathlib

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

/-- **Predicate.** "`γ` is real-analytic when read in any chart on the
open interior of each partition subinterval."

For each partition pair `s < t` and each interior point `u ∈ Ioo s t`,
the composite `(extChartAt 𝓘(ℂ) (γ u)) ∘ γ : ℝ → ℂ` is real-analytic at
`u`. Analyticity at `u` is purely local, so the chart-pullback is
guaranteed to be well-defined in a neighborhood of `u`. -/
def IsAnalyticArc (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (extend : ℝ → X) (partition : Finset ℝ) :
    Prop :=
  ∀ s ∈ partition, ∀ t ∈ partition, s < t →
    ∀ u ∈ Set.Ioo s t,
      AnalyticAt ℝ (fun r : ℝ => (extChartAt 𝓘(ℂ) (extend u)) (extend r)) u

/-- A piecewise-real-analytic arc in a complex 1-manifold `X`.

Data:
* `extend : ℝ → X` — continuous extension of the arc to the whole real
  line. Only values on `[0, 1]` are mathematically meaningful;
  outside, `extend` is a dummy continuation.
* `partition : Finset ℝ` — partition of `[0, 1]` including endpoints.
* `is_analytic` — real analyticity on each open partition interior
  (see `IsAnalyticArc`). -/
structure AnalyticArc (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  extend : ℝ → X
  continuous' : Continuous extend
  partition : Finset ℝ
  partition_subset : ↑partition ⊆ Set.Icc (0 : ℝ) 1
  zero_mem : (0 : ℝ) ∈ partition
  one_mem : (1 : ℝ) ∈ partition
  is_analytic : IsAnalyticArc X extend partition

namespace AnalyticArc

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Evaluation of the arc at a point in `unitInterval`, ignoring the
extension's out-of-range values. -/
def toFun (γ : AnalyticArc X) (t : unitInterval) : X := γ.extend t.val

lemma continuous_toFun (γ : AnalyticArc X) : Continuous γ.toFun :=
  γ.continuous'.comp continuous_subtype_val

end AnalyticArc

/-- A piecewise-real-analytic loop based at `x₀`. -/
structure AnalyticLoop (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) where
  arc : AnalyticArc X
  start_eq : arc.extend 0 = x₀
  end_eq   : arc.extend 1 = x₀

-- TODO (concat): concatenation of two analytic arcs `γ ++ δ` with
-- matching endpoints. Partition becomes a scaled union. Piecewise-
-- analytic is closed under concatenation.

-- TODO (reverse): `reverse γ (r) := γ (1 - r)`, partition reflected.

-- TODO (Path interop): convert `AnalyticArc` to/from `Path a b` in
-- Mathlib — `Path.extend` is the standard `ℝ → X` extension of a
-- Path.

end Jacobians.RiemannSurface
