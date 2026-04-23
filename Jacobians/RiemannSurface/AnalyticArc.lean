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
representative, and there exists a *symplectic* ℤ-basis of `H_1`
consisting of such representatives.

## Skeleton vs full theory

At this pin we define `AnalyticArc` / `AnalyticLoop` as **data carriers**
— a continuous path from `unitInterval` to `X` plus a record of the
piecewise-analytic partition. The actual content ("on each partition
piece, the chart-read of the path is real-analytic") is held as a
proposition predicate whose **stub form is `True`**; refining it to the
true content is a TODO in the same spirit as the `OneForm.lean`
predicate refinement.

At the stub level, `AnalyticArc X = { continuous path + partition data }`.
This matches the pattern used for `HolomorphicOneForm X` in `OneForm.lean`.
Downstream code (`AX_AnalyticCycleBasis`, the future `PathIntegral.lean`)
can typecheck against the data; analyticity content will be plumbed
through once the predicate is refined.

See `docs/formalization-plan.md` §4 and `docs/history.md` (2026-04-22
PathIntegral design discussion).
-/
import Mathlib

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

/-- **Predicate (stub).** "`γ` is real-analytic when read in any chart on
each closed subinterval of the partition". Currently `True` — to be
refined once chart-cocycle machinery lands. -/
def IsAnalyticArc (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (_toFun : unitInterval → X) (_partition : Finset ℝ) :
    Prop := True

/-- A piecewise-real-analytic arc in a complex 1-manifold `X`.

Data carrier: continuous path `toFun : unitInterval → X`, partition
`partition : Finset ℝ` of `[0, 1]`, and (stub-True until predicate
refined) the property that `toFun` is real-analytic in every chart on
each closed subinterval of `partition`. -/
structure AnalyticArc (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  toFun : unitInterval → X
  continuous' : Continuous toFun
  partition : Finset ℝ
  partition_subset : ↑partition ⊆ Set.Icc (0 : ℝ) 1
  zero_mem : (0 : ℝ) ∈ partition
  one_mem : (1 : ℝ) ∈ partition
  is_analytic : IsAnalyticArc X toFun partition

/-- A piecewise-real-analytic loop based at `x₀`. -/
structure AnalyticLoop (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) where
  arc : AnalyticArc X
  start_eq : arc.toFun ⟨0, by simp⟩ = x₀
  end_eq   : arc.toFun ⟨1, by simp⟩ = x₀

namespace AnalyticArc

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

-- TODO (IsAnalyticArc refinement): replace the `True` stub with the real
-- predicate:
--
--   IsAnalyticArc X γ P ↔
--     ∀ s ∈ P, ∀ t ∈ P, s < t →
--       (∀ u ∈ Ioo s t, ContMDiffWithinAt ℝ I_real_to_complex ω
--         (γ ∘ Subtype.val_restr_to_Icc) (Icc s t) u)
--
-- where `I_real_to_complex` models `ℝ → X` viewed as a real-smooth map
-- from `ℝ` to `X`-as-real-manifold. Needs Mathlib's `ModelWithCorners`
-- infrastructure for viewing a complex manifold as a real manifold of
-- twice the dimension (which at this pin does exist via
-- `Manifold.ModelWithCorners.complexification`-adjacent machinery).

-- TODO (concat): concatenation of two analytic arcs `γ ++ δ` with
-- matching endpoints. Partition becomes a scaled union. Piecewise-
-- analytic is closed under concatenation.

-- TODO (reverse): `reverse γ (t) := γ (1 - t)`, partition reflected.

end AnalyticArc

end Jacobians.RiemannSurface
