/-
`HolomorphicOneForm X` — holomorphic 1-forms on a complex 1-manifold `X`.

At the pinned Mathlib commit there is no cotangent-bundle API for complex
manifolds (nor a general `ContMDiff` section API that applies, since the
cotangent bundle isn't constructed). We therefore use the chart-cocycle
formulation per `docs/formalization-plan.md` §4.1 fallback path.

A holomorphic 1-form is specified by a chart-local coefficient at each
point, holomorphic on each chart target, satisfying the cotangent
transformation law on chart overlaps:

    coeff y ((φ_y ∘ φ_x⁻¹) z) · D(φ_y ∘ φ_x⁻¹)(z) = coeff x z

for `φ_x` the preferred chart at `x`.

**Status (2026-04-21): stub.** The two `Prop` predicates — holomorphicity
per chart and the cotangent cocycle — are currently placeholders (`True`).
With these stubs in place, `HolomorphicOneForm X` is an ambient ℂ-submodule
of `X → ℂ → ℂ`; everything downstream (ℂ-module, `genus X`, `periodMap`)
type-checks. Refining the predicates to their true content is a TODO that
will land before any concrete theorem about specific forms.

See `docs/formalization-plan.md` §4.1 and `docs/gemini-review-2.md` for
context on the chart-cocycle choice.
-/
import Mathlib

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff -- for ω notation
open Complex Set

/-- Placeholder predicate: "the family of chart-local coefficients
`coeff : X → ℂ → ℂ` is holomorphic on each chart target". Concrete
content TODO; currently the trivial predicate so the scaffolding type
checks. -/
def IsHolomorphicOneFormCoeff (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (_coeff : X → ℂ → ℂ) : Prop := True

/-- Placeholder predicate: "the cotangent cocycle compatibility condition
holds on chart overlaps". Concrete content TODO. -/
def SatisfiesCotangentCocycle (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (_coeff : X → ℂ → ℂ) : Prop := True

/-- The ℂ-submodule of `X → ℂ → ℂ` consisting of chart-local coefficient
families representing holomorphic 1-forms on `X`.

Because both predicates are currently `True`, this submodule is literally
all of `X → ℂ → ℂ` at the moment. Refining the predicates gets this to the
correct submodule; downstream API (coefficient access, `AddCommGroup`,
`Module ℂ`) is stable under the refinement. -/
def holomorphicOneFormSubmodule (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Submodule ℂ (X → ℂ → ℂ) where
  carrier := { f | IsHolomorphicOneFormCoeff X f ∧ SatisfiesCotangentCocycle X f }
  zero_mem' := ⟨trivial, trivial⟩
  add_mem' _ _ := ⟨trivial, trivial⟩
  smul_mem' _ _ _ := ⟨trivial, trivial⟩

/-- The ℂ-vector space of holomorphic 1-forms on `X`.

`abbrev` (not `def`) so that `AddCommGroup` and `Module ℂ` transfer
transparently from the underlying `Submodule`'s coerced type. -/
abbrev HolomorphicOneForm (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ↥(holomorphicOneFormSubmodule X)

namespace HolomorphicOneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Underlying chart-local-coefficient family of a holomorphic 1-form.

(Name `form` rather than `ω` to avoid conflict with the `ContDiff`
namespace's `ω` smoothness-level notation.) -/
def coeff (form : HolomorphicOneForm X) : X → ℂ → ℂ := form.1

-- TODO: refine `IsHolomorphicOneFormCoeff` and `SatisfiesCotangentCocycle`
-- to their true content. Suggested concrete forms:
--
--   IsHolomorphicOneFormCoeff coeff ↔
--     ∀ x : X, AnalyticOn ℂ (coeff x) (extChartAt 𝓘(ℂ) x).target
--
--   SatisfiesCotangentCocycle coeff ↔
--     ∀ x y : X, ∀ z ∈ (extChartAt 𝓘(ℂ) x).target,
--       (extChartAt 𝓘(ℂ) x).symm z ∈ (extChartAt 𝓘(ℂ) y).source →
--       coeff y (extChartAt 𝓘(ℂ) y ((extChartAt 𝓘(ℂ) x).symm z)) *
--         fderivWithin ℂ (extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) x).symm)
--           (range 𝓘(ℂ)) z 1 =
--       coeff x z
--
-- After refinement, verify that the `zero_mem'` / `add_mem'` / `smul_mem'`
-- proofs in `holomorphicOneFormSubmodule` still hold (they will: sum /
-- scalar multiple of holomorphic is holomorphic; cotangent cocycle is
-- ℂ-linear in the coefficient family).

end HolomorphicOneForm

end Jacobians.RiemannSurface
