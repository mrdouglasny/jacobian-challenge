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

**Status (2026-04-22): safe stub.** The submodule is fixed to `⊥` (the
zero submodule) while the true predicates `IsHolomorphicOneFormCoeff` and
`SatisfiesCotangentCocycle` are unavailable. A previous scaffold used
the carrier `{f | True ∧ True}`, which is the top submodule — ℂ-linearly
equivalent to the ambient `X → ℂ → ℂ`. Combined with `AX_FiniteDimOneForms`
installed as a global instance, that scaffold let us derive `False` (via
`rank_fun_infinite` + surjection onto `ℂ → ℂ`), so the scaffolding was
unsound. Replacing the carrier with `⊥` makes `HolomorphicOneForm X`
a zero-dimensional ℂ-module at the stub — trivially finite-dim, no axiom
needed. Everything downstream (ℂ-module, `genus X = 0`, `periodMap`) still
type-checks; refining the predicates will widen the submodule to its
correct content and `AX_FiniteDimOneForms` will become load-bearing.

See `docs/formalization-plan.md` §4.1 and `docs/gemini-review-axioms.md`
for context.
-/
import Mathlib

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff -- for ω notation
open Complex Set

/-- **Predicate (refined 2026-04-23).** "The family of chart-local
coefficients `coeff : X → ℂ → ℂ` is holomorphic on each chart target."

For each point `x : X`, the function `coeff x : ℂ → ℂ` should be
holomorphic on the image of the chart at `x`, i.e. on
`(extChartAt 𝓘(ℂ) x).target`. -/
def IsHolomorphicOneFormCoeff (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (coeff : X → ℂ → ℂ) : Prop :=
  ∀ x : X, AnalyticOn ℂ (coeff x) (extChartAt 𝓘(ℂ) x).target

/-- **Predicate (refined 2026-04-23).** "The cotangent cocycle
compatibility condition holds on chart overlaps."

For two points `x y : X` and `z ∈ (extChartAt 𝓘(ℂ) x).target` such that
the back-image `(extChartAt 𝓘(ℂ) x).symm z` lies in the source of the
chart at `y`, the coefficient values in the two charts must be related
by the derivative of the chart transition:

    coeff x z  =  coeff y w · D(φ_y ∘ φ_x⁻¹)(z) · 1

where `w := (extChartAt 𝓘(ℂ) y) ((extChartAt 𝓘(ℂ) x).symm z)` is the
`y`-chart coordinate of the same point. This is the classical
transformation law for a 1-form `ω = coeff x · dφ_x = coeff y · dφ_y`,
written intrinsically via the derivative `D(φ_y ∘ φ_x⁻¹)(z)` of the
chart transition map. -/
def SatisfiesCotangentCocycle (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (coeff : X → ℂ → ℂ) : Prop :=
  ∀ x y : X, ∀ z ∈ (extChartAt 𝓘(ℂ) x).target,
    (extChartAt 𝓘(ℂ) x).symm z ∈ (extChartAt 𝓘(ℂ) y).source →
    coeff x z =
      coeff y ((extChartAt 𝓘(ℂ) y) ((extChartAt 𝓘(ℂ) x).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ) y) ∘ (extChartAt 𝓘(ℂ) x).symm) z 1)

/-- The ℂ-submodule of `X → ℂ → ℂ` consisting of chart-local coefficient
families representing holomorphic 1-forms on `X`.

Closed under addition and scalar multiplication: analyticity is closed
under sums/smul (Mathlib `AnalyticOn.add`, `AnalyticOn.const_smul`); the
cocycle is ℂ-linear in the coefficient family because `fderiv` is
ℂ-linear and `0 = 0 · anything`. -/
noncomputable def holomorphicOneFormSubmodule (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Submodule ℂ (X → ℂ → ℂ) where
  carrier := { f | IsHolomorphicOneFormCoeff X f ∧ SatisfiesCotangentCocycle X f }
  zero_mem' := ⟨fun _ => analyticOn_const, fun _ _ _ _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf_an, hf_cocy⟩ ⟨hg_an, hg_cocy⟩
    refine ⟨fun x => (hf_an x).add (hg_an x), ?_⟩
    intro x y z hz hyzy
    have hf := hf_cocy x y z hz hyzy
    have hg := hg_cocy x y z hz hyzy
    simp only [Pi.add_apply, hf, hg]
    ring
  smul_mem' := by
    rintro c f ⟨hf_an, hf_cocy⟩
    refine ⟨fun x => (analyticOn_const).mul (hf_an x), ?_⟩
    intro x y z hz hyzy
    have hf := hf_cocy x y z hz hyzy
    simp only [Pi.smul_apply, smul_eq_mul, hf]
    ring

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
