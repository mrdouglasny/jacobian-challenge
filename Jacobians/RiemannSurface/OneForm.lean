/-
`HolomorphicOneForm X` — holomorphic 1-forms on a complex 1-manifold `X`.

We use the chart-cocycle formulation per `docs/formalization-plan.md`
§4.1 fallback path.

NOTE (corrected 2026-06-06): the original justification here — "no
cotangent-bundle API, nor a `ContMDiff` section API that applies" — is
**stale**. The intrinsic bundle path now type-checks at the pin:
  * `Cₛ^ω⟮𝓘(ℂ,E); E →L[ℂ] ℂ, CotangentSpace E X⟯`
    (`Mathlib/Geometry/Manifold/VectorBundle/ContMDiffSection.lean`)
    is exactly "holomorphic section of the cotangent bundle" — over the
    ℂ-model, `ContMDiff … ω` = `AnalyticOn ℂ` = holomorphic.
  * the cotangent bundle (`Jacobians/Vendor/Wallace/.../CotangentBundle.lean`,
    vendored 2026-06-02) carries a `ContMDiffVectorBundle ω` instance
    automatically: tangent (`Tangent.lean`, needs `IsManifold 𝓘(ℂ) ω X`,
    which we already have) ⊗ trivial line bundle, glued by the hom-bundle
    instance (`VectorBundle/Hom.lean`).
The chart-cocycle form persists for three *practical* reasons, not an
API gap: (1) it predates the vendored cotangent bundle; (2) populating
the section type fights the `not reducible` `TangentSpace` operator-norm
diamonds (`backward.isDefEq.respectTransparency false`); (3) the whole
downstream interface (`AX_FiniteDimOneForms`, periods, `ellipticDz`,
ProjectiveLine subsingleton) is wired against this submodule.

TODO (do not attempt without a tracking Discussion — touches a shared
interface, see CLAUDE.md "major change" rule): reformulate
`HolomorphicOneForm X := Cₛ^ω⟮𝓘(ℂ,E); E →L[ℂ] ℂ, CotangentSpace E X⟯`.
The section route is cleaner — coordinate-independence is free (no
hand-imposed cocycle) and `IsZeroOffChartTarget` becomes unnecessary (a
section *is* its fiber values, so no off-target slack), and
`ContMDiffSection` ships its own `Module ℂ` instance.

A holomorphic 1-form is specified by a chart-local coefficient
`coeff : X → ℂ → ℂ` (first argument: the centre point of the chart;
second: the coordinate in that chart's target) satisfying:

1. **Chart-local holomorphicity** (`IsHolomorphicOneFormCoeff`): for
   each `x : X`, the function `coeff x : ℂ → ℂ` is analytic on
   `(extChartAt 𝓘(ℂ) x).target`.
2. **Cotangent cocycle** (`SatisfiesCotangentCocycle`): on chart
   overlaps, the coefficient values transform via the derivative of the
   chart transition:
       coeff x z  =  coeff y (φ_y(φ_x⁻¹(z))) · D(φ_y ∘ φ_x⁻¹)(z)(1)
   (the classical 1-form transformation law).

## Current status (2026-04-23)

**Real definition**, not a stub. `HolomorphicOneForm X` is the
ℂ-submodule of `X → ℂ → ℂ` cut out by the two predicates above, with
`zero_mem' / add_mem' / smul_mem'` discharged.

The earlier history note about a `⊥`-stub refers to iterations before
the 2026-04-23 refactor. The carrier history:
  1. `{f | True ∧ True}` (≅ full function space): with
     `AX_FiniteDimOneForms` installed, gave an `exploit ⇒ False` via
     `rank_fun_infinite`. Caught by Gemini 2026-04-22.
  2. `⊥` (zero submodule): safe but vacuous — `genus X = 0` always.
  3. (**Current**) Real predicates with analyticity + cocycle. The
     `AX_FiniteDimOneForms` instance is load-bearing and finite-dim
     follows classically (Hodge / Serre duality — see
     `Jacobians/Axioms/FiniteDimOneForms.lean`).

## API available here

- `coeff form : X → ℂ → ℂ` — chart-local coefficient accessor.
- `coeff_zero` / `coeff_add` / `coeff_smul` — `@[simp]` compatibility
  with the `AddCommGroup` / `Module ℂ` structure (via `Submodule`).
- `ext_of_coeff` — two forms are equal if their coefficient families
  agree as functions.

See also:
  - `Jacobians/Axioms/FiniteDimOneForms.lean` — finite-dim axiom (classical theorem, still
    load-bearing).
  - `Jacobians/ProjectiveCurve/Line/OneForm.lean` — derived fact that `HolomorphicOneForm
    ProjectiveLine` is a subsingleton (genus-0 collapse).
  - `Jacobians/ProjectiveCurve/Elliptic/OneForm.lean` — explicit `ellipticDz` witness
    (invariant 1-form `dz`).

`docs/formalization-plan.md` §4.1 and `docs/gemini-review-axioms.md`
have further context.
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

/-- **Predicate (added 2026-04-24).** "The coefficient family is zero
off each chart target."

For each `x : X`, the function `coeff x : ℂ → ℂ` is required to be
zero outside `(extChartAt 𝓘(ℂ) x).target`. This normalisation eliminates
off-target ambiguity in the submodule representation: two coefficient
families agreeing on all chart targets are then equal as functions
`X → ℂ → ℂ`, so `HolomorphicOneForm.ext_of_coeff` gives the correct
extensionality. Without this, the submodule would contain functions
differing only off-target — which would be an infinite-dimensional
degree of freedom inconsistent with `AX_FiniteDimOneForms`. -/
def IsZeroOffChartTarget (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (coeff : X → ℂ → ℂ) : Prop :=
  ∀ x : X, ∀ z : ℂ, z ∉ (extChartAt 𝓘(ℂ) x).target → coeff x z = 0

/-- The ℂ-submodule of `X → ℂ → ℂ` consisting of chart-local coefficient
families representing holomorphic 1-forms on `X`.

Closed under addition and scalar multiplication: analyticity is closed
under sums/smul (Mathlib `AnalyticOn.add`, `AnalyticOn.const_smul`); the
cocycle is ℂ-linear in the coefficient family because `fderiv` is
ℂ-linear; off-target zero is trivially preserved under linearity. -/
noncomputable def holomorphicOneFormSubmodule (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Submodule ℂ (X → ℂ → ℂ) where
  carrier := { f | IsHolomorphicOneFormCoeff X f ∧ SatisfiesCotangentCocycle X f ∧
    IsZeroOffChartTarget X f }
  zero_mem' := ⟨fun _ => analyticOn_const, fun _ _ _ _ _ => by simp,
    fun _ _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf_an, hf_cocy, hf_off⟩ ⟨hg_an, hg_cocy, hg_off⟩
    refine ⟨fun x => (hf_an x).add (hg_an x), ?_, ?_⟩
    · intro x y z hz hyzy
      have hf := hf_cocy x y z hz hyzy
      have hg := hg_cocy x y z hz hyzy
      simp only [Pi.add_apply, hf, hg]
      ring
    · intro x z hz
      simp [Pi.add_apply, hf_off x z hz, hg_off x z hz]
  smul_mem' := by
    rintro c f ⟨hf_an, hf_cocy, hf_off⟩
    refine ⟨fun x => (analyticOn_const).mul (hf_an x), ?_, ?_⟩
    · intro x y z hz hyzy
      have hf := hf_cocy x y z hz hyzy
      simp only [Pi.smul_apply, smul_eq_mul, hf]
      ring
    · intro x z hz
      simp [Pi.smul_apply, hf_off x z hz]

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

/-- The coefficient of the zero 1-form is the zero function. -/
@[simp]
theorem coeff_zero : (0 : HolomorphicOneForm X).coeff = 0 := rfl

/-- The coefficient of a sum of 1-forms is the pointwise sum of
coefficients. -/
@[simp]
theorem coeff_add (form₁ form₂ : HolomorphicOneForm X) :
    (form₁ + form₂).coeff = form₁.coeff + form₂.coeff := rfl

/-- The coefficient of a scalar multiple of a 1-form is the pointwise
scalar multiple of the coefficient. -/
@[simp]
theorem coeff_smul (c : ℂ) (form : HolomorphicOneForm X) :
    (c • form).coeff = c • form.coeff := rfl

/-- Extensionality: two holomorphic 1-forms are equal iff their
coefficient families coincide as `X → ℂ → ℂ` functions. -/
@[ext]
theorem ext_of_coeff {form₁ form₂ : HolomorphicOneForm X}
    (h : form₁.coeff = form₂.coeff) : form₁ = form₂ :=
  Subtype.ext h

end HolomorphicOneForm

end Jacobians.RiemannSurface
