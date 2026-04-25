/-
# Bridge: cocycle 1-forms ↔ Kirov's bundle-section 1-forms

This file connects our chart-cocycle definition of holomorphic 1-forms
(`Jacobians.RiemannSurface.HolomorphicOneForm`, a `Submodule` of
`X → ℂ → ℂ` cut out by analyticity + cotangent-cocycle predicates) to
Kirov's `ContMDiffSection`-of-cotangent-bundle definition
(`Jacobians.Vendor.Kirov.HolomorphicOneForms`, vendored from
`rkirov/jacobian-claude`).

## Why a bridge

Kirov's repo proves `FiniteDimensional ℂ (HolomorphicOneForms X)` as a
real `instance` (Vendor/Kirov/HolomorphicForms.lean:89), derived via
Montel + Riesz from a real ~3.4 kLOC normal-families construction. Our
own previous route was the axiom `AX_FiniteDimOneForms` in
`Jacobians/Axioms/FiniteDimOneForms.lean`. By bridging the two
definitions we transfer Kirov's real instance to our type and retire
that axiom.

## Bridge content

We construct a ℂ-linear map and prove it injective:

```
noncomputable def bridgeForm     : HolomorphicOneForm X →ₗ[ℂ] Vendor.Kirov.HolomorphicOneForms X
theorem            bridgeForm_injective : Function.Injective (bridgeForm (X := X))
```

Mathematically `bridgeForm` is the canonical "cocycle ⇒ smooth bundle
section" construction: each chart's local coefficient `coeff x : ℂ → ℂ`
becomes the local representative of the section in that chart, and the
cotangent-cocycle condition is exactly the chart-transition compatibility
required by `ContMDiffSection`.

Both are mechanical (no deep classical analysis) — they are
structural constructions in Mathlib's bundle / smooth-section
formalism.

## Net effect

We replace one big abstract axiom (`AX_FiniteDimOneForms` ≈ Cartan–Serre)
with two concrete structural lemmas (the bridge map exists, and it is
injective). The deep analytic content — that the ContMDiffSection space
is finite-dimensional — is no longer asserted: it is derived from
Kirov's real Montel proof.

## Status

`bridgeForm` and `bridgeForm_injective` are currently scaffolded as
`theorem ... := by sorry`, with detailed proof sketches inline. Pick
either sorry and discharge it; the other can stay open during work on
the first.

See `vendor/kirov-jacobian-claude/HANDOFF.md` for the surrounding
classical-citation handoff.
-/

import Jacobians.RiemannSurface.OneForm
import Jacobians.Vendor.Kirov.HolomorphicForms

namespace Jacobians.Bridge

open scoped Manifold ContDiff Bundle Topology
open Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace BridgeForm

open Jacobians.Vendor.Kirov.Montel

/-- Some chart in Kirov's finite inner-open cover contains `y`. -/
private theorem exists_chartChoice [Nonempty X] (y : X) :
    ∃ x ∈ (chartCover : Finset X), y ∈ innerChartOpen (X := X) x := by
  have hy : y ∈ (Set.univ : Set X) := Set.mem_univ y
  rw [← iUnion_innerChartOpen_chartCover_eq (X := X)] at hy
  simp only [Set.mem_iUnion] at hy
  rcases hy with ⟨x, hx, hxy⟩
  exact ⟨x, hx, hxy⟩

/-- A chart in Kirov's finite inner-open cover containing `y`. -/
noncomputable def chartChoice [Nonempty X] (y : X) : X :=
  Classical.choose (exists_chartChoice (X := X) y)

theorem chartChoice_mem [Nonempty X] (y : X) :
    chartChoice (X := X) y ∈ (chartCover : Finset X) :=
  (Classical.choose_spec (exists_chartChoice (X := X) y)).1

theorem mem_innerChartOpen_chartChoice [Nonempty X] (y : X) :
    y ∈ innerChartOpen (X := X) (chartChoice (X := X) y) :=
  (Classical.choose_spec (exists_chartChoice (X := X) y)).2

/-- The cotangent value obtained from the chart-centered coefficient in the chart at `x`. -/
noncomputable def rawCLM [Nonempty X] (form : HolomorphicOneForm X) (x y : X) :
    TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y :=
  (form.coeff x ((extChartAt 𝓘(ℂ, ℂ) x) y)) •
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y)

end BridgeForm

/-! ## Construction of the bridge map

The construction proceeds by, for each holomorphic-1-form cocycle
`form : HolomorphicOneForm X` and each base point `p : X`, packaging
the chart-local coefficient `form.coeff p` into a continuous ℂ-linear
map `T_p X →L[ℂ] ℂ` (i.e. an element of the cotangent fiber at `p`).

### Per-point construction sketch

For `p : X` and `form : HolomorphicOneForm X`:

1. Let `c : ℂ := form.coeff p ((extChartAt 𝓘(ℂ) p) p)`. This is the
   value of the chart-local coefficient at the central point of the
   chart at `p` — well-defined since `p ∈ (extChartAt 𝓘(ℂ) p).source`
   (by `mem_extChartAt_source`) and so `extChartAt p p ∈ target`.

2. The chart at `p` gives a smooth identification
   `(extChartAt 𝓘(ℂ) p) : X ⊇ source ≃ ℂ ⊇ target`.
   Its `mfderiv` at `p` is a continuous ℂ-linear iso
   `T_p X →L[ℂ] ℂ` (because the chart is a partial diffeomorphism near
   `p`, `mfderiv_eq_chart` style fact).

3. The cotangent value is `c • (mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) p) p)`,
   i.e. multiplication by `c` post-composed with the chart's mfderiv.

4. By the cotangent-cocycle condition on `form`, the resulting cotangent
   value at `p` does not depend on which chart contains `p` — but we
   sidestep the dependence question by always using the **chart at `p`**
   (i.e., `extChartAt 𝓘(ℂ) p` itself). Compatibility on overlaps is
   what we need for **smoothness**, not well-definedness of the
   pointwise value.

### Smoothness sketch

Smoothness of the assembled section means: for each `p₀ : X`, in
`inCoordinates` form (push to chart at `p₀` on the source, push to
the trivial bundle's standard fiber on the target), the section is
analytic on a neighborhood of `(chart p₀) p₀`.

The local representative in the chart at `p₀` is exactly the function
`z ↦ (form.coeff p₀ z) · 1` (mapped to `ℂ →L[ℂ] ℂ` by scalar
multiplication), which is analytic on `(extChartAt 𝓘(ℂ) p₀).target`
by `form.2.1 p₀` (the `IsHolomorphicOneFormCoeff` predicate).

Compatibility on chart overlaps: switching from chart at `p₀` to chart
at any other `q` gives a coefficient related by the chart-transition
mfderiv via `form.2.2.1 p₀ q ...` (the `SatisfiesCotangentCocycle`
predicate). This is exactly the transition law `ContMDiffSection`
demands.

## Useful Mathlib API

The discharge needs (likely subset; iterate via `lean_leansearch`):

- `ContMDiffSection.mk` (or the structure literal) — construct a section.
- `mfderiv_extChartAt`, `extChartAt_target`, `mem_extChartAt_source`,
  `extChartAt_self`, `mfderiv_chart_isUnit` — chart bookkeeping.
- `contMDiffAt_hom_bundle` — reduces smoothness of a bundle hom-valued
  function to coordinate smoothness (used heavily by Kirov's
  `pullbackForm` proof in `Vendor/Kirov/HolomorphicForms.lean:122`,
  which is a useful template).
- `AnalyticOn.contMDiffOn` — promote `AnalyticOn` to `ContMDiffOn`.
- For the bundle target `Bundle.Trivial X ℂ` is just the constant fiber
  `ℂ`; the relevant `ContinuousLinearMap` arithmetic is straightforward.
-/

/-- **The bridge.** Canonical ℂ-linear map from chart-cocycle holomorphic
1-forms to Kirov's `ContMDiffSection`-encoded holomorphic 1-forms.

Discharges to a real `def` once the section construction + smoothness
proof are filled in. See the file-level docstring for the construction
sketch. -/
noncomputable def bridgeForm :
    HolomorphicOneForm X →ₗ[ℂ] Jacobians.Vendor.Kirov.HolomorphicOneForms X := by
  -- Construction skeleton:
  --
  --   refine
  --     { toFun := fun form =>
  --         { toFun := fun p => <build cotangent value at p from form.coeff p>
  --           contMDiff_toFun := <smoothness proof using form.2.1 (analyticity)
  --                              and form.2.2.1 (cocycle)> }
  --       map_add' := <pointwise; coeff_add + addition of CLMs>
  --       map_smul' := <pointwise; coeff_smul + scalar mul of CLMs> }
  --
  -- See file-level docstring for the per-point construction and the
  -- smoothness sketch. The Kirov `pullbackForm` proof in
  -- `Vendor/Kirov/HolomorphicForms.lean:122` is the closest in-repo
  -- template for the smoothness obligation.
  sorry

/-- **Injectivity of the bridge.** The cocycle ⇒ section map is
injective: distinct cocycle 1-forms give rise to distinct global
sections.

### Proof sketch

Suppose `bridgeForm form₁ = bridgeForm form₂`. The two sections agree
pointwise on `X`. Fix `p : X`; the cotangent values
`(bridgeForm form_i) p : T_p X →L[ℂ] ℂ` agree. By construction of
`bridgeForm`, this means
  `form_1.coeff p ((extChartAt 𝓘(ℂ) p) p) = form_2.coeff p ((extChartAt 𝓘(ℂ) p) p)`
(after extracting the scalar from the equation
`c₁ • (mfderiv chart p) = c₂ • (mfderiv chart p)` using non-degeneracy
of the chart's mfderiv).

But this only fixes the value of `coeff p` at the **single point**
`(extChartAt 𝓘(ℂ) p) p`. To conclude `form_1.coeff = form_2.coeff` we
need agreement on **all** chart targets:

* For `z ∈ (extChartAt 𝓘(ℂ) p).target`, let `q := (extChartAt 𝓘(ℂ) p).symm z`
  (the back-image of `z` under the chart at `p`). Then `q ∈ source`,
  hence `(extChartAt 𝓘(ℂ) q) q ∈ (extChartAt 𝓘(ℂ) q).target`, and the
  pointwise-at-`q` argument above gives
  `form_1.coeff q ((extChartAt 𝓘(ℂ) q) q) = form_2.coeff q ((extChartAt 𝓘(ℂ) q) q)`.
* Use the cotangent-cocycle condition (`form_i.2.2.1`) at the pair
  `(p, q, z)` to express both `form_i.coeff p z` in terms of
  `form_i.coeff q ((extChartAt 𝓘(ℂ) q) ((extChartAt 𝓘(ℂ) p).symm z))`,
  which after the chart-symm reduces to
  `form_i.coeff q ((extChartAt 𝓘(ℂ) q) q)`.
* Conclude `form_1.coeff p z = form_2.coeff p z`.

For `z ∉ (extChartAt 𝓘(ℂ) p).target`, both `form_i.coeff p z = 0` by
`form_i.2.2.2 p z` (the `IsZeroOffChartTarget` predicate).

So `form_1.coeff p = form_2.coeff p` for all `p`, i.e.
`form_1.coeff = form_2.coeff` as functions, and `form_1 = form_2` by
`HolomorphicOneForm.ext_of_coeff` / `Subtype.ext`.

### Useful Mathlib / project API

- `HolomorphicOneForm.ext_of_coeff` (`RiemannSurface/OneForm.lean:181`)
  — extensionality of cocycle 1-forms by coefficient.
- `IsHolomorphicOneFormCoeff` / `SatisfiesCotangentCocycle` /
  `IsZeroOffChartTarget` — the three cocycle predicates.
- `mem_extChartAt_source p : p ∈ (extChartAt 𝓘(ℂ) p).source`
- `extChartAt_target_subset_range`, `PartialEquiv.map_source` — chart
  source/target bookkeeping.
- `ContMDiffSection.ext` (or `Sigma.ext` / `funext` on `.toFun`) — section
  extensionality. -/
theorem bridgeForm_injective :
    Function.Injective (bridgeForm : HolomorphicOneForm X → _) := by
  -- See proof sketch in the docstring above. Suggested top-level shape:
  --
  --   intro form₁ form₂ hEq
  --   apply HolomorphicOneForm.ext_of_coeff
  --   funext p z
  --   by_cases hz : z ∈ (extChartAt 𝓘(ℂ) p).target
  --   · -- on-target: use sections agreeing at q := (extChartAt 𝓘(ℂ) p).symm z
  --     -- + cotangent cocycle (form_i.2.2.1) to unfold both sides
  --     sorry
  --   · -- off-target: form_i.coeff p z = 0 by IsZeroOffChartTarget
  --     rw [form₁.2.2.2 p z hz, form₂.2.2.2 p z hz]
  sorry

/-- **Derived instance.** Finite-dimensionality of `HolomorphicOneForm X`,
transferred via the injective bridge from Kirov's Montel-derived
`FiniteDimensional ℂ (HolomorphicOneForms X)` instance.

This replaces the previous `AX_FiniteDimOneForms` axiom: the abstract
Cartan–Serre / normal-families finiteness claim is now derived from
Kirov's real ~3.4 kLOC Montel proof (modulo the closed-ball-compactness
step, which Kirov's commit `7ce9e2e` resolves) plus the two structural
bridge lemmas above. -/
instance finiteDimensional_holomorphicOneForm :
    FiniteDimensional ℂ (HolomorphicOneForm X) :=
  Module.Finite.of_injective (bridgeForm (X := X)) bridgeForm_injective

end Jacobians.Bridge
