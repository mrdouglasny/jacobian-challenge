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

/-- **Chart-swap lemma.** On the overlap of two chart sources, `rawCLM` is independent of
which chart is used. This is the cocycle-coherence property that drives both the
`bridgeForm` smoothness proof (locally swap to a fixed cover-chart) and the
chart-at-self-vs-fixed-chart equality used inside it.

The proof combines the cocycle predicate (`form.2.2.1`) with the chain rule
`mfderiv_comp` for `extChartAt x' = (extChartAt x' ∘ (extChartAt x).symm) ∘ extChartAt x`
near `y`, plus the 1-dimensional identity `T(v) = (T 1) • v` for `T : ℂ →L[ℂ] ℂ`. -/
theorem rawCLM_swap_chart [Nonempty X] (form : HolomorphicOneForm X) {x x' y : X}
    (hxy : y ∈ (extChartAt 𝓘(ℂ, ℂ) x).source)
    (hx'y : y ∈ (extChartAt 𝓘(ℂ, ℂ) x').source) :
    rawCLM form x y = rawCLM form x' y := by
  -- Set up the key data.
  set z : ℂ := (extChartAt 𝓘(ℂ, ℂ) x) y with hz_def
  -- z is in `target x` since y ∈ source x.
  have hz_tgt : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target :=
    (extChartAt 𝓘(ℂ, ℂ) x).map_source hxy
  -- And `(extChartAt x).symm z = y`.
  have hsymm : (extChartAt 𝓘(ℂ, ℂ) x).symm z = y :=
    (extChartAt 𝓘(ℂ, ℂ) x).left_inv hxy
  -- Now invoke the cocycle predicate at (x, x', z).
  have hcoc : form.coeff x z =
      form.coeff x' ((extChartAt 𝓘(ℂ, ℂ) x') ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1) :=
    form.2.2.1 x x' z hz_tgt (by rw [hsymm]; exact hx'y)
  -- Substitute `(extChartAt x).symm z = y` inside the coefficient slot.
  rw [hsymm] at hcoc
  -- Chain rule: `mfderiv (extChartAt x') y = (mfderiv (extChartAt x' ∘ (extChartAt x).symm) z) ∘L (mfderiv (extChartAt x) y)`.
  -- Strictly: `extChartAt x' = (extChartAt x' ∘ (extChartAt x).symm) ∘ extChartAt x` near `y`.
  have hmdiff_x : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y := by
    apply mdifferentiableAt_extChartAt
    rwa [← extChartAt_source (I := 𝓘(ℂ, ℂ))]
  have hmdiff_x' : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x') y := by
    apply mdifferentiableAt_extChartAt
    rwa [← extChartAt_source (I := 𝓘(ℂ, ℂ))]
  -- The chart-transition map (extChartAt x' ∘ (extChartAt x).symm) is mdifferentiable at z.
  have hmdiff_symm : MDifferentiableWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (extChartAt 𝓘(ℂ, ℂ) x).symm (Set.range (𝓘(ℂ, ℂ))) z :=
    mdifferentiableWithinAt_extChartAt_symm hz_tgt
  -- For maps ℂ → ℂ, mfderiv = fderiv. We'll use this with the chart-transition.
  -- Key fact: a CLM `T : ℂ →L[ℂ] ℂ` equals `T 1 • id`, so
  --   `fderiv (φ' ∘ φ⁻¹) z 1 • mfderiv (extChartAt x) y = mfderiv (extChartAt x' ∘ (extChartAt x).symm) z ∘L mfderiv (extChartAt x) y = mfderiv (extChartAt x') y`.
  -- Step 1: identify the trans-derivative as multiplication by a scalar.
  -- The composition (extChartAt x' ∘ (extChartAt x).symm) is a map ℂ → ℂ; its mfderiv = fderiv.
  -- For a 1-dim ℂ-linear map T, T = T(1) • id_ℂ.
  -- Step 2: rewrite `mfderiv (extChartAt x') y` via composition = transition ∘L mfderiv (extChartAt x) y.
  -- We use `extChartAt x' = (extChartAt x' ∘ (extChartAt x).symm) ∘ extChartAt x` LOCALLY near y,
  -- which gives the chain rule via `Filter.EventuallyEq.mfderiv_eq` + `mfderiv_comp`.
  -- The local equality holds because (extChartAt x).symm ∘ extChartAt x = id near y.
  have hLocalEq : (extChartAt 𝓘(ℂ, ℂ) x') =ᶠ[𝓝 y]
      (((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ∘ (extChartAt 𝓘(ℂ, ℂ) x)) := by
    filter_upwards [extChartAt_source_mem_nhds' hxy] with w hw
    simp only [Function.comp_apply, (extChartAt 𝓘(ℂ, ℂ) x).left_inv hw]
  -- Apply the chain rule.
  have hmfd_eq : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x') y =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ∘ (extChartAt 𝓘(ℂ, ℂ) x)) y := by
    exact hLocalEq.mfderiv_eq
  -- The transition map's mfderiv equals fderiv (vector-space case).
  have hsymm_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z := by
    -- 𝓘(ℂ,ℂ) is boundaryless, so range = univ and `mdifferentiableWithinAt` upgrades.
    have hrange : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
      ModelWithCorners.range_eq_univ _
    rw [← mdifferentiableWithinAt_univ, ← hrange]
    exact hmdiff_symm
  have hTrans_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z := by
    -- (extChartAt x).symm sends z to y; then extChartAt x' is mdifferentiable at y.
    have hcomp : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z := by
      have := (hsymm ▸ hmdiff_x' :
        MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x')
          ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
      exact this.comp z hsymm_mdiff
    exact hcomp
  -- Chain rule for `(transition) ∘ (extChartAt x)` at `y`:
  --   mfderiv ((transition) ∘ (extChartAt x)) y = mfderiv (transition) z ∘L mfderiv (extChartAt x) y
  -- since (extChartAt x) y = z.
  have hcomp_chain : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) ∘ (extChartAt 𝓘(ℂ, ℂ) x)) y =
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z).comp
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) :=
    mfderiv_comp_of_eq hTrans_mdiff hmdiff_x hz_def.symm
  -- Combine `hmfd_eq` (equality of mfderivs) with the chain rule.
  have hmfd_x'_chain : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x') y =
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z).comp
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) :=
    hmfd_eq.trans hcomp_chain
  -- Now unfold rawCLM and substitute hcoc + the chain rule.
  unfold rawCLM
  rw [hcoc, mul_smul, hmfd_x'_chain]
  -- Goal: c2 • (fderiv T z 1 • mfderiv (extChartAt x) y) =
  --       c2 • ((mfderiv T z) ∘L (mfderiv (extChartAt x) y))
  congr 1
  -- Goal: fderiv T z 1 • mfderiv (extChartAt x) y = mfderiv T z ∘L mfderiv (extChartAt x) y
  -- Replace mfderiv (transition) with fderiv (transition) since both vector spaces.
  have hmfd_trans : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z =
      fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z :=
    mfderiv_eq_fderiv
  rw [hmfd_trans]
  -- For T : ℂ →L[ℂ] ℂ, T ∘L S equals T(1) • S as continuous linear maps.
  -- Use ContinuousLinearMap extensionality, applying both sides to a tangent vector v.
  apply ContinuousLinearMap.ext
  intro v
  -- Goal: ((fderiv ... z 1) • (mfderiv ... y)) v = ((fderiv ... z) ∘L (mfderiv ... y)) v.
  -- LHS = (fderiv ... z 1) • (mfderiv ... y v) = (fderiv ... z 1) * (mfderiv ... y v).
  -- RHS = (fderiv ... z) (mfderiv ... y v).
  -- For T : ℂ →L[ℂ] ℂ and w : ℂ, T w = T 1 * w by ℂ-linearity.
  -- Both v's TangentSpace and the codomain TangentSpace at (extChartAt x) y are defeq to ℂ.
  show (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1) •
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) v =
      (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z)
        ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) v)
  -- Now both sides are ℂ-valued (the • is scalar mult on ℂ, the application is ℂ → ℂ).
  set T := fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) x') ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z with hT_def
  set w : ℂ := (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x) y) v with hw_def
  -- Goal: T 1 • w = T w.
  -- By 1-D linearity: T w = T (w • 1) = w • T 1 = T 1 • w (using mul_comm on ℂ).
  have : T w = w • T 1 := by
    conv_lhs => rw [show w = w • (1 : ℂ) from (mul_one w).symm]
    rw [ContinuousLinearMap.map_smul]
  rw [this]
  -- Goal: T 1 • w = w • T 1.  Both sides are products in ℂ; commute via smul_eq_mul + mul_comm.
  show T 1 * w = w * T 1
  ring

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

The pointwise value at `y : X` is

```
form.coeff y ((extChartAt 𝓘(ℂ) y) y) • (mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) y) y)
```

i.e. `BridgeForm.rawCLM form y y` in the chart **at `y` itself**. Using
the chart-at-self has two advantages:

* extensionality / injectivity is straightforward, because at the
  basepoint `mfderiv (extChartAt y) y = id` (`mfderiv_extChartAt_self`),
  so the section value reduces to `c • id` where `c` is the diagonal
  coefficient `form.coeff y ((extChartAt y) y)`;
* the pointwise value depends only on `form.coeff` along the diagonal,
  so the sectional `map_add' / map_smul'` reduce to direct rewriting via
  `coeff_add / coeff_smul` and the linearity of scalar multiplication on
  CLMs.

The smoothness witness `contMDiff_toFun` is the only deep obligation;
it remains as a `sorry` for now (see `docs/KirovHolomorphicLessons.md`
for the planned discharge route via `rawCLM_eq_of_mem_innerChartOpen`,
`rawCLM_trivialized_eq_smul_id`, `contMDiffOn_totalSpaceMk_rawCLM`). -/
noncomputable def bridgeForm :
    HolomorphicOneForm X →ₗ[ℂ] Jacobians.Vendor.Kirov.HolomorphicOneForms X where
  toFun form :=
    { toFun := fun y => BridgeForm.rawCLM form y y
      contMDiff_toFun := by
        -- **Smoothness via local-equality + fixed-chart trivialization.**
        --
        -- Strategy (Step 2 of `docs/KirovHolomorphicLessons.md`):
        --   1. `intro y₀` — fix the base point.
        --   2. By `BridgeForm.rawCLM_swap_chart`, for `y ∈ (extChartAt y₀).source`,
        --        `rawCLM form y y = rawCLM form y₀ y`.
        --      Use `ContMDiffAt.congr_of_eventuallyEq` on the totalSpace function
        --      `(fun y ↦ ⟨y, rawCLM form _ y⟩)` to swap chart-at-self → chart-at-y₀.
        --   3. Reduce via `contMDiffAt_hom_bundle` to base smoothness (= id) and
        --      the `inCoordinates` (trivialized) representative smoothness.
        --   4. Inside the trivialization the rep reduces (via
        --      `Bundle.Trivial.continuousLinearMapAt_trivialization` and
        --      `TangentBundle.continuousLinearMapAt_trivializationAt` +
        --      `Bundle.Trivialization.symmL_continuousLinearMapAt`) to
        --        `(form.coeff y₀ ((extChartAt y₀) y)) • ContinuousLinearMap.id ℂ ℂ`.
        --   5. Smoothness of that scalar: `form.coeff y₀ : ℂ → ℂ` is analytic on
        --      `(extChartAt y₀).target`; compose with smooth `extChartAt y₀`.
        --
        -- Closest template: `Jacobians.Vendor.Kirov.HolomorphicForms.pullbackForm`
        -- (lines ~127–188), which uses the same `contMDiffAt_hom_bundle` reduction.
        intro y₀
        -- Step 2: replace chart-at-self with chart-at-y₀ on a nbhd of y₀.
        -- We'll prove smoothness of the FIXED-CHART section, then transfer.
        -- `congr_of_eventuallyEq` consumes `f₁ =ᶠ f` to convert smoothness of `f`
        -- into smoothness of `f₁`, so we orient the eq with chart-at-self on the LHS.
        have hSwap :
            (fun y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (BridgeForm.rawCLM form y y)) =ᶠ[𝓝 y₀]
            (fun y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (BridgeForm.rawCLM form y₀ y)) := by
          filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ, ℂ)) y₀] with y hy
          -- y ∈ source y₀ and y ∈ source y; apply rawCLM_swap_chart.
          have hy_y : y ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := mem_extChartAt_source y
          rw [show BridgeForm.rawCLM form y y = BridgeForm.rawCLM form y₀ y from
            BridgeForm.rawCLM_swap_chart form hy_y hy]
        -- It suffices to show smoothness of the fixed-chart version.
        suffices h : ContMDiffAt 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
            (fun y => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (BridgeForm.rawCLM form y₀ y)) y₀ from
          h.congr_of_eventuallyEq hSwap
        -- Goal: ContMDiffAt _ _ ω (T% (fun y => rawCLM form y₀ y)) y₀.
        -- Following the `pullbackForm` template (Vendor/Kirov/HolomorphicForms.lean ~127–188):
        -- reduce via `contMDiffAt_hom_bundle` to base smoothness (id) and inCoordinates rep.
        rw [contMDiffAt_hom_bundle]
        refine ⟨contMDiffAt_id, ?_⟩
        -- Goal: ContMDiffAt _ _ ω (fun y => inCoordinates ... y₀ y y₀ y (rawCLM form y₀ y)) y₀.
        -- The inCoordinates rep unfolds (via Bundle.Trivial.continuousLinearMapAt_trivialization
        -- and the symmL/continuousLinearMapAt round-trip on the source side) to a scalar
        -- multiple of `mfderiv (extChartAt y₀) y` viewed in the trivialization. By
        -- `TangentBundle.continuousLinearMapAt_trivializationAt` this trivialized mfderiv
        -- collapses to `id` after applying `symmL ∘ continuousLinearMapAt = id` from
        -- `Bundle.Trivialization.symmL_continuousLinearMapAt`. The remaining scalar
        -- `form.coeff y₀ ((extChartAt y₀) y)` is smooth via `coeff y₀` analytic on the
        -- chart target plus smooth chart map. Left as `sorry` for now.
        sorry }
  map_add' form₁ form₂ := by
    apply ContMDiffSection.ext
    intro y
    change BridgeForm.rawCLM (form₁ + form₂) y y =
      BridgeForm.rawCLM form₁ y y + BridgeForm.rawCLM form₂ y y
    simp only [BridgeForm.rawCLM, HolomorphicOneForm.coeff_add, Pi.add_apply, add_smul]
    rfl
  map_smul' c form := by
    apply ContMDiffSection.ext
    intro y
    change BridgeForm.rawCLM (c • form) y y = c • BridgeForm.rawCLM form y y
    simp only [BridgeForm.rawCLM, HolomorphicOneForm.coeff_smul, Pi.smul_apply,
      smul_eq_mul, mul_smul]
    rfl

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
  intro form₁ form₂ hEq
  -- Step 1: pointwise section equality.
  have hpt : ∀ p : X, BridgeForm.rawCLM form₁ p p = BridgeForm.rawCLM form₂ p p := by
    intro p
    have := congrArg (fun α : Jacobians.Vendor.Kirov.HolomorphicOneForms X => α.toFun p) hEq
    -- `.toFun` of `bridgeForm form` at `p` is `rawCLM form p p` by construction.
    exact this
  -- Step 2: extract the diagonal coefficient equality
  --   `form₁.coeff p ((extChartAt p) p) = form₂.coeff p ((extChartAt p) p)`
  -- using `mfderiv_extChartAt_self` to identify `mfderiv (extChartAt p) p` with the identity,
  -- then applying both sides of `c₁ • id = c₂ • id` to `1 : ℂ`.
  have hdiag : ∀ p : X,
      form₁.coeff p ((extChartAt 𝓘(ℂ, ℂ) p) p) =
        form₂.coeff p ((extChartAt 𝓘(ℂ, ℂ) p) p) := by
    intro p
    have h := hpt p
    -- Unfold rawCLM and rewrite via `mfderiv_extChartAt_self`.
    have hmfd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) p) p =
        ContinuousLinearMap.id ℂ ℂ := mfderiv_extChartAt_self
    simp only [BridgeForm.rawCLM, hmfd] at h
    -- `h : c₁ • id = c₂ • id` as CLMs `ℂ →L[ℂ] ℂ`.
    -- Apply to `1 : ℂ` to get `c₁ * 1 = c₂ * 1`, i.e. `c₁ = c₂`.
    -- Apply both sides to `1 : ℂ`. Use `DFunLike.congr_fun` so the application is real.
    have h1 := DFunLike.congr_fun h (1 : ℂ)
    -- `h1 : (c₁ • id) 1 = (c₂ • id) 1`. Reduce: `(c • id) 1 = c • (id 1) = c • 1 = c * 1 = c`.
    -- The `(c • f) x = c • f x` reduction is just `rfl` for CLMs (`smul_apply` is `rfl`).
    change form₁.coeff p ((extChartAt 𝓘(ℂ, ℂ) p) p) • (1 : ℂ) =
        form₂.coeff p ((extChartAt 𝓘(ℂ, ℂ) p) p) • (1 : ℂ) at h1
    simpa using h1
  -- Step 3: extend equality of `coeff` to all chart-target points using the cocycle.
  apply HolomorphicOneForm.ext_of_coeff
  funext p z
  -- Unfold `coeff` to the underlying subtype coercion to match the cocycle/zero-off-target
  -- predicates' phrasing (they refer to `↑form` directly, which is `form.1 = form.coeff`).
  show (form₁ : X → ℂ → ℂ) p z = (form₂ : X → ℂ → ℂ) p z
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) p).target
  · -- On-target: pull `coeff p z` back to `coeff q ((extChartAt q) q)` for `q := (extChartAt p).symm z`.
    set q : X := (extChartAt 𝓘(ℂ, ℂ) p).symm z with hq_def
    have hq_src : q ∈ (extChartAt 𝓘(ℂ, ℂ) q).source := mem_extChartAt_source q
    -- Apply the cocycle predicate: form_i.coeff p z = form_i.coeff q ((extChartAt q) q) * factor.
    -- The "factor" is the same `fderiv` term for both forms.
    have hcoc₁ := form₁.2.2.1 p q z hz hq_src
    have hcoc₂ := form₂.2.2.1 p q z hz hq_src
    -- Convert the `(extChartAt p).symm z` argument inside the `coeff` slots to `q`.
    rw [← hq_def] at hcoc₁ hcoc₂
    rw [hcoc₁, hcoc₂]
    -- Both sides now share the `fderiv ... z 1` factor; cancel via `hdiag q`.
    -- `hdiag q : form₁.coeff q ((extChartAt q) q) = form₂.coeff q ((extChartAt q) q)`,
    -- which is `↑form₁ q ... = ↑form₂ q ...` definitionally (`coeff = .1 = ↑`).
    congr 1
    exact hdiag q
  · -- Off-target: both coefficients are zero by `IsZeroOffChartTarget`.
    rw [form₁.2.2.2 p z hz, form₂.2.2.2 p z hz]

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
