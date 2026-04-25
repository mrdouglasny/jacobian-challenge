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

We assert (as axioms, for handoff) the existence and injectivity of a
ℂ-linear map from our cocycle definition to Kirov's section definition:

```
axiom bridgeForm     : HolomorphicOneForm X →ₗ[ℂ] Vendor.Kirov.HolomorphicOneForms X
axiom bridgeForm_injective : Function.Injective (bridgeForm (X := X))
```

Mathematically `bridgeForm` is the canonical "cocycle ⇒ smooth bundle
section" construction: each chart's local coefficient `coeff x : ℂ → ℂ`
becomes the local representative of the section in that chart, and the
cotangent-cocycle condition is exactly the chart-transition compatibility
required by `ContMDiffSection`.

Both axioms are mechanical (no deep classical analysis) — they are
structural constructions in Mathlib's bundle / smooth-section
formalism. Discharging them is the natural follow-up to this bridge
(see `vendor/kirov-jacobian-claude/HANDOFF.md` for the discharge
strategy).

## Net effect

We replace one big abstract axiom (`AX_FiniteDimOneForms` ≈ Cartan–Serre)
with two concrete structural axioms (the bridge map exists, and it is
injective). The deep analytic content — that the ContMDiffSection space
is finite-dimensional — is no longer asserted: it is derived from
Kirov's real Montel proof.
-/

import Jacobians.RiemannSurface.OneForm
import Jacobians.Vendor.Kirov.HolomorphicForms

namespace Jacobians.Bridge

open scoped Manifold ContDiff
open Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Bridge axiom (structural).** The canonical ℂ-linear map sending a
chart-cocycle holomorphic 1-form on `X` to the corresponding global
analytic section of the cotangent bundle, in Kirov's `ContMDiffSection`
encoding.

To discharge: construct the section directly from cocycle data. For a
cocycle `coeff : X → ℂ → ℂ`, the section at `x : X` is the cotangent
covector whose value on `v : TangentSpace 𝓘(ℂ) x` is
`coeff x ((extChartAt 𝓘(ℂ) x) x) · (mfderiv-of-chart applied to v)`.
Smoothness of the resulting section follows from analyticity of each
`coeff x` and the cotangent-cocycle condition on chart overlaps.

See `vendor/kirov-jacobian-claude/HANDOFF.md`. -/
axiom bridgeForm :
    HolomorphicOneForm X →ₗ[ℂ] Jacobians.Vendor.Kirov.HolomorphicOneForms X

/-- **Bridge axiom (structural).** The cocycle ⇒ section map is
injective: distinct cocycle 1-forms give rise to distinct global
sections.

To discharge: extract the cocycle data back from the section by
restriction to chart targets. Two sections agreeing globally must
restrict to the same local representatives in every chart, hence have
the same cocycle data, hence are equal as elements of the cocycle
submodule. -/
axiom bridgeForm_injective :
    Function.Injective (bridgeForm : HolomorphicOneForm X → _)

/-- **Derived instance.** Finite-dimensionality of `HolomorphicOneForm X`,
transferred via the injective bridge from Kirov's Montel-derived
`FiniteDimensional ℂ (HolomorphicOneForms X)` instance.

This replaces the previous `AX_FiniteDimOneForms` axiom: the abstract
Cartan–Serre / normal-families finiteness claim is now derived from
Kirov's real ~3.4 kLOC Montel proof (modulo the closed-ball-compactness
step, which Kirov's commit `7ce9e2e` resolves) and the two structural
bridge axioms above. -/
instance finiteDimensional_holomorphicOneForm :
    FiniteDimensional ℂ (HolomorphicOneForm X) :=
  Module.Finite.of_injective (bridgeForm (X := X)) bridgeForm_injective

end Jacobians.Bridge
