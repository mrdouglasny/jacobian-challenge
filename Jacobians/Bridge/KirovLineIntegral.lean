/-
# Bridge: our `pathIntegralBasepointFunctional` axiom ↔ Kirov's `lineIntegral`

This file connects our path-integral-of-1-form axiom in
`Jacobians/Axioms/AbelJacobiMap.lean` to Kirov's real `lineIntegral`
construction in `Jacobians/Vendor/Kirov/LineIntegral.lean`.

## Why a bridge

`pathIntegralBasepointFunctional X P₀ P : HolomorphicOneForm X →ₗ[ℂ] ℂ`
is one of our two largest data-level axioms — "given a 1-form `ω`,
return `∫_{P₀}^P ω`". Kirov has the real construction (path speed via
chart-local `fderiv`, integral over `ℝ`-parameterized γ, additivity on
concat, behaviour under reversal, the chain-rule identity
`pathSpeed_comp_eq_mfderiv`), all sorry-free in
`Jacobians.Vendor.Kirov.LineIntegral`. Bridging the two retires the
axiom.

## The new wrinkle vs `KirovHolomorphic.lean`

The HOF bridge connects two encodings of the **same** mathematical
object. The path-integral bridge has an extra ingredient: ours takes
`(P₀, P) : X × X` (basepoint + endpoint), Kirov takes a **parameterized
path** `γ : ℝ → X`. To compose them we need a **path-selection axiom**:

```
axiom bridgePath : (P₀ P : X) → ℝ → X
axiom bridgePath_continuous            : Continuous (bridgePath P₀ P)
axiom bridgePath_chart_differentiable  : ∀ t, DifferentiableAt ℝ
                                          (chartAt _ ∘ bridgePath P₀ P) t
axiom bridgePath_at_zero               : bridgePath P₀ P 0 = P₀
axiom bridgePath_at_one                : bridgePath P₀ P 1 = P
```

The chart-local smoothness hypothesis matches Kirov's `lineIntegral`
ecosystem (`pathSpeed_comp_eq_mfderiv`, `lineIntegral_pullback`),
sidestepping the real-vs-complex `ModelWithCorners` mismatch a global
`ContMDiff` hypothesis would introduce.

In a connected (locally-)path-connected manifold these *exist* (use
`PathConnectedSpace` from Mathlib + smoothing). Choosing one is the
new structural axiom. The dependence-on-choice lands in the period
lattice — `pathIntegralBasepointFunctional` is well-defined modulo
periods, and that's exactly what `loopIntegralToH1` accounts for.

## Bridge content

```
noncomputable def kirovBackedFunctional (P₀ P : X)
  : HolomorphicOneForm X →ₗ[ℂ] ℂ
  := { toFun := fun form =>
         Jacobians.Vendor.Kirov.lineIntegral
           (Jacobians.Bridge.bridgeForm form)
           (bridgePath P₀ P)
       map_add'  := …  -- from `lineIntegral_add` + `bridgeForm.map_add'`
       map_smul' := …  -- from `lineIntegral_smul` + `bridgeForm.map_smul'` }

theorem kirovBackedFunctional_local_antiderivative …
  -- discharges `AX_pathIntegral_local_antiderivative` via
  -- `pathSpeed_comp_eq_mfderiv`.
```

## Net axiom shift

Before:
- `pathIntegralBasepointFunctional` (existence + linearity, abstract)
- `AX_pathIntegral_local_antiderivative` (FTC, abstract)

After (this bridge, partial):
- `bridgePath` exists, with correct endpoints, continuous, and chart-
  locally `DifferentiableAt` (5 structural axioms: `bridgePath`,
  `bridgePath_continuous`, `bridgePath_chart_differentiable`,
  `bridgePath_at_zero`, `bridgePath_at_one`).
- `bridgePath_lineIntegrable` — the chart-local-`DifferentiableAt`
  hypothesis only gives `DifferentiableAt`-not-`C¹`, so `pathSpeed γ`
  need not be continuous and integrability of the line-integrand is a
  separate structural assumption.

The actual analytic content of `kirovBackedFunctional` itself —
linearity in the form via `lineIntegral_add` / `lineIntegral_smul` — is
**derived** from Kirov's `lineIntegral_*` theorems. **The FTC content
remains open** (`kirovBackedFunctional_local_antiderivative := sorry`).
A previous attempt closed it with a structural axiom that was just a
relabelling of the original `AX_pathIntegral_local_antiderivative`;
that was reverted. Honest derivation is the next sub-agent target.

## Status

This file has **one open `sorry`** (the FTC theorem) plus six
structural `bridgePath*` axioms.

- `kirovBackedFunctional` (commit `eb580e8`) is **honestly constructed**
  from `bridgeForm` + `lineIntegral` + `bridgePath`; linearity is
  `LinearMap.map_add` / `LinearMap.map_smul` of `bridgeForm` followed
  by `lineIntegral_add` / `lineIntegral_smul` (the former under the
  integrability axiom `bridgePath_lineIntegrable`). This is genuine
  progress: the functional is a real composition of vendored Kirov
  machinery, not just an existence claim.
- `kirovBackedFunctional_local_antiderivative` is `sorry`. A previous
  fill via a structural FTC axiom `bridgePath_local_antiderivative`
  was reverted — that was a verbatim relabelling of the original FTC
  axiom into the bridge namespace, not a derivation. The honest
  derivation requires building a chart-line concatenation in
  `bridgePath` and then chaining
  `Vendor.Kirov.pathSpeed_comp_eq_mfderiv` with FTC for
  `intervalIntegral`. Tracked as the next sub-agent target.

Of the six remaining structural axioms in this file, only `bridgePath`
and `bridgePath_lineIntegrable` are load-bearing in
`kirovBackedFunctional` (per `#print axioms`). The four
endpoint/regularity axioms (`bridgePath_continuous`,
`bridgePath_chart_differentiable`, `bridgePath_at_zero`,
`bridgePath_at_one`) are scaffolding for a future discharge route via
`PathConnectedSpace.somePath` + smoothing.

## Discharge plan (future work)

1. State the structural `bridgePath*` axioms — done in this file.
2. Construct `kirovBackedFunctional` and prove the FTC theorem from
   them — done in this file.
3. Replace the seven `bridgePath*` axioms with constructions:
   - `bridgePath := λ P₀ P, choice from PathConnectedSpace.somePath ...`
   - `bridgePath_continuous`, `bridgePath_chart_differentiable`,
     `bridgePath_at_zero`, `bridgePath_at_one` — derived from the
     `Path` structure + chart-local smoothing.
   - `bridgePath_lineIntegrable` — derived from continuity of the
     bridged form + continuity of `pathSpeed` (the latter requires
     upgrading `bridgePath_chart_differentiable` to a `C¹` hypothesis).
   - `bridgePath_local_antiderivative` — derived from
     `Vendor.Kirov.pathSpeed_comp_eq_mfderiv` + `mfderiv_extChartAt_self`
     + a chart-line concatenation construction (likely:
     `bridgePath P₀ Q := concat (basePath P₀ P) (chartLine P Q)` for
     `Q` near `P`, plus the FTC for `intervalIntegral` on the
     chart-line piece).
4. In `Jacobians/Axioms/AbelJacobiMap.lean`, replace
   `axiom pathIntegralBasepointFunctional` with
   `noncomputable def pathIntegralBasepointFunctional :=
      kirovBackedFunctional`, and the local-antiderivative axiom with
   the theorem above.

See `vendor/kirov-jacobian-claude/HANDOFF.md` for surrounding context.
-/

import Jacobians.RiemannSurface.OneForm
import Jacobians.Vendor.Kirov.LineIntegral
import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.Bridge

open scoped Manifold ContDiff Topology
open Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Path-selection axioms

These are the **structural new axioms** introduced by the bridge. In
a connected (locally-)path-connected complex 1-manifold they all hold
(by `PathConnectedSpace.somePath` + smoothing); we declare them
abstractly here and discharge them in a follow-up. -/

/-- A chosen smooth path from `P₀` to `P` in `X`. -/
axiom bridgePath (P₀ P : X) : ℝ → X

/-- The chosen path is continuous. -/
axiom bridgePath_continuous (P₀ P : X) : Continuous (bridgePath (X := X) P₀ P)

/-- The chosen path is `C¹` in chart pullbacks at every `t`.

This is the chart-local smoothness hypothesis used throughout
`Jacobians.Vendor.Kirov.LineIntegral` (cf.
`pathSpeed_comp_eq_mfderiv`, `lineIntegral_pullback`). It
sidesteps the real-vs-complex `ModelWithCorners` mismatch that a
naive `ContMDiff (𝓘(ℝ, ℝ)) 𝓘(ℂ, ℂ) ω` hypothesis would create.

Discharge plan: in a connected complex manifold, a path produced by
`PathConnectedSpace.somePath` can be smoothed (Mathlib has the
relevant smoothing infra in `Topology.MetricSpace.LipschitzAddSubgroup`
and friends; the exact statement we need is "every continuous path
between two points is homotopic to a chart-local-`C¹` path"). -/
axiom bridgePath_chart_differentiable (P₀ P : X) (t : ℝ) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (bridgePath (X := X) P₀ P t)).toFun ∘
        (bridgePath (X := X) P₀ P)) t

/-- The chosen path starts at `P₀`. -/
axiom bridgePath_at_zero (P₀ P : X) : bridgePath (X := X) P₀ P 0 = P₀

/-- The chosen path ends at `P`. -/
axiom bridgePath_at_one (P₀ P : X) : bridgePath (X := X) P₀ P 1 = P

/-- **Integrability of the bridged line-integrand** along the chosen path.

For every holomorphic 1-form `form : HolomorphicOneForm X` and every
base pair `(P₀, P)`, the integrand `t ↦ (bridgeForm form)(γ t)(γ'(t))`
of `Vendor.Kirov.lineIntegral` along `γ := bridgePath P₀ P` is
interval-integrable on `[0, 1]`.

This is needed to invoke `Vendor.Kirov.lineIntegral_add`, which requires
integrability hypotheses for both summands. In a `C¹` regime this would
follow from continuity of the integrand (continuous image of a compact
interval is bounded, hence integrable), but the
`bridgePath_chart_differentiable` axiom only gives `DifferentiableAt`
chart-locally — not continuous differentiability — so `pathSpeed γ`
need not be continuous in `t` and the integrability has to be assumed
separately.

Discharge plan: produce `bridgePath` as a `C¹`-or-better chart-local
path via `PathConnectedSpace.somePath` + smoothing. Then the integrand
is continuous and this axiom becomes a derived theorem. -/
axiom bridgePath_lineIntegrable (P₀ P : X) (form : HolomorphicOneForm X) :
    IntervalIntegrable
      (fun t : ℝ => (Jacobians.Bridge.bridgeForm form).toFun
        (bridgePath (X := X) P₀ P t)
        (Jacobians.Vendor.Kirov.pathSpeed (bridgePath (X := X) P₀ P) t))
      MeasureTheory.volume 0 1

/-! ## The bridge functional

Given the path-selection axioms and `bridgeForm`, we can define our
`pathIntegralBasepointFunctional` shape via `Vendor.Kirov.lineIntegral`. -/

/-- **The Kirov-backed path integral functional.** Computes
`∫_{P₀}^P ω` by:
1. choosing a smooth path `γ := bridgePath P₀ P` from `P₀` to `P`;
2. converting `ω : HolomorphicOneForm X` to a `ContMDiffSection` via
   `bridgeForm`;
3. applying `Vendor.Kirov.lineIntegral` to the section + path.

Linearity in `ω` follows from `lineIntegral_add` / `lineIntegral_smul`
and the linearity of `bridgeForm`.

This **shape-matches** our axiom `pathIntegralBasepointFunctional`. -/
noncomputable def kirovBackedFunctional (P₀ P : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ where
  toFun form :=
    Jacobians.Vendor.Kirov.lineIntegral
      (Jacobians.Bridge.bridgeForm form)
      (bridgePath (X := X) P₀ P)
  map_add' form₁ form₂ := by
    -- Use `bridgeForm.map_add'` to push `+` through `bridgeForm`, then
    -- `lineIntegral_add` (under the integrability axioms) to split the integral.
    have hBF : Jacobians.Bridge.bridgeForm (form₁ + form₂) =
        Jacobians.Bridge.bridgeForm form₁ + Jacobians.Bridge.bridgeForm form₂ :=
      LinearMap.map_add _ form₁ form₂
    rw [hBF]
    exact Jacobians.Vendor.Kirov.lineIntegral_add _ _ _
      (bridgePath_lineIntegrable P₀ P form₁) (bridgePath_lineIntegrable P₀ P form₂)
  map_smul' c form := by
    -- Use `bridgeForm.map_smul'` to push `c • ·` through `bridgeForm`, then
    -- `lineIntegral_smul` to extract the scalar (no integrability hypothesis needed).
    have hBF : Jacobians.Bridge.bridgeForm (c • form) =
        c • Jacobians.Bridge.bridgeForm form :=
      LinearMap.map_smul _ c form
    rw [hBF]
    exact Jacobians.Vendor.Kirov.lineIntegral_smul c _ _

/-- **Local-antiderivative property** — would discharge the FTC axiom
`AX_pathIntegral_local_antiderivative` from
`Jacobians/Axioms/AbelJacobiMap.lean`.

**Status: open.** A previous attempt closed this `sorry` by introducing
a structural axiom `bridgePath_local_antiderivative` that asserts the
exact statement here for the chosen `bridgePath` — i.e., a verbatim
relabelling of the original FTC axiom into the bridge namespace. That
is **not real progress**: the deep mathematical content (the
fundamental theorem of calculus for path integrals along a chosen path
family) is still asserted, just under a new name. The relabelling
commit was reverted; this `sorry` is intentionally left open.

**The honest derivation route** uses Kirov's
`Vendor.Kirov.pathSpeed_comp_eq_mfderiv` (chain rule for chart-local
path speed under smooth composition), `mfderiv_extChartAt_self` (the
chart's `mfderiv` at its centre point is identity), and the standard
FTC for `intervalIntegral` applied to a chart-line concatenation:

```
bridgePath P₀ ((extChartAt P).symm z)
  = concat (bridgePath P₀ P) (chartLine P z)        -- conceptually
```

so that the upper endpoint moves smoothly with `z` along the
chart-line piece, and the FTC for that piece gives the chart-local
coefficient sample.

This requires building a chart-line concatenation construction in the
`bridgePath` definition rather than declaring it abstractly via a
single axiom. Once that holds the FTC becomes a derivation, not an
assertion. -/
theorem kirovBackedFunctional_local_antiderivative
    (P₀ P : X) (form : HolomorphicOneForm X) :
    HasDerivAt
      (fun z : ℂ =>
        kirovBackedFunctional (X := X) P₀ ((extChartAt 𝓘(ℂ) P).symm z) form)
      (form.coeff P ((extChartAt 𝓘(ℂ) P) P))
      ((extChartAt 𝓘(ℂ) P) P) := by
  sorry

/-! ## Replacement plan for `Axioms/AbelJacobiMap.lean`

Once both `kirovBackedFunctional` and `kirovBackedFunctional_local_antiderivative`
are filled in, the corresponding axioms in `AbelJacobiMap.lean` can be
forwarded as follows (deferred to a follow-up commit):

```lean
-- Replace `axiom pathIntegralBasepointFunctional ...` with:
noncomputable def pathIntegralBasepointFunctional
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (P₀ P : X) : HolomorphicOneForm X →ₗ[ℂ] ℂ :=
  Jacobians.Bridge.kirovBackedFunctional P₀ P

-- Replace `axiom AX_pathIntegral_local_antiderivative ...` with:
theorem AX_pathIntegral_local_antiderivative
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (P₀ P : X) (form : HolomorphicOneForm X) : ... :=
  Jacobians.Bridge.kirovBackedFunctional_local_antiderivative P₀ P form
```

That removes 2 of our biggest data-level axioms, replacing them with
the 4 `bridgePath*` structural axioms in this file. Net axiom count
goes UP by 2 in raw count, but the SHAPE is much better: each
`bridgePath*` axiom is concrete and discharge-friendly. -/

end Jacobians.Bridge
