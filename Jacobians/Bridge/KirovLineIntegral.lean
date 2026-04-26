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
axiom bridgePath_isSmooth : ContMDiff (𝓘(ℝ, ℝ)) 𝓘(ℂ, ℂ) ω (bridgePath P₀ P)
axiom bridgePath_at_zero  : bridgePath P₀ P 0 = P₀
axiom bridgePath_at_one   : bridgePath P₀ P 1 = P
```

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

After (this bridge):
- `bridgePath` exists, smooth, with correct endpoints (4 small
  structural axioms — discharge by extracting from `PathConnectedSpace`
  + smoothing in connected manifolds).

The actual analytic content — that the assembled functional satisfies
linearity and the chart-local FTC — is **derived** from Kirov's
`lineIntegral_*` theorems and `pathSpeed_comp_eq_mfderiv`.

## Status

This file is currently a **scaffold**. The bridge function and FTC
theorem are stated but their bodies are `sorry`. The path-selection
axioms are the new contributions; we do not duplicate the HOF bridge
work (which is in flight in `Jacobians/Bridge/KirovHolomorphic.lean`).

## Discharge plan

1. State the four `bridgePath*` axioms (this file).
2. Construct `kirovBackedFunctional` using `bridgeForm` + `lineIntegral`
   + `bridgePath`. Linearity follows from `lineIntegral_add`,
   `lineIntegral_smul`, and the linearity of `bridgeForm`.
3. Prove `kirovBackedFunctional` satisfies the local-antiderivative
   property via Kirov's `pathSpeed_comp_eq_mfderiv` chain rule.
4. In `Jacobians/Axioms/AbelJacobiMap.lean`, replace
   `axiom pathIntegralBasepointFunctional` with
   `noncomputable def pathIntegralBasepointFunctional :=
      kirovBackedFunctional`, and the local-antiderivative axiom with a
   theorem.

After (4), the only path-integral-side axioms are the four
`bridgePath*` structural axioms — concrete enough that someone can
discharge them via `PathConnectedSpace.somePath` + smoothing in a
follow-up.

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

/-- The chosen path is smooth (analytic) as a map `ℝ → X`. -/
axiom bridgePath_contMDiff (P₀ P : X) :
    ContMDiff (𝓘(ℝ, ℝ)) 𝓘(ℂ, ℂ) ω (bridgePath (X := X) P₀ P)

/-- The chosen path starts at `P₀`. -/
axiom bridgePath_at_zero (P₀ P : X) : bridgePath (X := X) P₀ P 0 = P₀

/-- The chosen path ends at `P`. -/
axiom bridgePath_at_one (P₀ P : X) : bridgePath (X := X) P₀ P 1 = P

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
    HolomorphicOneForm X →ₗ[ℂ] ℂ := by
  -- Construction skeleton:
  --
  --   refine
  --     { toFun := fun form =>
  --         Jacobians.Vendor.Kirov.lineIntegral
  --           (bridgeForm form)
  --           (bridgePath P₀ P)
  --       map_add' := <use lineIntegral_add + bridgeForm.map_add>
  --       map_smul' := <use lineIntegral_smul + bridgeForm.map_smul> }
  --
  -- Both linearity proofs are 2-3 lines, depending on the API of
  -- `Jacobians.Vendor.Kirov.lineIntegral_{add,smul}`.
  sorry

/-- **Local-antiderivative property** — discharges the FTC axiom
`AX_pathIntegral_local_antiderivative` from
`Jacobians/Axioms/AbelJacobiMap.lean`.

The proof reduces to Kirov's `pathSpeed_comp_eq_mfderiv` plus the
inverse-function-theorem behaviour of `extChartAt P` near `P`. -/
theorem kirovBackedFunctional_local_antiderivative
    (P₀ P : X) (form : HolomorphicOneForm X) :
    HasDerivAt
      (fun z : ℂ =>
        kirovBackedFunctional (X := X) P₀ ((extChartAt 𝓘(ℂ) P).symm z) form)
      (form.coeff P ((extChartAt 𝓘(ℂ) P) P))
      ((extChartAt 𝓘(ℂ) P) P) := by
  -- Proof sketch:
  -- 1. Unfold `kirovBackedFunctional` to `lineIntegral (bridgeForm form) (bridgePath P₀ ·)`.
  -- 2. The derivative w.r.t. the upper endpoint factors through
  --    `pathSpeed_comp_eq_mfderiv` applied to `bridgePath`.
  -- 3. Evaluating at the chart center `(extChartAt P) P` collapses
  --    `mfderiv (extChartAt P) P` to identity (`mfderiv_extChartAt_self`).
  -- 4. The resulting scalar is `bridgeForm form` evaluated at the
  --    cotangent identity at `P`, which is `form.coeff P ((extChartAt P) P)`
  --    (this last step uses the `bridgeForm` definition + the
  --    `BridgeForm.rawCLM`-at-self formula).
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
