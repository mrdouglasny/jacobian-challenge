/-
# Challenge extensions: hyperelliptic curves, even-degree case

Companion to [`Jacobians/Extensions/Hyperelliptic.lean`](Hyperelliptic.lean)
(odd-degree warm-ups + headline genus). This file states the analogous
theorems for the even-degree parity:
`HyperellipticEvenProj H` for `h : ¬ Odd H.f.natDegree`.

Each theorem mirrors the odd-degree version with adjusted finiteness
checks at the **two** points at infinity (vs the single one in odd
degree). The classical formula:
```
genus (HyperellipticEvenProj H) = H.f.natDegree / 2 - 1
```

## Discharge order recommended

1. `hyperellipticEvenDxOverY` — `dx/y` as a holomorphic 1-form.
2. `hyperellipticEvenBasisDifferential` — the canonical basis
   `x^k dx/y` for `k = 0, …, g-1` where `g = H.f.natDegree / 2 - 1`.
3. `hyperellipticEvenBasisDifferential_linearIndependent`.
4. `genus_HyperellipticEven_eq` — the headline test, lower bound from
   the basis + upper bound from `AX_RiemannRoch`.

## Prerequisites in scope

* `HyperellipticEvenProj.instChartedSpace` and `instIsManifold` from
  `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` — provide
  the chart structure on `HyperellipticEvenProj H` under
  `[Fact (¬ Odd H.f.natDegree)]`. Callers below declare
  `haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩` once.
* `Jacobians.Bridge.finiteDimensional_holomorphicOneForm` — the
  bridge-derived `FiniteDimensional` instance via Kirov's Montel.
  Crucial: without it `Module.finrank` collapses to `0` and the
  genus theorem becomes vacuously true.

## Cross-references

Classical references (same as the odd case):
* Forster, *Lectures on Riemann Surfaces*, §17.
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. VII §1–2.
* Mumford, *Tata Lectures on Theta I*, §III.3.

See `docs/hyperelliptic-even-atlas-plan.md` for the full plan.
-/

import Jacobians.Challenge
import Jacobians.ProjectiveCurve.Hyperelliptic
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.Extensions.HyperellipticEven

open scoped Manifold ContDiff
open Jacobians.ProjectiveCurve
open Jacobians.RiemannSurface

/-! ## Warm-up 1 — `dx/y` is a holomorphic 1-form

The differential `dx/y` is the standard "everywhere-finite" 1-form on
the hyperelliptic curve `y² = f(x)` when `deg f` is even. In the affine
chart it reads literally `dx/y`; near a Weierstrass point (a root of
`f`, where `y = 0`) it is finite via the local change of coordinates
`y = √(x - α) · u` for `u` analytic and nonzero. At each of the **two**
infinity points (in even degree there are `∞₊` and `∞₋`,
distinguished by the sign of the leading `y`), it is also finite via
the analogous local-change-of-coordinates argument in the
`HyperellipticAffineInfinity` chart.

This is the simplest test of the cocycle definition on the even
parity: one form, four or more local representatives (two affine, two
infinity), glued by the `SatisfiesCotangentCocycle` predicate
including across the affine ↔ affine-infinity gluing region.
-/

/-- The holomorphic 1-form `dx / y` on a hyperelliptic curve with even
degree `f`. The hypothesis `¬ Odd H.f.natDegree` is wrapped as `Fact`
so that `ChartedSpace ℂ (HyperellipticEvenProj H)` resolves at signature
elaboration time. Callers in even-degree contexts declare
`haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩` once. -/
noncomputable def hyperellipticEvenDxOverY
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)] :
    HolomorphicOneForm (HyperellipticEvenProj H) := by
  -- Construct the cocycle (`coeff`, three predicates) explicitly. In
  -- the affine chart at `(x₀, y₀)` with `y₀ ≠ 0`, the local
  -- representative is `1 / y(z)` where `y(z)` is the chart-local
  -- branch of `√f(z)`. Same form on the affine-infinity side via
  -- the `reverseData` polynomial. At Weierstrass points use the local
  -- uniformizer `t` with `t² = x - α`. On the gluing overlap, the
  -- cocycle compatibility comes from the chain-rule transformation
  -- of `dx/y` under the change of coordinates `x ↦ 1/x`,
  -- `y ↦ y / x^{g+1}`.
  sorry

/-! ## Warm-up 2 — `x^k dx / y` for `k = 0, ..., g-1`

The canonical basis differentials. Each one is a holomorphic 1-form
by the same local-coords analysis as `dx/y`. The constraint
`k ≤ g - 1` is exactly what keeps the form finite at **both**
infinity points in the even case (vs the single ∞ in odd).
-/

/-- The holomorphic 1-form `x^k · dx / y` on an even-degree
hyperelliptic curve, valid for `k ≤ g - 1` where
`g = H.f.natDegree / 2 - 1`. -/
noncomputable def hyperellipticEvenBasisDifferential
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)]
    (k : ℕ) (_hk : k < H.f.natDegree / 2 - 1) :
    HolomorphicOneForm (HyperellipticEvenProj H) := by
  -- Multiply the local coefficient of `hyperellipticEvenDxOverY` by `x^k`.
  -- Use the same cocycle argument; `x^k` is analytic and the
  -- transition law is multiplicative on the chart-transition mfderiv.
  -- The `k < g - 1` constraint ensures the resulting form remains
  -- holomorphic at both infinity points: in the infinity chart, the
  -- coordinate change `x = 1/t` introduces a `t^{2k - 2g - 2 + 1}`
  -- factor, finite iff `k ≤ g - 1`.
  sorry

/-! ## Linear independence of the basis family

The family `{ x^k · dx / y : 0 ≤ k < g }` is linearly independent in
`HolomorphicOneForm (HyperellipticEvenProj H)`. Same argument as the
odd case: in the local affine chart, the family becomes
`{ x^k / y : 0 ≤ k < g }` which are linearly independent as germs
of meromorphic functions because `1, x, x^2, …, x^(g-1)` are linearly
independent polynomials.
-/

/-- The canonical basis of holomorphic 1-forms on an even-degree
hyperelliptic curve is linearly independent. -/
theorem hyperellipticEvenBasisDifferential_linearIndependent
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)] :
    LinearIndependent ℂ
      (fun k : Fin (H.f.natDegree / 2 - 1) =>
        hyperellipticEvenBasisDifferential H k.val k.isLt) := by
  sorry

/-! ## Headline test — genus theorem for even hyperelliptic

The classical formula:
```
genus (HyperellipticEvenProj H) = H.f.natDegree / 2 - 1
```
when `H.f.natDegree = 2g + 2`.

* **Lower bound** (`H.f.natDegree / 2 - 1 ≤ genus`): the basis above
  is linearly independent in `HolomorphicOneForm`, so its rank gives
  a lower bound on `Module.finrank`. Crucially uses the bridge-derived
  `FiniteDimensional` instance.
* **Upper bound** (`genus ≤ H.f.natDegree / 2 - 1`): apply
  Riemann–Roch (`AX_RiemannRoch`) to the canonical divisor.
-/

/-- **Genus formula for even-degree hyperelliptic curves.** Mirrors
`genus_HyperellipticOdd_eq` for the even parity. Tests the
formalization end-to-end on the even-quotient atlas + bridge +
basis + Riemann-Roch. -/
theorem genus_HyperellipticEven_eq
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)] :
    Jacobians.RiemannSurface.genus (HyperellipticEvenProj H) =
      H.f.natDegree / 2 - 1 := by
  sorry

/-- **Consistency check.** For even-degree-4 hyperelliptic curves
(`y² = quartic`), the genus formula gives `1`. Together with the
analogous `genus_HyperellipticOdd_eq_one_of_deg_three`, this confirms
that "genus 1 curve" is consistently realized across all three
parameterizations: `Elliptic`, `HyperellipticOdd` with `deg = 3`, and
`HyperellipticEvenProj` with `deg = 4`. -/
theorem genus_HyperellipticEven_eq_one_of_deg_four
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)]
    (hdeg : H.f.natDegree = 4) :
    Jacobians.RiemannSurface.genus (HyperellipticEvenProj H) = 1 := by
  rw [genus_HyperellipticEven_eq H, hdeg]

end Jacobians.Extensions.HyperellipticEven
