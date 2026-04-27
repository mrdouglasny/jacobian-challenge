/-
# Hyperelliptic 1-form framework: `g(x) dx / y` as a `HolomorphicOneForm`

This file provides a **reusable cocycle constructor** that takes any
polynomial `g : Polynomial ℂ` and produces the holomorphic 1-form
`g(x) dx / y` on the hyperelliptic curve, packaged as a real
`HolomorphicOneForm`.

Once this constructor lands, the basis differentials and the genus
theorem follow naturally:

* `hyperellipticEvenDxOverY := hyperellipticForm 1`
* `hyperellipticEvenBasisDifferential k := hyperellipticForm (Polynomial.X ^ k)`
* Linear independence of `{ x^k dx/y : 0 ≤ k < g }` ↔ linear
  independence of `{ X^k : 0 ≤ k < g }` in `Polynomial ℂ`
  (degree-`< g` polynomials are linearly independent — standard fact).
* The genus formula combines the lower bound (basis cardinality) with
  the upper bound from `AX_RiemannRoch`.

## Local structure of `g(x) dx / y`

In each chart of `HyperellipticEvenProj H` (and analogously
`HyperellipticOdd H h`), the form `g(x) dx / y` has a chart-local
coefficient determined by the chart projection:

* **`affineChartProjX`** (chart `(x, y) ↦ x` on `y ≠ 0`): coefficient
  is `g(z) / (chart symm z).val.2 = g(x) / y(x)`. Analytic on the
  chart target since `g` is polynomial and `y(x)` is the analytic
  branch of `√f(x)`.
* **`affineChartProjY`** (chart `(x, y) ↦ y` on `f'(x) ≠ 0`): after
  the change of variable `dx = (2y / f'(x)) dy`, the coefficient is
  `2 g(x(y)) / f'(x(y))`. Analytic where `f'(x) ≠ 0`.
* **Affine-infinity charts** (for `HyperellipticEvenProj`): same
  shape, with `Polynomial.reverse H.f` instead of `H.f`. Need to
  account for the change of variable `x = 1/x'`, `y = y' / x'^{g+1}`,
  giving an extra `x^{2k - 2g}` style factor that is finite iff
  `deg g ≤ g - 1`.

Cocycle on overlaps: the chart-transition mfderiv is the chain-rule
factor that exactly absorbs the change of variable above.

## Status

This file is currently **scaffolded** — the constructor and all
supporting lemmas are stated with `sorry` bodies. The discharge plan
documents the concrete proof obligations.

## Discharge plan

1. **Affine chart-local coefficient.** Define the case-split on
   `smoothLocusY` vs `smoothLocusX` for the affine `(x, y)`-chart and
   verify analyticity on each chart's target. Reuses Codex's
   `affineChartProjX` / `affineChartProjY` from
   `OddAtlas/AffineChart.lean`.
2. **Cocycle on affine-affine overlaps.** Four sub-cases (projX/Y ×
   projX/Y); the cross sub-cases use the chain rule
   `dy/dx = f'(x)/(2y)`.
3. **Affine-infinity coefficient.** Mirror of (1) using
   `Polynomial.reverse H.f` and the EA1 definitional equality.
4. **Cross-summand cocycle on the gluing region.** The Möbius-like
   transition `x ↦ 1/x` from EA2 cross-summand axioms.
5. **Off-target normalization.** Set `coeff` to 0 outside chart
   targets to satisfy `IsZeroOffChartTarget`.
6. **Linearity** (`map_add`, `map_smul`) — straightforward once (1)–(5)
   land.
7. **Linear independence** of `{ hyperellipticForm (X^k) : k < g }`:
   reduce to linear independence of `{ X^k : k < g }` in `Polynomial ℂ`
   via `Polynomial.linearIndependent_pow`.
8. **Genus theorem** as corollary: combine (7) with `AX_RiemannRoch`
   upper bound. ~30 LOC.

See `docs/hyperelliptic-even-atlas-plan.md` for the broader plan.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenForm
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.ProjectiveCurve.HyperellipticEvenProj

open scoped Manifold ContDiff
open Jacobians.RiemannSurface
open Polynomial

variable {H : HyperellipticData} [Fact (¬ Odd H.f.natDegree)]

/-! ## The reusable `hyperellipticForm` constructor -/

/-- The "infinity-side" polynomial paired with `g` in the gluing.

For a basis monomial `g = X^k` (with `k ≤ g_topology - 1`), this is
`-X^(g_topology - 1 - k)`. In general it is `-Polynomial.reflect
(g_topology - 1) g`, where `g_topology = H.f.natDegree / 2 - 1` is the
expected geometric genus. This is the polynomial such that the form
`g(x) dx / y` extends holomorphically across the gluing region — the
relation `g_inf(u) = -u^(g_topology - 1) g(1/u)` exactly cancels the
factors `dx = -du/u^2` and `y = v / u^(g_topology + 1)`. -/
noncomputable def infReverse (H : HyperellipticData) (g : Polynomial ℂ) :
    Polynomial ℂ :=
  -Polynomial.reflect (H.f.natDegree / 2 - 2) g

/-- The holomorphic 1-form `g(x) dx / y` on `HyperellipticEvenProj H`,
parameterized by an arbitrary polynomial `g : Polynomial ℂ`.

Constructed as the unified coefficient family
`hyperellipticEvenCoeff g (infReverse H g)` together with its
`holomorphicOneFormSubmodule` membership proof. The membership proof
is real on the within-summand cocycle predicates (analyticity,
off-target, same-summand cocycle) and rests on two cross-summand
axioms in `EvenForm.lean` for the Möbius gluing region. -/
noncomputable def hyperellipticForm (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] (g : Polynomial ℂ) :
    HolomorphicOneForm (HyperellipticEvenProj H) :=
  ⟨hyperellipticEvenCoeff (H := H) g (infReverse H g),
   hyperellipticEvenCoeff_mem_submodule g (infReverse H g)⟩

/-! ## Linearity -/

/-- `hyperellipticForm` is additive in the polynomial. -/
theorem hyperellipticForm_add (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] (g g' : Polynomial ℂ) :
    hyperellipticForm H (g + g') =
      hyperellipticForm H g + hyperellipticForm H g' := by
  sorry

/-- `hyperellipticForm` is ℂ-linear (scalar mult side). -/
theorem hyperellipticForm_smul (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] (c : ℂ) (g : Polynomial ℂ) :
    hyperellipticForm H (c • g) = c • hyperellipticForm H g := by
  sorry

/-- `hyperellipticForm` of the zero polynomial is the zero form. -/
theorem hyperellipticForm_zero (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    hyperellipticForm H (0 : Polynomial ℂ) = 0 := by
  sorry

/-- The packaged ℂ-linear map version of `hyperellipticForm`. -/
noncomputable def hyperellipticFormLinearMap (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    Polynomial ℂ →ₗ[ℂ] HolomorphicOneForm (HyperellipticEvenProj H) where
  toFun := hyperellipticForm H
  map_add' := hyperellipticForm_add H
  map_smul' c g := by
    simpa [RingHom.id_apply] using hyperellipticForm_smul H c g

/-! ## Linear independence

The family `{ hyperellipticForm (X^k) : 0 ≤ k < g }` is linearly
independent in `HolomorphicOneForm`. Reduces to linear independence
of `{ X^k : 0 ≤ k < g }` in `Polynomial ℂ` (standard Mathlib fact)
via injectivity of `hyperellipticFormLinearMap` restricted to the
degree-`< g` subspace.
-/

/-- Injectivity of `hyperellipticForm` on polynomials of degree
`< H.f.natDegree / 2 - 1`. The form `g(x) dx / y` is nonzero whenever
`g` is a nonzero polynomial of degree `< g_topology` (the geometric
genus). -/
theorem hyperellipticForm_injOn_lowDegree
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)] :
    Set.InjOn (hyperellipticForm H)
      { g : Polynomial ℂ | g.natDegree < H.f.natDegree / 2 - 1 } := by
  sorry

/-- Linear independence of the canonical basis. Combines
`Polynomial.linearIndependent_pow_lt` with `hyperellipticForm_injOn_lowDegree`. -/
theorem hyperellipticForm_linearIndependent (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    LinearIndependent ℂ
      (fun k : Fin (H.f.natDegree / 2 - 1) =>
        hyperellipticForm H (Polynomial.X ^ k.val)) := by
  sorry

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
