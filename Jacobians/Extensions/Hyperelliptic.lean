/-
# Challenge extensions: hyperelliptic curves

This file states a sequence of theorems **extending Buzzard's challenge**
to concrete computations on the hyperelliptic curves we have already
constructed (`HyperellipticOdd`, `HyperellipticEven`,
[`Hyperelliptic`](../ProjectiveCurve/Hyperelliptic.lean)). Each theorem
is a meaningful test of the formalization end-to-end:

- it forces the cocycle definition `HolomorphicOneForm` to compute
  correctly on a non-elliptic curve;
- it forces our finite-dimensionality bridge
  (`Jacobians.Bridge.finiteDimensional_holomorphicOneForm`, which
  routes through Kirov's Montel proof) to deliver a real `finrank`
  rather than the `0` collapse we'd see on a vacuous module;
- it forces the `genus`, `Jacobian`, `ofCurve`, `pullback`, `pushforward`
  API to match its classical meaning, not just type-check.

All theorems below are stated as `theorem … := by sorry` (or
`noncomputable def … := sorry` when the construction itself is the
deliverable). Discharge order recommended:

1. **Warm-ups** (single-form constructions): `hyperellipticDxOverY`,
   `hyperellipticBasisDifferential`. Each is a single witness — no
   upper bound work, just the cocycle predicates on a concrete form.
2. **Linear independence of the basis family** (`x^k dx/y` for
   `k = 0, … , g-1`): combinatorial / power-series argument.
3. **Genus theorem** (`genus_HyperellipticOdd_eq`): combine the basis
   for the lower bound with `AX_RiemannRoch` for the upper bound.
4. **Consistency** (`genus_HyperellipticOdd_eq_one_of_deg_three`): the
   `g = 1` case agrees with `genus_Elliptic_eq_one`.
5. **Stretch** (`hyperellipticInvolution_*`): the hyperelliptic
   involution `σ : (x, y) ↦ (x, -y)` and the fact `σ^* = -id` on
   `H^0(X, Ω^1)`. Tests `pullback`/functoriality. Requires defining
   the involution as a real Lean function first.

Classical references:

* Forster, *Lectures on Riemann Surfaces*, §17 (genus of hyperelliptic
  curves; canonical basis).
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. VII §1–2.
* Mumford, *Tata Lectures on Theta I*, §III.3 (canonical basis,
  hyperelliptic involution).
-/

import Jacobians.Challenge
import Jacobians.ProjectiveCurve.Hyperelliptic
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.Extensions.Hyperelliptic

open scoped Manifold ContDiff
open Jacobians.ProjectiveCurve
open Jacobians.RiemannSurface

/-! ## Warm-up 1 — `dx/y` is a holomorphic 1-form

The differential `dx/y` is the standard "everywhere-finite" 1-form on
the hyperelliptic curve `y² = f(x)` when `deg f` is odd. In the affine
chart it reads literally `dx/y`; near a Weierstrass point (a root of
`f`, where `y = 0`) it is finite via the local change of coordinates
`y = √(x - α) · u` for `u` analytic and nonzero. At infinity (no branch
point in the odd-degree case, but a pair of points in the even-degree
case) it is also finite, with a similar local-change-of-coordinates
argument.

This is **the simplest possible test of the cocycle definition**: one
form, three or more local representatives, glued by the
`SatisfiesCotangentCocycle` predicate.
-/

/-- The holomorphic 1-form `dx / y` on a hyperelliptic curve with odd
degree `f`. -/
noncomputable def hyperellipticDxOverY
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    HolomorphicOneForm (HyperellipticOdd H h) := by
  -- Construct the cocycle (`coeff`, three predicates) explicitly. In
  -- the affine chart at `(x₀, y₀)` with `y₀ ≠ 0`, the local
  -- representative is the constant `1 / y₀` (since `dx/y` already
  -- equals `(1/y) · dx` and the chart projection is `x ↦ x`). At a
  -- Weierstrass point use the local uniformizer `t` with `t² = x - α`.
  sorry

/-! ## Warm-up 2 — `x^k dx / y` for `k = 0, ..., g-1`

These are the canonical basis differentials. Each one is a holomorphic
1-form by the same local-coords analysis as `dx/y`, with the extra
`x^k` factor lowering the order at infinity by `k`; the constraint
`k ≤ g - 1` is exactly what keeps the form finite there.
-/

/-- The holomorphic 1-form `x^k · dx / y` on a hyperelliptic curve with
odd degree `f`, valid for `k ≤ g - 1` where `g = (deg f - 1) / 2`. -/
noncomputable def hyperellipticBasisDifferential
    (H : HyperellipticData) (h : Odd H.f.natDegree)
    (k : ℕ) (_hk : k < (H.f.natDegree - 1) / 2) :
    HolomorphicOneForm (HyperellipticOdd H h) := by
  -- Multiply the local coefficient of `hyperellipticDxOverY` by `x^k`.
  -- Use the same cocycle argument; `x^k` is analytic and the
  -- transition law is multiplicative on the chart-transition mfderiv.
  sorry

/-! ## Linear independence of the basis family

The family `{ x^k · dx / y : 0 ≤ k < g }` is linearly independent in
`HolomorphicOneForm (HyperellipticOdd H h)`. Classical argument: in
the local affine chart, the family becomes `{ x^k / y : 0 ≤ k < g }`
which are linearly independent as germs of meromorphic functions
because `1, x, x^2, …, x^(g-1)` are linearly independent polynomials.
-/

/-- The canonical basis of holomorphic 1-forms on a hyperelliptic curve
with odd-degree `f` is linearly independent. -/
theorem hyperellipticBasisDifferential_linearIndependent
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    LinearIndependent ℂ
      (fun k : Fin ((H.f.natDegree - 1) / 2) =>
        hyperellipticBasisDifferential H h k.val k.isLt) := by
  sorry

/-! ## Main test — genus theorem

The classical formula: `genus (HyperellipticOdd H h) = (deg f - 1) / 2`
when `f` has odd degree.

* **Lower bound** (`(deg f - 1) / 2 ≤ genus`): the basis above is
  linearly independent in `HolomorphicOneForm`, so its rank gives a
  lower bound on `Module.finrank`. Crucially uses the bridge-derived
  `FiniteDimensional` instance — without it `finrank` would silently
  return `0`.
* **Upper bound** (`genus ≤ (deg f - 1) / 2`): apply Riemann–Roch
  (`AX_RiemannRoch`) to the canonical divisor or to a divisor
  `(2g - 2) ∞` and take the dimension count. -/

/-- **Genus formula for odd-degree hyperelliptic curves.** Tests the
formalization end-to-end: cocycle definition + Kirov-Montel
finite-dim bridge + Riemann–Roch axiom + the canonical basis. -/
theorem genus_HyperellipticOdd_eq
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Jacobians.RiemannSurface.genus (HyperellipticOdd H h) =
      (H.f.natDegree - 1) / 2 := by
  sorry

/-- **Consistency check.** For odd-degree-3 hyperelliptic curves
(`y² = cubic`), the genus formula gives `1`, agreeing with our
existing `genus_Elliptic_eq_one`. This catches the failure mode in
which the two definitions of "genus 1 curve" — via `Elliptic` and
via `HyperellipticOdd` with `deg = 3` — yield different values. -/
theorem genus_HyperellipticOdd_eq_one_of_deg_three
    (H : HyperellipticData) (h : Odd H.f.natDegree)
    (hdeg : H.f.natDegree = 3) :
    Jacobians.RiemannSurface.genus (HyperellipticOdd H h) = 1 := by
  -- Direct corollary of `genus_HyperellipticOdd_eq` after computing
  -- `(3 - 1) / 2 = 1`.
  rw [genus_HyperellipticOdd_eq H h, hdeg]

/-! ## Stretch — hyperelliptic involution and `σ^* = -id`

The involution `σ : (x, y) ↦ (x, -y)` on the affine chart extends to
the smooth model. It is an order-2 automorphism, fixes the Weierstrass
points, and acts as `-id` on `H^0(X, Ω^1)` — a foundational fact about
hyperelliptic Jacobians.

Defining `σ` as a Lean function and proving its properties is itself a
worthwhile exercise on the chart machinery; the `pullback`-action
identity then tests the functoriality side of the challenge API.
-/

/-- **Hyperelliptic involution** `σ : (x, y) ↦ (x, -y)` on the smooth
model of a hyperelliptic curve. -/
noncomputable def hyperellipticInvolution
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    HyperellipticOdd H h → HyperellipticOdd H h := by
  -- On the affine chart: send `⟨(x, y), hxy⟩` to `⟨(x, -y), neg_pow ▸ hxy⟩`.
  -- At infinity (single point in the odd-degree case): identity.
  sorry

/-- The hyperelliptic involution is an order-2 map: `σ ∘ σ = id`. -/
theorem hyperellipticInvolution_involutive
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Function.Involutive (hyperellipticInvolution H h) := by
  sorry

/-- The hyperelliptic involution is smooth (hence in particular
`ContMDiff` for the `ω` smoothness level Buzzard's challenge uses). -/
theorem hyperellipticInvolution_contMDiff
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (hyperellipticInvolution H h) := by
  sorry

/-- **The involution acts as `-id` on holomorphic 1-forms.** Tests the
`pullback` side of the challenge API end-to-end: the well-known
identity `σ^* (x^k · dx/y) = -(x^k · dx/y)` (because `σ^* dx = dx`
while `σ^* (1/y) = -1/y`) lifts to the global statement that pullback
under `σ` is the negation map on `HolomorphicOneForm (HyperellipticOdd H h)`.

NOTE: stating this requires either (a) our cocycle-side pullback API
on `HolomorphicOneForm` (not yet built — currently lives only as the
axiom `pullbackOneForm` in `Axioms/AbelJacobiMap.lean`), or (b) routing
through the Kirov-bridge to use `Vendor.Kirov.HolomorphicForms.pullbackForm`.
The signature below uses option (a), so this theorem also exercises the
`pullbackOneForm` axiom — discharging it is the prerequisite. -/
theorem pullback_hyperellipticInvolution_eq_neg
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    True := by
  -- Placeholder signature — see NOTE in the docstring. Real statement:
  --   pullbackOneForm (hyperellipticInvolution H h)
  --       (hyperellipticInvolution_contMDiff H h)
  --     = (-LinearMap.id : HolomorphicOneForm _ →ₗ[ℂ] HolomorphicOneForm _)
  -- once `pullbackOneForm` is real and not an axiom.
  trivial

/-! ## Stretch — Weierstrass points

In the odd-degree case `deg f = 2g + 1`, the smooth model has exactly
`2g + 2` Weierstrass points: the `2g + 1` roots of `f` (each lifted to
a single point with `y = 0`) plus the single point at infinity.
-/

/-- **Count of Weierstrass points** on a hyperelliptic curve. The fixed
locus of `hyperellipticInvolution` has cardinality `H.f.natDegree + 1`
(in the odd-degree case: roots of `f` plus the point at infinity). -/
theorem card_fixedPoints_hyperellipticInvolution
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Nat.card { p : HyperellipticOdd H h //
      hyperellipticInvolution H h p = p } = H.f.natDegree + 1 := by
  sorry

end Jacobians.Extensions.Hyperelliptic
