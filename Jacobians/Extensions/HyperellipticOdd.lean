/-
# Challenge extensions: hyperelliptic curves, odd-degree case

Companion to [`Jacobians/Extensions/HyperellipticEven.lean`](HyperellipticEven.lean)
(even-degree warm-ups + headline genus, **completed**). This file is the
**odd-degree extension project**: the analogous theorems for
`HyperellipticOdd H h` with `h : Odd H.f.natDegree`, structured to mirror
the even-degree file decl-for-decl and section-for-section.

Unlike the even file — whose genus theorem is **discharged** (PR #96, via
the Liouville/maximum-modulus axiom hierarchy) — the odd-degree warm-ups
and headline genus are **deliberately left as `sorry`** scaffolds: this is
a *stretch / extension* track, **not required for Buzzard's challenge**
(the core challenge headlines are ℙ¹ and `Elliptic`; the even file is the
completed real-example vetting). The odd file exists to (a) mirror the even
structure on the single-∞ parity and (b) host the hyperelliptic-involution
and Weierstrass-point stretch material the even file omits.

Each theorem is a meaningful test of the formalization end-to-end:

- it forces the cocycle definition `HolomorphicOneForm` to compute
  correctly on a non-elliptic curve;
- it forces our finite-dimensionality bridge
  (`Jacobians.Bridge.finiteDimensional_holomorphicOneForm`, which
  routes through Kirov's Montel proof) to deliver a real `finrank`
  rather than the `0` collapse we'd see on a vacuous module;
- it forces the `genus`, `Jacobian`, `ofCurve`, `pullback`, `pushforward`
  API to match its classical meaning, not just type-check.

## Discharge order recommended

1. `hyperellipticOddDxOverY` — `dx/y` as a holomorphic 1-form.
2. `hyperellipticOddBasisDifferential` — the canonical basis `x^k dx/y`
   for `k = 0, …, g-1` where `g = (H.f.natDegree - 1) / 2`.
3. `hyperellipticOddBasisDifferential_linearIndependent`.
4. `genus_HyperellipticOdd_eq` — the headline test, lower bound from the
   basis (`hyperellipticOddGenus_lower_bound`) + upper bound from
   Riemann–Roch / the Liouville axiom hierarchy (the remaining gap).
5. **Consistency** (`genus_HyperellipticOdd_eq_one_of_deg_three`): the
   `g = 1` case agrees with `genus_Elliptic_eq_one`.
6. **Stretch** (`hyperellipticInvolution_*`, `card_fixedPoints_*`): the
   hyperelliptic involution `σ : (x, y) ↦ (x, -y)`, the fact `σ^* = -id`
   on `H^0(X, Ω^1)`, and the Weierstrass-point count.

## Cross-references

Classical references (same as the even case):
* Forster, *Lectures on Riemann Surfaces*, §17 (genus of hyperelliptic
  curves; canonical basis).
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. VII §1–2.
* Mumford, *Tata Lectures on Theta I*, §III.3 (canonical basis,
  hyperelliptic involution).

See `docs/hyperelliptic-odd-atlas-plan.md` for the full plan.
-/

import Jacobians.Challenge
import Jacobians.ProjectiveCurve.Hyperelliptic
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.Extensions.HyperellipticOdd

open scoped Manifold ContDiff
open Jacobians.ProjectiveCurve
open Jacobians.RiemannSurface

namespace HyperellipticAffine

variable {H : HyperellipticData}

/-- Affine sign-flip `(x, y) ↦ (x, -y)` on the hyperelliptic equation
`y² = f(x)`. -/
def involution (p : HyperellipticAffine H) : HyperellipticAffine H := by
  refine ⟨(p.val.1, -p.val.2), ?_⟩
  calc
    (-p.val.2) ^ 2 = p.val.2 ^ 2 := by ring
    _ = H.f.eval p.val.1 := p.property

@[simp] theorem involution_val_fst (p : HyperellipticAffine H) :
    (involution p).val.1 = p.val.1 :=
  rfl

@[simp] theorem involution_val_snd (p : HyperellipticAffine H) :
    (involution p).val.2 = -p.val.2 :=
  rfl

@[simp] theorem involution_involution (p : HyperellipticAffine H) :
    involution (involution p) = p := by
  apply Subtype.ext
  simp [involution]

end HyperellipticAffine

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
noncomputable def hyperellipticOddDxOverY
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
noncomputable def hyperellipticOddBasisDifferential
    (H : HyperellipticData) (h : Odd H.f.natDegree)
    (k : ℕ) (_hk : k < (H.f.natDegree - 1) / 2) :
    HolomorphicOneForm (HyperellipticOdd H h) := by
  -- Multiply the local coefficient of `hyperellipticOddDxOverY` by `x^k`.
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
theorem hyperellipticOddBasisDifferential_linearIndependent
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    LinearIndependent ℂ
      (fun k : Fin ((H.f.natDegree - 1) / 2) =>
        hyperellipticOddBasisDifferential H h k.val k.isLt) := by
  sorry

/-! ## Headline test — genus theorem for odd hyperelliptic

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

/-- **Lower bound for the genus.** The linear independence of the
canonical basis `{x^k dx/y : k < g}` immediately gives `g ≤ genus` via
`LinearIndependent.fintype_card_le_finrank`. Mirrors
`hyperellipticEvenGenus_lower_bound`. The `FiniteDimensional` instance
comes from `Jacobians.Bridge.KirovHolomorphic` (without it `Module.finrank`
would silently collapse to 0). Proved modulo the still-`sorry`ed
`hyperellipticOddBasisDifferential_linearIndependent`. -/
theorem hyperellipticOddGenus_lower_bound
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    (H.f.natDegree - 1) / 2 ≤
      Jacobians.RiemannSurface.genus (HyperellipticOdd H h) := by
  have hLI := hyperellipticOddBasisDifferential_linearIndependent H h
  simpa using hLI.fintype_card_le_finrank

/-- **Upper bound for the genus.** The remaining genuine gap on the odd
track: unlike the even case — where the bound is supplied by
`Jacobians.Axioms.HyperellipticLiouville.genus_HyperellipticEven_le`
(PR #96) — there is as yet **no odd analogue** of the Liouville/
Riemann–Roch upper bound. Discharge via Riemann–Roch (`AX_RiemannRoch`)
on the canonical divisor, or by porting the even Liouville hierarchy to
the single-∞ parity. -/
theorem genus_HyperellipticOdd_le
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Jacobians.RiemannSurface.genus (HyperellipticOdd H h) ≤
      (H.f.natDegree - 1) / 2 := by
  sorry

/-- **Genus formula for odd-degree hyperelliptic curves.** Mirrors
`genus_HyperellipticEven_eq` for the odd parity. Tests the formalization
end-to-end: cocycle definition + Kirov-Montel finite-dim bridge +
canonical basis (lower) + the upper-bound gap. -/
theorem genus_HyperellipticOdd_eq
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Jacobians.RiemannSurface.genus (HyperellipticOdd H h) =
      (H.f.natDegree - 1) / 2 :=
  le_antisymm (genus_HyperellipticOdd_le H h) (hyperellipticOddGenus_lower_bound H h)

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
    HyperellipticOdd H h → HyperellipticOdd H h :=
  -- On the affine chart: send `⟨(x, y), hxy⟩` to `⟨(x, -y), neg_pow ▸ hxy⟩`.
  -- At infinity (single point in the odd-degree case): identity.
  fun p =>
    p.elim (OnePoint.infty : HyperellipticOdd H h)
      (fun q => (((HyperellipticAffine.involution q : HyperellipticAffine H) :
        OnePoint (HyperellipticAffine H)) : HyperellipticOdd H h))

/-- The hyperelliptic involution is an order-2 map: `σ ∘ σ = id`. -/
theorem hyperellipticInvolution_involutive
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Function.Involutive (hyperellipticInvolution H h) := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
      simp [hyperellipticInvolution]
  | coe q =>
      simp [hyperellipticInvolution, HyperellipticAffine.involution_involution]

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
axiom `pullbackOneForm` in `Axioms/AbelJacobiMap.lean`), or (b) routing\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\) -- not-an-axiom (doc text, ignore in counts)
through the Kirov-bridge to use `Vendor.Kirov.HolomorphicForms.pullbackForm`.
The signature below uses option (a), so this theorem also exercises the
`pullbackOneForm` axiom — discharging it is the prerequisite. -/
theorem pullback_hyperellipticInvolution_eq_neg
    (H : HyperellipticData) (_h : Odd H.f.natDegree) :
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

end Jacobians.Extensions.HyperellipticOdd
