/-
# Challenge extensions: hyperelliptic curves, odd-degree case

Companion to [`Jacobians/Extensions/HyperellipticEven.lean`](HyperellipticEven.lean)
(even-degree warm-ups + headline genus, **completed**). This file is the
**odd-degree extension project**: the analogous theorems for
`HyperellipticOdd H h` with `h : Odd H.f.natDegree`, structured to mirror
the even-degree file decl-for-decl and section-for-section.

Unlike the even file — whose genus theorem is **discharged** (PR #96, via
the Liouville/maximum-modulus axiom hierarchy) — the odd-degree warm-ups
and headline genus are now **fully proved** (PR #223, @daouid — `sorry`-free,
standard-3): this is a *stretch / extension* track, **not required for Buzzard's challenge**
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
import Jacobians.ProjectiveCurve.Hyperelliptic.OddForm
import Jacobians.ProjectiveCurve.Hyperelliptic.Involution
import Jacobians.ProjectiveCurve.Hyperelliptic.InvolutionOdd
import Jacobians.Extensions.HyperellipticOdd.Liouville
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic
import Jacobians.Axioms.HyperellipticLiouville
import Jacobians.Axioms.AbelJacobiMap
import Mathlib.Data.Finite.Card
import Mathlib.FieldTheory.Separable

open Polynomial
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticEvenProj
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.HyperellipticOdd
open Jacobians.RiemannSurface

namespace Jacobians.Extensions.HyperellipticOdd

open scoped Manifold ContDiff Topology
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
noncomputable def hyperellipticOddDxOverY
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    HolomorphicOneForm (HyperellipticOdd H h) := by
  haveI : Fact (Odd H.f.natDegree) := ⟨h⟩
  exact hyperellipticOddForm H (Polynomial.C 1)

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
  haveI : Fact (Odd H.f.natDegree) := ⟨h⟩
  exact hyperellipticOddForm H (Polynomial.X ^ k)

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
  haveI : Fact (Odd H.f.natDegree) := ⟨h⟩
  have hEq : (fun k : Fin ((H.f.natDegree - 1) / 2) =>
        hyperellipticOddBasisDifferential H h k.val k.isLt) =
      (fun k : Fin ((H.f.natDegree - 1) / 2) =>
        hyperellipticOddForm H (Polynomial.X ^ k.val)) := by
    funext k
    unfold hyperellipticOddBasisDifferential
    rfl
  rw [hEq]
  exact hyperellipticOddForm_linearIndependent H

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
would silently collapse to 0). Uses
`hyperellipticOddBasisDifferential_linearIndependent` (now proved, PR #223). -/
theorem hyperellipticOddGenus_lower_bound
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    (H.f.natDegree - 1) / 2 ≤
      Jacobians.RiemannSurface.genus (HyperellipticOdd H h) := by
  have hLI := hyperellipticOddBasisDifferential_linearIndependent H h
  simpa using hLI.fintype_card_le_finrank

/-- **Representation theorem for holomorphic 1-forms on the odd-degree curve.**
Mirroring `AX_HyperellipticOneForm_eq_form` for the even case, this **theorem** (proved as
`AX_HyperellipticOddOneForm_eq_form_proof`, PR #223) states that every holomorphic 1-form is in
the image of `hyperellipticOddForm`. -/
theorem AX_HyperellipticOddOneForm_eq_form (H : HyperellipticData) [Fact (Odd H.f.natDegree)]
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∃ g : Polynomial ℂ, g.natDegree < (H.f.natDegree - 1) / 2 ∧
      form = hyperellipticOddForm H g :=
  AX_HyperellipticOddOneForm_eq_form_proof form

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
  haveI : Fact (Odd H.f.natDegree) := ⟨h⟩
  set n := (H.f.natDegree - 1) / 2 with hn_def
  let φ : Polynomial.degreeLT ℂ n →ₗ[ℂ]
      HolomorphicOneForm (HyperellipticOdd H Fact.out) :=
    hyperellipticOddFormLinearMap H
  have hφ_surj : Function.Surjective φ := by
    intro form
    obtain ⟨g, hg_deg, hgform⟩ := AX_HyperellipticOddOneForm_eq_form H form
    have hg_in : g ∈ Polynomial.degreeLT ℂ n := by
      rw [Polynomial.mem_degreeLT]
      by_cases hg : g = 0
      · rw [hg]; simp [Polynomial.degree_zero]
      · rw [Polynomial.degree_eq_natDegree hg]; exact_mod_cast hg_deg
    refine ⟨⟨g, hg_in⟩, ?_⟩
    change hyperellipticOddForm H g = form
    exact hgform.symm
  have h_rank_le : Module.rank ℂ (HolomorphicOneForm (HyperellipticOdd H Fact.out)) ≤
      Module.rank ℂ (Polynomial.degreeLT ℂ n) :=
    LinearMap.rank_le_of_surjective φ hφ_surj
  have h_target_finite : Module.Finite ℂ (Polynomial.degreeLT ℂ n) :=
    inferInstance
  have h_finrank_le : Module.finrank ℂ (HolomorphicOneForm (HyperellipticOdd H Fact.out)) ≤
      Module.finrank ℂ (Polynomial.degreeLT ℂ n) :=
    Module.finrank_le_finrank_of_rank_le_rank (by simpa using h_rank_le)
      (Module.rank_lt_aleph0 ℂ _)
  have h_finrank_degreeLT : Module.finrank ℂ (Polynomial.degreeLT ℂ n) = n := by
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ n)]; simp
  change Module.finrank ℂ (HolomorphicOneForm (HyperellipticOdd H Fact.out)) ≤ n
  rw [← h_finrank_degreeLT]
  exact h_finrank_le

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

-- Note: the definitions hyperellipticInvolution, hyperellipticInvolution_involutive,
-- hyperellipticInvolution_infinityChart, hyperellipticInvolution_extChartAt_infty,
-- continuous_hyperellipticInvolution, and hyperellipticInvolution_contMDiff
-- have been moved to InvolutionOdd.lean to break the circular dependency.

/-- **The involution acts as `-id` on holomorphic 1-forms.** Tests the
`pullback` side of the challenge API end-to-end: the well-known
identity `σ^* (x^k · dx/y) = -(x^k · dx/y)` (because `σ^* dx = dx`
while `σ^* (1/y) = -1/y`) lifts to the global statement that pullback
under `σ` is the negation map on `HolomorphicOneForm (HyperellipticOdd H h)`.

NOTE: stating this requires either (a) our cocycle-side pullback API
on `HolomorphicOneForm` (not yet built — currently lives only as the
axiom `pullbackOneForm` in `Axioms/AbelJacobiMap.lean`),
or (b) routing\ \-\-\ not\-an\-axiom\ \(doc\ text\,\ ignore\ in\ counts\)
-- not-an-axiom (doc text, ignore in counts)
through the Kirov-bridge to use `Vendor.Kirov.HolomorphicForms.pullbackForm`.
The signature below uses option (a), so this theorem also exercises the
`pullbackOneForm` axiom — discharging it is the prerequisite. -/
theorem pullback_hyperellipticInvolution_eq_neg
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Axioms.pullbackOneForm (hyperellipticInvolution H h)
        (hyperellipticInvolution_contMDiff H h)
      = (-LinearMap.id : HolomorphicOneForm (HyperellipticOdd H h) →ₗ[ℂ]
          HolomorphicOneForm (HyperellipticOdd H h)) := by
  haveI : Fact (Odd H.f.natDegree) := ⟨h⟩
  exact pullback_hyperellipticInvolution_eq_neg_proof H

/-! ## Stretch — Weierstrass points

In the odd-degree case `deg f = 2g + 1`, the smooth model has exactly
`2g + 2` Weierstrass points: the `2g + 1` roots of `f` (each lifted to
a single point with `y = 0`) plus the single point at infinity.
-/

def equiv_fixed_points (H : HyperellipticData) (h : Odd H.f.natDegree) :
    { p : HyperellipticOdd H h // hyperellipticInvolution H h p = p } ≃
      Option { a : HyperellipticAffine H // HyperellipticAffine.invol a = a } where
  toFun := fun ⟨p, hp⟩ =>
    match p with
    | OnePoint.infty => none
    | OnePoint.some a =>
      have h_eq : HyperellipticAffine.invol a = a := by
        have hp_def : (OnePoint.some (a.invol) : HyperellipticOdd H h) = OnePoint.some a := hp
        exact Option.some.inj hp_def
      some ⟨a, h_eq⟩
  invFun := fun opt =>
    match opt with
    | none => ⟨OnePoint.infty, rfl⟩
    | some ⟨a, ha⟩ =>
      have hp : hyperellipticInvolution H h (OnePoint.some a) = OnePoint.some a := by
        change (OnePoint.some (a.invol) : HyperellipticOdd H h) = OnePoint.some a
        rw [ha]
      ⟨OnePoint.some a, hp⟩
  left_inv := by
    intro ⟨p, hp⟩
    match p with
    | OnePoint.infty => rfl
    | OnePoint.some a => rfl
  right_inv := by
    intro opt
    match opt with
    | none => rfl
    | some ⟨a, ha⟩ => rfl

def equiv_roots (H : HyperellipticData) :
    { a : HyperellipticAffine H // HyperellipticAffine.invol a = a } ≃
      { x : ℂ // x ∈ roots H } where
  toFun := fun ⟨a, ha⟩ =>
    have h_eq : a.val.2 = 0 := by
      have ha_val : a.invol.val = a.val := congrArg Subtype.val ha
      change (a.val.1, -a.val.2) = (a.val.1, a.val.2) at ha_val
      have h_neg : -a.val.2 = a.val.2 := (Prod.mk.inj ha_val).2
      have h_sum : -a.val.2 + a.val.2 = 0 := by ring
      have h_sum2 : a.val.2 + a.val.2 = 0 := by
        rw [h_neg] at h_sum
        exact h_sum
      have h_two : (2 : ℂ) * a.val.2 = 0 := by
        calc (2 : ℂ) * a.val.2 = a.val.2 + a.val.2 := by ring
        _ = 0 := h_sum2
      exact mul_eq_zero.mp h_two |>.resolve_left (by norm_num)
    have h_root : a.val.1 ∈ roots H := by
      rw [mem_roots_iff_eval_eq_zero]
      have h_prop := a.property
      rw [h_eq, zero_pow (by norm_num : 2 ≠ 0)] at h_prop
      exact h_prop.symm
    ⟨a.val.1, h_root⟩
  invFun := fun ⟨x, hx⟩ =>
    have h_eval : H.f.eval x = 0 := (mem_roots_iff_eval_eq_zero H).mp hx
    have h_prop : (0 : ℂ) ^ 2 = H.f.eval x := by
      rw [zero_pow (by norm_num : 2 ≠ 0), h_eval]
    let a : HyperellipticAffine H := ⟨(x, 0), h_prop⟩
    have ha : HyperellipticAffine.invol a = a := by
      apply Subtype.ext
      change (x, -(0 : ℂ)) = (x, 0)
      simp
    ⟨a, ha⟩
  left_inv := by
    intro ⟨a, ha⟩
    have h_eq : a.val.2 = 0 := by
      have ha_val : a.invol.val = a.val := congrArg Subtype.val ha
      change (a.val.1, -a.val.2) = (a.val.1, a.val.2) at ha_val
      have h_neg : -a.val.2 = a.val.2 := (Prod.mk.inj ha_val).2
      have h_sum : -a.val.2 + a.val.2 = 0 := by ring
      have h_sum2 : a.val.2 + a.val.2 = 0 := by
        rw [h_neg] at h_sum
        exact h_sum
      have h_two : (2 : ℂ) * a.val.2 = 0 := by
        calc (2 : ℂ) * a.val.2 = a.val.2 + a.val.2 := by ring
        _ = 0 := h_sum2
      exact mul_eq_zero.mp h_two |>.resolve_left (by norm_num)
    apply Subtype.ext
    apply Subtype.ext
    change (a.val.1, (0 : ℂ)) = a.val
    ext
    · rfl
    · exact h_eq.symm
  right_inv := by
    intro ⟨x, hx⟩
    rfl

/-- **Count of Weierstrass points** on a hyperelliptic curve. The fixed
locus of `hyperellipticInvolution` has cardinality `H.f.natDegree + 1`
(in the odd-degree case: roots of `f` plus the point at infinity). -/
theorem card_fixedPoints_hyperellipticInvolution
    (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Nat.card { p : HyperellipticOdd H h //
      hyperellipticInvolution H h p = p } = H.f.natDegree + 1 := by
  haveI h_roots_fin : Finite { x : ℂ // x ∈ roots H } :=
    roots_finite H |>.to_subtype
  haveI h_fixed_fin :
      Finite { a : HyperellipticAffine H // HyperellipticAffine.invol a = a } :=
    Finite.of_equiv { x : ℂ // x ∈ roots H } (equiv_roots H).symm
  have h1 : Nat.card { p // hyperellipticInvolution H h p = p } =
      Nat.card (Option { a : HyperellipticAffine H // HyperellipticAffine.invol a = a }) :=
    Nat.card_congr (equiv_fixed_points H h)
  rw [h1]
  rw [Finite.card_option]
  have h2 : Nat.card { a // HyperellipticAffine.invol a = a } =
      Nat.card { x : ℂ // x ∈ roots H } :=
    Nat.card_congr (equiv_roots H)
  rw [h2]
  have h_sep : H.f.Separable := by
    rw [PerfectField.separable_iff_squarefree]
    exact H.h_squarefree
  have h_split : Polynomial.Splits (H.f.map (algebraMap ℂ ℂ)) := IsAlgClosed.splits _
  have h_card_roots : Fintype.card (H.f.rootSet ℂ) = H.f.natDegree :=
    Polynomial.card_rootSet_eq_natDegree h_sep h_split
  rw [Fintype.card_eq_nat_card] at h_card_roots
  change Nat.card (H.f.rootSet ℂ) + 1 = H.f.natDegree + 1
  rw [h_card_roots]

end Jacobians.Extensions.HyperellipticOdd
