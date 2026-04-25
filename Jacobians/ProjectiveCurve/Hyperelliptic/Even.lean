/-
# Even-degree hyperelliptic curves: two-point compactification

For even `deg f = 2g + 2`, the classical projective hyperelliptic curve
`y² = f(x)` has two distinct points at infinity. This file provides a
real `def HyperellipticEvenProj H h` as the pushout of two affine
charts:

- **Affine chart**: `HyperellipticAffine H = {(x, y) | y² = f(x)}`.
- **Infinity chart**: `HyperellipticAffineInfinity H = {(t, u) | u² = f_rev(t)}`,
  parametrized by `t = 1/x`, `u = y/x^{g+1}`.

The overlap is `x ≠ 0 ↔ t ≠ 0`, with gluing
`(x, y) ↔ (1/x, y/x^{g+1})`.

At `t = 0` (the infinity point), `u² = f_rev(0) = leadCoef f ≠ 0`,
giving two distinct solutions `u = ±√(leadCoef f)`. These are the two
points at infinity of the classical projective model.

## Status

Building toward a real `def HyperellipticEvenProj` to retire the
axiom-stub `HyperellipticEven` in `Hyperelliptic.lean`. **Partial
progress in this file**: affine-infinity chart defined with topology
instances; gluing/quotient construction + instance proofs remain.

## Reference

* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. VII §1.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Basic

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open scoped BigOperators

/-- **The second affine chart at infinity** for an even-degree
hyperelliptic curve. Parametrized by `(t, u)` with `t = 1/x`,
`u = y/x^{g+1}`, satisfying `u² = f_reversed(t)` where
`f_reversed(t) = t^d · f(1/t)`.

For even `deg f = 2g + 2`, `f_reversed(0) = leadCoef f ≠ 0`, so at
`t = 0` there are two distinct solutions `u = ±√(leadCoef f)` — these
are the two points at infinity of the projective model. -/
def HyperellipticAffineInfinity (H : HyperellipticData) : Type :=
  { p : ℂ × ℂ // p.2 ^ 2 = (Polynomial.reverse H.f).eval p.1 }

namespace HyperellipticAffineInfinity

variable {H : HyperellipticData}

instance : TopologicalSpace (HyperellipticAffineInfinity H) :=
  inferInstanceAs (TopologicalSpace
    { p : ℂ × ℂ // p.2 ^ 2 = (Polynomial.reverse H.f).eval p.1 })

instance : T2Space (HyperellipticAffineInfinity H) :=
  inferInstanceAs (T2Space
    { p : ℂ × ℂ // p.2 ^ 2 = (Polynomial.reverse H.f).eval p.1 })

/-- Closed subset of `ℂ × ℂ` as the zero-set of `(t, u) ↦ u² - f_rev(t)`. -/
theorem isClosed_carrier (H : HyperellipticData) :
    IsClosed { p : ℂ × ℂ | p.2 ^ 2 = (Polynomial.reverse H.f).eval p.1 } := by
  have hcont : Continuous (fun p : ℂ × ℂ => p.2 ^ 2 - (Polynomial.reverse H.f).eval p.1) := by
    have h1 : Continuous (fun p : ℂ × ℂ => p.2 ^ 2) :=
      (continuous_snd).pow 2
    have h2 : Continuous (fun p : ℂ × ℂ => (Polynomial.reverse H.f).eval p.1) :=
      (Polynomial.continuous _).comp continuous_fst
    exact h1.sub h2
  have : { p : ℂ × ℂ | p.2 ^ 2 = (Polynomial.reverse H.f).eval p.1 } =
      { p : ℂ × ℂ | p.2 ^ 2 - (Polynomial.reverse H.f).eval p.1 = 0 } := by
    ext p
    simp [sub_eq_zero]
  rw [this]
  exact isClosed_eq hcont continuous_const

instance : LocallyCompactSpace (HyperellipticAffineInfinity H) := by
  have hclosed := isClosed_carrier H
  exact hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- For even `deg f`, at `t = 0` the equation `u² = f_reversed(0) =
leadCoef f` has two distinct solutions `u = ±√(leadCoef f)`, since
`leadCoef f ≠ 0` (as `f ≠ 0` with `deg f ≥ 3`). So the infinity chart
is nonempty. (The construction here works for any `f ≠ 0`, not just
even-degree.) -/
noncomputable instance : Nonempty (HyperellipticAffineInfinity H) := by
  obtain ⟨c, hc⟩ : ∃ r, H.f.leadingCoeff = r * r :=
    (Complex.isSquare H.f.leadingCoeff).exists_mul_self
  refine ⟨⟨(0, c), ?_⟩⟩
  have hev : (Polynomial.reverse H.f).eval 0 = H.f.leadingCoeff := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero_reverse]
  rw [hev, sq, hc]

/-- **Axiom (NOT VERIFIED).** The affine-infinity chart is connected.
Classical: same reasoning as `AX_HyperellipticAffine_connected` — the
curve `u² = f_rev(t)` is an irreducible algebraic variety for `f`
squarefree, hence connected in the classical topology. -/
axiom AX_HyperellipticAffineInfinity_connected (H : HyperellipticData) :
    ConnectedSpace (HyperellipticAffineInfinity H)

attribute [instance] AX_HyperellipticAffineInfinity_connected

/-- **Axiom (NOT VERIFIED).** The affine-infinity chart is noncompact
(mirror of `AX_HyperellipticAffine_noncompact`). -/
axiom AX_HyperellipticAffineInfinity_noncompact (H : HyperellipticData) :
    NoncompactSpace (HyperellipticAffineInfinity H)

attribute [instance] AX_HyperellipticAffineInfinity_noncompact

end HyperellipticAffineInfinity

/-! ## Pushout construction (skeleton)

The projective even-degree hyperelliptic curve as the pushout of the
two affine charts along their overlap `x ≠ 0 ↔ t ≠ 0` with gluing
`(x, y) ↔ (1/x, y/x^{g+1})`.

**Skeleton in place (this section):** sum pre-type, raw gluing
relation, setoid via `Relation.EqvGen`, quotient type `HyperellipticEvenProj`,
quotient `TopologicalSpace`, `Nonempty`. All real defs, all
compile-clean.

**Remaining (Codex handoff):**
- `T2Space`: requires the equivalence relation to be a closed subset
  of the product (standard obstacle in pushout constructions).
- `CompactSpace`: finite-chart-cover argument — the quotient is the
  union of the image of `{|x| ≤ R} ∩ affine` (compact) and the image
  of `{|t| ≤ 1/R} ∩ infinity` (compact) for some `R > 0`.

**Landed in this file:**
- `HyperellipticAffineInfinity.mem_of_affine`: the overlap map
  `(x, y) ↦ (1/x, y/x^{g+1})` lands in the infinity chart for even
  degree.
- `ConnectedSpace (HyperellipticEvenProj H)`: quotient connectedness
  via the two connected chart images with nonempty overlap.

Once those land, flip `HyperellipticEven` in `Hyperelliptic.lean` from
axiom stub to a real `def := HyperellipticEvenProj` and retire the 5
typeclass-instance axioms on `HyperellipticEven`.
-/

/-- **Pre-pushout**: disjoint sum of the two affine charts. Topology
inherited as `Sum` topology. -/
def HyperellipticEvenPre (H : HyperellipticData) : Type :=
  HyperellipticAffine H ⊕ HyperellipticAffineInfinity H

instance (H : HyperellipticData) : TopologicalSpace (HyperellipticEvenPre H) :=
  inferInstanceAs (TopologicalSpace
    (HyperellipticAffine H ⊕ HyperellipticAffineInfinity H))

instance (H : HyperellipticData) : T2Space (HyperellipticEvenPre H) :=
  inferInstanceAs (T2Space
    (HyperellipticAffine H ⊕ HyperellipticAffineInfinity H))

/-- **Raw gluing relation**: a point `(x, y)` in the affine chart is
identified with the point `(1/x, y/x^{g+1})` in the infinity chart,
whenever `x ≠ 0`. Here `g+1 = H.f.natDegree / 2` (well-defined and
matches the classical exponent for even `deg f = 2g+2`; for odd
`deg f` this relation still typechecks but is not the classical
construction, which should use `HyperellipticOdd` instead).

This relation is not yet an equivalence relation; take its `Relation.EqvGen`
closure via `hyperellipticEvenSetoid`. -/
def HyperellipticEvenGlue (H : HyperellipticData) :
    HyperellipticEvenPre H → HyperellipticEvenPre H → Prop
  | Sum.inl a, Sum.inr b =>
      a.val.1 ≠ 0 ∧ b.val.1 = (a.val.1)⁻¹ ∧
      b.val.2 = a.val.2 * (a.val.1)⁻¹ ^ (H.f.natDegree / 2)
  | _, _ => False

/-- **Gluing setoid** via the equivalence closure of
`HyperellipticEvenGlue`. -/
def hyperellipticEvenSetoid (H : HyperellipticData) :
    Setoid (HyperellipticEvenPre H) where
  r := Relation.EqvGen (HyperellipticEvenGlue H)
  iseqv := Relation.EqvGen.is_equivalence _

/-- **Projective even-degree hyperelliptic curve** via two-chart
pushout: the quotient of `HyperellipticAffine H ⊕ HyperellipticAffineInfinity H`
by the gluing `(x, y) ↔ (1/x, y/x^{g+1})` on the overlap `x ≠ 0`. -/
def HyperellipticEvenProj (H : HyperellipticData) : Type :=
  Quotient (hyperellipticEvenSetoid H)

/-- **Quotient topology** on `HyperellipticEvenProj` — inherited from
the sum topology on `HyperellipticEvenPre` via the `Quotient`
construction. -/
instance (H : HyperellipticData) : TopologicalSpace (HyperellipticEvenProj H) :=
  inferInstanceAs (TopologicalSpace (Quotient (hyperellipticEvenSetoid H)))

/-- **Nonempty** — trivially, via the affine chart's nonempty
instance. -/
instance (H : HyperellipticData) : Nonempty (HyperellipticEvenProj H) := by
  inhabit HyperellipticAffine H
  exact ⟨Quotient.mk _ (Sum.inl default)⟩

lemma HyperellipticAffineInfinity.mem_of_affine (H : HyperellipticData)
    (hd : ¬ Odd H.f.natDegree) (x y : ℂ) (hxy : y ^ 2 = H.f.eval x) (hx : x ≠ 0) :
    (y * x⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = (Polynomial.reverse H.f).eval x⁻¹ := by
  have hd_even : Even H.f.natDegree := Nat.not_odd_iff_even.mp hd
  obtain ⟨m, hm⟩ := hd_even
  have hdiv : H.f.natDegree / 2 = m := by
    omega
  have hm2 : m * 2 = m + m := by
    omega
  have hxpow : x ^ H.f.natDegree ≠ 0 := pow_ne_zero _ hx
  have hrev : (Polynomial.reverse H.f).eval x⁻¹ = H.f.eval x * x⁻¹ ^ H.f.natDegree := by
    letI : Invertible x := invertibleOfNonzero hx
    apply mul_right_cancel₀ hxpow
    have h1 : (Polynomial.reverse H.f).eval x⁻¹ * x ^ H.f.natDegree = H.f.eval x := by
      simpa [RingHom.id_apply] using
        (Polynomial.eval₂_reverse_mul_pow (i := RingHom.id ℂ) (x := x) H.f)
    have h2 : (H.f.eval x * x⁻¹ ^ H.f.natDegree) * x ^ H.f.natDegree = H.f.eval x := by
      calc
        (Polynomial.eval x H.f * x⁻¹ ^ H.f.natDegree) * x ^ H.f.natDegree
            = Polynomial.eval x H.f * (x⁻¹ ^ H.f.natDegree * x ^ H.f.natDegree) := by
                ring_nf
        _ = Polynomial.eval x H.f * ((x⁻¹ * x) ^ H.f.natDegree) := by
              rw [← mul_pow]
        _ = Polynomial.eval x H.f := by
              simp [hx]
    exact h1.trans h2.symm
  calc
    (y * x⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = y ^ 2 * x⁻¹ ^ H.f.natDegree := by
      rw [hdiv, mul_pow, sq]
      congr 1
      rw [← pow_mul]
      simp [hm, hm2]
    _ = H.f.eval x * x⁻¹ ^ H.f.natDegree := by
      rw [hxy]
    _ = (Polynomial.reverse H.f).eval x⁻¹ := by
      simpa using hrev.symm

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    ConnectedSpace (HyperellipticEvenProj H) := by
  let qA : HyperellipticAffine H → HyperellipticEvenProj H :=
    fun a => Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let qB : HyperellipticAffineInfinity H → HyperellipticEvenProj H :=
    fun b => Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)
  have hA : IsConnected (Set.range qA) := by
    refine isConnected_range ?_
    simpa [qA] using (continuous_quotient_mk'.comp continuous_inl)
  have hB : IsConnected (Set.range qB) := by
    refine isConnected_range ?_
    simpa [qB] using (continuous_quotient_mk'.comp continuous_inr)
  have hpoly_ne : Polynomial.X * H.f ≠ 0 := by
    refine mul_ne_zero Polynomial.X_ne_zero ?_
    intro hf
    have hdeg := H.h_degree
    rw [hf, Polynomial.natDegree_zero] at hdeg
    omega
  have hcard : ((Polynomial.X * H.f).natDegree : Cardinal) < Cardinal.mk ℂ := by
    exact
      (Cardinal.natCast_lt_aleph0 :
        ((Polynomial.X * H.f).natDegree : Cardinal) < Cardinal.aleph0).trans_le
        (Cardinal.aleph0_le_mk ℂ)
  obtain ⟨x, hx_eval⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card
    (Polynomial.X * H.f) hpoly_ne hcard
  have hx : x ≠ 0 := by
    intro hx0
    apply hx_eval
    simp [Polynomial.eval_mul, hx0]
  obtain ⟨y, hy⟩ : ∃ y : ℂ, H.f.eval x = y * y :=
    (Complex.isSquare (H.f.eval x)).exists_mul_self
  have hxy : y ^ 2 = H.f.eval x := by
    simpa [sq, mul_comm] using hy.symm
  let a : HyperellipticAffine H := ⟨(x, y), hxy⟩
  let b : HyperellipticAffineInfinity H :=
    ⟨(x⁻¹, y * x⁻¹ ^ (H.f.natDegree / 2)),
      HyperellipticAffineInfinity.mem_of_affine H h x y hxy hx⟩
  have hinter : (Set.range qA ∩ Set.range qB).Nonempty := by
    refine ⟨Quotient.mk _ (Sum.inl a), ?_⟩
    constructor
    · exact ⟨a, rfl⟩
    · refine ⟨b, ?_⟩
      simpa [qB] using
        (Quotient.sound
          (Relation.EqvGen.rel _ _
            (by
              dsimp [HyperellipticEvenGlue, a, b]
              exact ⟨hx, rfl, rfl⟩)) :
          Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) =
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)).symm
  have hUnion : Set.range qA ∪ Set.range qB = Set.univ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨w, rfl⟩ := Quotient.mk_surjective
        (s := hyperellipticEvenSetoid H) z
      cases w with
      | inl a => exact Or.inl ⟨a, rfl⟩
      | inr b => exact Or.inr ⟨b, rfl⟩
  rw [connectedSpace_iff_univ]
  have hConn : IsConnected (Set.range qA ∪ Set.range qB) :=
    IsConnected.union hinter hA hB
  simpa [hUnion] using hConn

lemma HyperellipticAffine.mem_of_infinity (H : HyperellipticData)
    (hd : ¬ Odd H.f.natDegree) (t u : ℂ)
    (htu : u ^ 2 = (Polynomial.reverse H.f).eval t) (ht : t ≠ 0) :
    (u * t⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = H.f.eval t⁻¹ := by
  have hd_even : Even H.f.natDegree := Nat.not_odd_iff_even.mp hd
  obtain ⟨m, hm⟩ := hd_even
  have hdiv : H.f.natDegree / 2 = m := by
    omega
  have hm2 : m * 2 = m + m := by
    omega
  have hrev : H.f.eval t⁻¹ = (Polynomial.reverse H.f).eval t * t⁻¹ ^ H.f.natDegree := by
    letI : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht)
    simpa [RingHom.id_apply] using
      (Polynomial.eval₂_reverse_mul_pow (i := RingHom.id ℂ) (x := t⁻¹) H.f).symm
  calc
    (u * t⁻¹ ^ (H.f.natDegree / 2)) ^ 2 = u ^ 2 * t⁻¹ ^ H.f.natDegree := by
      rw [hdiv, mul_pow, sq]
      congr 1
      rw [← pow_mul]
      simp [hm, hm2]
    _ = (Polynomial.reverse H.f).eval t * t⁻¹ ^ H.f.natDegree := by
      rw [htu]
    _ = H.f.eval t⁻¹ := by
      simpa using hrev.symm

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    CompactSpace (HyperellipticEvenProj H) := by
  let R₁ : ℝ := max 1 (Finset.sum (Finset.range (H.f.natDegree + 1)) fun i => ‖H.f.coeff i‖)
  let R₂ : ℝ := max 1
    (Finset.sum (Finset.range ((Polynomial.reverse H.f).natDegree + 1))
      fun i => ‖(Polynomial.reverse H.f).coeff i‖)
  let K₁ : Set (HyperellipticAffine H) := { p | ‖p.val.1‖ ≤ 1 }
  let K₂ : Set (HyperellipticAffineInfinity H) := { p | ‖p.val.1‖ ≤ 1 }
  let I₁ : Set (HyperellipticEvenProj H) :=
    (fun a : HyperellipticAffine H =>
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) '' K₁
  let I₂ : Set (HyperellipticEvenProj H) :=
    (fun b : HyperellipticAffineInfinity H =>
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)) '' K₂
  have hbound_eval :
      ∀ x : ℂ, ‖x‖ ≤ 1 →
        ‖H.f.eval x‖ ≤
          Finset.sum (Finset.range (H.f.natDegree + 1)) fun i => ‖H.f.coeff i‖ := by
    intro x hx
    rw [Polynomial.eval_eq_sum_range]
    have hsum :
        ‖∑ i ∈ Finset.range (H.f.natDegree + 1), H.f.coeff i * x ^ i‖ ≤
          ∑ i ∈ Finset.range (H.f.natDegree + 1), ‖H.f.coeff i * x ^ i‖ :=
      norm_sum_le (s := Finset.range (H.f.natDegree + 1)) (f := fun i => H.f.coeff i * x ^ i)
    refine hsum.trans ?_
    refine Finset.sum_le_sum fun i hi => ?_
    calc
      ‖H.f.coeff i * x ^ i‖ = ‖H.f.coeff i‖ * ‖x‖ ^ i := by
        rw [norm_mul, norm_pow]
      _ ≤ ‖H.f.coeff i‖ * 1 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ (norm_nonneg x) hx : ‖x‖ ^ i ≤ 1) (norm_nonneg _)
      _ = ‖H.f.coeff i‖ := by
        ring
  have hbound_eval_rev :
      ∀ t : ℂ, ‖t‖ ≤ 1 →
        ‖(Polynomial.reverse H.f).eval t‖ ≤
          Finset.sum (Finset.range ((Polynomial.reverse H.f).natDegree + 1))
            fun i => ‖(Polynomial.reverse H.f).coeff i‖ := by
    intro t ht
    rw [Polynomial.eval_eq_sum_range]
    have hsum :
        ‖∑ i ∈ Finset.range ((Polynomial.reverse H.f).natDegree + 1),
            (Polynomial.reverse H.f).coeff i * t ^ i‖ ≤
          ∑ i ∈ Finset.range ((Polynomial.reverse H.f).natDegree + 1),
            ‖(Polynomial.reverse H.f).coeff i * t ^ i‖ :=
      norm_sum_le (s := Finset.range ((Polynomial.reverse H.f).natDegree + 1))
        (f := fun i => (Polynomial.reverse H.f).coeff i * t ^ i)
    refine hsum.trans ?_
    refine Finset.sum_le_sum fun i hi => ?_
    calc
      ‖(Polynomial.reverse H.f).coeff i * t ^ i‖ =
          ‖(Polynomial.reverse H.f).coeff i‖ * ‖t‖ ^ i := by
            rw [norm_mul, norm_pow]
      _ ≤ ‖(Polynomial.reverse H.f).coeff i‖ * 1 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_one₀ (norm_nonneg t) ht : ‖t‖ ^ i ≤ 1) (norm_nonneg _)
      _ = ‖(Polynomial.reverse H.f).coeff i‖ := by
        ring
  have hK₁_closed : IsClosed K₁ := by
    have hcont :
        Continuous fun p : HyperellipticAffine H => ‖p.val.1‖ :=
      continuous_norm.comp (continuous_fst.comp continuous_subtype_val)
    simpa [K₁] using isClosed_le hcont continuous_const
  have hK₂_closed : IsClosed K₂ := by
    have hcont :
        Continuous fun p : HyperellipticAffineInfinity H => ‖p.val.1‖ :=
      continuous_norm.comp (continuous_fst.comp continuous_subtype_val)
    simpa [K₂] using isClosed_le hcont continuous_const
  have hK₁_subset :
      K₁ ⊆ (Subtype.val : HyperellipticAffine H → ℂ × ℂ) ⁻¹' Metric.closedBall 0 R₁ := by
    intro p hp
    have hx : ‖p.val.1‖ ≤ R₁ := le_trans hp (le_max_left _ _)
    have hy_eval :
        ‖H.f.eval p.val.1‖ ≤ R₁ := by
      exact (hbound_eval p.val.1 hp).trans (le_max_right _ _)
    have hy_sq : ‖p.val.2‖ ^ 2 = ‖H.f.eval p.val.1‖ := by
      calc
        ‖p.val.2‖ ^ 2 = ‖p.val.2 ^ 2‖ := by
          rw [norm_pow]
        _ = ‖H.f.eval p.val.1‖ := by
          rw [p.property]
    have hR₁_sq : R₁ ≤ R₁ ^ 2 := by
      nlinarith [le_max_left (1 : ℝ)
        (Finset.sum (Finset.range (H.f.natDegree + 1)) fun i => ‖H.f.coeff i‖)]
    have hy : ‖p.val.2‖ ≤ R₁ := by
      have hy_sq_le : ‖p.val.2‖ ^ 2 ≤ R₁ ^ 2 := by
        nlinarith [hy_sq, hy_eval, hR₁_sq]
      nlinarith [norm_nonneg p.val.2, hy_sq_le]
    simpa [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def] using And.intro hx hy
  have hK₂_subset :
      K₂ ⊆ (Subtype.val : HyperellipticAffineInfinity H → ℂ × ℂ) ⁻¹' Metric.closedBall 0 R₂ := by
    intro p hp
    have ht : ‖p.val.1‖ ≤ R₂ := le_trans hp (le_max_left _ _)
    have hu_eval :
        ‖(Polynomial.reverse H.f).eval p.val.1‖ ≤ R₂ := by
      exact (hbound_eval_rev p.val.1 hp).trans (le_max_right _ _)
    have hu_sq : ‖p.val.2‖ ^ 2 = ‖(Polynomial.reverse H.f).eval p.val.1‖ := by
      calc
        ‖p.val.2‖ ^ 2 = ‖p.val.2 ^ 2‖ := by
          rw [norm_pow]
        _ = ‖(Polynomial.reverse H.f).eval p.val.1‖ := by
          rw [p.property]
    have hR₂_sq : R₂ ≤ R₂ ^ 2 := by
      nlinarith [le_max_left (1 : ℝ)
        (Finset.sum (Finset.range ((Polynomial.reverse H.f).natDegree + 1))
          fun i => ‖(Polynomial.reverse H.f).coeff i‖)]
    have hu : ‖p.val.2‖ ≤ R₂ := by
      have hu_sq_le : ‖p.val.2‖ ^ 2 ≤ R₂ ^ 2 := by
        nlinarith [hu_sq, hu_eval, hR₂_sq]
      nlinarith [norm_nonneg p.val.2, hu_sq_le]
    simpa [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def] using And.intro ht hu
  have hClosedEmb₁ :
      Topology.IsClosedEmbedding (Subtype.val : HyperellipticAffine H → ℂ × ℂ) :=
    (HyperellipticAffine.isClosed_carrier H).isClosedEmbedding_subtypeVal
  have hClosedEmb₂ :
      Topology.IsClosedEmbedding (Subtype.val : HyperellipticAffineInfinity H → ℂ × ℂ) :=
    (HyperellipticAffineInfinity.isClosed_carrier H).isClosedEmbedding_subtypeVal
  have hK₁_comp :
      IsCompact K₁ := by
    refine
      (hClosedEmb₁.isCompact_preimage (isCompact_closedBall (0 : ℂ × ℂ) R₁)).of_isClosed_subset
        hK₁_closed hK₁_subset
  have hK₂_comp :
      IsCompact K₂ := by
    refine
      (hClosedEmb₂.isCompact_preimage (isCompact_closedBall (0 : ℂ × ℂ) R₂)).of_isClosed_subset
        hK₂_closed hK₂_subset
  have hI₁_comp : IsCompact I₁ := by
    simpa [I₁] using
      hK₁_comp.image (continuous_quotient_mk'.comp continuous_inl)
  have hI₂_comp : IsCompact I₂ := by
    simpa [I₂] using
      hK₂_comp.image (continuous_quotient_mk'.comp continuous_inr)
  have hCover : I₁ ∪ I₂ = Set.univ := by
    ext z
    constructor
    · intro _
      simp
    · intro _
      obtain ⟨w, rfl⟩ := Quotient.mk_surjective (s := hyperellipticEvenSetoid H) z
      cases w with
      | inl a =>
          by_cases hx : ‖a.val.1‖ ≤ 1
          · exact Or.inl ⟨a, hx, rfl⟩
          · have hx0 : a.val.1 ≠ 0 := by
              intro hx'
              apply hx
              simpa [hx'] using (norm_nonneg (0 : ℂ))
            have hx1 : 1 ≤ ‖a.val.1‖ := le_of_lt (lt_of_not_ge hx)
            let b : HyperellipticAffineInfinity H :=
              ⟨(a.val.1⁻¹, a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2)),
                HyperellipticAffineInfinity.mem_of_affine H h a.val.1 a.val.2 a.property hx0⟩
            have hb : b ∈ K₂ := by
              rw [show b = ⟨(a.val.1⁻¹, a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2)),
                  HyperellipticAffineInfinity.mem_of_affine H h a.val.1 a.val.2 a.property hx0⟩ by
                    rfl]
              change ‖a.val.1⁻¹‖ ≤ 1
              rw [norm_inv]
              exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hx1)).2 hx1
            exact Or.inr <| by
              refine ⟨b, hb, ?_⟩
              symm
              exact Quotient.sound <|
                Relation.EqvGen.rel _ _ <| by
                  dsimp [HyperellipticEvenGlue, b]
                  exact ⟨hx0, rfl, rfl⟩
      | inr b =>
          by_cases ht : ‖b.val.1‖ ≤ 1
          · exact Or.inr ⟨b, ht, rfl⟩
          · have ht0 : b.val.1 ≠ 0 := by
              intro ht'
              apply ht
              simpa [ht'] using (norm_nonneg (0 : ℂ))
            have ht1 : 1 ≤ ‖b.val.1‖ := le_of_lt (lt_of_not_ge ht)
            let a : HyperellipticAffine H :=
              ⟨(b.val.1⁻¹, b.val.2 * b.val.1⁻¹ ^ (H.f.natDegree / 2)),
                HyperellipticAffine.mem_of_infinity H h b.val.1 b.val.2 b.property ht0⟩
            have ha : a ∈ K₁ := by
              rw [show a = ⟨(b.val.1⁻¹, b.val.2 * b.val.1⁻¹ ^ (H.f.natDegree / 2)),
                  HyperellipticAffine.mem_of_infinity H h b.val.1 b.val.2 b.property ht0⟩ by
                    rfl]
              change ‖b.val.1⁻¹‖ ≤ 1
              rw [norm_inv]
              exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one ht1)).2 ht1
            exact Or.inl <| by
              refine ⟨a, ha, ?_⟩
              have hEq :
                  Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a) =
                    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b) := by
                exact Quotient.sound <|
                  Relation.EqvGen.rel _ _ <| by
                    dsimp [HyperellipticEvenGlue, a]
                    refine ⟨inv_ne_zero ht0, ?_, ?_⟩
                    · simp
                    · rw [inv_inv]
                      symm
                      calc
                        (b.val.2 * b.val.1⁻¹ ^ (H.f.natDegree / 2)) * b.val.1 ^ (H.f.natDegree / 2)
                            = b.val.2 * (b.val.1⁻¹ ^ (H.f.natDegree / 2) *
                                b.val.1 ^ (H.f.natDegree / 2)) := by
                                ring_nf
                        _ = b.val.2 * ((b.val.1⁻¹ * b.val.1) ^ (H.f.natDegree / 2)) := by
                              rw [← mul_pow]
                        _ = b.val.2 := by
                              simp [ht0]
              exact hEq
  exact ⟨by simpa [hCover] using hI₁_comp.union hI₂_comp⟩

lemma hyperellipticEvenGlue_target_unique (H : HyperellipticData)
    {p q r : HyperellipticEvenPre H}
    (hpq : HyperellipticEvenGlue H p q) (hpr : HyperellipticEvenGlue H p r) :
    q = r := by
  cases p <;> cases q <;> cases r <;> simp [HyperellipticEvenGlue] at hpq hpr ⊢
  rcases hpq with ⟨_, hq1, hq2⟩
  rcases hpr with ⟨_, hr1, hr2⟩
  congr
  apply Subtype.ext
  exact Prod.ext (hq1.trans hr1.symm) (hq2.trans hr2.symm)

lemma hyperellipticEvenGlue_source_unique (H : HyperellipticData)
    {p q r : HyperellipticEvenPre H}
    (hpq : HyperellipticEvenGlue H p q) (hrq : HyperellipticEvenGlue H r q) :
    p = r := by
  cases p <;> cases q <;> cases r <;> simp [HyperellipticEvenGlue] at hpq hrq ⊢
  rename_i a b c
  rcases hpq with ⟨hp0, hp1, hp2⟩
  rcases hrq with ⟨_, hr1, hr2⟩
  have h1 : a.val.1 = c.val.1 := inv_injective (hp1.symm.trans hr1)
  have h2 : a.val.2 = c.val.2 := by
    have hp2' :
        b.val.2 = a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2) := by
      simpa [inv_pow] using hp2
    have hr2' :
        b.val.2 = c.val.2 * c.val.1⁻¹ ^ (H.f.natDegree / 2) := by
      simpa [inv_pow] using hr2
    have hr2'' :
        b.val.2 = c.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2) := by
      simpa [h1] using hr2'
    have hmul :
        a.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2) =
          c.val.2 * a.val.1⁻¹ ^ (H.f.natDegree / 2) := by
      rw [← hp2', ← hr2'']
    exact mul_right_cancel₀ (pow_ne_zero _ (inv_ne_zero hp0)) hmul
  congr
  apply Subtype.ext
  exact Prod.ext h1 h2

lemma hyperellipticEvenSetoid_rel_iff (H : HyperellipticData)
    (p q : HyperellipticEvenPre H) :
    (hyperellipticEvenSetoid H).r p q ↔
      p = q ∨ HyperellipticEvenGlue H p q ∨ HyperellipticEvenGlue H q p := by
  change Relation.EqvGen (HyperellipticEvenGlue H) p q ↔
    p = q ∨ HyperellipticEvenGlue H p q ∨ HyperellipticEvenGlue H q p
  let R : HyperellipticEvenPre H → HyperellipticEvenPre H → Prop :=
    fun a b => a = b ∨ HyperellipticEvenGlue H a b ∨ HyperellipticEvenGlue H b a
  have hR : Equivalence R := by
    constructor
    · intro a
      exact Or.inl rfl
    · intro a b hab
      rcases hab with rfl | hab | hab
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hab)
      · exact Or.inr (Or.inl hab)
    · intro a b c hab hbc
      rcases hab with rfl | hab | hab <;> rcases hbc with rfl | hbc | hbc
      · exact Or.inl rfl
      · exact Or.inr (Or.inl hbc)
      · exact Or.inr (Or.inr hbc)
      · exact Or.inr (Or.inl hab)
      · cases a <;> cases b <;> cases c <;> simp [HyperellipticEvenGlue] at hab hbc
      · exact Or.inl (hyperellipticEvenGlue_source_unique H hab hbc)
      · exact Or.inr (Or.inr hab)
      · exact Or.inl (hyperellipticEvenGlue_target_unique H hab hbc)
      · cases a <;> cases b <;> cases c <;> simp [HyperellipticEvenGlue] at hab hbc
  constructor
  · intro hpq
    induction hpq with
    | rel _ _ hpq => exact Or.inr (Or.inl hpq)
    | refl _ => exact Or.inl rfl
    | symm _ _ _ ih =>
        rcases ih with rfl | ih | ih
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ih)
        · exact Or.inr (Or.inl ih)
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact hR.3 ih₁ ih₂
  · rintro (rfl | hpq | hpq)
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ hpq
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hpq)

def affineOverlap (H : HyperellipticData) : Type :=
  { a : HyperellipticAffine H // a.val.1 ≠ 0 }

def infinityOverlap (H : HyperellipticData) : Type :=
  { b : HyperellipticAffineInfinity H // b.val.1 ≠ 0 }

instance (H : HyperellipticData) : TopologicalSpace (affineOverlap H) :=
  inferInstanceAs (TopologicalSpace { a : HyperellipticAffine H // a.val.1 ≠ 0 })

instance (H : HyperellipticData) : TopologicalSpace (infinityOverlap H) :=
  inferInstanceAs (TopologicalSpace { b : HyperellipticAffineInfinity H // b.val.1 ≠ 0 })

lemma isOpen_affineOverlap (H : HyperellipticData) :
    IsOpen { a : HyperellipticAffine H | a.val.1 ≠ 0 } := by
  simpa [Set.compl_setOf, eq_comm] using
    (isClosed_eq
      (continuous_fst.comp continuous_subtype_val)
      (continuous_const : Continuous fun _ : HyperellipticAffine H => (0 : ℂ))).isOpen_compl

lemma isOpen_infinityOverlap (H : HyperellipticData) :
    IsOpen { b : HyperellipticAffineInfinity H | b.val.1 ≠ 0 } := by
  simpa [Set.compl_setOf, eq_comm] using
    (isClosed_eq
      (continuous_fst.comp continuous_subtype_val)
      (continuous_const : Continuous fun _ : HyperellipticAffineInfinity H => (0 : ℂ))).isOpen_compl

noncomputable def affineToInfinityOverlap (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    affineOverlap H → infinityOverlap H := fun a =>
  ⟨⟨(a.1.val.1⁻¹, a.1.val.2 * a.1.val.1⁻¹ ^ (H.f.natDegree / 2)),
      HyperellipticAffineInfinity.mem_of_affine H h a.1.val.1 a.1.val.2 a.1.property a.2⟩,
    inv_ne_zero a.2⟩

noncomputable def infinityToAffineOverlap (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    infinityOverlap H → affineOverlap H := fun b =>
  ⟨⟨(b.1.val.1⁻¹, b.1.val.2 * b.1.val.1⁻¹ ^ (H.f.natDegree / 2)),
      HyperellipticAffine.mem_of_infinity H h b.1.val.1 b.1.val.2 b.1.property b.2⟩,
    inv_ne_zero b.2⟩

noncomputable def affineInfinityOverlapHomeomorph
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    affineOverlap H ≃ₜ infinityOverlap H where
  toFun := affineToInfinityOverlap H h
  invFun := infinityToAffineOverlap H h
  left_inv := by
    intro a
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · simp [affineToInfinityOverlap, infinityToAffineOverlap, a.2]
    · calc
        a.1.val.2 * a.1.val.1⁻¹ ^ (H.f.natDegree / 2) * (a.1.val.1⁻¹)⁻¹ ^ (H.f.natDegree / 2)
            = a.1.val.2 *
                (a.1.val.1⁻¹ ^ (H.f.natDegree / 2) * a.1.val.1 ^ (H.f.natDegree / 2)) := by
                simp [a.2]
        _ = a.1.val.2 * ((a.1.val.1⁻¹ * a.1.val.1) ^ (H.f.natDegree / 2)) := by
              rw [← mul_pow]
        _ = a.1.val.2 := by
              simp [a.2]
  right_inv := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · simp [affineToInfinityOverlap, infinityToAffineOverlap, b.2]
    · calc
        b.1.val.2 * b.1.val.1⁻¹ ^ (H.f.natDegree / 2) * (b.1.val.1⁻¹)⁻¹ ^ (H.f.natDegree / 2)
            = b.1.val.2 *
                (b.1.val.1⁻¹ ^ (H.f.natDegree / 2) * b.1.val.1 ^ (H.f.natDegree / 2)) := by
                simp [b.2]
        _ = b.1.val.2 * ((b.1.val.1⁻¹ * b.1.val.1) ^ (H.f.natDegree / 2)) := by
              rw [← mul_pow]
        _ = b.1.val.2 := by
              simp [b.2]
  continuous_toFun := by
    have hx : Continuous fun a : affineOverlap H => a.1.val.1 := by
      fun_prop
    have hy : Continuous fun a : affineOverlap H => a.1.val.2 := by
      fun_prop
    have hxin : Continuous fun a : affineOverlap H => (a.1.val.1)⁻¹ := by
      exact hx.inv₀ fun a => a.2
    have hpair : Continuous fun a : affineOverlap H =>
        ((a.1.val.1)⁻¹, a.1.val.2 * (a.1.val.1)⁻¹ ^ (H.f.natDegree / 2)) := by
      exact hxin.prodMk (hy.mul (hxin.pow _))
    exact Continuous.subtype_mk
      (Continuous.subtype_mk hpair fun a =>
        HyperellipticAffineInfinity.mem_of_affine H h a.1.val.1 a.1.val.2 a.1.property a.2)
      fun a => inv_ne_zero a.2
  continuous_invFun := by
    have ht : Continuous fun b : infinityOverlap H => b.1.val.1 := by
      fun_prop
    have hu : Continuous fun b : infinityOverlap H => b.1.val.2 := by
      fun_prop
    have htin : Continuous fun b : infinityOverlap H => (b.1.val.1)⁻¹ := by
      exact ht.inv₀ fun b => b.2
    have hpair : Continuous fun b : infinityOverlap H =>
        ((b.1.val.1)⁻¹, b.1.val.2 * (b.1.val.1)⁻¹ ^ (H.f.natDegree / 2)) := by
      exact htin.prodMk (hu.mul (htin.pow _))
    exact Continuous.subtype_mk
      (Continuous.subtype_mk hpair fun b =>
        HyperellipticAffine.mem_of_infinity H h b.1.val.1 b.1.val.2 b.1.property b.2)
      fun b => inv_ne_zero b.2

noncomputable def affineToInfinity (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    affineOverlap H → HyperellipticAffineInfinity H :=
  fun a => (affineToInfinityOverlap H h a).1

noncomputable def infinityToAffine (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    infinityOverlap H → HyperellipticAffine H :=
  fun b => (infinityToAffineOverlap H h b).1

lemma isOpenMap_affineToInfinity (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    IsOpenMap (affineToInfinity H h) := by
  exact (isOpen_infinityOverlap H).isOpenMap_subtype_val.comp
    (affineInfinityOverlapHomeomorph H h).isOpenMap

lemma isOpenMap_infinityToAffine (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    IsOpenMap (infinityToAffine H h) := by
  exact (isOpen_affineOverlap H).isOpenMap_subtype_val.comp
    (affineInfinityOverlapHomeomorph H h).symm.isOpenMap

lemma isOpen_image_affineChart (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    {U : Set (HyperellipticAffine H)} (hU : IsOpen U) :
    IsOpen ((fun a : HyperellipticAffine H =>
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) '' U) := by
  let q : HyperellipticEvenPre H → HyperellipticEvenProj H := fun x =>
    Quotient.mk (hyperellipticEvenSetoid H) x
  let qA : HyperellipticAffine H → HyperellipticEvenProj H := fun a =>
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)
  let V : Set (HyperellipticAffineInfinity H) :=
    (affineToInfinity H h) '' ((Subtype.val : affineOverlap H → HyperellipticAffine H) ⁻¹' U)
  have hV : IsOpen V := by
    exact (isOpenMap_affineToInfinity H h) _
      (hU.preimage continuous_subtype_val)
  have hpre :
      q ⁻¹' (qA '' U) = Sum.inl '' U ∪ Sum.inr '' V := by
    ext w
    cases w with
    | inl a =>
        constructor
        · rintro ⟨a', ha'U, hEq⟩
          have hrel : (hyperellipticEvenSetoid H).r (Sum.inl a) (Sum.inl a') :=
            Quotient.exact hEq.symm
          rw [hyperellipticEvenSetoid_rel_iff] at hrel
          rcases hrel with hEq' | hglue | hglue
          · exact Or.inl ⟨a, (Sum.inl_injective hEq').symm ▸ ha'U, rfl⟩
          · cases hglue
          · cases hglue
        · rintro (ha | ha)
          · rcases ha with ⟨a', ha'U, hEq⟩
            have : a' = a := Sum.inl_injective hEq
            subst this
            exact ⟨a', ha'U, rfl⟩
          · rcases ha with ⟨b, _, hEq⟩
            cases hEq
    | inr b =>
        constructor
        · rintro ⟨a', ha'U, hEq⟩
          have hrel : (hyperellipticEvenSetoid H).r (Sum.inl a') (Sum.inr b) :=
            Quotient.exact hEq
          rw [hyperellipticEvenSetoid_rel_iff] at hrel
          rcases hrel with hEq' | hglue | hglue_symm
          · cases hEq'
          · rcases hglue with ⟨hx, h1, h2⟩
            let a0 : affineOverlap H := ⟨a', hx⟩
            have hglue0 :
                HyperellipticEvenGlue H (Sum.inl a0.1) (Sum.inr (affineToInfinity H h a0)) := by
              dsimp [HyperellipticEvenGlue, affineToInfinity, affineToInfinityOverlap]
              exact ⟨a0.2, rfl, rfl⟩
            have hglueA :
                HyperellipticEvenGlue H (Sum.inl a') (Sum.inr b) := by
              exact ⟨hx, h1, h2⟩
            have hb' :
                (Sum.inr (affineToInfinity H h a0) : HyperellipticEvenPre H) = Sum.inr b :=
              hyperellipticEvenGlue_target_unique H hglue0 hglueA
            exact Or.inr ⟨affineToInfinity H h a0, ⟨a0, ha'U, rfl⟩, hb'⟩
          · cases hglue_symm
        · rintro (ha | hb)
          · rcases ha with ⟨a, ha, hEq⟩
            cases hEq
          · rcases hb with ⟨b', hb'V, hb'eq⟩
            rcases Sum.inr_injective hb'eq with rfl
            rcases hb'V with ⟨a0, ha0U, rfl⟩
            refine ⟨a0.1, ha0U, ?_⟩
            simpa [q, qA, affineToInfinity, affineToInfinityOverlap] using
              (Quotient.sound
                (Relation.EqvGen.rel _ _
                  (by
                    dsimp [HyperellipticEvenGlue]
                    exact ⟨a0.2, rfl, rfl⟩)) :
                q (Sum.inl a0.1) = q (Sum.inr (affineToInfinity H h a0)))
  have hpreOpen : IsOpen (q ⁻¹' (qA '' U)) := by
    rw [hpre]
    exact (isOpenMap_inl _ hU).union (isOpenMap_inr _ hV)
  exact (isQuotientMap_quotient_mk'
    (X := HyperellipticEvenPre H) (s := hyperellipticEvenSetoid H)).isCoinducing.isOpen_preimage.mp
      (by simpa [q, qA] using hpreOpen)

lemma isOpen_image_infinityChart (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    {U : Set (HyperellipticAffineInfinity H)} (hU : IsOpen U) :
    IsOpen ((fun b : HyperellipticAffineInfinity H =>
      Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)) '' U) := by
  let q : HyperellipticEvenPre H → HyperellipticEvenProj H := fun x =>
    Quotient.mk (hyperellipticEvenSetoid H) x
  let qB : HyperellipticAffineInfinity H → HyperellipticEvenProj H := fun b =>
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)
  let V : Set (HyperellipticAffine H) :=
    (infinityToAffine H h) ''
      ((Subtype.val : infinityOverlap H → HyperellipticAffineInfinity H) ⁻¹' U)
  have hV : IsOpen V := by
    exact (isOpenMap_infinityToAffine H h) _
      (hU.preimage continuous_subtype_val)
  have hpre :
      q ⁻¹' (qB '' U) = Sum.inr '' U ∪ Sum.inl '' V := by
    ext w
    cases w with
    | inl a =>
        constructor
        · rintro ⟨b', hb'U, hEq⟩
          have hrel : (hyperellipticEvenSetoid H).r (Sum.inl a) (Sum.inr b') :=
            Quotient.exact hEq.symm
          rw [hyperellipticEvenSetoid_rel_iff] at hrel
          rcases hrel with hEq' | hglue | hglue_symm
          · cases hEq'
          · rcases hglue with ⟨hx, h1, h2⟩
            let b0 : infinityOverlap H := ⟨b', by
              rw [h1]
              exact inv_ne_zero hx⟩
            have hglue0 :
                HyperellipticEvenGlue H (Sum.inl (infinityToAffine H h b0)) (Sum.inr b0.1) := by
              dsimp [HyperellipticEvenGlue, infinityToAffine, infinityToAffineOverlap]
              refine ⟨inv_ne_zero b0.2, by simp, ?_⟩
              exact (calc
                b0.1.val.2 * b0.1.val.1⁻¹ ^ (H.f.natDegree / 2) *
                    (b0.1.val.1⁻¹)⁻¹ ^ (H.f.natDegree / 2)
                    = b0.1.val.2 *
                        (b0.1.val.1⁻¹ ^ (H.f.natDegree / 2) *
                          b0.1.val.1 ^ (H.f.natDegree / 2)) := by
                          simp [b0.2]
                _ = b0.1.val.2 * ((b0.1.val.1⁻¹ * b0.1.val.1) ^ (H.f.natDegree / 2)) := by
                      rw [← mul_pow]
                _ = b0.1.val.2 := by
                      simp [b0.2]).symm
            have hglueA :
                HyperellipticEvenGlue H (Sum.inl a) (Sum.inr b') := by
              exact ⟨hx, h1, h2⟩
            have ha' :
                (Sum.inl (infinityToAffine H h b0) : HyperellipticEvenPre H) = Sum.inl a :=
              hyperellipticEvenGlue_source_unique H hglue0 hglueA
            exact Or.inr ⟨infinityToAffine H h b0, ⟨b0, hb'U, rfl⟩, ha'⟩
          · cases hglue_symm
        · rintro (hb | ha)
          · rcases hb with ⟨b, hb, hEq⟩
            cases hEq
          · rcases ha with ⟨a', ha'V, ha'eq⟩
            rcases Sum.inl_injective ha'eq with rfl
            rcases ha'V with ⟨b0, hb0U, rfl⟩
            have hglue0 :
                HyperellipticEvenGlue H (Sum.inl (infinityToAffine H h b0)) (Sum.inr b0.1) := by
              dsimp [HyperellipticEvenGlue, infinityToAffine, infinityToAffineOverlap]
              refine ⟨inv_ne_zero b0.2, by simp, ?_⟩
              exact (calc
                b0.1.val.2 * b0.1.val.1⁻¹ ^ (H.f.natDegree / 2) *
                    (b0.1.val.1⁻¹)⁻¹ ^ (H.f.natDegree / 2)
                    = b0.1.val.2 *
                        (b0.1.val.1⁻¹ ^ (H.f.natDegree / 2) *
                          b0.1.val.1 ^ (H.f.natDegree / 2)) := by
                          simp [b0.2]
                _ = b0.1.val.2 * ((b0.1.val.1⁻¹ * b0.1.val.1) ^ (H.f.natDegree / 2)) := by
                      rw [← mul_pow]
                _ = b0.1.val.2 := by
                      simp [b0.2]).symm
            refine ⟨b0.1, hb0U, ?_⟩
            simpa [q, qB, infinityToAffine, infinityToAffineOverlap] using
              (Quotient.sound
                (Relation.EqvGen.rel _ _ hglue0) :
                q (Sum.inl (infinityToAffine H h b0)) = q (Sum.inr b0.1)).symm
    | inr b =>
        constructor
        · rintro ⟨b', hb'U, hEq⟩
          have hrel : (hyperellipticEvenSetoid H).r (Sum.inr b) (Sum.inr b') :=
            Quotient.exact hEq.symm
          rw [hyperellipticEvenSetoid_rel_iff] at hrel
          rcases hrel with hEq' | hglue | hglue
          · exact Or.inl ⟨b, (Sum.inr_injective hEq').symm ▸ hb'U, rfl⟩
          · cases hglue
          · cases hglue
        · rintro (hb | ha)
          · rcases hb with ⟨b', hb'U, hEq⟩
            have : b' = b := Sum.inr_injective hEq
            subst this
            exact ⟨b', hb'U, rfl⟩
          · rcases ha with ⟨a, _, hEq⟩
            cases hEq
  have hpreOpen : IsOpen (q ⁻¹' (qB '' U)) := by
    rw [hpre]
    exact (isOpenMap_inr _ hU).union (isOpenMap_inl _ hV)
  exact (isQuotientMap_quotient_mk'
    (X := HyperellipticEvenPre H) (s := hyperellipticEvenSetoid H)).isCoinducing.isOpen_preimage.mp
      (by simpa [q, qB] using hpreOpen)

lemma hyperellipticEven_isOpenQuotientMap (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    IsOpenQuotientMap (fun x : HyperellipticEvenPre H =>
      Quotient.mk (hyperellipticEvenSetoid H) x) := by
  refine IsOpenQuotientMap.of_isOpenMap_isQuotientMap ?_
    (isQuotientMap_quotient_mk' (X := HyperellipticEvenPre H) (s := hyperellipticEvenSetoid H))
  intro U hU
  let UA : Set (HyperellipticAffine H) := Sum.inl ⁻¹' U
  let UB : Set (HyperellipticAffineInfinity H) := Sum.inr ⁻¹' U
  have hUA : IsOpen UA := hU.preimage continuous_inl
  have hUB : IsOpen UB := hU.preimage continuous_inr
  have hdecomp : U = Sum.inl '' UA ∪ Sum.inr '' UB := by
    ext w
    cases w with
    | inl a =>
        constructor
        · intro ha
          exact Or.inl ⟨a, ha, rfl⟩
        · rintro (ha | ha)
          · rcases ha with ⟨a', ha', hEq⟩
            exact hEq ▸ ha'
          · rcases ha with ⟨b, hb, hEq⟩
            cases hEq
    | inr b =>
        constructor
        · intro hb
          exact Or.inr ⟨b, hb, rfl⟩
        · rintro (ha | ha)
          · rcases ha with ⟨a, ha, hEq⟩
            cases hEq
          · rcases ha with ⟨b', hb', hEq⟩
            exact hEq ▸ hb'
  rw [hdecomp]
  have hImageEq :
      ((fun x : HyperellipticEvenPre H => Quotient.mk (hyperellipticEvenSetoid H) x) ''
          (Sum.inl '' UA ∪ Sum.inr '' UB)) =
        (((fun a : HyperellipticAffine H =>
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a)) '' UA) ∪
          ((fun b : HyperellipticAffineInfinity H =>
            Quotient.mk (hyperellipticEvenSetoid H) (Sum.inr b)) '' UB)) := by
    simp [Set.image_union, Set.image_image]
  exact hImageEq ▸ (isOpen_image_affineChart H h hUA).union (isOpen_image_infinityChart H h hUB)

lemma hyperellipticEvenGlue_iff_mul (H : HyperellipticData)
    (a : HyperellipticAffine H) (b : HyperellipticAffineInfinity H) :
    HyperellipticEvenGlue H (Sum.inl a) (Sum.inr b) ↔
      b.val.1 * a.val.1 = 1 ∧
        b.val.2 = a.val.2 * b.val.1 ^ (H.f.natDegree / 2) := by
  constructor
  · rintro ⟨hx, h1, h2⟩
    refine ⟨?_, ?_⟩
    · simpa [h1] using inv_mul_cancel₀ hx
    · simpa [h1] using h2
  · rintro ⟨hmul, h2⟩
    have hx : a.val.1 ≠ 0 := by
      intro hzero
      have : (0 : ℂ) = 1 := by
        simpa [hzero] using hmul
      exact zero_ne_one this
    have h1 : b.val.1 = a.val.1⁻¹ := eq_inv_of_mul_eq_one_left hmul
    refine ⟨hx, h1, ?_⟩
    simpa [h1] using h2

lemma isClosed_hyperellipticEvenGlueCore (H : HyperellipticData) :
    IsClosed {ab : HyperellipticAffine H × HyperellipticAffineInfinity H |
      ab.2.val.1 * ab.1.val.1 = 1 ∧
        ab.2.val.2 = ab.1.val.2 * ab.2.val.1 ^ (H.f.natDegree / 2)} := by
  have hmul :
      IsClosed {ab : HyperellipticAffine H × HyperellipticAffineInfinity H |
        ab.2.val.1 * ab.1.val.1 = 1} := by
    exact isClosed_eq
      (by fun_prop : Continuous fun ab : HyperellipticAffine H × HyperellipticAffineInfinity H =>
        ab.2.val.1 * ab.1.val.1)
      continuous_const
  have hpow :
      IsClosed {ab : HyperellipticAffine H × HyperellipticAffineInfinity H |
        ab.2.val.2 = ab.1.val.2 * ab.2.val.1 ^ (H.f.natDegree / 2)} := by
    exact isClosed_eq
      (by fun_prop : Continuous fun ab : HyperellipticAffine H × HyperellipticAffineInfinity H =>
        ab.2.val.2)
      (by fun_prop : Continuous fun ab : HyperellipticAffine H × HyperellipticAffineInfinity H =>
        ab.1.val.2 * ab.2.val.1 ^ (H.f.natDegree / 2))
  simpa [Set.setOf_and] using hmul.inter hpow

lemma isClosed_hyperellipticEvenGlue (H : HyperellipticData) :
    IsClosed {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
      HyperellipticEvenGlue H pq.1 pq.2} := by
  let S : Set (HyperellipticAffine H × HyperellipticAffineInfinity H) := fun ab =>
    ab.2.val.1 * ab.1.val.1 = 1 ∧
      ab.2.val.2 = ab.1.val.2 * ab.2.val.1 ^ (H.f.natDegree / 2)
  have hS : IsClosed S := by
    simpa [S] using isClosed_hyperellipticEvenGlueCore H
  have hclosedEmb :
      Topology.IsClosedEmbedding
        (Prod.map (Sum.inl : HyperellipticAffine H → HyperellipticEvenPre H)
          (Sum.inr : HyperellipticAffineInfinity H → HyperellipticEvenPre H)) :=
    Topology.IsClosedEmbedding.inl.prodMap Topology.IsClosedEmbedding.inr
  have hImage :
      Prod.map (Sum.inl : HyperellipticAffine H → HyperellipticEvenPre H)
          (Sum.inr : HyperellipticAffineInfinity H → HyperellipticEvenPre H) '' S =
        {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
          HyperellipticEvenGlue H pq.1 pq.2} := by
    ext pq
    cases pq with
    | mk p q =>
        cases p with
        | inl a =>
            cases q with
            | inl a' =>
                constructor
                · rintro ⟨⟨a0, b0⟩, _, hEq⟩
                  cases hEq
                · intro h
                  cases h
            | inr b =>
                constructor
                · rintro ⟨⟨a0, b0⟩, hab, hEq⟩
                  cases hEq
                  exact (hyperellipticEvenGlue_iff_mul H a b).2 hab
                · intro hab
                  exact ⟨(a, b), (hyperellipticEvenGlue_iff_mul H a b).1 hab, rfl⟩
        | inr b =>
            cases q with
            | inl a =>
                constructor
                · rintro ⟨⟨a0, b0⟩, _, hEq⟩
                  cases hEq
                · intro h
                  cases h
            | inr b' =>
                constructor
                · rintro ⟨⟨a0, b0⟩, _, hEq⟩
                  cases hEq
                · intro h
                  cases h
  simpa [hImage] using hclosedEmb.isClosedMap _ hS

lemma isClosed_hyperellipticEvenSetoidRel (H : HyperellipticData) :
    IsClosed {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
      (hyperellipticEvenSetoid H).r pq.1 pq.2} := by
  have hdiag :
      IsClosed {pq : HyperellipticEvenPre H × HyperellipticEvenPre H | pq.1 = pq.2} := by
    exact isClosed_eq continuous_fst continuous_snd
  have hglue :
      IsClosed {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
        HyperellipticEvenGlue H pq.1 pq.2} :=
    isClosed_hyperellipticEvenGlue H
  have hglue_symm :
      IsClosed {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
        HyperellipticEvenGlue H pq.2 pq.1} := by
    simpa [Set.preimage, Prod.swap] using hglue.preimage
      (Homeomorph.prodComm (HyperellipticEvenPre H) (HyperellipticEvenPre H)).continuous
  have hEq :
      {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
          (hyperellipticEvenSetoid H).r pq.1 pq.2} =
        {pq : HyperellipticEvenPre H × HyperellipticEvenPre H | pq.1 = pq.2} ∪
          {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
            HyperellipticEvenGlue H pq.1 pq.2} ∪
          {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
            HyperellipticEvenGlue H pq.2 pq.1} := by
    ext pq
    constructor
    · intro hpq
      rcases (hyperellipticEvenSetoid_rel_iff H pq.1 pq.2).1 hpq with hpq | hpq | hpq
      · exact Or.inl (Or.inl hpq)
      · exact Or.inl (Or.inr hpq)
      · exact Or.inr hpq
    · rintro (hpq | hpq)
      · rcases hpq with hpq | hpq
        · exact (hyperellipticEvenSetoid_rel_iff H pq.1 pq.2).2 (Or.inl hpq)
        · exact (hyperellipticEvenSetoid_rel_iff H pq.1 pq.2).2 (Or.inr (Or.inl hpq))
      · exact (hyperellipticEvenSetoid_rel_iff H pq.1 pq.2).2 (Or.inr (Or.inr hpq))
  rw [hEq]
  exact (hdiag.union hglue).union hglue_symm

instance (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    T2Space (HyperellipticEvenProj H) := by
  let π : HyperellipticEvenPre H → HyperellipticEvenProj H := fun x =>
    Quotient.mk (hyperellipticEvenSetoid H) x
  have hπ : IsOpenQuotientMap π := hyperellipticEven_isOpenQuotientMap H h
  have hclosed :
      IsClosed {pq : HyperellipticEvenPre H × HyperellipticEvenPre H | π pq.1 = π pq.2} := by
    have hrel : IsClosed {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
        (hyperellipticEvenSetoid H).r pq.1 pq.2} :=
      isClosed_hyperellipticEvenSetoidRel H
    have hEqRel :
        {pq : HyperellipticEvenPre H × HyperellipticEvenPre H | π pq.1 = π pq.2} =
          {pq : HyperellipticEvenPre H × HyperellipticEvenPre H |
            (hyperellipticEvenSetoid H).r pq.1 pq.2} := by
      ext pq
      constructor
      · intro hpq
        exact Quotient.exact hpq
      · intro hpq
        exact Quotient.sound hpq
    exact hEqRel.symm ▸ hrel
  exact (t2Space_iff_of_isOpenQuotientMap hπ).2 hclosed

end Jacobians.ProjectiveCurve
