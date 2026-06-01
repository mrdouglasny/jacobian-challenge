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

All theorems in this file are **sorry-free and axiom-free** (task #21,
2026-06-01). The two cross-summand cocycle axioms that this construction
used to rest on are now real theorems in `EvenForm.lean`
(`hyperellipticEvenCoeff_cocycle_{inl_inr,inr_inl}`, the latter via
chart-transition symmetry), so `hyperellipticForm` no longer invokes any
axiom. To stay sound it is defined to return the zero form for `deg g ≥
N/2 − 1` (where `g(x) dx/y` has a pole at ∞), and the linear-algebra API
(`hyperellipticFormLinearMap`, injectivity, linear independence) lives on
the low-degree subspace `Polynomial.degreeLT ℂ (N/2 − 1)`.

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
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticAffineInfinity

variable {H : HyperellipticData} [Fact (¬ Odd H.f.natDegree)]

/-! ## The reusable `hyperellipticForm` constructor -/

/-- The holomorphic 1-form `g(x) dx / y` on `HyperellipticEvenProj H`, for a
polynomial `g` of degree `< N/2 − 1` (the bound under which it is a genuine
holomorphic 1-form — the cross-summand cocycle holds, `EvenForm.lean`).
Outside that range it returns the zero form, keeping the constructor total
and **axiom-free** (no longer invoking the retired high-degree cocycle
axioms; task #21). -/
noncomputable def hyperellipticForm (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] (g : Polynomial ℂ) :
    HolomorphicOneForm (HyperellipticEvenProj H) :=
  if h : g.natDegree < H.f.natDegree / 2 - 1 then
    ⟨hyperellipticEvenCoeff (H := H) g (infReverse H g),
     hyperellipticEvenCoeff_mem_submodule g (infReverse H g) rfl h⟩
  else 0

/-- On low-degree polynomials, `hyperellipticForm` is the real form. -/
theorem hyperellipticForm_of_lt (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] {g : Polynomial ℂ}
    (hDeg : g.natDegree < H.f.natDegree / 2 - 1) :
    hyperellipticForm H g =
      ⟨hyperellipticEvenCoeff (H := H) g (infReverse H g),
       hyperellipticEvenCoeff_mem_submodule g (infReverse H g) rfl hDeg⟩ :=
  dif_pos hDeg

/-- The coefficient of a low-degree `hyperellipticForm`. -/
theorem hyperellipticForm_coeff_of_lt (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] {g : Polynomial ℂ}
    (hDeg : g.natDegree < H.f.natDegree / 2 - 1) :
    (hyperellipticForm H g).coeff = hyperellipticEvenCoeff (H := H) g (infReverse H g) := by
  rw [hyperellipticForm_of_lt H hDeg]; rfl

/-- A polynomial in `degreeLT ℂ n` with `0 < n` has `natDegree < n`. -/
theorem natDegree_lt_of_mem_degreeLT {n : ℕ} (hn : 0 < n) {g : Polynomial ℂ}
    (hg : g ∈ Polynomial.degreeLT ℂ n) : g.natDegree < n := by
  by_cases h0 : g = 0
  · simpa [h0] using hn
  · rw [Polynomial.mem_degreeLT] at hg
    exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hg

/-! ## Linearity (on the low-degree subspace) -/

/-- `hyperellipticForm` is additive on low-degree polynomials. -/
theorem hyperellipticForm_add_of_lt (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] {g g' : Polynomial ℂ}
    (h : g.natDegree < H.f.natDegree / 2 - 1)
    (h' : g'.natDegree < H.f.natDegree / 2 - 1)
    (h'' : (g + g').natDegree < H.f.natDegree / 2 - 1) :
    hyperellipticForm H (g + g') =
      hyperellipticForm H g + hyperellipticForm H g' := by
  rw [hyperellipticForm_of_lt H h, hyperellipticForm_of_lt H h', hyperellipticForm_of_lt H h'']
  apply Subtype.ext
  show hyperellipticEvenCoeff (H := H) (g + g') (infReverse H (g + g')) = _
  rw [infReverse_add]
  exact hyperellipticEvenCoeff_add g (infReverse H g) g' (infReverse H g')

/-- `hyperellipticForm` is ℂ-linear (scalar mult side) on low-degree
polynomials. -/
theorem hyperellipticForm_smul_of_lt (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] (c : ℂ) {g : Polynomial ℂ}
    (h : g.natDegree < H.f.natDegree / 2 - 1)
    (h' : (c • g).natDegree < H.f.natDegree / 2 - 1) :
    hyperellipticForm H (c • g) = c • hyperellipticForm H g := by
  rw [hyperellipticForm_of_lt H h, hyperellipticForm_of_lt H h']
  apply Subtype.ext
  show hyperellipticEvenCoeff (H := H) (c • g) (infReverse H (c • g)) = _
  rw [infReverse_smul]
  exact hyperellipticEvenCoeff_smul c g (infReverse H g)

/-- `hyperellipticForm` of the zero polynomial is the zero form. -/
@[simp] theorem hyperellipticForm_zero (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    hyperellipticForm H (0 : Polynomial ℂ) = 0 := by
  unfold hyperellipticForm
  split
  · apply Subtype.ext
    show hyperellipticEvenCoeff (H := H) 0 (infReverse H 0) = 0
    rw [infReverse_zero]; exact hyperellipticEvenCoeff_zero
  · rfl

/-- Every element of `degreeLT ℂ 0` is the zero polynomial. -/
private theorem eq_zero_of_mem_degreeLT_zero {p : Polynomial ℂ}
    (hp : p ∈ Polynomial.degreeLT ℂ 0) : p = 0 := by
  rw [Polynomial.mem_degreeLT, Nat.cast_zero, Nat.WithBot.lt_zero_iff,
    Polynomial.degree_eq_bot] at hp
  exact hp

/-- The packaged ℂ-linear map version of `hyperellipticForm`, on the
low-degree subspace `Polynomial.degreeLT ℂ (N/2−1)`. -/
noncomputable def hyperellipticFormLinearMap (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    Polynomial.degreeLT ℂ (H.f.natDegree / 2 - 1) →ₗ[ℂ]
      HolomorphicOneForm (HyperellipticEvenProj H) where
  toFun gd := hyperellipticForm H gd.1
  map_add' gd gd' := by
    rcases Nat.eq_zero_or_pos (H.f.natDegree / 2 - 1) with hn | hn
    · -- n = 0: degreeLT is {0}, all forms are 0
      have e : ∀ p : Polynomial.degreeLT ℂ (H.f.natDegree / 2 - 1), p.1 = 0 := by
        intro p; exact eq_zero_of_mem_degreeLT_zero (hn ▸ p.2)
      simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, e, add_zero,
        hyperellipticForm_zero]
    · have h1 := natDegree_lt_of_mem_degreeLT hn gd.2
      have h2 := natDegree_lt_of_mem_degreeLT hn gd'.2
      have h3 : (gd.1 + gd'.1).natDegree < H.f.natDegree / 2 - 1 :=
        lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt h1 h2)
      exact hyperellipticForm_add_of_lt H h1 h2 h3
  map_smul' c gd := by
    rcases Nat.eq_zero_or_pos (H.f.natDegree / 2 - 1) with hn | hn
    · have e : ∀ p : Polynomial.degreeLT ℂ (H.f.natDegree / 2 - 1), p.1 = 0 := by
        intro p; exact eq_zero_of_mem_degreeLT_zero (hn ▸ p.2)
      simp only [RingHom.id_apply, SetLike.val_smul, e, smul_zero, hyperellipticForm_zero]
    · have h1 := natDegree_lt_of_mem_degreeLT hn gd.2
      have h2 : (c • gd.1).natDegree < H.f.natDegree / 2 - 1 :=
        lt_of_le_of_lt (Polynomial.natDegree_smul_le _ _) h1
      show hyperellipticForm H (c • gd.1) = c • hyperellipticForm H gd.1
      exact hyperellipticForm_smul_of_lt H c h1 h2

/-! ## Linear independence

The family `{ hyperellipticForm (X^k) : 0 ≤ k < g }` is linearly
independent in `HolomorphicOneForm`. Reduces to linear independence
of `{ X^k : 0 ≤ k < g }` in `Polynomial ℂ` (standard Mathlib fact)
via injectivity of `hyperellipticFormLinearMap` restricted to the
degree-`< g` subspace.
-/

/-! ### Form-level injectivity

The architectural pattern: a `hyperellipticForm` is determined by its
underlying coefficient function on `HyperellipticEvenProj H`. Evaluating
the coefficient at a quotient point `q` whose `Quotient.out q = Sum.inl a`
recovers the affine coefficient `hyperellipticAffineCoeff g a`, from which
`g` is determined (via the affine-side polynomial-recovery argument).

The "conditional" injectivity below assumes the existence of such a
witness `(q, a)`; full injectivity will follow once we discharge the
existence (pick an affine point `a₀` not in the gluing region — typically
`x₀ = 0` when `H.f(0) ≠ 0`). -/

/-- **Conditional form-level injectivity.** If two `hyperellipticForm`s
agree at a quotient point whose `Quotient.out` lands on the affine
summand at a `smoothLocusY` representative, then the underlying
polynomials are equal. -/
theorem hyperellipticForm_eq_of_agree_at_affine_smoothY
    {g g' : Polynomial ℂ}
    (hg : g.natDegree < H.f.natDegree / 2 - 1) (hg' : g'.natDegree < H.f.natDegree / 2 - 1)
    {q : HyperellipticEvenProj H}
    {a : HyperellipticAffine H} (hpY : a ∈ smoothLocusY H)
    (hQ : Quotient.out q = Sum.inl a)
    (hCoeff : (hyperellipticForm H g).coeff q =
              (hyperellipticForm H g').coeff q) :
    g = g' := by
  have hReduce : ∀ (g₀ : Polynomial ℂ), g₀.natDegree < H.f.natDegree / 2 - 1 →
      (hyperellipticForm H g₀).coeff q = hyperellipticAffineCoeff (H := H) g₀ a := by
    intro g₀ hg₀
    rw [hyperellipticForm_coeff_of_lt H hg₀]
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g₀ a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) (infReverse H g₀) b) = _
    rw [hQ]
  rw [hReduce g hg, hReduce g' hg'] at hCoeff
  exact hyperellipticAffineCoeff_injective_at_smoothLocusY a hpY hCoeff

/-- **Conditional form-level injectivity** (smoothLocusX variant).
Mirror of `hyperellipticForm_eq_of_agree_at_affine_smoothY` for the
projY chart family: if two `hyperellipticForm`s agree at `q` whose
`Quotient.out` is `Sum.inl a` with `a ∈ smoothLocusX H \ smoothLocusY H`,
then the underlying polynomials are equal.

Useful when `H.f(0) = 0`: the witness point is `(0, 0)`, which lies in
`smoothLocusX` (since `f'(0) ≠ 0` follows from `H.f` being squarefree)
but not in `smoothLocusY`. -/
theorem hyperellipticForm_eq_of_agree_at_affine_smoothX
    {g g' : Polynomial ℂ}
    (hg : g.natDegree < H.f.natDegree / 2 - 1) (hg' : g'.natDegree < H.f.natDegree / 2 - 1)
    {q : HyperellipticEvenProj H}
    {a : HyperellipticAffine H}
    (hpX : a ∈ smoothLocusX H) (hpYn : a ∉ smoothLocusY H)
    (hQ : Quotient.out q = Sum.inl a)
    (hCoeff : (hyperellipticForm H g).coeff q =
              (hyperellipticForm H g').coeff q) :
    g = g' := by
  have hReduce : ∀ (g₀ : Polynomial ℂ), g₀.natDegree < H.f.natDegree / 2 - 1 →
      (hyperellipticForm H g₀).coeff q = hyperellipticAffineCoeff (H := H) g₀ a := by
    intro g₀ hg₀
    rw [hyperellipticForm_coeff_of_lt H hg₀]
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g₀ a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) (infReverse H g₀) b) = _
    rw [hQ]
  rw [hReduce g hg, hReduce g' hg'] at hCoeff
  exact hyperellipticAffineCoeff_injective_at_smoothLocusX a hpX hpYn hCoeff

/-! ### Witness existence and full injectivity

To discharge `injOn_lowDegree` we need a quotient point `q` whose
`Quotient.out` lands on the affine summand at a point in either
`smoothLocusY` or `smoothLocusX`. The natural witness is
`a₀ = (0, ±√H.f(0))`: any affine point with `x = 0` is isolated in
the gluing graph, since `HyperellipticEvenGlue (Sum.inl a) (Sum.inr b)`
requires `a.val.1 ≠ 0`. Case-splitting on `H.f(0) = 0`:
* `H.f(0) ≠ 0`: `a₀ ∈ smoothLocusY` (since `a₀.val.2² = H.f(0) ≠ 0`).
* `H.f(0) = 0`: `a₀ = (0, 0) ∈ smoothLocusX` (since `H.f` squarefree
  implies `f'(0) ≠ 0` when `0` is a root). -/

omit [Fact (¬ Odd H.f.natDegree)] in
/-- `Quotient.out` returns the input when the gluing graph isolates it
(no glue arrow touches `Sum.inl a₀` when `a₀.val.1 = 0`). -/
lemma quotient_out_of_zero_x (a₀ : HyperellipticAffine H) (h0 : a₀.val.1 = 0) :
    Quotient.out (Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a₀)) = Sum.inl a₀ := by
  set q : HyperellipticEvenProj H := Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl a₀)
  set u := Quotient.out q
  have hRel : (hyperellipticEvenSetoid H).r u (Sum.inl a₀) :=
    Quotient.exact (Quotient.out_eq q)
  rw [hyperellipticEvenSetoid_rel_iff] at hRel
  rcases hRel with hEq | hGl1 | hGl2
  · exact hEq
  · rcases u with a' | b' <;> simp [HyperellipticEvenGlue] at hGl1
  · rcases u with a' | b' <;> simp [HyperellipticEvenGlue] at hGl2
    exact absurd hGl2.1 (by simp [h0])

/-- Witness affine point for the injectivity proof: `(0, y)` where
`y² = H.f(0)`. Has `x = 0` so it sits outside the gluing region. -/
noncomputable def witnessZeroX (H : HyperellipticData) : HyperellipticAffine H :=
  ⟨(0, (exists_complex_sq_eq (H.f.eval 0)).choose), by
    simpa using (exists_complex_sq_eq (H.f.eval 0)).choose_spec⟩

@[simp] lemma witnessZeroX_val_fst (H : HyperellipticData) :
    (witnessZeroX H).val.1 = 0 := rfl

lemma witnessZeroX_val_snd_sq (H : HyperellipticData) :
    (witnessZeroX H).val.2 ^ 2 = H.f.eval 0 := by
  simpa using (witnessZeroX H).property

lemma witnessZeroX_mem_smoothLocusY_iff (H : HyperellipticData) :
    witnessZeroX H ∈ smoothLocusY H ↔ H.f.eval 0 ≠ 0 := by
  unfold smoothLocusY
  constructor
  · intro hY h0
    apply hY
    have hSq : (witnessZeroX H).val.2 ^ 2 = 0 := by
      rw [witnessZeroX_val_snd_sq]; exact h0
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hSq
  · intro h0 hY
    have hSq : (witnessZeroX H).val.2 ^ 2 = H.f.eval 0 := witnessZeroX_val_snd_sq H
    rw [hY, zero_pow (by norm_num : 2 ≠ 0)] at hSq
    exact h0 hSq.symm

lemma witnessZeroX_mem_smoothLocusX_of_zero_root (H : HyperellipticData)
    (h0 : H.f.eval 0 = 0) :
    witnessZeroX H ∈ smoothLocusX H := by
  unfold smoothLocusX
  show (Polynomial.derivative H.f).eval (witnessZeroX H).val.1 ≠ 0
  rw [witnessZeroX_val_fst]
  exact eval_derivative_ne_zero_of_eval_eq_zero H h0

/-- **Injectivity of `hyperellipticForm` on the low-degree subspace.**
Two polynomials of degree `< N/2 − 1` yielding equal forms are equal.
(No longer unconditional: high-degree polynomials all map to the zero form.) -/
theorem hyperellipticForm_injOn_lowDegree
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)] :
    Set.InjOn (hyperellipticForm H)
      { g : Polynomial ℂ | g.natDegree < H.f.natDegree / 2 - 1 } := by
  intro g hg g' hg' hForm
  simp only [Set.mem_setOf_eq] at hg hg'
  set q : HyperellipticEvenProj H :=
    Quotient.mk (hyperellipticEvenSetoid H) (Sum.inl (witnessZeroX H))
  have hQ : Quotient.out q = Sum.inl (witnessZeroX H) :=
    quotient_out_of_zero_x (witnessZeroX H) (witnessZeroX_val_fst H)
  have hCoeff : (hyperellipticForm H g).coeff q = (hyperellipticForm H g').coeff q := by
    rw [hForm]
  by_cases h0 : H.f.eval 0 = 0
  · have hpX := witnessZeroX_mem_smoothLocusX_of_zero_root H h0
    have hpYn : witnessZeroX H ∉ smoothLocusY H := by
      rw [witnessZeroX_mem_smoothLocusY_iff]
      exact fun h => h h0
    exact hyperellipticForm_eq_of_agree_at_affine_smoothX hg hg' hpX hpYn hQ hCoeff
  · have hpY : witnessZeroX H ∈ smoothLocusY H :=
      (witnessZeroX_mem_smoothLocusY_iff H).mpr h0
    exact hyperellipticForm_eq_of_agree_at_affine_smoothY hg hg' hpY hQ hCoeff

/-- The low-degree linear map `hyperellipticFormLinearMap` is injective. -/
theorem hyperellipticFormLinearMap_injective (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    Function.Injective (hyperellipticFormLinearMap H) := by
  intro gd gd' h
  apply Subtype.ext
  rcases Nat.eq_zero_or_pos (H.f.natDegree / 2 - 1) with hn | hn
  · have e : ∀ p : Polynomial.degreeLT ℂ (H.f.natDegree / 2 - 1), p.1 = 0 := by
      intro p; exact eq_zero_of_mem_degreeLT_zero (hn ▸ p.2)
    rw [e gd, e gd']
  · exact hyperellipticForm_injOn_lowDegree H
      (Set.mem_setOf.mpr (natDegree_lt_of_mem_degreeLT hn gd.2))
      (Set.mem_setOf.mpr (natDegree_lt_of_mem_degreeLT hn gd'.2)) h

/-- Linear independence of the canonical basis `{ hyperellipticForm (X^k) :
0 ≤ k < N/2 − 1 }`, via injectivity of the low-degree linear map. -/
theorem hyperellipticForm_linearIndependent (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    LinearIndependent ℂ
      (fun k : Fin (H.f.natDegree / 2 - 1) =>
        hyperellipticForm H (Polynomial.X ^ k.val)) := by
  set n := H.f.natDegree / 2 - 1 with hn
  -- X^k ∈ degreeLT ℂ n
  have hmem : ∀ k : Fin n, (Polynomial.X ^ k.val : Polynomial ℂ) ∈ Polynomial.degreeLT ℂ n := by
    intro k; rw [Polynomial.mem_degreeLT, Polynomial.degree_X_pow]; exact_mod_cast k.isLt
  set v : Fin n → Polynomial.degreeLT ℂ n := fun k => ⟨Polynomial.X ^ k.val, hmem k⟩ with hv
  -- (1) X^k linearly independent in ℂ[X]
  have hCoe : ⇑(Polynomial.basisMonomials ℂ) = fun m => (Polynomial.X : Polynomial ℂ) ^ m := by
    funext m; rw [Polynomial.coe_basisMonomials, ← Polynomial.monomial_one_right_eq_X_pow m]
  have hPowLI : LinearIndependent ℂ (fun m : ℕ => (Polynomial.X : Polynomial ℂ) ^ m) := by
    have := (Polynomial.basisMonomials ℂ).linearIndependent; rw [hCoe] at this; exact this
  have hFinLI : LinearIndependent ℂ (fun k : Fin n => (Polynomial.X : Polynomial ℂ) ^ k.val) :=
    hPowLI.comp (fun k : Fin n => k.val) Fin.val_injective
  -- (2) v linearly independent in degreeLT (reflect through the injective subtype;
  --     `subtype ∘ v = fun k => X^k` holds by `rfl`)
  have hvLI : LinearIndependent ℂ v :=
    LinearIndependent.of_comp (Polynomial.degreeLT ℂ n).subtype hFinLI
  -- (3) push through the injective low-degree map
  have hKer : LinearMap.ker (hyperellipticFormLinearMap H) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (hyperellipticFormLinearMap_injective H)
  have hmap := hvLI.map' (hyperellipticFormLinearMap H) hKer
  exact hmap

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
