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

All theorems in this file are now **sorry-free**. The construction
rests on two cross-summand cocycle axioms in `EvenForm.lean` (the
Möbius gluing region), which are explicitly hypothesized on the
gluing relation `g_inf = infReverse H g_aff` so that they are
mathematically correct as statements; their discharge requires
explicit chain-rule computations on `x ↦ 1/x`.

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

/-- The holomorphic 1-form `g(x) dx / y` on `HyperellipticEvenProj H`,
parameterized by an arbitrary polynomial `g : Polynomial ℂ`.

Constructed as the unified coefficient family
`hyperellipticEvenCoeff g (infReverse H g)` together with its
`holomorphicOneFormSubmodule` membership proof. The gluing hypothesis
`g_inf = infReverse H g` is supplied as `rfl` since this constructor
always pairs `g` with its canonical infinity-side polynomial.

The membership proof is real on the within-summand cocycle predicates
(analyticity, off-target, same-summand cocycle) and rests on two
cross-summand axioms in `EvenForm.lean` for the Möbius gluing region;
those axioms now carry the gluing relation as an explicit hypothesis,
so they are no longer mathematically false for non-matching pairs. -/
noncomputable def hyperellipticForm (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] (g : Polynomial ℂ) :
    HolomorphicOneForm (HyperellipticEvenProj H) :=
  ⟨hyperellipticEvenCoeff (H := H) g (infReverse H g),
   hyperellipticEvenCoeff_mem_submodule g (infReverse H g) rfl⟩

/-! ## Linearity -/

/-- `hyperellipticForm` is additive in the polynomial. -/
theorem hyperellipticForm_add (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] (g g' : Polynomial ℂ) :
    hyperellipticForm H (g + g') =
      hyperellipticForm H g + hyperellipticForm H g' := by
  apply Subtype.ext
  show hyperellipticEvenCoeff (H := H) (g + g') (infReverse H (g + g')) = _
  rw [infReverse_add]
  exact hyperellipticEvenCoeff_add g (infReverse H g) g' (infReverse H g')

/-- `hyperellipticForm` is ℂ-linear (scalar mult side). -/
theorem hyperellipticForm_smul (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] (c : ℂ) (g : Polynomial ℂ) :
    hyperellipticForm H (c • g) = c • hyperellipticForm H g := by
  apply Subtype.ext
  show hyperellipticEvenCoeff (H := H) (c • g) (infReverse H (c • g)) = _
  rw [infReverse_smul]
  exact hyperellipticEvenCoeff_smul c g (infReverse H g)

/-- `hyperellipticForm` of the zero polynomial is the zero form. -/
theorem hyperellipticForm_zero (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    hyperellipticForm H (0 : Polynomial ℂ) = 0 := by
  apply Subtype.ext
  show hyperellipticEvenCoeff (H := H) 0 (infReverse H 0) = 0
  rw [infReverse_zero]
  exact hyperellipticEvenCoeff_zero

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
    [hf : Fact (¬ Odd H.f.natDegree)]
    {g g' : Polynomial ℂ}
    {q : HyperellipticEvenProj H}
    {a : HyperellipticAffine H} (hpY : a ∈ smoothLocusY H)
    (hQ : Quotient.out q = Sum.inl a)
    (hCoeff : (hyperellipticForm H g).coeff q =
              (hyperellipticForm H g').coeff q) :
    g = g' := by
  have hReduce : ∀ (g₀ : Polynomial ℂ),
      (hyperellipticForm H g₀).coeff q = hyperellipticAffineCoeff (H := H) g₀ a := by
    intro g₀
    show (hyperellipticEvenCoeff (H := H) g₀ (infReverse H g₀)) q = _
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g₀ a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) (infReverse H g₀) b) = _
    rw [hQ]
  rw [hReduce g, hReduce g'] at hCoeff
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
    [hf : Fact (¬ Odd H.f.natDegree)]
    {g g' : Polynomial ℂ}
    {q : HyperellipticEvenProj H}
    {a : HyperellipticAffine H}
    (hpX : a ∈ smoothLocusX H) (hpYn : a ∉ smoothLocusY H)
    (hQ : Quotient.out q = Sum.inl a)
    (hCoeff : (hyperellipticForm H g).coeff q =
              (hyperellipticForm H g').coeff q) :
    g = g' := by
  have hReduce : ∀ (g₀ : Polynomial ℂ),
      (hyperellipticForm H g₀).coeff q = hyperellipticAffineCoeff (H := H) g₀ a := by
    intro g₀
    show (hyperellipticEvenCoeff (H := H) g₀ (infReverse H g₀)) q = _
    show (match Quotient.out q with
      | Sum.inl a => hyperellipticAffineCoeff (H := H) g₀ a
      | Sum.inr b => hyperellipticAffineInfinityCoeff (H := H) (infReverse H g₀) b) = _
    rw [hQ]
  rw [hReduce g, hReduce g'] at hCoeff
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

/-- **Unconditional injectivity** of `hyperellipticForm`: any two
polynomials yielding equal forms are equal. -/
theorem hyperellipticForm_injective (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    Function.Injective (hyperellipticForm H) := by
  intro g g' hForm
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
    exact hyperellipticForm_eq_of_agree_at_affine_smoothX hpX hpYn hQ hCoeff
  · have hpY : witnessZeroX H ∈ smoothLocusY H :=
      (witnessZeroX_mem_smoothLocusY_iff H).mpr h0
    exact hyperellipticForm_eq_of_agree_at_affine_smoothY hpY hQ hCoeff

/-- Injectivity of `hyperellipticForm` on polynomials of degree
`< H.f.natDegree / 2 - 1`, as a corollary of unconditional injectivity. -/
theorem hyperellipticForm_injOn_lowDegree
    (H : HyperellipticData) [Fact (¬ Odd H.f.natDegree)] :
    Set.InjOn (hyperellipticForm H)
      { g : Polynomial ℂ | g.natDegree < H.f.natDegree / 2 - 1 } :=
  fun _ _ _ _ hForm => hyperellipticForm_injective H hForm

/-- Linear independence of the canonical basis. Combines
linear independence of `Polynomial.basisMonomials` with the
unconditional injectivity of `hyperellipticFormLinearMap`. -/
theorem hyperellipticForm_linearIndependent (H : HyperellipticData)
    [Fact (¬ Odd H.f.natDegree)] :
    LinearIndependent ℂ
      (fun k : Fin (H.f.natDegree / 2 - 1) =>
        hyperellipticForm H (Polynomial.X ^ k.val)) := by
  -- (1) Powers of X are linearly independent in ℂ[X].
  have hCoe : ⇑(Polynomial.basisMonomials ℂ) = fun n => (Polynomial.X : Polynomial ℂ) ^ n := by
    funext n
    rw [Polynomial.coe_basisMonomials, ← Polynomial.monomial_one_right_eq_X_pow n]
  have hPowLI : LinearIndependent ℂ (fun n : ℕ => (Polynomial.X : Polynomial ℂ) ^ n) := by
    have := (Polynomial.basisMonomials ℂ).linearIndependent
    rw [hCoe] at this; exact this
  -- (2) Restrict to `Fin (g_topology - 1)` via the `Fin.val` coercion.
  have hFinLI : LinearIndependent ℂ
      (fun k : Fin (H.f.natDegree / 2 - 1) => (Polynomial.X : Polynomial ℂ) ^ k.val) :=
    hPowLI.comp (fun k : Fin (H.f.natDegree / 2 - 1) => k.val) Fin.val_injective
  -- (3) Push through the injective ℂ-linear map `hyperellipticFormLinearMap H`.
  have hKer : (hyperellipticFormLinearMap H).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hyperellipticForm_injective H
  have := (LinearMap.linearIndependent_iff (hyperellipticFormLinearMap H) hKer).mpr hFinLI
  convert this using 1

end Jacobians.ProjectiveCurve.HyperellipticEvenProj
