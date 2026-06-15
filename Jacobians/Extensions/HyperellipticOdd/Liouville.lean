/-
# Liouville argument for odd-degree hyperelliptic curves

Proves that every holomorphic 1-form on `HyperellipticOdd H` equals
`hyperellipticOddForm H g` for a unique polynomial `g` with
`g.natDegree < (H.f.natDegree - 1) / 2`.

This is the odd-degree counterpart of
`Jacobians.Axioms.HyperellipticLiouville.AX_HyperellipticOneForm_eq_form`.

**Proof strategy (mirroring the even case):**
1. Define raw numerator `G(z) = form.coeff(coe a)(z) · a.val.2`
2. Show `G` extends to an entire function (removable singularities at roots)
3. Show `G` has polynomial growth at infinity
4. Extract polynomial `g` via `differentiable_eq_polynomial_of_growth`
5. Show `form = hyperellipticOddForm H g`

**Key simplification vs even case:** `HyperellipticOdd` is `OnePoint`
(no quotient), so there is no `Quotient.out` case-splitting. The single
infinity point also simplifies the growth bound.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.OddForm
import Jacobians.Axioms.HyperellipticLiouville
import Jacobians.ProjectiveCurve.Hyperelliptic.LiouvilleSupport
import Jacobians.GeneralResults.EntireGrowth
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace Jacobians.Extensions.HyperellipticOdd

open scoped Manifold ContDiff Topology
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.ProjectiveCurve.HyperellipticOdd

variable {H : HyperellipticData} [Fact (Odd H.f.natDegree)]

/-! ## Definitions -/

/-- The raw single-sheet numerator: `form.coeff(coe a)(z) · y` where
`a` is an arbitrary affine lift of `z` (chosen via `liouvilleChosenAffinePoint`). -/
noncomputable def liouvilleRawNumerator
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) (z : ℂ) : ℂ :=
  let a := liouvilleChosenAffinePoint (H := H) z
  form.coeff (coe a : HyperellipticOdd H Fact.out) z * a.val.2

/-- The removable global numerator for the odd-degree curve.
At roots of `f`, we take the punctured limit; elsewhere we use the raw value. -/
noncomputable def liouvilleRemovableNumerator
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) (z : ℂ) : ℂ :=
  if H.f.eval z = 0 then
    Filter.limUnder (nhdsWithin z {z}ᶜ) (liouvilleRawNumerator form)
  else
    liouvilleRawNumerator form z

@[simp] theorem liouvilleRemovableNumerator_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) {z : ℂ}
    (hz : H.f.eval z ≠ 0) :
    liouvilleRemovableNumerator form z = liouvilleRawNumerator form z := by
  simp [liouvilleRemovableNumerator, hz]

/-- The global two-sheet sum of chart coefficients. -/
noncomputable def liouvilleTwoSheetSum
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) (z : ℂ) : ℂ :=
  if H.f.eval z = 0 then
    0
  else
    let a := liouvilleChosenAffinePoint (H := H) z
    form.coeff (coe a : HyperellipticOdd H Fact.out) z +
      form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z

/-- The removable version of the two-sheet sum. -/
noncomputable def liouvilleTwoSheetSumRemovable
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) (z : ℂ) : ℂ :=
  if H.f.eval z = 0 then
    Filter.limUnder (nhdsWithin z {z}ᶜ) (liouvilleTwoSheetSum form)
  else
    liouvilleTwoSheetSum form z

/-! ## Part A: Anti-invariance of the raw numerator

The product `form.coeff(coe a)(z) · a.val.2` is invariant under sheet
switching `a ↦ a.invol`. This is because the chart transition between the
`affineLiftChart` at `coe a` and at `coe a.invol` (through the overlap
with the infinity chart or a branch-point chart) introduces a sign flip
in the coefficient that cancels the sign flip in `y`.

Concretely: `form.coeff(coe a)(z) = −form.coeff(coe a.invol)(z)` for
`a ∈ smoothLocusY`, so `coeff · y = (−coeff) · (−y)`.
-/

/-- Anti-invariance: the chart coefficient negates when switching sheets.
For `a ∈ smoothLocusY H`, `form.coeff (coe a) z = −form.coeff (coe a.invol) z`
on the chart target. -/
theorem form_coeff_anti_invariance
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z =
      -form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z := by
  sorry

/-- Consequence: the raw numerator is sheet-invariant. -/
theorem liouvilleRawNumerator_sheet_invariant
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z * a.val.2 =
      form.coeff (coe a.invol : HyperellipticOdd H Fact.out) z *
        a.invol.val.2 := by
  rw [form_coeff_anti_invariance form a haY hz]
  simp only [HyperellipticAffine.invol_val]
  ring

/-! ## Part B: Analyticity of the raw numerator away from roots

For `z₀` with `H.f.eval z₀ ≠ 0`, the function `z ↦ liouvilleRawNumerator form z`
is analytic at `z₀`. The proof fixes a model branch using the chart's own
inverse and shows agreement with the raw numerator via anti-invariance.
-/

/-- The model function using a fixed branch: `form.coeff(coe a₀)(z) · y₀(z)`
where `y₀` is the continuous branch selected by `a₀`'s chart. -/
noncomputable def liouvilleModelNumerator
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a₀ : HyperellipticAffine H) (ha₀Y : a₀ ∈ smoothLocusY H)
    (z : ℂ) : ℂ :=
  form.coeff (coe a₀ : HyperellipticOdd H Fact.out) z *
    (squareLocalHomeomorph (H := H) a₀ ha₀Y).symm (H.f.eval z)

/-- The raw numerator is analytic at every `z₀` where `f(z₀) ≠ 0`. -/
theorem liouvilleRawNumerator_analyticAt_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ ≠ 0) :
    AnalyticAt ℂ (liouvilleRawNumerator form) z₀ := by
  sorry

/-! ## Part C: Removable numerator is analytic off roots -/

/-- The removable numerator is analytic at every non-root point. -/
theorem liouvilleRemovableNumerator_analyticAt_of_eval_ne_zero
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z : ℂ} (hz : H.f.eval z ≠ 0) :
    AnalyticAt ℂ (liouvilleRemovableNumerator form) z := by
  have hRaw := liouvilleRawNumerator_analyticAt_of_eval_ne_zero form hz
  apply hRaw.congr
  have hEval : ∀ᶠ w in 𝓝 z, H.f.eval w ≠ 0 := by
    exact (Polynomial.continuous H.f).continuousAt.eventually_ne hz
  filter_upwards [hEval] with w hw
  exact (liouvilleRemovableNumerator_of_eval_ne_zero form hw).symm

/-! ## Part D: Branch-point limits

At each root `z₀` of `f`, the raw numerator has a removable singularity
with a finite limit. The argument: near a root, the coefficient
`form.coeff(coe a)(z)` is analytic and bounded, while `y(z) → 0`.
More precisely, the chart at a Weierstrass point uses the `y`-coordinate
(projY chart), and the form coefficient in that chart gives the limit. -/

/-- At each root of `f`, the raw numerator tends to a finite limit. -/
theorem liouvilleRawNumerator_tendsto_at_root
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    {z₀ : ℂ} (hz₀ : H.f.eval z₀ = 0) :
    ∃ L : ℂ, Filter.Tendsto (liouvilleRawNumerator form)
      (nhdsWithin z₀ {z₀}ᶜ) (𝓝 L) := by
  sorry

/-! ## Part E: Continuity of the removable numerator -/

/-- The removable numerator is continuous on all of `ℂ`. -/
theorem liouvilleRemovableNumerator_continuous
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    Continuous (liouvilleRemovableNumerator form) := by
  sorry

/-! ## Part F: Differentiability of the removable numerator

Combines: analytic off finitely many roots + continuous everywhere
→ entire (differentiable on all of `ℂ`). -/

/-- The removable numerator is an entire function. -/
theorem liouvilleRemovableNumerator_differentiable
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    Differentiable ℂ (liouvilleRemovableNumerator form) := by
  sorry

/-! ## Part G: Polynomial growth bound at infinity

Using the infinity chart of `HyperellipticOdd`, we show
`‖liouvilleRemovableNumerator form z / z^n‖ ≤ R` for large `z`,
where `n = (H.f.natDegree - 1) / 2 - 1`.

The odd-degree curve has a single infinity point (unlike the even case
with two infinity sheets), which simplifies this argument.

**Key idea:** the form coefficient at infinity is bounded near `t = 0`
(holomorphicity). The chart transition from affine to infinity gives a
Jacobian factor that, combined with the `y`-factor in the numerator,
produces the growth bound. -/

/-- The removable numerator has polynomial growth of degree
at most `(H.f.natDegree - 1) / 2 - 1`. -/
theorem liouvilleRemovableNumerator_eventually_norm_div_pow_le
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ᶠ z : ℂ in Filter.cocompact ℂ,
        ‖liouvilleRemovableNumerator form z /
            z ^ ((H.f.natDegree - 1) / 2 - 1)‖ ≤ R := by
  sorry

/-! ## Part H: Readout — recover form coefficient from removable numerator

On every smooth-Y projX chart target, the form coefficient equals
the removable numerator divided by the local square root `y`. -/

/-- On smooth-Y chart targets, the form coefficient is the removable
numerator divided by the local `y`-function. -/
theorem liouvilleRemovableNumerator_readout
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out))
    (a : HyperellipticAffine H) (haY : a ∈ smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjX (H := H) a haY).target) :
    form.coeff (coe a : HyperellipticOdd H Fact.out) z =
      liouvilleRemovableNumerator form z /
        (squareLocalHomeomorph (H := H) a haY).symm (H.f.eval z) := by
  sorry

/-! ## Part I: Main representation theorem

Every holomorphic 1-form on `HyperellipticOdd H` equals
`hyperellipticOddForm H g` for a polynomial `g` of bounded degree. -/

/-- **Level 3 for odd-degree curves.** Every holomorphic 1-form is a
canonical hyperelliptic form `hyperellipticOddForm H g`.

**Proof sketch (to be filled once Parts A–H are discharged):**
1. `liouvilleRemovableNumerator_eventually_norm_div_pow_le` (Part G)
   → growth bound on the removable numerator
2. `polynomial_growth_bound_of_eventually_norm_div_pow_le`
   → converts cocompact ratio bound to polynomial growth bound
3. `differentiable_eq_polynomial_of_growth` (from `EntireGrowth.lean`)
   → extracts polynomial `g` with `g.natDegree ≤ (d-1)/2 - 1`
4. Degree arithmetic: `≤ (d-1)/2 - 1` implies `< (d-1)/2`
5. Form equality via readout (Part H) + chart coverage -/
theorem AX_HyperellipticOddOneForm_eq_form_proof
    (form : HolomorphicOneForm (HyperellipticOdd H Fact.out)) :
    ∃ g : Polynomial ℂ, g.natDegree < (H.f.natDegree - 1) / 2 ∧
      form = hyperellipticOddForm H g := by
  sorry

end Jacobians.Extensions.HyperellipticOdd

