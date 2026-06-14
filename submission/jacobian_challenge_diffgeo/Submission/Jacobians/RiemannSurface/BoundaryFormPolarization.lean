/-
# The box L² inner product and the polarized Green identity

HW lane (#226 follow-up; route note
`docs/planning/P10_BW_HYPERELLIPTIC_ROUTE.md`, follow-up 1).

The port's Green bridge (`boundaryForm_eq_area`) is the DIAGONAL of a
sesquilinear identity: `∮_{∂box} F̄·h dz = 2i·∬_box f̄·h` whenever
`F' = f`, `H' = h` are entire.  This file:

* packages the complex box integral `∬_box f̄·g` as `boxInner f g` with
  its sesquilinear API (`boxInner_sum_smul`), conjugate symmetry,
  diagonal positivity (via the port's `integral_normSq_pos`);
* proves the **polarized Green identity**
  `boundaryForm g F = 2i·boxInner f g` for entire data
  (`boundaryForm_eq_boxInner`), by polarization from the port's
  diagonal `boundaryForm_eq_area` — no new Green/Stokes analysis.

This is the device that converts the hyperelliptic R2 Gram word into a
statement about box-L² Grams of polynomial families, hence (with the
Cholesky factorization `Jacobians/GeneralResults/PosDefCholesky.lean`)
into bare positive-definiteness of the arc-period Gram.
-/
import Submission.KirovDolbeault.BoundaryPositivity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Jacobians

open MeasureTheory Set intervalIntegral Complex

/-! ### The box inner product -/

/-- The box L² pairing `∬_{[0,1]²} conj (f w) · g w` (conjugate-linear in
`f`, linear in `g`), over the `wCLM` coordinates of the unit box. -/
noncomputable def boxInner (f g : ℂ → ℂ) : ℂ :=
  ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
    (starRingEnd ℂ) (f (wCLM (x, y))) * g (wCLM (x, y))

/-- Inner-slice interval integrability of a continuous box integrand. -/
private lemma intervalIntegrable_slice {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ)
    (x : ℝ) : IntervalIntegrable (fun y => Φ (x, y)) volume (0:ℝ) 1 :=
  (hΦ.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

/-- Continuity of the inner parametric integral of a continuous box
integrand. -/
private lemma continuous_inner_integral {Φ : ℝ × ℝ → ℂ} (hΦ : Continuous Φ) :
    Continuous fun x => ∫ y in (0:ℝ)..1, Φ (x, y) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x y => Φ (x, y)) (hΦ.comp (continuous_fst.prodMk continuous_snd))
    0 1

/-- Double box integrals split over finite sums of continuous integrands. -/
private lemma double_integral_finset_sum {ι : Type*} (s : Finset ι)
    (Φ : ι → ℝ × ℝ → ℂ) (hΦ : ∀ i, Continuous (Φ i)) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ∑ i ∈ s, Φ i (x, y))
      = ∑ i ∈ s, ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Φ i (x, y) := by
  have hinner : ∀ x : ℝ, (∫ y in (0:ℝ)..1, ∑ i ∈ s, Φ i (x, y))
      = ∑ i ∈ s, ∫ y in (0:ℝ)..1, Φ i (x, y) := fun x =>
    intervalIntegral.integral_finsetSum fun i _ =>
      intervalIntegrable_slice (hΦ i) x
  simp_rw [hinner]
  exact intervalIntegral.integral_finsetSum fun i _ =>
    (continuous_inner_integral (hΦ i)).intervalIntegrable _ _

/-- Constants pull out of double box integrals. -/
private lemma double_integral_const_mul (c : ℂ) (Φ : ℝ × ℝ → ℂ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, c * Φ (x, y))
      = c * ∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, Φ (x, y) := by
  simp_rw [intervalIntegral.integral_const_mul]

/-- Four-way split of an interval integral of a scaled sum (free-variable
form, so the `integral_add` rewrites are syntactically unambiguous). -/
private lemma integral_four_split (A B C D : ℝ → ℂ)
    (hA : IntervalIntegrable A volume (0:ℝ) 1)
    (hB : IntervalIntegrable B volume (0:ℝ) 1)
    (hC : IntervalIntegrable C volume (0:ℝ) 1)
    (hD : IntervalIntegrable D volume (0:ℝ) 1) (μ ν ρ : ℂ) :
    (∫ t in (0:ℝ)..1, A t + (μ * B t + (ν * C t + ρ * D t)))
      = (∫ t in (0:ℝ)..1, A t) + μ * (∫ t in (0:ℝ)..1, B t)
        + ν * (∫ t in (0:ℝ)..1, C t) + ρ * ∫ t in (0:ℝ)..1, D t := by
  rw [intervalIntegral.integral_add hA
      ((hB.const_mul μ).add ((hC.const_mul ν).add (hD.const_mul ρ))),
    intervalIntegral.integral_add (hB.const_mul μ)
      ((hC.const_mul ν).add (hD.const_mul ρ)),
    intervalIntegral.integral_add (hC.const_mul ν) (hD.const_mul ρ),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- **Sesquilinear expansion** of `boxInner` over finite combinations of
continuous functions: conjugate-linear in the first slot, linear in the
second. -/
theorem boxInner_sum_smul {ι : Type*} [Fintype ι] (c d : ι → ℂ)
    (e : ι → ℂ → ℂ) (he : ∀ a, Continuous (e a)) :
    boxInner (fun z => ∑ a, c a * e a z) (fun z => ∑ b, d b * e b z)
      = ∑ a, ∑ b, (starRingEnd ℂ) (c a) * d b * boxInner (e a) (e b) := by
  unfold boxInner
  have hpt : ∀ w : ℂ,
      (starRingEnd ℂ) (∑ a, c a * e a w) * (∑ b, d b * e b w)
        = ∑ p : ι × ι, (starRingEnd ℂ) (c p.1) * d p.2 *
            ((starRingEnd ℂ) (e p.1 w) * e p.2 w) := by
    intro w
    rw [Fintype.sum_prod_type, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul]
    ring
  simp_rw [hpt]
  rw [double_integral_finset_sum Finset.univ
    (fun p : ι × ι => fun q : ℝ × ℝ => (starRingEnd ℂ) (c p.1) * d p.2 *
      ((starRingEnd ℂ) (e p.1 (wCLM q)) * e p.2 (wCLM q)))
    (fun p => continuous_const.mul
      ((continuous_star.comp ((he p.1).comp wCLM.continuous)).mul
        ((he p.2).comp wCLM.continuous)))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only
  exact double_integral_const_mul ((starRingEnd ℂ) (c a) * d b)
    (fun q => (starRingEnd ℂ) (e a (wCLM q)) * e b (wCLM q))

/-- The diagonal of `boxInner` is the (real) box norm-square integral. -/
theorem boxInner_self (f : ℂ → ℂ) :
    boxInner f f
      = ((∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, ‖f (wCLM (x, y))‖ ^ 2 : ℝ) : ℂ) := by
  unfold boxInner
  have hpt : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hinner : ∀ x : ℝ,
      (∫ y in (0:ℝ)..1, (starRingEnd ℂ) (f (wCLM (x, y))) * f (wCLM (x, y)))
        = ((∫ y in (0:ℝ)..1, ‖f (wCLM (x, y))‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun y _ => hpt _
  simp_rw [hinner]
  exact intervalIntegral.integral_ofReal

open scoped ComplexOrder in
/-- **Diagonal positivity**: `0 < boxInner f f` (a positive real, in the
complex order) for continuous `f` nonvanishing somewhere in the open box. -/
theorem boxInner_self_pos {f : ℂ → ℂ} (hf : Continuous f) (p₀ : ℝ × ℝ)
    (hp₀ : p₀ ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1) (hne : f (wCLM p₀) ≠ 0) :
    0 < boxInner f f := by
  rw [boxInner_self, Complex.zero_lt_real]
  have hcont : ContinuousOn (fun p : ℝ × ℝ => f (wMap p)) (Icc 0 1 ×ˢ Icc 0 1) := by
    rw [wMap_eq_wCLM]
    exact (hf.comp wCLM.continuous).continuousOn
  have hne' : f (wMap p₀) ≠ 0 := by rw [wMap_eq_wCLM]; exact hne
  have := integral_normSq_pos f hcont p₀ hp₀ hne'
  rwa [wMap_eq_wCLM] at this

/-- Interval integrals commute with complex conjugation. -/
private lemma intervalIntegral_conj {F : ℝ → ℂ} {a b : ℝ} :
    (∫ t in a..b, (starRingEnd ℂ) (F t)) = (starRingEnd ℂ) (∫ t in a..b, F t) := by
  simp only [intervalIntegral, integral_conj, map_sub]

/-- Conjugate symmetry of the box pairing. -/
theorem boxInner_conj_symm (f g : ℂ → ℂ) :
    (starRingEnd ℂ) (boxInner f g) = boxInner g f := by
  unfold boxInner
  rw [← intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

/-! ### Diagonal combination expansions for the polarization -/

/-- Expansion of the `boxInner` diagonal at the combination `f + μ·g`. -/
theorem boxInner_add_smul (μ : ℂ) {f g : ℂ → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    boxInner (fun z => f z + μ * g z) (fun z => f z + μ * g z)
      = boxInner f f + μ * boxInner f g
        + (starRingEnd ℂ) μ * boxInner g f
        + (starRingEnd ℂ) μ * μ * boxInner g g := by
  have he : ∀ a : Fin 2, Continuous (![f, g] a) := by
    intro a
    fin_cases a <;> simpa
  have h := boxInner_sum_smul (ι := Fin 2) ![1, μ] ![1, μ] ![f, g] he
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, map_one] at h
  linear_combination h

/-- Expansion of the `boundaryForm` diagonal at the combination
`(f + μ·g, F + μ·G)` — sesquilinearity of the boundary pairing in the
(primitive, coefficient) pair. -/
theorem boundaryForm_add_smul (μ : ℂ) {f g F G : ℂ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (hF : Continuous F) (hG : Continuous G) :
    boundaryForm (fun z => f z + μ * g z) (fun z => F z + μ * G z)
      = boundaryForm f F + μ * boundaryForm g F
        + (starRingEnd ℂ) μ * boundaryForm f G
        + (starRingEnd ℂ) μ * μ * boundaryForm g G := by
  have edge : ∀ e : ℝ → ℂ, Continuous e →
      (∫ t in (0:ℝ)..1,
          (starRingEnd ℂ) (F (e t) + μ * G (e t)) * (f (e t) + μ * g (e t)))
        = (∫ t in (0:ℝ)..1, (starRingEnd ℂ) (F (e t)) * f (e t))
          + μ * (∫ t in (0:ℝ)..1, (starRingEnd ℂ) (F (e t)) * g (e t))
          + (starRingEnd ℂ) μ *
              (∫ t in (0:ℝ)..1, (starRingEnd ℂ) (G (e t)) * f (e t))
          + (starRingEnd ℂ) μ * μ *
              (∫ t in (0:ℝ)..1, (starRingEnd ℂ) (G (e t)) * g (e t)) := by
    intro e he
    have hint : ∀ {u v : ℂ → ℂ}, Continuous u → Continuous v →
        IntervalIntegrable
          (fun t => (starRingEnd ℂ) (u (e t)) * v (e t)) volume (0:ℝ) 1 :=
      fun hu hv => ((continuous_star.comp (hu.comp he)).mul
        (hv.comp he)).intervalIntegrable _ _
    have hpt : ∀ t : ℝ,
        (starRingEnd ℂ) (F (e t) + μ * G (e t)) * (f (e t) + μ * g (e t))
          = (starRingEnd ℂ) (F (e t)) * f (e t)
            + (μ * ((starRingEnd ℂ) (F (e t)) * g (e t))
              + ((starRingEnd ℂ) μ * ((starRingEnd ℂ) (G (e t)) * f (e t))
                + (starRingEnd ℂ) μ * μ *
                    ((starRingEnd ℂ) (G (e t)) * g (e t)))) := by
      intro t
      rw [map_add, map_mul]
      ring
    exact (intervalIntegral.integral_congr fun t _ => hpt t).trans
      (integral_four_split _ _ _ _ (hint hF hf) (hint hF hg) (hint hG hf)
        (hint hG hg) μ ((starRingEnd ℂ) μ) ((starRingEnd ℂ) μ * μ))
  unfold boundaryForm
  simp only [edge (fun t => wCLM (t, 0)) (by fun_prop),
    edge (fun t => wCLM (1, t)) (by fun_prop),
    edge (fun t => wCLM (t, 1)) (by fun_prop),
    edge (fun t => wCLM (0, t)) (by fun_prop)]
  ring

/-! ### The polarized Green identity -/

/-- **Polarized Green identity** (the sesquilinear extension of the port's
diagonal `boundaryForm_eq_area`): for entire `f`, `g` with primitives `F`,
`G`, the boundary pairing is `2i` times the box L² pairing:
`∮_{∂box} F̄·g dz = 2i·∬_box f̄·g`. -/
theorem boundaryForm_eq_boxInner {f g F G : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hF : ∀ z, HasDerivAt F (f z) z) (hG : ∀ z, HasDerivAt G (g z) z) :
    boundaryForm g F = 2 * Complex.I * boxInner f g := by
  have hcf : Continuous f := hf.continuous
  have hcg : Continuous g := hg.continuous
  have hcF : Continuous F :=
    Differentiable.continuous (fun z => (hF z).differentiableAt)
  have hcG : Continuous G :=
    Differentiable.continuous (fun z => (hG z).differentiableAt)
  -- the diagonal Green identity at each combination `f + μ·g`
  have area : ∀ μ : ℂ,
      boundaryForm (fun z => f z + μ * g z) (fun z => F z + μ * G z)
        = 2 * Complex.I *
            boxInner (fun z => f z + μ * g z) (fun z => f z + μ * g z) := by
    intro μ
    have hdh : Differentiable ℂ fun z => f z + μ * g z :=
      hf.add (hg.const_mul μ)
    have h1 := boundaryForm_eq_area (U := Set.univ) (Set.subset_univ _)
      (fun z _ => (hdh z).hasDerivAt)
      (fun z _ => (hF z).add ((hG z).const_mul μ))
    have hbox : boxInner (fun z => f z + μ * g z) (fun z => f z + μ * g z)
        = ((∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
            ‖f (wCLM (x, y)) + μ * g (wCLM (x, y))‖ ^ 2 : ℝ) : ℂ) :=
      boxInner_self _
    rw [hbox]
    linear_combination (2 * Complex.I) * h1
      + boundaryForm (fun z => f z + μ * g z) (fun z => F z + μ * G z)
        * Complex.I_mul_I
  have e1 := area 1
  have e2 := area (-1)
  have e3 := area Complex.I
  have e4 := area (-Complex.I)
  rw [boundaryForm_add_smul 1 hcf hcg hcF hcG, boxInner_add_smul 1 hcf hcg] at e1
  rw [boundaryForm_add_smul (-1) hcf hcg hcF hcG,
    boxInner_add_smul (-1) hcf hcg] at e2
  rw [boundaryForm_add_smul Complex.I hcf hcg hcF hcG,
    boxInner_add_smul Complex.I hcf hcg] at e3
  rw [boundaryForm_add_smul (-Complex.I) hcf hcg hcF hcG,
    boxInner_add_smul (-Complex.I) hcf hcg] at e4
  simp only [map_one, map_neg, Complex.conj_I, one_mul, neg_mul, mul_neg,
    neg_neg] at e1 e2 e3 e4
  -- the two polarization combinations
  have hTS : boundaryForm g F + boundaryForm f G
      = 2 * Complex.I * (boxInner f g + boxInner g f) := by
    linear_combination (1/2 : ℂ) * e1 - (1/2 : ℂ) * e2
  have hTmS : 2 * Complex.I * (boundaryForm g F - boundaryForm f G)
      = -4 * (boxInner f g - boxInner g f) := by
    linear_combination e3 - e4
      + (4 * (boxInner f g - boxInner g f)) * Complex.I_mul_I
  linear_combination (1/2 : ℂ) * hTS - (Complex.I/4) * hTmS
    + ((boundaryForm g F - boundaryForm f G)/2) * Complex.I_mul_I

end Jacobians
