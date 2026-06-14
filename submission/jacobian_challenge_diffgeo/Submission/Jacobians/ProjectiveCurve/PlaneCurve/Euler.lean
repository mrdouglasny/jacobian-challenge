import Mathlib

open MvPolynomial
open BigOperators

namespace Jacobians.ProjectiveCurve

lemma eval_nsmul {σ : Type*} {R : Type*} [CommSemiring R] (x : σ → R) (n : ℕ)
    (p : MvPolynomial σ R) :
    eval x (n • p) = n • eval x p := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, eval_add, ih, succ_nsmul]

lemma euler_monomial {σ : Type*} [Fintype σ]
    (m : σ →₀ ℕ) (a : ℂ) :
    (∑ i : σ, X i * pderiv i (monomial m a)) = (∑ i : σ, m i) • monomial m a := by
  simp_rw [MvPolynomial.X_mul_pderiv_monomial]
  rw [← Finset.sum_smul]

lemma monomial_deg_of_homogeneous {σ : Type*} [Fintype σ]
    {p : MvPolynomial σ ℂ} {d : ℕ} (hp : p.IsHomogeneous d)
    {v : σ →₀ ℕ} (hv : v ∈ p.support) :
    (∑ i : σ, v i) = d := by
  have h1 := hp.degree_eq_sum_deg_support hv
  have h2 : (∑ i : σ, v i) = v.sum (fun _ n => n) := by
    exact (Finsupp.sum_fintype v (fun _ n => n) (by simp)).symm
  rw [h2]
  exact h1.symm

theorem euler_homogeneous {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℂ) (d : ℕ) (hp : p.IsHomogeneous d) :
    (∑ i : σ, X i * pderiv i p) = d • p := by
  rw [as_sum p]
  have h_pderiv : ∀ i : σ, pderiv i (∑ v ∈ p.support, monomial v (coeff v p)) =
      ∑ v ∈ p.support, pderiv i (monomial v (coeff v p)) := by
    intro i
    exact map_sum (pderiv i) (fun v => monomial v (coeff v p)) p.support
  simp_rw [h_pderiv]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h_inner : ∀ v ∈ p.support, (∑ i : σ, X i * pderiv i (monomial v (coeff v p))) =
      d • monomial v (coeff v p) := by
    intro v hv
    rw [euler_monomial]
    rw [monomial_deg_of_homogeneous hp hv]
  have h_congr : (∑ v ∈ p.support, ∑ i : σ, X i * pderiv i (monomial v (coeff v p))) =
      ∑ v ∈ p.support, d • monomial v (coeff v p) := by
    refine Finset.sum_congr rfl h_inner
  rw [h_congr]
  rw [← Finset.smul_sum]

/-- Derivative of a polynomial `p` at a point `v`, as a continuous linear map. -/
noncomputable def fderiv_poly {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) (v : σ → ℂ) :
    (σ → ℂ) →L[ℂ] ℂ :=
  ∑ i : σ, (pderiv i p).eval v • ContinuousLinearMap.proj i

lemma fderiv_poly_mul_X {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℂ) (n : σ) (v : σ → ℂ) :
    fderiv_poly (p * X n) v = p.eval v • ContinuousLinearMap.proj n + v n • fderiv_poly p v := by
  classical
  ext w
  simp only [fderiv_poly, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, pderiv_mul,
    eval_add, eval_mul, eval_X, smul_eq_mul]
  have h_lhs :
      (∑ i : σ, ((pderiv i p).eval v * v n + p.eval v * (pderiv i (X n)).eval v) * w i) =
      (∑ i : σ, v n * ((pderiv i p).eval v * w i)) +
      (∑ i : σ, p.eval v * ((pderiv i (X n)).eval v * w i)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [h_lhs]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h_pderiv_eval : ∀ i : σ, (pderiv i (X n)).eval v = if i = n then 1 else 0 := by
    intro i
    rw [pderiv_X]
    split_ifs with h
    · subst h; simp
    · simp [h]
  have h_sum2 : (∑ i : σ, (pderiv i (X n)).eval v * w i) = w n := by
    simp_rw [h_pderiv_eval]
    simp
  rw [h_sum2]
  ring

theorem hasFDerivAt_eval {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℂ) (v : σ → ℂ) :
    HasFDerivAt (fun x => p.eval x) (fderiv_poly p v) v := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h_zero : fderiv_poly (C a) v = 0 := by
      ext w
      simp [fderiv_poly]
    rw [h_zero]
    simp only [eval_C]
    exact hasFDerivAt_const (𝕜 := ℂ) a v
  | add p q hp hq =>
    have h_add : fderiv_poly (p + q) v = fderiv_poly p v + fderiv_poly q v := by
      ext w
      simp [fderiv_poly, add_smul, Finset.sum_add_distrib]
    rw [h_add]
    simp only [eval_add]
    exact hp.add hq
  | mul_X p n hp =>
    have h_mul : fderiv_poly (p * X n) v =
        p.eval v • ContinuousLinearMap.proj n + v n • fderiv_poly p v := by
      exact fderiv_poly_mul_X p n v
    rw [h_mul]
    have h_prod := HasFDerivAt.mul hp
      (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj n))
    simp only [eval_mul, eval_X]
    exact h_prod

end Jacobians.ProjectiveCurve
