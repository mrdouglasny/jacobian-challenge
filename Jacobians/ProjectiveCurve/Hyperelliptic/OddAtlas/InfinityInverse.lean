import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

namespace Jacobians.ProjectiveCurve.HyperellipticOdd.InfinityInverse

open Polynomial

variable {H : HyperellipticData}

lemma leadingCoeff_ne_zero (H : HyperellipticData) : H.f.leadingCoeff ≠ 0 := by
  have h_deg : 3 ≤ H.f.natDegree := H.h_degree
  have h_ne : H.f ≠ 0 := by
    intro hc
    rw [hc] at h_deg
    simp at h_deg
  rwa [Ne, leadingCoeff_eq_zero]

lemma P_eval_zero (H : HyperellipticData) : H.f.reverse.eval 0 = H.f.leadingCoeff := by
  rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]

noncomputable def S (H : HyperellipticData) (z : ℂ) : ℂ :=
  Complex.sqrt H.f.leadingCoeff • ((H.f.leadingCoeff⁻¹ • H.f.reverse.eval z) ^ (2⁻¹ : ℂ))

lemma S_eval_zero (H : HyperellipticData) : S H 0 = Complex.sqrt H.f.leadingCoeff := by
  unfold S
  rw [P_eval_zero]
  have h_lc_ne := leadingCoeff_ne_zero H
  have h1 : H.f.leadingCoeff⁻¹ • H.f.leadingCoeff = 1 := by
    change H.f.leadingCoeff⁻¹ * H.f.leadingCoeff = 1
    exact inv_mul_cancel₀ h_lc_ne
  rw [h1]
  rw [Complex.one_cpow, smul_eq_mul, mul_one]

lemma S_analyticAt (H : HyperellipticData) : AnalyticAt ℂ (S H) 0 := by
  have h_rev : AnalyticAt ℂ (fun z => H.f.reverse.eval z) 0 :=
    H.f.reverse.differentiable.analyticAt 0
  have h_scaled : AnalyticAt ℂ (fun z => H.f.leadingCoeff⁻¹ • H.f.reverse.eval z) 0 :=
    h_rev.const_smul (c := H.f.leadingCoeff⁻¹)
  have h_two : AnalyticAt ℂ (fun _ : ℂ => (2⁻¹ : ℂ)) 0 :=
    analyticAt_const
  have h_eval : (H.f.leadingCoeff⁻¹ • H.f.reverse.eval 0) ∈ Complex.slitPlane := by
    dsimp
    rw [P_eval_zero]
    have h_lc_ne := leadingCoeff_ne_zero H
    change H.f.leadingCoeff⁻¹ * H.f.leadingCoeff ∈ Complex.slitPlane
    rw [inv_mul_cancel₀ h_lc_ne]
    exact Or.inl (by norm_num)
  have h_pow : AnalyticAt ℂ (fun z =>
      (H.f.leadingCoeff⁻¹ • H.f.reverse.eval z) ^ (2⁻¹ : ℂ)) 0 :=
    h_scaled.cpow h_two h_eval
  have h_S : AnalyticAt ℂ (fun z => Complex.sqrt H.f.leadingCoeff •
      ((H.f.leadingCoeff⁻¹ • H.f.reverse.eval z) ^ (2⁻¹ : ℂ))) 0 :=
    h_pow.const_smul (c := Complex.sqrt H.f.leadingCoeff)
  exact h_S

noncomputable def t (H : HyperellipticData) (w : ℂ) : ℂ :=
  w * S H (w ^ 2)

lemma t_analyticAt (H : HyperellipticData) : AnalyticAt ℂ (t H) 0 := by
  have h_id : AnalyticAt ℂ (fun w : ℂ => w) 0 :=
    differentiable_id.analyticAt 0
  have h_w2 : AnalyticAt ℂ (fun w : ℂ => w ^ 2) 0 :=
    (differentiable_id.pow 2).analyticAt 0
  have h_S_comp : AnalyticAt ℂ (fun w : ℂ => S H (w ^ 2)) 0 := by
    have h_comp := AnalyticAt.comp_of_eq (S_analyticAt H) h_w2 (by simp)
    change AnalyticAt ℂ (S H ∘ (fun w : ℂ => w ^ 2)) 0 at h_comp
    exact h_comp
  have h_t := h_id.mul h_S_comp
  change AnalyticAt ℂ (fun w => w * S H (w ^ 2)) 0 at h_t
  exact h_t

lemma t_hasDerivAt (H : HyperellipticData) : HasDerivAt (t H) (S H 0) 0 := by
  have h_id : HasDerivAt (fun w : ℂ => w) 1 0 := hasDerivAt_id' 0
  have h_w2 : HasDerivAt (fun w : ℂ => w ^ 2) 0 0 := by
    have h := hasDerivAt_pow 2 (0 : ℂ)
    simpa using h
  have h_S_deriv : HasDerivAt (S H) (deriv (S H) 0) 0 :=
    (S_analyticAt H).differentiableAt.hasDerivAt
  have h_S_comp : HasDerivAt (fun w : ℂ => S H (w ^ 2)) 0 0 := by
    have h := HasDerivAt.comp_of_eq 0 h_S_deriv h_w2 (by simp)
    simpa using h
  have h_t_deriv := HasDerivAt.mul h_id h_S_comp
  simpa [t] using h_t_deriv

lemma sqrt_ne_zero_of_ne_zero {x : ℂ} (h : x ≠ 0) : Complex.sqrt x ≠ 0 := by
  unfold Complex.sqrt
  rw [ne_eq, Complex.cpow_eq_zero_iff]
  have : (2⁻¹ : ℂ) ≠ 0 := by norm_num
  simp [h, this]

lemma S_eval_zero_ne_zero (H : HyperellipticData) : S H 0 ≠ 0 := by
  rw [S_eval_zero]
  exact sqrt_ne_zero_of_ne_zero (leadingCoeff_ne_zero H)

noncomputable def w (H : HyperellipticData) : ℂ → ℂ :=
  HasStrictDerivAt.localInverse (t H) (deriv (t H) 0) 0
    (t_analyticAt H).hasStrictDerivAt
    (by
      have h_deriv_eq : deriv (t H) 0 = S H 0 := (t_hasDerivAt H).deriv
      rw [h_deriv_eq]
      exact S_eval_zero_ne_zero H)

noncomputable def infinityInverseMap (H : HyperellipticData) (_h : Odd H.f.natDegree) (z : ℂ) :
    HyperellipticAffine H := by
  by_cases hz : w H z = 0
  · exact Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))
  · let x := (w H z)⁻¹ ^ 2
    let y := Complex.sqrt (H.f.eval x)
    have h_eq : y ^ 2 = H.f.eval x := by
      exact Complex.cpow_nat_inv_pow (H.f.eval x) (by decide)
    exact ⟨(x, y), h_eq⟩

end Jacobians.ProjectiveCurve.HyperellipticOdd.InfinityInverse
