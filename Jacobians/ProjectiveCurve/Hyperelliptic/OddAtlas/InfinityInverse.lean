import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Mathlib.Analysis.Analytic.Inverse
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

namespace Jacobians.ProjectiveCurve.HyperellipticOdd.InfinityInverse

open Polynomial
open scoped ContDiff

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

lemma t_deriv_ne_zero (H : HyperellipticData) : deriv (t H) 0 ≠ 0 := by
  have h_deriv_eq : deriv (t H) 0 = S H 0 := (t_hasDerivAt H).deriv
  rw [h_deriv_eq]
  exact S_eval_zero_ne_zero H

noncomputable def tLocalHomeomorph_hd (H : HyperellipticData) :
    HasStrictFDerivAt (t H) (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv (t H) 0) (t_deriv_ne_zero H)) : ℂ →L[ℂ] ℂ) 0 :=
  ((t_analyticAt H).hasStrictDerivAt).hasStrictFDerivAt

def slitPlane : Set ℂ := {z : ℂ | 0 < z.re ∨ z.im ≠ 0}

lemma isOpen_slitPlane : IsOpen slitPlane := by
  have h1 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
  exact IsOpen.union h1 h2

def U_S (H : HyperellipticData) : Set ℂ :=
  (fun w : ℂ => H.f.leadingCoeff⁻¹ * H.f.reverse.eval (w ^ 2)) ⁻¹' slitPlane

lemma isOpen_U_S (H : HyperellipticData) : IsOpen (U_S H) := by
  have h_cont : Continuous (fun w : ℂ => H.f.leadingCoeff⁻¹ * H.f.reverse.eval (w ^ 2)) := by
    refine continuous_const.mul ?_
    exact H.f.reverse.continuous.comp (continuous_pow 2)
  exact IsOpen.preimage h_cont isOpen_slitPlane

lemma mem_U_S_zero (H : HyperellipticData) : (0 : ℂ) ∈ U_S H := by
  simp [U_S, P_eval_zero]
  have h_lc_ne := leadingCoeff_ne_zero H
  rw [inv_mul_cancel₀ h_lc_ne]
  left
  norm_num

lemma S_analyticAt_of_mem (H : HyperellipticData) {w : ℂ} (hw : w ∈ U_S H) :
    AnalyticAt ℂ (fun z => S H (z ^ 2)) w := by
  have h_sq : AnalyticAt ℂ (fun z => z ^ 2) w := by
    have h_eq : (fun z : ℂ => z ^ 2) = (fun z => z * z) := by ext; ring
    rw [h_eq]
    exact analyticAt_id.mul analyticAt_id
  have h_rev : AnalyticAt ℂ (fun z => H.f.reverse.eval (z ^ 2)) w :=
    AnalyticAt.comp (f := fun z => z ^ 2)
      (AnalyticOnNhd.eval_polynomial H.f.reverse (w ^ 2) (Set.mem_univ (w ^ 2))) h_sq
  have h_scaled : AnalyticAt ℂ (fun z => H.f.leadingCoeff⁻¹ * H.f.reverse.eval (z ^ 2)) w :=
    analyticAt_const.mul h_rev
  have h_two : AnalyticAt ℂ (fun _ : ℂ => (2⁻¹ : ℂ)) w :=
    analyticAt_const
  have h_pow : AnalyticAt ℂ (fun z =>
      (H.f.leadingCoeff⁻¹ * H.f.reverse.eval (z ^ 2)) ^ (2⁻¹ : ℂ)) w := by
    exact AnalyticAt.cpow h_scaled h_two hw
  exact analyticAt_const.mul h_pow

lemma t_analyticAt_of_mem (H : HyperellipticData) {w : ℂ} (hw : w ∈ U_S H) :
    AnalyticAt ℂ (t H) w := by
  have h_id : AnalyticAt ℂ (fun z => z) w := analyticAt_id
  have h_S := S_analyticAt_of_mem H hw
  exact h_id.mul h_S

lemma t_contDiffOn_U_S (H : HyperellipticData) :
    ContDiffOn ℂ ω (t H) (U_S H) := by
  intro w hw
  have h_ana := t_analyticAt_of_mem H hw
  rw [contDiffWithinAt_iff_contDiffAt ((isOpen_U_S H).mem_nhds hw)]
  exact h_ana.contDiffAt

noncomputable def tLocalHomeomorph (H : HyperellipticData) : OpenPartialHomeomorph ℂ ℂ :=
  let e := HasStrictFDerivAt.toOpenPartialHomeomorph (t H) (tLocalHomeomorph_hd H)
  e.restrOpen (U_S H) (isOpen_U_S H)

noncomputable def w (H : HyperellipticData) (z : ℂ) : ℂ :=
  (tLocalHomeomorph H).symm z

lemma tLocalHomeomorph_coe (H : HyperellipticData) :
    (↑(tLocalHomeomorph H) : ℂ → ℂ) = t H := by
  rw [tLocalHomeomorph, OpenPartialHomeomorph.coe_restrOpen]
  exact HasStrictFDerivAt.toOpenPartialHomeomorph_coe (tLocalHomeomorph_hd H)

lemma tLocalHomeomorph_source (H : HyperellipticData) :
    (0 : ℂ) ∈ (tLocalHomeomorph H).source := by
  have h_hd := tLocalHomeomorph_hd H
  have h_e_source : (0 : ℂ) ∈ (HasStrictFDerivAt.toOpenPartialHomeomorph (t H) h_hd).source :=
    HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source h_hd
  exact ⟨h_e_source, mem_U_S_zero H⟩

lemma tLocalHomeomorph_apply_zero (H : HyperellipticData) :
    tLocalHomeomorph H 0 = 0 := by
  have h_coe := tLocalHomeomorph_coe H
  have h_app : (tLocalHomeomorph H) 0 = (↑(tLocalHomeomorph H) : ℂ → ℂ) 0 := rfl
  rw [h_app, h_coe]
  unfold t
  simp

lemma tLocalHomeomorph_target_zero (H : HyperellipticData) :
    (0 : ℂ) ∈ (tLocalHomeomorph H).target := by
  have h := (tLocalHomeomorph H).map_source (tLocalHomeomorph_source H)
  rw [tLocalHomeomorph_apply_zero] at h
  exact h

lemma tLocalHomeomorph_right_inv (H : HyperellipticData) {z : ℂ} (hz : z ∈ (tLocalHomeomorph H).target) :
    t H ((tLocalHomeomorph H).symm z) = z := by
  have h := (tLocalHomeomorph H).right_inv hz
  have h_coe := tLocalHomeomorph_coe H
  have h_app : (tLocalHomeomorph H) ((tLocalHomeomorph H).symm z) = (↑(tLocalHomeomorph H) : ℂ → ℂ) ((tLocalHomeomorph H).symm z) := rfl
  rw [h_app, h_coe] at h
  exact h

lemma y_sq_eq_eval_x (h_odd : Odd H.f.natDegree) (z : ℂ) (hz : z ∈ (tLocalHomeomorph H).target) (hz0 : z ≠ 0) :
    (z * (((tLocalHomeomorph H).symm z)⁻¹ ^ 2) ^ (H.genus + 1)) ^ 2 = H.f.eval (((tLocalHomeomorph H).symm z)⁻¹ ^ 2) := by
  set W := (tLocalHomeomorph H).symm z
  have hw : W ≠ 0 := by
    intro hW0
    have h_tz := tLocalHomeomorph_right_inv H hz
    change (tLocalHomeomorph H).symm z = 0 at hW0
    rw [hW0] at h_tz
    unfold t at h_tz
    simp at h_tz
    exact hz0 h_tz.symm
  have h_tz := tLocalHomeomorph_right_inv H hz
  have hz_eq : z = W * S H (W ^ 2) := h_tz.symm
  rw [hz_eq]
  have h_deg : H.f.natDegree = 2 * H.genus + 1 := by
    rcases h_odd with ⟨k, hk⟩
    dsimp [HyperellipticData.genus]
    rw [hk]
    simp
  have hpow1 : ((W⁻¹ : ℂ) ^ 2) ^ (H.genus + 1) = W⁻¹ ^ (2 * H.genus + 2) := by
    rw [← pow_mul]
    ring
  rw [hpow1]
  have h_w_inv : W * W⁻¹ = 1 := mul_inv_cancel₀ hw
  rw [show 2 * H.genus + 2 = (2 * H.genus + 1) + 1 by ring]
  rw [pow_add, pow_one]
  have hpow2 : W * S H (W ^ 2) * (W⁻¹ ^ (2 * H.genus + 1) * W⁻¹) = S H (W ^ 2) * W⁻¹ ^ (2 * H.genus + 1) := by
    calc W * S H (W ^ 2) * (W⁻¹ ^ (2 * H.genus + 1) * W⁻¹)
      _ = S H (W ^ 2) * W⁻¹ ^ (2 * H.genus + 1) * (W * W⁻¹) := by ring
      _ = S H (W ^ 2) * W⁻¹ ^ (2 * H.genus + 1) * 1 := by rw [h_w_inv]
      _ = S H (W ^ 2) * W⁻¹ ^ (2 * H.genus + 1) := by ring
  rw [hpow2]
  have hpow3 : (S H (W ^ 2) * W⁻¹ ^ (2 * H.genus + 1)) ^ 2 = (S H (W ^ 2)) ^ 2 * W⁻¹ ^ (4 * H.genus + 2) := by
    rw [mul_pow, ← pow_mul]
    congr 2
    ring
  rw [hpow3]
  have hS_sq : (S H (W ^ 2)) ^ 2 = (H.f.reverse).eval (W ^ 2) := by
    unfold S
    rw [smul_eq_mul, smul_eq_mul]
    rw [mul_pow]
    have h_sqrt_sq := Complex.cpow_nat_inv_pow (H.f.leadingCoeff) (n := 2) (by decide)
    change ((Complex.sqrt H.f.leadingCoeff) ^ 2) = H.f.leadingCoeff at h_sqrt_sq
    rw [h_sqrt_sq]
    have h_pow2 := Complex.cpow_nat_inv_pow (H.f.leadingCoeff⁻¹ * H.f.reverse.eval (W ^ 2)) (n := 2) (by decide)
    change ((H.f.leadingCoeff⁻¹ * eval (W ^ 2) H.f.reverse) ^ (2⁻¹ : ℂ)) ^ 2 = H.f.leadingCoeff⁻¹ * eval (W ^ 2) H.f.reverse at h_pow2
    rw [h_pow2]
    rw [← mul_assoc, mul_inv_cancel₀ (leadingCoeff_ne_zero H), one_mul]
  rw [hS_sq]
  have h_w2 : W ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have h_rev := reverse_eval_inv_eq (H := H) (W ^ 2)⁻¹ (by exact inv_ne_zero h_w2)
  rw [show (W ^ 2)⁻¹⁻¹ = W ^ 2 by rw [inv_inv]] at h_rev
  rw [show (W ^ 2)⁻¹ = W⁻¹ ^ 2 by rw [inv_pow]] at h_rev
  rw [h_rev]
  have h_pow_eq : W⁻¹ ^ (4 * H.genus + 2) = (W⁻¹ ^ 2) ^ H.f.natDegree := by
    rw [show 4 * H.genus + 2 = 2 * H.f.natDegree by omega]
    rw [← pow_mul]
  rw [h_pow_eq]
  have h_mul_cancel : (W ^ 2) ^ H.f.natDegree * (W⁻¹ ^ 2) ^ H.f.natDegree = 1 := by
    rw [← mul_pow]
    rw [show W ^ 2 * W⁻¹ ^ 2 = (W * W⁻¹) ^ 2 by ring]
    rw [h_w_inv, one_pow, one_pow]
  calc eval (W⁻¹ ^ 2) H.f * (W ^ 2) ^ H.f.natDegree * (W⁻¹ ^ 2) ^ H.f.natDegree
    _ = eval (W⁻¹ ^ 2) H.f * ((W ^ 2) ^ H.f.natDegree * (W⁻¹ ^ 2) ^ H.f.natDegree) := by ring
    _ = eval (W⁻¹ ^ 2) H.f * 1 := by rw [h_mul_cancel]
    _ = eval (W⁻¹ ^ 2) H.f := mul_one _

noncomputable def infinityInverseMap (H : HyperellipticData) (h : Odd H.f.natDegree) (z : ℂ) :
    HyperellipticAffine H := by
  by_cases hz : z ∈ (tLocalHomeomorph H).target ∧ z ≠ 0
  · let W := (tLocalHomeomorph H).symm z
    let x := W⁻¹ ^ 2
    let y := z * x ^ (H.genus + 1)
    have h_eq : y ^ 2 = H.f.eval x := by
      exact y_sq_eq_eval_x h z hz.1 hz.2
    exact ⟨(x, y), h_eq⟩
  · exact Classical.choice (inferInstance : Nonempty (HyperellipticAffine H))

lemma S_sq_eq_eval_rev (H : HyperellipticData) (u : ℂ) : (S H u) ^ 2 = (H.f.reverse).eval u := by
  unfold S
  rw [smul_eq_mul, smul_eq_mul]
  rw [mul_pow]
  have h_sqrt_sq := Complex.cpow_nat_inv_pow (H.f.leadingCoeff) (n := 2) (by decide)
  change ((Complex.sqrt H.f.leadingCoeff) ^ 2) = H.f.leadingCoeff at h_sqrt_sq
  rw [h_sqrt_sq]
  have h_pow2 := Complex.cpow_nat_inv_pow (H.f.leadingCoeff⁻¹ * H.f.reverse.eval u) (n := 2) (by decide)
  change ((H.f.leadingCoeff⁻¹ * eval u H.f.reverse) ^ (2⁻¹ : ℂ)) ^ 2 = H.f.leadingCoeff⁻¹ * eval u H.f.reverse at h_pow2
  rw [h_pow2]
  rw [← mul_assoc]
  have h_lc_ne := leadingCoeff_ne_zero H
  rw [mul_inv_cancel₀ h_lc_ne, one_mul]

lemma w_q_sq_eq_inv (h : Odd H.f.natDegree) (q : HyperellipticAffine H)
    (hq1 : q.val.1 ≠ 0) (hq2 : q.val.2 ≠ 0) :
    (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (S H q.val.1⁻¹)⁻¹) ^ 2 = q.val.1⁻¹ := by
  have h_deg : H.f.natDegree = 2 * H.genus + 1 := by
    rcases h with ⟨k, hk⟩
    dsimp [HyperellipticData.genus]
    rw [hk]
    simp
  have h_rev := reverse_eval_inv_eq (H := H) q.val.1 hq1
  have h_S_sq := S_sq_eq_eval_rev H q.val.1⁻¹
  have h_y_sq : q.val.2 ^ 2 = H.f.eval q.val.1 := q.property
  have h_f_eval_nz : H.f.eval q.val.1 ≠ 0 := by
    intro hc
    have hc2 : q.val.2 ^ 2 = 0 := by rw [h_y_sq, hc]
    exact hq2 (sq_eq_zero_iff.mp hc2)
  have h_rev_nz : (H.f.reverse).eval q.val.1⁻¹ ≠ 0 := by
    rw [h_rev]
    exact mul_ne_zero h_f_eval_nz (pow_ne_zero _ (inv_ne_zero hq1))
  have h_S_nz : S H q.val.1⁻¹ ≠ 0 := by
    intro hc
    have hc2 : (S H q.val.1⁻¹) ^ 2 = 0 := by rw [hc, zero_pow (by decide)]
    rw [h_S_sq] at hc2
    exact h_rev_nz hc2
  have h_S_inv_sq : (S H q.val.1⁻¹)⁻¹ ^ 2 = ((S H q.val.1⁻¹) ^ 2)⁻¹ := inv_pow (S H q.val.1⁻¹) 2
  calc (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (S H q.val.1⁻¹)⁻¹) ^ 2
    _ = q.val.2 ^ 2 * (q.val.1⁻¹ ^ (H.genus + 1)) ^ 2 * (S H q.val.1⁻¹)⁻¹ ^ 2 := by ring
    _ = H.f.eval q.val.1 * q.val.1⁻¹ ^ (2 * H.genus + 2) * ((S H q.val.1⁻¹) ^ 2)⁻¹ := by
      rw [h_y_sq, h_S_inv_sq]
      congr 1
      rw [← pow_mul]
      ring
    _ = H.f.eval q.val.1 * q.val.1⁻¹ ^ (2 * H.genus + 2) * ((H.f.reverse).eval q.val.1⁻¹)⁻¹ := by rw [h_S_sq]
    _ = H.f.eval q.val.1 * q.val.1⁻¹ ^ (2 * H.genus + 2) * (H.f.eval q.val.1 * q.val.1⁻¹ ^ H.f.natDegree)⁻¹ := by rw [h_rev]
    _ = H.f.eval q.val.1 * q.val.1⁻¹ ^ (2 * H.genus + 2) * ((H.f.eval q.val.1)⁻¹ * (q.val.1⁻¹ ^ (2 * H.genus + 1))⁻¹) := by
      rw [h_deg, mul_inv]
    _ = (H.f.eval q.val.1 * (H.f.eval q.val.1)⁻¹) * (q.val.1⁻¹ ^ (2 * H.genus + 2) * (q.val.1⁻¹ ^ (2 * H.genus + 1))⁻¹) := by ring
    _ = 1 * (q.val.1⁻¹ ^ (2 * H.genus + 2) * (q.val.1⁻¹ ^ (2 * H.genus + 1))⁻¹) := by
      rw [mul_inv_cancel₀ h_f_eval_nz]
    _ = q.val.1⁻¹ ^ (2 * H.genus + 2) * (q.val.1⁻¹ ^ (2 * H.genus + 1))⁻¹ := by rw [one_mul]
    _ = q.val.1⁻¹ := by
      have h1 : q.val.1⁻¹ ^ (2 * H.genus + 2) = q.val.1⁻¹ ^ (2 * H.genus + 1) * q.val.1⁻¹ := by
        rw [show 2 * H.genus + 2 = (2 * H.genus + 1) + 1 by ring, pow_succ]
      have h_pow_nz : q.val.1⁻¹ ^ (2 * H.genus + 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hq1)
      calc q.val.1⁻¹ ^ (2 * H.genus + 2) * (q.val.1⁻¹ ^ (2 * H.genus + 1))⁻¹
        _ = (q.val.1⁻¹ ^ (2 * H.genus + 1) * q.val.1⁻¹) * (q.val.1⁻¹ ^ (2 * H.genus + 1))⁻¹ := by rw [h1]
        _ = q.val.1⁻¹ * (q.val.1⁻¹ ^ (2 * H.genus + 1) * (q.val.1⁻¹ ^ (2 * H.genus + 1))⁻¹) := by ring
        _ = q.val.1⁻¹ * 1 := by rw [mul_inv_cancel₀ h_pow_nz]
        _ = q.val.1⁻¹ := mul_one _

end Jacobians.ProjectiveCurve.HyperellipticOdd.InfinityInverse
