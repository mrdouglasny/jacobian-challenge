/-
# G3 toolkit — the open half-plane is homeomorphic to the plane

Issue #171 / `docs/planning/B1_GENERATION_ROUTE.md` rung **G3** (toolkit
half).  The separating-line induction presents each side of a split
`ℂ ∖ T` as a half-plane minus its punctures; to apply the induction
hypothesis (and the G2 cell computation) the half-plane must be identified
with the full plane.  This file provides the explicit homeomorphism

  `halfPlaneHomeo c : {z : ℂ // z.re < c} ≃ₜ ℂ`,
  `z ↦ ⟨−log (c − Re z), Im z⟩`,  inverse `w ↦ ⟨c − exp (−Re w), Im w⟩`

— an order isomorphism in the real part, the identity in the imaginary
part.  Mathlib-only imports.
-/
import Mathlib

namespace Jacobians.Topology

open Set Complex

/-- **The open half-plane `Re z < c` is homeomorphic to `ℂ`**, by
`z ↦ ⟨−log (c − Re z), Im z⟩` componentwise. -/
noncomputable def halfPlaneHomeo (c : ℝ) : {z : ℂ // z.re < c} ≃ₜ ℂ where
  toFun z := Complex.mk (-Real.log (c - (z : ℂ).re)) (z : ℂ).im
  invFun w := ⟨Complex.mk (c - Real.exp (-w.re)) w.im, by
    have hexp : (0 : ℝ) < Real.exp (-w.re) := Real.exp_pos _
    show c - Real.exp (-w.re) < c
    linarith⟩
  left_inv z := by
    apply Subtype.ext
    apply Complex.ext
    · show c - Real.exp (-(-Real.log (c - (z : ℂ).re))) = (z : ℂ).re
      rw [neg_neg, Real.exp_log (by linarith [z.2])]
      ring
    · rfl
  right_inv w := by
    apply Complex.ext
    · show -Real.log (c - (c - Real.exp (-w.re))) = w.re
      rw [show c - (c - Real.exp (-w.re)) = Real.exp (-w.re) by ring,
        Real.log_exp, neg_neg]
    · rfl
  continuous_toFun := by
    simp only [Complex.mk_eq_add_mul_I]
    refine Continuous.add ?_ ?_
    · refine Complex.continuous_ofReal.comp ?_
      refine Continuous.neg ?_
      refine ContinuousOn.comp_continuous Real.continuousOn_log
        (continuous_const.sub
          (Complex.continuous_re.comp continuous_subtype_val)) ?_
      intro z
      have := z.2
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      positivity
    · exact (Complex.continuous_ofReal.comp
        (Complex.continuous_im.comp continuous_subtype_val)).mul continuous_const
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    simp only [Complex.mk_eq_add_mul_I]
    refine Continuous.add ?_ ?_
    · exact Complex.continuous_ofReal.comp
        (continuous_const.sub (Real.continuous_exp.comp Complex.continuous_re.neg))
    · exact (Complex.continuous_ofReal.comp Complex.continuous_im).mul
        continuous_const

/-- Negation maps the open right half-plane `c < Re z` onto the open left
half-plane `Re z < -c`. -/
noncomputable def negHalfPlaneHomeo (c : ℝ) :
    {z : ℂ // c < z.re} ≃ₜ {z : ℂ // z.re < -c} where
  toFun z := ⟨-(z : ℂ), by
    have := z.2
    simp only [Complex.neg_re]
    linarith⟩
  invFun w := ⟨-(w : ℂ), by
    have := w.2
    simp only [Complex.neg_re]
    linarith⟩
  left_inv z := Subtype.ext (neg_neg _)
  right_inv w := Subtype.ext (neg_neg _)
  continuous_toFun := (continuous_subtype_val.neg).subtype_mk _
  continuous_invFun := (continuous_subtype_val.neg).subtype_mk _

/-- **The open right half-plane `c < Re z` is homeomorphic to `ℂ`** —
the mirror companion of `halfPlaneHomeo`, for the right side of the
separating-line split. -/
noncomputable def halfPlaneHomeoGT (c : ℝ) : {z : ℂ // c < z.re} ≃ₜ ℂ :=
  (negHalfPlaneHomeo c).trans (halfPlaneHomeo (-c))

section PuncturedBall

/-- **The punctured open ball is homeomorphic to the punctured plane**,
radially: `z ↦ c + (z-c)/(R-‖z-c‖)`, fixing the puncture `c` at the
center.  The radial profile `ρ ↦ ρ/(R-ρ)` is an order isomorphism
`(0,R) ≃ (0,∞)` — the disk companion of `halfPlaneHomeo`. -/
noncomputable def puncturedBallHomeo (c : ℂ) (R : ℝ) (hR : 0 < R) :
    {z : ℂ // z ∈ Metric.ball c R ∧ z ≠ c} ≃ₜ {w : ℂ // w ≠ c} where
  toFun z := ⟨c + (z.1 - c) * (((R - ‖z.1 - c‖)⁻¹ : ℝ) : ℂ), by
    intro heq
    have hz : z.1 - c ≠ 0 := sub_ne_zero.mpr z.2.2
    have hball : ‖z.1 - c‖ < R := by
      have hb := z.2.1
      rwa [Metric.mem_ball, Complex.dist_eq] at hb
    have h0 : (z.1 - c) * (((R - ‖z.1 - c‖)⁻¹ : ℝ) : ℂ) = 0 := by
      linear_combination heq
    rcases mul_eq_zero.mp h0 with h | h
    · exact hz h
    · rw [Complex.ofReal_eq_zero] at h
      exact (ne_of_gt (by positivity : (0:ℝ) < (R - ‖z.1 - c‖)⁻¹)) h⟩
  invFun w := ⟨c + (w.1 - c) * (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ), by
    have hw : w.1 - c ≠ 0 := sub_ne_zero.mpr w.2
    have hnorm0 : (0 : ℝ) < ‖w.1 - c‖ := norm_pos_iff.mpr hw
    have hfac : (0 : ℝ) < R * (1 + ‖w.1 - c‖)⁻¹ := by positivity
    constructor
    · rw [Metric.mem_ball, Complex.dist_eq]
      have harg : c + (w.1 - c) * (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ) - c
          = (w.1 - c) * (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ) := by ring
      rw [harg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hfac]
      rw [show ‖w.1 - c‖ * (R * (1 + ‖w.1 - c‖)⁻¹)
          = R * (‖w.1 - c‖ * (1 + ‖w.1 - c‖)⁻¹) by ring]
      have h1 : ‖w.1 - c‖ * (1 + ‖w.1 - c‖)⁻¹ < 1 := by
        rw [mul_inv_lt_iff₀ (by positivity), one_mul]
        linarith
      calc R * (‖w.1 - c‖ * (1 + ‖w.1 - c‖)⁻¹) < R * 1 :=
            mul_lt_mul_of_pos_left h1 hR
        _ = R := mul_one R
    · intro heq
      have h0 : (w.1 - c) * (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ) = 0 := by
        linear_combination heq
      rcases mul_eq_zero.mp h0 with h | h
      · exact hw h
      · rw [Complex.ofReal_eq_zero] at h
        exact (ne_of_gt hfac) h⟩
  left_inv z := by
    apply Subtype.ext
    have hz : z.1 - c ≠ 0 := sub_ne_zero.mpr z.2.2
    have hball : ‖z.1 - c‖ < R := by
      have hb := z.2.1
      rwa [Metric.mem_ball, Complex.dist_eq] at hb
    have hRρ : (0 : ℝ) < R - ‖z.1 - c‖ := by linarith
    have hsub : c + (z.1 - c) * (((R - ‖z.1 - c‖)⁻¹ : ℝ) : ℂ) - c
        = (z.1 - c) * (((R - ‖z.1 - c‖)⁻¹ : ℝ) : ℂ) := by ring
    show c + (c + (z.1 - c) * (((R - ‖z.1 - c‖)⁻¹ : ℝ) : ℂ) - c)
        * (((R * (1 + ‖c + (z.1 - c) * (((R - ‖z.1 - c‖)⁻¹ : ℝ) : ℂ) - c‖)⁻¹
            : ℝ)) : ℂ) = z.1
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < (R - ‖z.1 - c‖)⁻¹)]
    have hcancel : (((R - ‖z.1 - c‖)⁻¹ : ℝ) : ℂ)
        * (((R * (1 + ‖z.1 - c‖ * (R - ‖z.1 - c‖)⁻¹)⁻¹ : ℝ)) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      have h1 : 1 + ‖z.1 - c‖ * (R - ‖z.1 - c‖)⁻¹
          = R * (R - ‖z.1 - c‖)⁻¹ := by
        field_simp
        ring
      rw [h1]
      rw [show ((R - ‖z.1 - c‖)⁻¹ * (R * (R * (R - ‖z.1 - c‖)⁻¹)⁻¹) : ℝ)
          = (R - ‖z.1 - c‖)⁻¹ * (R - ‖z.1 - c‖) * (R * R⁻¹) by
        rw [mul_inv, inv_inv]; ring]
      rw [inv_mul_cancel₀ (ne_of_gt hRρ), mul_inv_cancel₀ (ne_of_gt hR),
        one_mul, Complex.ofReal_one]
    linear_combination (z.1 - c) * hcancel
  right_inv w := by
    apply Subtype.ext
    have hw : w.1 - c ≠ 0 := sub_ne_zero.mpr w.2
    have hnorm0 : (0 : ℝ) < ‖w.1 - c‖ := norm_pos_iff.mpr hw
    have hfac : (0 : ℝ) < R * (1 + ‖w.1 - c‖)⁻¹ := by positivity
    have hsub : c + (w.1 - c) * (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ) - c
        = (w.1 - c) * (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ) := by ring
    show c + (c + (w.1 - c) * (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ) - c)
        * (((R - ‖c + (w.1 - c) * (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ) - c‖)⁻¹
            : ℝ) : ℂ) = w.1
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hfac]
    have hcancel : (((R * (1 + ‖w.1 - c‖)⁻¹ : ℝ)) : ℂ)
        * (((R - ‖w.1 - c‖ * (R * (1 + ‖w.1 - c‖)⁻¹))⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul]
      have h1 : (0 : ℝ) < 1 + ‖w.1 - c‖ := by positivity
      have hden : R - ‖w.1 - c‖ * (R * (1 + ‖w.1 - c‖)⁻¹)
          = R * (1 + ‖w.1 - c‖)⁻¹ := by
        field_simp
        ring
      rw [hden, mul_inv_cancel₀ (ne_of_gt hfac), Complex.ofReal_one]
    linear_combination (w.1 - c) * hcancel
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_const.add (Continuous.mul ?_ ?_)
    · exact continuous_subtype_val.sub continuous_const
    · refine Complex.continuous_ofReal.comp (Continuous.inv₀ ?_ ?_)
      · exact continuous_const.sub
          ((continuous_subtype_val.sub continuous_const).norm)
      · intro z
        have hball : ‖z.1 - c‖ < R := by
          have hb := z.2.1
          rwa [Metric.mem_ball, Complex.dist_eq] at hb
        intro h0
        have hRz : R = ‖z.1 - c‖ := by linarith [sub_eq_zero.mp h0]
        linarith
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_const.add (Continuous.mul ?_ ?_)
    · exact continuous_subtype_val.sub continuous_const
    · refine Complex.continuous_ofReal.comp
        (continuous_const.mul (Continuous.inv₀ ?_ ?_))
      · exact continuous_const.add
          ((continuous_subtype_val.sub continuous_const).norm)
      · intro w
        positivity

end PuncturedBall

/-- A homeomorphism restricts to a homeomorphism between complements of a
set and its image — the puncture-transport companion of `halfPlaneHomeo`
(restricting it to a half-plane minus finitely many punctures gives the
plane minus their images). -/
noncomputable def complCongr {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : X ≃ₜ Y) (s : Set X) :
    (↥sᶜ) ≃ₜ (↥(⇑φ '' s)ᶜ) :=
  (φ.image sᶜ).trans (Homeomorph.setCongr (Equiv.image_compl φ.toEquiv s))

end Jacobians.Topology
