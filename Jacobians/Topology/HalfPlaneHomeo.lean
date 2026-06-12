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

/-- A homeomorphism restricts to a homeomorphism between complements of a
set and its image — the puncture-transport companion of `halfPlaneHomeo`
(restricting it to a half-plane minus finitely many punctures gives the
plane minus their images). -/
noncomputable def complCongr {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : X ≃ₜ Y) (s : Set X) :
    (↥sᶜ) ≃ₜ (↥(⇑φ '' s)ᶜ) :=
  (φ.image sᶜ).trans (Homeomorph.setCongr (Equiv.image_compl φ.toEquiv s))

end Jacobians.Topology
