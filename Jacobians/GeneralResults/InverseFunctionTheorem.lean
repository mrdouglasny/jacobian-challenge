import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open scoped Topology ContDiff NNReal

namespace Jacobians.GeneralResults

lemma norm_sub_le_of_approx {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {f' : E →L[ℂ] F} {s : Set E} {c : ℝ≥0} (hs : IsOpen s)
    (hf : ApproximatesLinearOn f f' s c) {z : E} (hz : z ∈ s)
    {df : E →L[ℂ] F} (hdf : HasFDerivAt f df z) :
    ‖df - f'‖ ≤ c := by
  have h_lip : LipschitzOnWith c (f - ⇑f') s := hf.lipschitzOnWith
  have h_deriv : HasFDerivAt (f - ⇑f') (df - f') z := hdf.sub f'.hasFDerivAt
  exact h_deriv.le_of_lipschitzOn (hs.mem_nhds hz) h_lip

noncomputable def equivOfApproxLinear {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f' : E ≃L[ℂ] F} {df : E →L[ℂ] F} {c : ℝ≥0}
    (hc : c < ‖(f'.symm : F →L[ℂ] E)‖₊⁻¹)
    (h_approx : ∀ x y : E, ‖df x - df y - f' (x - y)‖ ≤ c * ‖x - y‖) :
    E ≃L[ℂ] F := by
  have h_linear : ApproximatesLinearOn df (f' : E →L[ℂ] F) Set.univ c := by
    intro x _ y _
    exact h_approx x y
  have h_inj : Function.Injective df := by
    have h_restrict := h_linear.injective (Or.inr hc)
    intro x y hxy
    have h1 : Set.restrict Set.univ df ⟨x, Set.mem_univ x⟩ =
        Set.restrict Set.univ df ⟨y, Set.mem_univ y⟩ := hxy
    have h2 := h_restrict h1
    have h3 : (⟨x, Set.mem_univ x⟩ : {x // x ∈ Set.univ}) =
        ⟨y, Set.mem_univ y⟩ := h2
    exact Subtype.ext_iff.mp h3
  have h_surj : Function.Surjective df := h_linear.surjective (Or.inr hc)
  exact ContinuousLinearEquiv.ofBijective df
    (LinearMap.ker_eq_bot.mpr h_inj) (LinearMap.range_eq_top.mpr h_surj)

noncomputable def equivOfApproxAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {f : E → F} {f' : E ≃L[ℂ] F} {s : Set E} {c : ℝ≥0}
    (hs : IsOpen s) (hf : ApproximatesLinearOn f (f' : E →L[ℂ] F) s c)
    {z : E} (hz : z ∈ s) {df : E →L[ℂ] F} (hdf : HasFDerivAt f df z)
    (hc : c < ‖(f'.symm : F →L[ℂ] E)‖₊⁻¹) :
    E ≃L[ℂ] F := by
  have h_norm : ‖df - (f' : E →L[ℂ] F)‖ ≤ c :=
    norm_sub_le_of_approx hs hf hz hdf
  have h_approx : ∀ x y : E,
      ‖df x - df y - (f' : E →L[ℂ] F) (x - y)‖ ≤ c * ‖x - y‖ := by
    intro x y
    have h_eq : df x - df y - (f' : E →L[ℂ] F) (x - y) =
        (df - (f' : E →L[ℂ] F)) (x - y) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      abel
    rw [h_eq]
    have h1 := (df - (f' : E →L[ℂ] F)).le_opNorm (x - y)
    have h2 : ‖df - (f' : E →L[ℂ] F)‖ * ‖x - y‖ ≤ c * ‖x - y‖ := by
      gcongr
    exact le_trans h1 h2
  exact equivOfApproxLinear hc h_approx

/-- The inverse branch produced by `ContDiffAt.toOpenPartialHomeomorph` is smooth
on its whole target, not just pointwise. -/
theorem contDiffOn_symm_toOpenPartialHomeomorph
    {f : ℂ → ℂ} {a : ℂ} {f' : ℂ ≃L[ℂ] ℂ}
    (hf : ContDiffAt ℂ ω f a) (hf' : HasFDerivAt f (f' : ℂ →L[ℂ] ℂ) a)
    (h_global : ContDiff ℂ ω f) :
    let e := hf.toOpenPartialHomeomorph f hf' (by simp)
    ContDiffOn ℂ ω e.symm e.target := by
  intro e y hy
  have hx : e.symm y ∈ e.source := e.map_target' hy
  have h_open := e.open_source
  have h_approx : ApproximatesLinearOn f (f' : ℂ →L[ℂ] ℂ) e.source
      (‖(f'.symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ / 2) := by
    exact (Classical.choose_spec (hf.hasStrictFDerivAt' hf'
      (by simp)).approximates_deriv_on_open_nhds).2.2
  have h_cd_x : ContDiffAt ℂ ω f (e.symm y) := h_global.contDiffAt
  have h_deriv_x : HasFDerivAt f (fderiv ℂ f (e.symm y)) (e.symm y) :=
    h_cd_x.differentiableAt (by simp) |>.hasFDerivAt
  have h_pos : 0 < ‖(f'.symm : ℂ →L[ℂ] ℂ)‖₊ := by
    cases f'.subsingleton_or_nnnorm_symm_pos with
    | inl h_sub =>
      have h_eq : (0 : ℂ) = 1 := Subsingleton.elim 0 1
      norm_num at h_eq
    | inr h_pos => exact h_pos
  have h_lt : ‖(f'.symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ / 2 < ‖(f'.symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ := by
    apply NNReal.half_lt_self
    exact inv_ne_zero (ne_of_gt h_pos)
  let df_equiv := equivOfApproxAt h_open h_approx hx h_deriv_x h_lt
  have h_deriv_e_x : HasFDerivAt (⇑e) (df_equiv : ℂ →L[ℂ] ℂ) (e.symm y) := h_deriv_x
  have h_cd_e_x : ContDiffAt ℂ ω (⇑e) (e.symm y) := h_cd_x
  rw [contDiffWithinAt_iff_contDiffAt (e.open_target.mem_nhds hy)]
  exact e.contDiffAt_symm hy h_deriv_e_x h_cd_e_x

/-- The inverse branch produced by `ContDiffAt.toOpenPartialHomeomorph` is smooth
on its target assuming it is locally smooth on its source. -/
theorem contDiffOn_symm_toOpenPartialHomeomorph_local
    {f : ℂ → ℂ} {a : ℂ} {f' : ℂ ≃L[ℂ] ℂ}
    (hf : ContDiffAt ℂ ω f a) (hf' : HasFDerivAt f (f' : ℂ →L[ℂ] ℂ) a)
    (h_local : ContDiffOn ℂ ω f (hf.toOpenPartialHomeomorph f hf' (by simp)).source) :
    let e := hf.toOpenPartialHomeomorph f hf' (by simp)
    ContDiffOn ℂ ω e.symm e.target := by
  intro e y hy
  have hx : e.symm y ∈ e.source := e.map_target' hy
  have h_open := e.open_source
  have h_approx : ApproximatesLinearOn f (f' : ℂ →L[ℂ] ℂ) e.source
      (‖(f'.symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ / 2) := by
    exact (Classical.choose_spec (hf.hasStrictFDerivAt' hf'
      (by simp)).approximates_deriv_on_open_nhds).2.2
  have h_cd_x : ContDiffAt ℂ ω f (e.symm y) :=
    (contDiffWithinAt_iff_contDiffAt (e.open_source.mem_nhds hx)).mp (h_local (e.symm y) hx)
  have h_deriv_x : HasFDerivAt f (fderiv ℂ f (e.symm y)) (e.symm y) :=
    h_cd_x.differentiableAt (by simp) |>.hasFDerivAt
  have h_pos : 0 < ‖(f'.symm : ℂ →L[ℂ] ℂ)‖₊ := by
    cases f'.subsingleton_or_nnnorm_symm_pos with
    | inl h_sub =>
      have h_eq : (0 : ℂ) = 1 := Subsingleton.elim 0 1
      norm_num at h_eq
    | inr h_pos => exact h_pos
  have h_lt : ‖(f'.symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ / 2 < ‖(f'.symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ := by
    apply NNReal.half_lt_self
    exact inv_ne_zero (ne_of_gt h_pos)
  let df_equiv := equivOfApproxAt h_open h_approx hx h_deriv_x h_lt
  have h_deriv_e_x : HasFDerivAt (⇑e) (df_equiv : ℂ →L[ℂ] ℂ) (e.symm y) := h_deriv_x
  have h_cd_e_x : ContDiffAt ℂ ω (⇑e) (e.symm y) := h_cd_x
  rw [contDiffWithinAt_iff_contDiffAt (e.open_target.mem_nhds hy)]
  exact e.contDiffAt_symm hy h_deriv_e_x h_cd_e_x

end Jacobians.GeneralResults

