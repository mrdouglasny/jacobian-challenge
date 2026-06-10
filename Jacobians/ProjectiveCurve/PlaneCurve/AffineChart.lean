import Mathlib
import Jacobians.ProjectiveCurve.PlaneCurve
import Jacobians.ProjectiveCurve.PlaneCurve.Euler

open MvPolynomial
open BigOperators
open ContinuousLinearMap
open scoped ContDiff Manifold

namespace Jacobians.ProjectiveCurve

variable {H : PlaneCurveData}

/-- Smooth locus for projecting to Y (where ∂_x F ≠ 0). -/
def PlaneCurveAffine.smoothLocusX (H : PlaneCurveData) : Set (PlaneCurveAffine H) :=
  { p | (pderiv 0 H.F.val).eval ![p.val.1, p.val.2, 1] ≠ 0 }

/-- Smooth locus for projecting to X (where ∂_y F ≠ 0). -/
def PlaneCurveAffine.smoothLocusY (H : PlaneCurveData) : Set (PlaneCurveAffine H) :=
  { p | (pderiv 1 H.F.val).eval ![p.val.1, p.val.2, 1] ≠ 0 }

theorem smooth_locus_cover (p : PlaneCurveAffine H) :
    p ∈ PlaneCurveAffine.smoothLocusX H ∨ p ∈ PlaneCurveAffine.smoothLocusY H := by
  by_contra h
  simp only [PlaneCurveAffine.smoothLocusX, PlaneCurveAffine.smoothLocusY,
    Set.mem_setOf_eq, not_or, not_not] at h
  have h_x : (pderiv 0 H.F.val).eval ![p.val.1, p.val.2, 1] = 0 := h.1
  have h_y : (pderiv 1 H.F.val).eval ![p.val.1, p.val.2, 1] = 0 := h.2
  -- Apply Euler's homogeneous theorem:
  have h_euler := euler_homogeneous H.F.val H.d H.F.homogeneous
  have h_eval := congr_arg (fun q : MvPolynomial (Fin 3) ℂ =>
    q.eval ![p.val.1, p.val.2, 1]) h_euler
  -- Simplify LHS of h_eval:
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X] at h_eval
  -- Evaluate the sum over Fin 3:
  have h_sum : (∑ i : Fin 3, ![p.val.1, p.val.2, 1] i *
      (pderiv i H.F.val).eval ![p.val.1, p.val.2, 1]) =
      ![p.val.1, p.val.2, 1] 0 * (pderiv 0 H.F.val).eval ![p.val.1, p.val.2, 1] +
      ![p.val.1, p.val.2, 1] 1 * (pderiv 1 H.F.val).eval ![p.val.1, p.val.2, 1] +
      ![p.val.1, p.val.2, 1] 2 * (pderiv 2 H.F.val).eval ![p.val.1, p.val.2, 1] := by
    -- Expand the sum over Fin 3:
    rw [Fin.sum_univ_three]
  rw [h_sum] at h_eval
  -- We know h_x and h_y are 0:
  rw [h_x, h_y] at h_eval
  simp only [mul_zero, add_zero, zero_add] at h_eval
  -- v 2 = 1:
  change (1 : ℂ) * (pderiv 2 H.F.val).eval ![p.val.1, p.val.2, 1] = _ at h_eval
  rw [one_mul] at h_eval
  -- Simplify RHS of h_eval:
  rw [eval_nsmul] at h_eval
  -- Since p is on the curve, F(v) = 0:
  have h_prop := p.property
  change H.F.val.eval ![p.val.1, p.val.2, 1] = 0 at h_prop
  rw [h_prop, smul_zero] at h_eval
  -- So (pderiv 2 H.F.val).eval v = 0:
  have h_z : (pderiv 2 H.F.val).eval ![p.val.1, p.val.2, 1] = 0 := h_eval
  -- Thus all three partial derivatives are 0 at v:
  have h_grad : ∀ i : Fin 3, (pderiv i H.F.val).eval ![p.val.1, p.val.2, 1] = 0 := by
    intro i
    fin_cases i
    · exact h_x
    · exact h_y
    · exact h_z
  -- But v ≠ 0 (since v 2 = 1):
  have hv : (![p.val.1, p.val.2, 1] : Fin 3 → ℂ) ≠ 0 := by
    intro h_zero
    have h_z_zero : (![p.val.1, p.val.2, 1] : Fin 3 → ℂ) 2 = 0 := congrFun h_zero 2
    exact one_ne_zero h_z_zero
  -- This contradicts smoothness of H:
  rcases H.h_smooth ![p.val.1, p.val.2, 1] hv h_prop with ⟨i, hi⟩
  exact hi (h_grad i)

def V (p : ℂ × ℂ) : Fin 3 → ℂ := ![p.1, p.2, 1]

theorem continuous_V : Continuous V := by
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd
  · exact continuous_const

/-- Locus where the `phi` straightening has invertible derivative. -/
def phiDerivNonzeroLocus (H : PlaneCurveData) : Set (ℂ × ℂ) :=
  { q | (pderiv 0 H.F.val).eval (V q) ≠ 0 }

/-- Locus where the `psi` straightening has invertible derivative. -/
def psiDerivNonzeroLocus (H : PlaneCurveData) : Set (ℂ × ℂ) :=
  { q | (pderiv 1 H.F.val).eval (V q) ≠ 0 }

noncomputable def dV : (ℂ × ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun dp => ![dp.1, dp.2, 0]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun r x => by
        ext i
        fin_cases i <;> simp }

theorem dV_apply (dp : ℂ × ℂ) : dV dp = ![dp.1, dp.2, 0] := rfl

theorem hasFDerivAt_V (p : ℂ × ℂ) : HasFDerivAt V dV p := by
  have h_eq : (fun x => V x - dV x) = (fun _ => ![0, 0, 1]) := by
    ext x i
    fin_cases i <;> simp [V, dV_apply]
  have h_deriv : HasFDerivAt (fun x => V x - dV x) (0 : (ℂ × ℂ) →L[ℂ] (Fin 3 → ℂ)) p := by
    rw [h_eq]
    exact hasFDerivAt_const (𝕜 := ℂ) ![0, 0, 1] p
  have h_add := h_deriv.add dV.hasFDerivAt
  simp only [zero_add] at h_add
  have h_fn : (fun x => V x - dV x) + ⇑dV = V := by
    ext x i
    fin_cases i <;> simp [V, dV_apply]
  rw [h_fn] at h_add
  exact h_add

noncomputable def dphi (a b : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun dp => (a * dp.1 + b * dp.2, dp.2)
      map_add' := fun x y => by
        ext
        · simp; ring
        · simp
      map_smul' := fun r x => by
        ext
        · simp; ring
        · simp }

theorem dphi_apply (a b : ℂ) (dp : ℂ × ℂ) : dphi a b dp = (a * dp.1 + b * dp.2, dp.2) := rfl

noncomputable def dphi_equiv (a b : ℂ) (ha : a ≠ 0) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (dphi a b)
    (dphi a⁻¹ (- a⁻¹ * b))
    (fun x => by
      ext
      · simp only [dphi_apply, mul_add, neg_mul, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
        ring
      · simp [dphi_apply])
    (fun x => by
      ext
      · simp only [dphi_apply, mul_add, neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ ha,
          one_mul]
        ring
      · simp [dphi_apply])

noncomputable def phi (H : PlaneCurveData) (p : ℂ × ℂ) : ℂ × ℂ :=
  (H.F.val.eval (V p), p.2)

theorem hasFDerivAt_phi (H : PlaneCurveData) (p : ℂ × ℂ) :
    let a := (pderiv 0 H.F.val).eval (V p)
    let b := (pderiv 1 H.F.val).eval (V p)
    HasFDerivAt (phi H) (dphi a b) p := by
  intro a b
  have h_eval := hasFDerivAt_eval H.F.val (V p)
  have h_comp := h_eval.comp p (hasFDerivAt_V p)
  have h_snd := (snd ℂ ℂ ℂ).hasFDerivAt (x := p)
  have h_prod := h_comp.prodMk h_snd
  have h_eq : (fderiv_poly H.F.val (V p)).comp dV =
      (a • fst ℂ ℂ ℂ + b • snd ℂ ℂ ℂ) := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    simp only [comp_apply, fderiv_poly, sum_apply, proj_apply, add_apply, smul_apply]
    rw [Fin.sum_univ_three]
    simp [V, a, b, dV_apply]
  have h_deriv_eq : ((fderiv_poly H.F.val (V p)).comp dV).prod (snd ℂ ℂ ℂ) = dphi a b := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    ext
    · simp [h_eq, dphi_apply]
    · simp [dphi_apply]
  rw [← h_deriv_eq]
  exact h_prod

theorem contDiff_eval {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℂ) (n : ℕ∞ω) :
    ContDiff ℂ n (fun x => p.eval x) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact contDiff_const
  | add p q hp hq =>
    simp only [eval_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [eval_mul, eval_X]
    exact hp.mul (contDiff_apply ℂ ℂ i)

theorem isOpen_phiDerivNonzeroLocus (H : PlaneCurveData) :
    IsOpen (phiDerivNonzeroLocus H) := by
  have hcont : Continuous (fun q : ℂ × ℂ => (pderiv 0 H.F.val).eval (V q)) :=
    (contDiff_eval (pderiv 0 H.F.val) ω).continuous.comp continuous_V
  simpa [phiDerivNonzeroLocus] using (isOpen_ne (x := (0 : ℂ))).preimage hcont

theorem isOpen_psiDerivNonzeroLocus (H : PlaneCurveData) :
    IsOpen (psiDerivNonzeroLocus H) := by
  have hcont : Continuous (fun q : ℂ × ℂ => (pderiv 1 H.F.val).eval (V q)) :=
    (contDiff_eval (pderiv 1 H.F.val) ω).continuous.comp continuous_V
  simpa [psiDerivNonzeroLocus] using (isOpen_ne (x := (0 : ℂ))).preimage hcont

theorem contDiff_phi (H : PlaneCurveData) (n : ℕ∞ω) :
    ContDiff ℂ n (phi H) := by
  have h_V : ContDiff ℂ n V := by
    refine contDiff_pi.mpr (fun i => ?_)
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_snd
    · exact contDiff_const
  have h1 : ContDiff ℂ n (fun p : ℂ × ℂ => H.F.val.eval (V p)) :=
    (contDiff_eval H.F.val n).comp h_V
  exact h1.prodMk contDiff_snd

noncomputable def phiLocalHomeomorph (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H) : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) := by
  let a := (pderiv 0 H.F.val).eval ![p.val.1, p.val.2, 1]
  let b := (pderiv 1 H.F.val).eval ![p.val.1, p.val.2, 1]
  have ha : a ≠ 0 := hp
  let e' := dphi_equiv a b ha
  have hf : HasFDerivAt (phi H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val := hasFDerivAt_phi H p.val
  exact ((contDiff_phi H ω).contDiffAt.toOpenPartialHomeomorph (phi H) hf (by simp)).restrOpen
    (phiDerivNonzeroLocus H) (isOpen_phiDerivNonzeroLocus H)

theorem phiLocalHomeomorph_coe (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H) :
    ⇑(phiLocalHomeomorph H p hp) = phi H := by
  unfold phiLocalHomeomorph
  simp

theorem phiLocalHomeomorph_mem_source (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H) :
    p.val ∈ (phiLocalHomeomorph H p hp).source := by
  unfold phiLocalHomeomorph
  let a := (pderiv 0 H.F.val).eval ![p.val.1, p.val.2, 1]
  let b := (pderiv 1 H.F.val).eval ![p.val.1, p.val.2, 1]
  have ha : a ≠ 0 := hp
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dphi_equiv a b ha
  have hf : HasFDerivAt (phi H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_phi H p.val
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((contDiff_phi H ω).contDiffAt (x := p.val))
    (hf' := hf) (hn := by simp), by
      simpa [phiDerivNonzeroLocus, V, PlaneCurveAffine.smoothLocusX] using hp⟩

theorem phiLocalHomeomorph_deriv_ne_zero_of_mem_source (H : PlaneCurveData)
    (p : PlaneCurveAffine H) (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    {q : ℂ × ℂ} (hq : q ∈ (phiLocalHomeomorph H p hp).source) :
    (pderiv 0 H.F.val).eval (V q) ≠ 0 := by
  unfold phiLocalHomeomorph at hq
  exact hq.2

theorem affineChartProjY_invFun_prop (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H) (y : ℂ)
    (hy : (0, y) ∈ (phiLocalHomeomorph H p hp).target) :
    H.F.val.eval ![ ((phiLocalHomeomorph H p hp).symm (0, y)).1, y, 1 ] = 0 := by
  let e := phiLocalHomeomorph H p hp
  have h_coe : ⇑e = phi H := phiLocalHomeomorph_coe H p hp
  have h_eq : phi H (e.symm (0, y)) = (0, y) := by
    rw [← h_coe]
    exact e.right_inv hy
  have h_eq_fst : H.F.val.eval (V (e.symm (0, y))) = 0 := congrArg Prod.fst h_eq
  have h_eq_snd : (e.symm (0, y)).2 = y := congrArg Prod.snd h_eq
  change H.F.val.eval ![ (e.symm (0, y)).1, (e.symm (0, y)).2, 1 ] = 0 at h_eq_fst
  rwa [h_eq_snd] at h_eq_fst

noncomputable def affineChartProjY (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H) [Nonempty (PlaneCurveAffine H)] :
    OpenPartialHomeomorph (PlaneCurveAffine H) ℂ := by
  classical
  let e := phiLocalHomeomorph H p hp
  have h_coe : ⇑e = phi H := phiLocalHomeomorph_coe H p hp
  let source : Set (PlaneCurveAffine H) := { q | q.val ∈ e.source }
  let target : Set ℂ := { y | (0, y) ∈ e.target }
  letI : DecidablePred fun y : ℂ => y ∈ target := Classical.decPred _
  let invFun : ℂ → PlaneCurveAffine H := fun y =>
    if hy : y ∈ target then
      ⟨((e.symm (0, y)).1, y), affineChartProjY_invFun_prop H p hp y hy⟩
    else Classical.choice inferInstance
  refine
    { toPartialEquiv :=
        { toFun := fun q => q.val.2
          invFun := invFun
          source := source
          target := target
          map_source' := by
            intro q hq
            change (0, q.val.2) ∈ e.target
            have hq' : q.val ∈ e.source := hq
            have h_eq := e.map_source hq'
            rw [h_coe] at h_eq
            change (H.F.val.eval ![q.val.1, q.val.2, 1], q.val.2) ∈ e.target at h_eq
            have h_prop := q.property
            change H.F.val.eval ![q.val.1, q.val.2, 1] = 0 at h_prop
            rwa [h_prop] at h_eq
          map_target' := by
            intro y hy
            simp only [source]
            dsimp [invFun]
            rw [dif_pos hy]
            have hy' : (0, y) ∈ e.target := hy
            have h_mem := e.map_target hy'
            have h_eq : phi H (e.symm (0, y)) = (0, y) := by
              rw [← h_coe]
              exact e.right_inv hy'
            have h_pair : ((e.symm (0, y)).1, y) = e.symm (0, y) := by
              ext
              · rfl
              · have h_eq_snd : (e.symm (0, y)).2 = y := congrArg Prod.snd h_eq
                exact h_eq_snd.symm
            change ((e.symm (0, y)).1, y) ∈ e.source
            rw [h_pair]
            exact h_mem
          left_inv' := by
            intro q hq
            have hy : q.val.2 ∈ target := by
              change (0, q.val.2) ∈ e.target
              have hq' : q.val ∈ e.source := hq
              have h_eq := e.map_source hq'
              rw [h_coe] at h_eq
              change (H.F.val.eval ![q.val.1, q.val.2, 1], q.val.2) ∈ e.target at h_eq
              have h_prop := q.property
              change H.F.val.eval ![q.val.1, q.val.2, 1] = 0 at h_prop
              rwa [h_prop] at h_eq
            dsimp [invFun]
            rw [dif_pos hy]
            apply Subtype.ext
            dsimp
            have h_phi : (0, q.val.2) = phi H q.val := by
              have h_prop := q.property
              change H.F.val.eval ![q.val.1, q.val.2, 1] = 0 at h_prop
              simp [phi, V, h_prop]
            have h_inv : e.symm (0, q.val.2) = q.val := by
              rw [h_phi]
              rw [← h_coe]
              exact e.left_inv hq
            have h_eq_snd : (e.symm (0, q.val.2)).2 = q.val.2 := congrArg Prod.snd h_inv
            have h_pair : ((e.symm (0, q.val.2)).1, q.val.2) = e.symm (0, q.val.2) := by
              ext
              · rfl
              · exact h_eq_snd.symm
            rw [h_pair]
            exact h_inv
          right_inv' := by
            intro y hy
            dsimp [invFun]
            rw [dif_pos hy] }
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := by
        have h_cont : Continuous (fun y : ℂ => ((0 : ℂ), y)) :=
          continuous_zero.prodMk continuous_id
        exact e.open_target.preimage h_cont
      continuousOn_toFun := continuous_subtype_val.snd.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        change Continuous (fun y : target => invFun y)
        have hEq : (fun y : target => invFun y) =
            (fun y : target =>
              ⟨((e.symm (0, y.val)).1, y.val),
                affineChartProjY_invFun_prop H p hp y.val y.property⟩) := by
          funext y
          dsimp [invFun]
          rw [dif_pos y.property]
        rw [hEq]
        have h_cont1 : Continuous (fun y : target => e.symm (0, y.val)) := by
          have h_comp : Continuous (fun y : target => ((0 : ℂ), y.val)) :=
            continuous_zero.prodMk continuous_subtype_val
          have h_cont_symm : ContinuousOn e.symm e.target := e.continuousOn_invFun
          have h_sub_map : ∀ y : target, ((0 : ℂ), y.val) ∈ e.target := fun y => y.property
          exact ContinuousOn.comp_continuous h_cont_symm h_comp h_sub_map
        have h_fst : Continuous (fun y : target => (e.symm (0, y.val)).1) :=
          continuous_fst.comp h_cont1
        have h_snd : Continuous (fun y : target => y.val) := continuous_subtype_val
        exact Continuous.subtype_mk (h_fst.prodMk h_snd) _
    }

noncomputable def dpsi (a b : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun dp => (a * dp.1 + b * dp.2, dp.1)
      map_add' := fun x y => by
        ext
        · simp; ring
        · simp
      map_smul' := fun r x => by
        ext
        · simp; ring
        · simp }

theorem dpsi_apply (a b : ℂ) (dp : ℂ × ℂ) : dpsi a b dp = (a * dp.1 + b * dp.2, dp.1) := rfl

noncomputable def dpsi_inv (a b : ℂ) (_hb : b ≠ 0) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun dp => (dp.2, b⁻¹ * dp.1 - b⁻¹ * a * dp.2)
      map_add' := fun x y => by
        ext
        · simp
        · simp; ring
      map_smul' := fun r x => by
        ext
        · simp
        · simp; ring }

theorem dpsi_inv_apply (a b : ℂ) (hb : b ≠ 0) (dp : ℂ × ℂ) :
    dpsi_inv a b hb dp = (dp.2, b⁻¹ * dp.1 - b⁻¹ * a * dp.2) := rfl

noncomputable def dpsi_equiv (a b : ℂ) (hb : b ≠ 0) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (dpsi a b)
    (dpsi_inv a b hb)
    (fun x => by
      ext
      · rfl
      · simp only [dpsi_apply, dpsi_inv_apply]
        simp [inv_mul_cancel_left₀ hb, mul_add]
        ring)
    (fun x => by
      ext
      · simp only [dpsi_apply, dpsi_inv_apply]
        simp [mul_inv_cancel_left₀ hb, mul_sub, mul_assoc]
      · rfl)

noncomputable def psi (H : PlaneCurveData) (p : ℂ × ℂ) : ℂ × ℂ :=
  (H.F.val.eval (V p), p.1)

theorem hasFDerivAt_psi (H : PlaneCurveData) (p : ℂ × ℂ) :
    let a := (pderiv 0 H.F.val).eval (V p)
    let b := (pderiv 1 H.F.val).eval (V p)
    HasFDerivAt (psi H) (dpsi a b) p := by
  intro a b
  have h_eval := hasFDerivAt_eval H.F.val (V p)
  have h_comp := h_eval.comp p (hasFDerivAt_V p)
  have h_fst := (fst ℂ ℂ ℂ).hasFDerivAt (x := p)
  have h_prod := h_comp.prodMk h_fst
  have h_eq : (fderiv_poly H.F.val (V p)).comp dV =
      (a • fst ℂ ℂ ℂ + b • snd ℂ ℂ ℂ) := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    simp only [comp_apply, fderiv_poly, sum_apply, proj_apply, add_apply, smul_apply]
    rw [Fin.sum_univ_three]
    simp [V, a, b, dV_apply]
  have h_deriv_eq : ((fderiv_poly H.F.val (V p)).comp dV).prod (fst ℂ ℂ ℂ) =
      dpsi a b := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    ext
    · simp [h_eq, dpsi_apply]
    · simp [dpsi_apply]
  rw [← h_deriv_eq]
  exact h_prod

theorem contDiff_psi (H : PlaneCurveData) (n : ℕ∞ω) :
    ContDiff ℂ n (psi H) := by
  have h_V : ContDiff ℂ n V := by
    refine contDiff_pi.mpr (fun i => ?_)
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_snd
    · exact contDiff_const
  have h1 : ContDiff ℂ n (fun p : ℂ × ℂ => H.F.val.eval (V p)) :=
    (contDiff_eval H.F.val n).comp h_V
  exact h1.prodMk contDiff_fst

noncomputable def psiLocalHomeomorph (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H) : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) := by
  let a := (pderiv 0 H.F.val).eval ![p.val.1, p.val.2, 1]
  let b := (pderiv 1 H.F.val).eval ![p.val.1, p.val.2, 1]
  have hb : b ≠ 0 := hp
  let e' := dpsi_equiv a b hb
  have hf : HasFDerivAt (psi H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val := hasFDerivAt_psi H p.val
  exact ((contDiff_psi H ω).contDiffAt.toOpenPartialHomeomorph (psi H) hf (by simp)).restrOpen
    (psiDerivNonzeroLocus H) (isOpen_psiDerivNonzeroLocus H)

theorem psiLocalHomeomorph_coe (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H) :
    ⇑(psiLocalHomeomorph H p hp) = psi H := by
  unfold psiLocalHomeomorph
  simp

theorem psiLocalHomeomorph_mem_source (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H) :
    p.val ∈ (psiLocalHomeomorph H p hp).source := by
  unfold psiLocalHomeomorph
  let a := (pderiv 0 H.F.val).eval ![p.val.1, p.val.2, 1]
  let b := (pderiv 1 H.F.val).eval ![p.val.1, p.val.2, 1]
  have hb : b ≠ 0 := hp
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dpsi_equiv a b hb
  have hf : HasFDerivAt (psi H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_psi H p.val
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((contDiff_psi H ω).contDiffAt (x := p.val))
    (hf' := hf) (hn := by simp), by
      simpa [psiDerivNonzeroLocus, V, PlaneCurveAffine.smoothLocusY] using hp⟩

theorem psiLocalHomeomorph_deriv_ne_zero_of_mem_source (H : PlaneCurveData)
    (p : PlaneCurveAffine H) (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    {q : ℂ × ℂ} (hq : q ∈ (psiLocalHomeomorph H p hp).source) :
    (pderiv 1 H.F.val).eval (V q) ≠ 0 := by
  unfold psiLocalHomeomorph at hq
  exact hq.2

theorem affineChartProjX_invFun_prop (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H) (x : ℂ)
    (hx : (0, x) ∈ (psiLocalHomeomorph H p hp).target) :
    H.F.val.eval ![ x, ((psiLocalHomeomorph H p hp).symm (0, x)).2, 1 ] = 0 := by
  let e := psiLocalHomeomorph H p hp
  have h_coe : ⇑e = psi H := psiLocalHomeomorph_coe H p hp
  have h_eq : psi H (e.symm (0, x)) = (0, x) := by
    rw [← h_coe]
    exact e.right_inv hx
  have h_eq_fst : H.F.val.eval (V (e.symm (0, x))) = 0 := congrArg Prod.fst h_eq
  have h_eq_snd : (e.symm (0, x)).1 = x := congrArg Prod.snd h_eq
  change H.F.val.eval ![ (e.symm (0, x)).1, (e.symm (0, x)).2, 1 ] = 0 at h_eq_fst
  rwa [h_eq_snd] at h_eq_fst

noncomputable def affineChartProjX (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H) [Nonempty (PlaneCurveAffine H)] :
    OpenPartialHomeomorph (PlaneCurveAffine H) ℂ := by
  classical
  let e := psiLocalHomeomorph H p hp
  have h_coe : ⇑e = psi H := psiLocalHomeomorph_coe H p hp
  let source : Set (PlaneCurveAffine H) := { q | q.val ∈ e.source }
  let target : Set ℂ := { x | (0, x) ∈ e.target }
  letI : DecidablePred fun x : ℂ => x ∈ target := Classical.decPred _
  let invFun : ℂ → PlaneCurveAffine H := fun x =>
    if hx : x ∈ target then
      ⟨(x, (e.symm (0, x)).2), affineChartProjX_invFun_prop H p hp x hx⟩
    else Classical.choice inferInstance
  refine
    { toPartialEquiv :=
        { toFun := fun q => q.val.1
          invFun := invFun
          source := source
          target := target
          map_source' := by
            intro q hq
            change (0, q.val.1) ∈ e.target
            have hq' : q.val ∈ e.source := hq
            have h_eq := e.map_source hq'
            rw [h_coe] at h_eq
            change (H.F.val.eval ![q.val.1, q.val.2, 1], q.val.1) ∈ e.target at h_eq
            have h_prop := q.property
            change H.F.val.eval ![q.val.1, q.val.2, 1] = 0 at h_prop
            rwa [h_prop] at h_eq
          map_target' := by
            intro x hx
            simp only [source]
            dsimp [invFun]
            rw [dif_pos hx]
            have hx' : (0, x) ∈ e.target := hx
            have h_mem := e.map_target hx'
            have h_eq : psi H (e.symm (0, x)) = (0, x) := by
              rw [← h_coe]
              exact e.right_inv hx'
            have h_pair : (x, (e.symm (0, x)).2) = e.symm (0, x) := by
              ext
              · have h_eq_snd : (e.symm (0, x)).1 = x := congrArg Prod.snd h_eq
                exact h_eq_snd.symm
              · rfl
            change (x, (e.symm (0, x)).2) ∈ e.source
            rw [h_pair]
            exact h_mem
          left_inv' := by
            intro q hq
            have hx : q.val.1 ∈ target := by
              change (0, q.val.1) ∈ e.target
              have hq' : q.val ∈ e.source := hq
              have h_eq := e.map_source hq'
              rw [h_coe] at h_eq
              change (H.F.val.eval ![q.val.1, q.val.2, 1], q.val.1) ∈ e.target at h_eq
              have h_prop := q.property
              change H.F.val.eval ![q.val.1, q.val.2, 1] = 0 at h_prop
              rwa [h_prop] at h_eq
            dsimp [invFun]
            rw [dif_pos hx]
            apply Subtype.ext
            dsimp
            have h_psi : (0, q.val.1) = psi H q.val := by
              have h_prop := q.property
              change H.F.val.eval ![q.val.1, q.val.2, 1] = 0 at h_prop
              simp [psi, V, h_prop]
            have h_inv : e.symm (0, q.val.1) = q.val := by
              rw [h_psi]
              rw [← h_coe]
              exact e.left_inv hq
            have h_eq_snd : (e.symm (0, q.val.1)).1 = q.val.1 := congrArg Prod.fst h_inv
            have h_pair : (q.val.1, (e.symm (0, q.val.1)).2) = e.symm (0, q.val.1) := by
              ext
              · exact h_eq_snd.symm
              · rfl
            rw [h_pair]
            exact h_inv
          right_inv' := by
            intro x hx
            dsimp [invFun]
            rw [dif_pos hx] }
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := by
        have h_cont : Continuous (fun x : ℂ => ((0 : ℂ), x)) :=
          continuous_zero.prodMk continuous_id
        exact e.open_target.preimage h_cont
      continuousOn_toFun := continuous_subtype_val.fst.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        change Continuous (fun x : target => invFun x)
        have hEq : (fun x : target => invFun x) =
            (fun x : target =>
              ⟨(x.val, (e.symm (0, x.val)).2),
                affineChartProjX_invFun_prop H p hp x.val x.property⟩) := by
          funext x
          dsimp [invFun]
          rw [dif_pos x.property]
        rw [hEq]
        have h_cont1 : Continuous (fun x : target => e.symm (0, x.val)) := by
          have h_comp : Continuous (fun x : target => ((0 : ℂ), x.val)) :=
            continuous_zero.prodMk continuous_subtype_val
          have h_cont_symm : ContinuousOn e.symm e.target := e.continuousOn_invFun
          have h_sub_map : ∀ x : target, ((0 : ℂ), x.val) ∈ e.target := fun x => x.property
          exact ContinuousOn.comp_continuous h_cont_symm h_comp h_sub_map
        have h_fst : Continuous (fun x : target => x.val) := continuous_subtype_val
        have h_snd : Continuous (fun x : target => (e.symm (0, x.val)).2) :=
          continuous_snd.comp h_cont1
        exact Continuous.subtype_mk (h_fst.prodMk h_snd) _
    }

def VY (p : ℂ × ℂ) : Fin 3 → ℂ := ![p.1, 1, p.2]

theorem continuous_VY : Continuous VY := by
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · exact continuous_fst
  · exact continuous_const
  · exact continuous_snd

/-- Locus where the `phiY` straightening has invertible derivative. -/
def phiYDerivNonzeroLocus (H : PlaneCurveData) : Set (ℂ × ℂ) :=
  { q | (pderiv 0 H.F.val).eval (VY q) ≠ 0 }

/-- Locus where the `psiY` straightening has invertible derivative. -/
def psiYDerivNonzeroLocus (H : PlaneCurveData) : Set (ℂ × ℂ) :=
  { q | (pderiv 2 H.F.val).eval (VY q) ≠ 0 }

theorem isOpen_phiYDerivNonzeroLocus (H : PlaneCurveData) :
    IsOpen (phiYDerivNonzeroLocus H) := by
  have hcont : Continuous (fun q : ℂ × ℂ => (pderiv 0 H.F.val).eval (VY q)) :=
    (contDiff_eval (pderiv 0 H.F.val) ω).continuous.comp continuous_VY
  simpa [phiYDerivNonzeroLocus] using (isOpen_ne (x := (0 : ℂ))).preimage hcont

theorem isOpen_psiYDerivNonzeroLocus (H : PlaneCurveData) :
    IsOpen (psiYDerivNonzeroLocus H) := by
  have hcont : Continuous (fun q : ℂ × ℂ => (pderiv 2 H.F.val).eval (VY q)) :=
    (contDiff_eval (pderiv 2 H.F.val) ω).continuous.comp continuous_VY
  simpa [psiYDerivNonzeroLocus] using (isOpen_ne (x := (0 : ℂ))).preimage hcont

noncomputable def dVY : (ℂ × ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun dp => ![dp.1, 0, dp.2]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun r x => by
        ext i
        fin_cases i <;> simp }

theorem dVY_apply (dp : ℂ × ℂ) : dVY dp = ![dp.1, 0, dp.2] := rfl

theorem hasFDerivAt_VY (p : ℂ × ℂ) : HasFDerivAt VY dVY p := by
  have h_eq : (fun x => VY x - dVY x) = (fun _ => ![0, 1, 0]) := by
    ext x i
    fin_cases i <;> simp [VY, dVY_apply]
  have h_deriv : HasFDerivAt (fun x => VY x - dVY x)
      (0 : (ℂ × ℂ) →L[ℂ] (Fin 3 → ℂ)) p := by
    rw [h_eq]
    exact hasFDerivAt_const (𝕜 := ℂ) ![0, 1, 0] p
  have h_add := h_deriv.add dVY.hasFDerivAt
  simp only [zero_add] at h_add
  have h_fn : (fun x => VY x - dVY x) + ⇑dVY = VY := by
    ext x i
    fin_cases i <;> simp [VY, dVY_apply]
  rw [h_fn] at h_add
  exact h_add

/-- Smooth locus for projecting to Z (where ∂_x F ≠ 0). -/
def PlaneCurveAffineY.smoothLocusX (H : PlaneCurveData) : Set (PlaneCurveAffineY H) :=
  { p | (pderiv 0 H.F.val).eval ![p.val.1, 1, p.val.2] ≠ 0 }

/-- Smooth locus for projecting to X (where ∂_z F ≠ 0). -/
def PlaneCurveAffineY.smoothLocusZ (H : PlaneCurveData) : Set (PlaneCurveAffineY H) :=
  { p | (pderiv 2 H.F.val).eval ![p.val.1, 1, p.val.2] ≠ 0 }

theorem smooth_locus_coverY (p : PlaneCurveAffineY H) :
    p ∈ PlaneCurveAffineY.smoothLocusX H ∨ p ∈ PlaneCurveAffineY.smoothLocusZ H := by
  by_contra h
  simp only [PlaneCurveAffineY.smoothLocusX, PlaneCurveAffineY.smoothLocusZ,
    Set.mem_setOf_eq, not_or, not_not] at h
  have h_x : (pderiv 0 H.F.val).eval ![p.val.1, 1, p.val.2] = 0 := h.1
  have h_z : (pderiv 2 H.F.val).eval ![p.val.1, 1, p.val.2] = 0 := h.2
  have h_euler := euler_homogeneous H.F.val H.d H.F.homogeneous
  have h_eval := congr_arg (fun q : MvPolynomial (Fin 3) ℂ =>
    q.eval ![p.val.1, 1, p.val.2]) h_euler
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X] at h_eval
  have h_sum : (∑ i : Fin 3, ![p.val.1, 1, p.val.2] i *
      (pderiv i H.F.val).eval ![p.val.1, 1, p.val.2]) =
      ![p.val.1, 1, p.val.2] 0 * (pderiv 0 H.F.val).eval ![p.val.1, 1, p.val.2] +
      ![p.val.1, 1, p.val.2] 1 * (pderiv 1 H.F.val).eval ![p.val.1, 1, p.val.2] +
      ![p.val.1, 1, p.val.2] 2 * (pderiv 2 H.F.val).eval ![p.val.1, 1, p.val.2] := by
    rw [Fin.sum_univ_three]
  rw [h_sum] at h_eval
  rw [h_x, h_z] at h_eval
  simp only [mul_zero, add_zero, zero_add] at h_eval
  change (1 : ℂ) * (pderiv 1 H.F.val).eval ![p.val.1, 1, p.val.2] = _ at h_eval
  rw [one_mul] at h_eval
  rw [eval_nsmul] at h_eval
  have h_prop := p.property
  change H.F.val.eval ![p.val.1, 1, p.val.2] = 0 at h_prop
  rw [h_prop, smul_zero] at h_eval
  have h_y : (pderiv 1 H.F.val).eval ![p.val.1, 1, p.val.2] = 0 := h_eval
  have h_grad : ∀ i : Fin 3, (pderiv i H.F.val).eval ![p.val.1, 1, p.val.2] = 0 := by
    intro i
    fin_cases i
    · exact h_x
    · exact h_y
    · exact h_z
  have hv : (![p.val.1, 1, p.val.2] : Fin 3 → ℂ) ≠ 0 := by
    intro h_zero
    have h_y_zero : (![p.val.1, 1, p.val.2] : Fin 3 → ℂ) 1 = 0 := congrFun h_zero 1
    exact one_ne_zero h_y_zero
  rcases H.h_smooth ![p.val.1, 1, p.val.2] hv h_prop with ⟨i, hi⟩
  exact hi (h_grad i)

noncomputable def phiY (H : PlaneCurveData) (p : ℂ × ℂ) : ℂ × ℂ :=
  (H.F.val.eval (VY p), p.2)

theorem hasFDerivAt_phiY (H : PlaneCurveData) (p : ℂ × ℂ) :
    let a := (pderiv 0 H.F.val).eval (VY p)
    let b := (pderiv 2 H.F.val).eval (VY p)
    HasFDerivAt (phiY H) (dphi a b) p := by
  intro a b
  have h_eval := hasFDerivAt_eval H.F.val (VY p)
  have h_comp := h_eval.comp p (hasFDerivAt_VY p)
  have h_snd := (snd ℂ ℂ ℂ).hasFDerivAt (x := p)
  have h_prod := h_comp.prodMk h_snd
  have h_eq : (fderiv_poly H.F.val (VY p)).comp dVY =
      (a • fst ℂ ℂ ℂ + b • snd ℂ ℂ ℂ) := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    simp only [comp_apply, fderiv_poly, sum_apply, proj_apply, add_apply, smul_apply]
    rw [Fin.sum_univ_three]
    simp [VY, a, b, dVY_apply]
  have h_deriv_eq : ((fderiv_poly H.F.val (VY p)).comp dVY).prod (snd ℂ ℂ ℂ) =
      dphi a b := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    ext
    · simp [h_eq, dphi_apply]
    · simp [dphi_apply]
  rw [← h_deriv_eq]
  exact h_prod

theorem contDiff_phiY (H : PlaneCurveData) (n : ℕ∞ω) :
    ContDiff ℂ n (phiY H) := by
  have h_VY : ContDiff ℂ n VY := by
    refine contDiff_pi.mpr (fun i => ?_)
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_const
    · exact contDiff_snd
  have h1 : ContDiff ℂ n (fun p : ℂ × ℂ => H.F.val.eval (VY p)) :=
    (contDiff_eval H.F.val n).comp h_VY
  exact h1.prodMk contDiff_snd

noncomputable def phiYLocalHomeomorph (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) := by
  let a := (pderiv 0 H.F.val).eval ![p.val.1, 1, p.val.2]
  let b := (pderiv 2 H.F.val).eval ![p.val.1, 1, p.val.2]
  have ha : a ≠ 0 := hp
  let e' := dphi_equiv a b ha
  have hf : HasFDerivAt (phiY H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_phiY H p.val
  exact ((contDiff_phiY H ω).contDiffAt.toOpenPartialHomeomorph (phiY H) hf
    (by simp)).restrOpen (phiYDerivNonzeroLocus H) (isOpen_phiYDerivNonzeroLocus H)

theorem phiYLocalHomeomorph_coe (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H) :
    ⇑(phiYLocalHomeomorph H p hp) = phiY H := by
  unfold phiYLocalHomeomorph
  simp

theorem phiYLocalHomeomorph_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H) :
    p.val ∈ (phiYLocalHomeomorph H p hp).source := by
  unfold phiYLocalHomeomorph
  let a := (pderiv 0 H.F.val).eval ![p.val.1, 1, p.val.2]
  let b := (pderiv 2 H.F.val).eval ![p.val.1, 1, p.val.2]
  have ha : a ≠ 0 := hp
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dphi_equiv a b ha
  have hf : HasFDerivAt (phiY H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_phiY H p.val
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((contDiff_phiY H ω).contDiffAt (x := p.val))
    (hf' := hf) (hn := by simp), by
      simpa [phiYDerivNonzeroLocus, VY, PlaneCurveAffineY.smoothLocusX] using hp⟩

theorem phiYLocalHomeomorph_deriv_ne_zero_of_mem_source (H : PlaneCurveData)
    (p : PlaneCurveAffineY H) (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    {q : ℂ × ℂ} (hq : q ∈ (phiYLocalHomeomorph H p hp).source) :
    (pderiv 0 H.F.val).eval (VY q) ≠ 0 := by
  unfold phiYLocalHomeomorph at hq
  exact hq.2

theorem affineChartProjZ_Y_invFun_prop (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H) (z : ℂ)
    (hz : (0, z) ∈ (phiYLocalHomeomorph H p hp).target) :
    H.F.val.eval ![ ((phiYLocalHomeomorph H p hp).symm (0, z)).1, 1, z ] = 0 := by
  let e := phiYLocalHomeomorph H p hp
  have h_coe : ⇑e = phiY H := phiYLocalHomeomorph_coe H p hp
  have h_eq : phiY H (e.symm (0, z)) = (0, z) := by
    rw [← h_coe]
    exact e.right_inv hz
  have h_eq_fst : H.F.val.eval (VY (e.symm (0, z))) = 0 := congrArg Prod.fst h_eq
  have h_eq_snd : (e.symm (0, z)).2 = z := congrArg Prod.snd h_eq
  change H.F.val.eval ![ (e.symm (0, z)).1, 1, (e.symm (0, z)).2 ] = 0 at h_eq_fst
  rwa [h_eq_snd] at h_eq_fst

noncomputable def affineChartProjZ_Y (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H) [Nonempty (PlaneCurveAffineY H)] :
    OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ := by
  classical
  let e := phiYLocalHomeomorph H p hp
  have h_coe : ⇑e = phiY H := phiYLocalHomeomorph_coe H p hp
  let source : Set (PlaneCurveAffineY H) := { q | q.val ∈ e.source }
  let target : Set ℂ := { z | (0, z) ∈ e.target }
  letI : DecidablePred fun z : ℂ => z ∈ target := Classical.decPred _
  let invFun : ℂ → PlaneCurveAffineY H := fun z =>
    if hz : z ∈ target then
      ⟨((e.symm (0, z)).1, z), affineChartProjZ_Y_invFun_prop H p hp z hz⟩
    else Classical.choice inferInstance
  refine
    { toPartialEquiv :=
        { toFun := fun q => q.val.2
          invFun := invFun
          source := source
          target := target
          map_source' := by
            intro q hq
            change (0, q.val.2) ∈ e.target
            have hq' : q.val ∈ e.source := hq
            have h_eq := e.map_source hq'
            rw [h_coe] at h_eq
            change (H.F.val.eval ![q.val.1, 1, q.val.2], q.val.2) ∈ e.target at h_eq
            have h_prop := q.property
            change H.F.val.eval ![q.val.1, 1, q.val.2] = 0 at h_prop
            rwa [h_prop] at h_eq
          map_target' := by
            intro z hz
            simp only [source]
            dsimp [invFun]
            rw [dif_pos hz]
            have hz' : (0, z) ∈ e.target := hz
            have h_mem := e.map_target hz'
            have h_eq : phiY H (e.symm (0, z)) = (0, z) := by
              rw [← h_coe]
              exact e.right_inv hz'
            have h_pair : ((e.symm (0, z)).1, z) = e.symm (0, z) := by
              ext
              · rfl
              · have h_eq_snd : (e.symm (0, z)).2 = z := congrArg Prod.snd h_eq
                exact h_eq_snd.symm
            change ((e.symm (0, z)).1, z) ∈ e.source
            rw [h_pair]
            exact h_mem
          left_inv' := by
            intro q hq
            have hz : q.val.2 ∈ target := by
              change (0, q.val.2) ∈ e.target
              have hq' : q.val ∈ e.source := hq
              have h_eq := e.map_source hq'
              rw [h_coe] at h_eq
              change (H.F.val.eval ![q.val.1, 1, q.val.2], q.val.2) ∈ e.target at h_eq
              have h_prop := q.property
              change H.F.val.eval ![q.val.1, 1, q.val.2] = 0 at h_prop
              rwa [h_prop] at h_eq
            dsimp [invFun]
            rw [dif_pos hz]
            apply Subtype.ext
            dsimp
            have h_phi : (0, q.val.2) = phiY H q.val := by
              have h_prop := q.property
              change H.F.val.eval ![q.val.1, 1, q.val.2] = 0 at h_prop
              simp [phiY, VY, h_prop]
            have h_inv : e.symm (0, q.val.2) = q.val := by
              rw [h_phi]
              rw [← h_coe]
              exact e.left_inv hq
            have h_eq_snd : (e.symm (0, q.val.2)).2 = q.val.2 :=
              congrArg Prod.snd h_inv
            have h_pair : ((e.symm (0, q.val.2)).1, q.val.2) = e.symm (0, q.val.2) := by
              ext
              · rfl
              · exact h_eq_snd.symm
            rw [h_pair]
            exact h_inv
          right_inv' := by
            intro z hz
            dsimp [invFun]
            rw [dif_pos hz] }
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := by
        have h_cont : Continuous (fun z : ℂ => ((0 : ℂ), z)) :=
          continuous_zero.prodMk continuous_id
        exact e.open_target.preimage h_cont
      continuousOn_toFun := continuous_subtype_val.snd.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        change Continuous (fun z : target => invFun z)
        have hEq : (fun z : target => invFun z) =
            (fun z : target =>
              ⟨((e.symm (0, z.val)).1, z.val),
                affineChartProjZ_Y_invFun_prop H p hp z.val z.property⟩) := by
          funext z
          dsimp [invFun]
          rw [dif_pos z.property]
        rw [hEq]
        have h_cont1 : Continuous (fun z : target => e.symm (0, z.val)) := by
          have h_comp : Continuous (fun z : target => ((0 : ℂ), z.val)) :=
            continuous_zero.prodMk continuous_subtype_val
          have h_cont_symm : ContinuousOn e.symm e.target := e.continuousOn_invFun
          have h_sub_map : ∀ z : target, ((0 : ℂ), z.val) ∈ e.target :=
            fun z => z.property
          exact ContinuousOn.comp_continuous h_cont_symm h_comp h_sub_map
        have h_fst : Continuous (fun z : target => (e.symm (0, z.val)).1) :=
          continuous_fst.comp h_cont1
        have h_snd : Continuous (fun z : target => z.val) := continuous_subtype_val
        exact Continuous.subtype_mk (h_fst.prodMk h_snd) _
    }

noncomputable def psiY (H : PlaneCurveData) (p : ℂ × ℂ) : ℂ × ℂ :=
  (H.F.val.eval (VY p), p.1)

theorem hasFDerivAt_psiY (H : PlaneCurveData) (p : ℂ × ℂ) :
    let a := (pderiv 0 H.F.val).eval (VY p)
    let b := (pderiv 2 H.F.val).eval (VY p)
    HasFDerivAt (psiY H) (dpsi a b) p := by
  intro a b
  have h_eval := hasFDerivAt_eval H.F.val (VY p)
  have h_comp := h_eval.comp p (hasFDerivAt_VY p)
  have h_fst := (fst ℂ ℂ ℂ).hasFDerivAt (x := p)
  have h_prod := h_comp.prodMk h_fst
  have h_eq : (fderiv_poly H.F.val (VY p)).comp dVY =
      (a • fst ℂ ℂ ℂ + b • snd ℂ ℂ ℂ) := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    simp only [comp_apply, fderiv_poly, sum_apply, proj_apply, add_apply, smul_apply]
    rw [Fin.sum_univ_three]
    simp [VY, a, b, dVY_apply]
  have h_deriv_eq : ((fderiv_poly H.F.val (VY p)).comp dVY).prod (fst ℂ ℂ ℂ) =
      dpsi a b := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    ext
    · simp [h_eq, dpsi_apply]
    · simp [dpsi_apply]
  rw [← h_deriv_eq]
  exact h_prod

theorem contDiff_psiY (H : PlaneCurveData) (n : ℕ∞ω) :
    ContDiff ℂ n (psiY H) := by
  have h_VY : ContDiff ℂ n VY := by
    refine contDiff_pi.mpr (fun i => ?_)
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_const
    · exact contDiff_snd
  have h1 : ContDiff ℂ n (fun p : ℂ × ℂ => H.F.val.eval (VY p)) :=
    (contDiff_eval H.F.val n).comp h_VY
  exact h1.prodMk contDiff_fst

noncomputable def psiYLocalHomeomorph (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) := by
  let a := (pderiv 0 H.F.val).eval ![p.val.1, 1, p.val.2]
  let b := (pderiv 2 H.F.val).eval ![p.val.1, 1, p.val.2]
  have hb : b ≠ 0 := hp
  let e' := dpsi_equiv a b hb
  have hf : HasFDerivAt (psiY H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_psiY H p.val
  exact ((contDiff_psiY H ω).contDiffAt.toOpenPartialHomeomorph (psiY H) hf
    (by simp)).restrOpen (psiYDerivNonzeroLocus H) (isOpen_psiYDerivNonzeroLocus H)

theorem psiYLocalHomeomorph_coe (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H) :
    ⇑(psiYLocalHomeomorph H p hp) = psiY H := by
  unfold psiYLocalHomeomorph
  simp

theorem psiYLocalHomeomorph_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H) :
    p.val ∈ (psiYLocalHomeomorph H p hp).source := by
  unfold psiYLocalHomeomorph
  let a := (pderiv 0 H.F.val).eval ![p.val.1, 1, p.val.2]
  let b := (pderiv 2 H.F.val).eval ![p.val.1, 1, p.val.2]
  have hb : b ≠ 0 := hp
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dpsi_equiv a b hb
  have hf : HasFDerivAt (psiY H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_psiY H p.val
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((contDiff_psiY H ω).contDiffAt (x := p.val))
    (hf' := hf) (hn := by simp), by
      simpa [psiYDerivNonzeroLocus, VY, PlaneCurveAffineY.smoothLocusZ] using hp⟩

theorem psiYLocalHomeomorph_deriv_ne_zero_of_mem_source (H : PlaneCurveData)
    (p : PlaneCurveAffineY H) (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    {q : ℂ × ℂ} (hq : q ∈ (psiYLocalHomeomorph H p hp).source) :
    (pderiv 2 H.F.val).eval (VY q) ≠ 0 := by
  unfold psiYLocalHomeomorph at hq
  exact hq.2

theorem affineChartProjX_Y_invFun_prop (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H) (x : ℂ)
    (hx : (0, x) ∈ (psiYLocalHomeomorph H p hp).target) :
    H.F.val.eval ![ x, 1, ((psiYLocalHomeomorph H p hp).symm (0, x)).2 ] = 0 := by
  let e := psiYLocalHomeomorph H p hp
  have h_coe : ⇑e = psiY H := psiYLocalHomeomorph_coe H p hp
  have h_eq : psiY H (e.symm (0, x)) = (0, x) := by
    rw [← h_coe]
    exact e.right_inv hx
  have h_eq_fst : H.F.val.eval (VY (e.symm (0, x))) = 0 := congrArg Prod.fst h_eq
  have h_eq_snd : (e.symm (0, x)).1 = x := congrArg Prod.snd h_eq
  change H.F.val.eval ![ (e.symm (0, x)).1, 1, (e.symm (0, x)).2 ] = 0 at h_eq_fst
  rwa [h_eq_snd] at h_eq_fst

noncomputable def affineChartProjX_Y (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H) [Nonempty (PlaneCurveAffineY H)] :
    OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ := by
  classical
  let e := psiYLocalHomeomorph H p hp
  have h_coe : ⇑e = psiY H := psiYLocalHomeomorph_coe H p hp
  let source : Set (PlaneCurveAffineY H) := { q | q.val ∈ e.source }
  let target : Set ℂ := { x | (0, x) ∈ e.target }
  letI : DecidablePred fun x : ℂ => x ∈ target := Classical.decPred _
  let invFun : ℂ → PlaneCurveAffineY H := fun x =>
    if hx : x ∈ target then
      ⟨(x, (e.symm (0, x)).2), affineChartProjX_Y_invFun_prop H p hp x hx⟩
    else Classical.choice inferInstance
  refine
    { toPartialEquiv :=
        { toFun := fun q => q.val.1
          invFun := invFun
          source := source
          target := target
          map_source' := by
            intro q hq
            change (0, q.val.1) ∈ e.target
            have hq' : q.val ∈ e.source := hq
            have h_eq := e.map_source hq'
            rw [h_coe] at h_eq
            change (H.F.val.eval ![q.val.1, 1, q.val.2], q.val.1) ∈ e.target at h_eq
            have h_prop := q.property
            change H.F.val.eval ![q.val.1, 1, q.val.2] = 0 at h_prop
            rwa [h_prop] at h_eq
          map_target' := by
            intro x hx
            simp only [source]
            dsimp [invFun]
            rw [dif_pos hx]
            have hx' : (0, x) ∈ e.target := hx
            have h_mem := e.map_target hx'
            have h_eq : psiY H (e.symm (0, x)) = (0, x) := by
              rw [← h_coe]
              exact e.right_inv hx'
            have h_pair : (x, (e.symm (0, x)).2) = e.symm (0, x) := by
              ext
              · have h_eq_snd : (e.symm (0, x)).1 = x := congrArg Prod.snd h_eq
                exact h_eq_snd.symm
              · rfl
            change (x, (e.symm (0, x)).2) ∈ e.source
            rw [h_pair]
            exact h_mem
          left_inv' := by
            intro q hq
            have hx : q.val.1 ∈ target := by
              change (0, q.val.1) ∈ e.target
              have hq' : q.val ∈ e.source := hq
              have h_eq := e.map_source hq'
              rw [h_coe] at h_eq
              change (H.F.val.eval ![q.val.1, 1, q.val.2], q.val.1) ∈ e.target at h_eq
              have h_prop := q.property
              change H.F.val.eval ![q.val.1, 1, q.val.2] = 0 at h_prop
              rwa [h_prop] at h_eq
            dsimp [invFun]
            rw [dif_pos hx]
            apply Subtype.ext
            dsimp
            have h_psi : (0, q.val.1) = psiY H q.val := by
              have h_prop := q.property
              change H.F.val.eval ![q.val.1, 1, q.val.2] = 0 at h_prop
              simp [psiY, VY, h_prop]
            have h_inv : e.symm (0, q.val.1) = q.val := by
              rw [h_psi]
              rw [← h_coe]
              exact e.left_inv hq
            have h_eq_snd : (e.symm (0, q.val.1)).1 = q.val.1 :=
              congrArg Prod.fst h_inv
            have h_pair : (q.val.1, (e.symm (0, q.val.1)).2) = e.symm (0, q.val.1) := by
              ext
              · exact h_eq_snd.symm
              · rfl
            rw [h_pair]
            exact h_inv
          right_inv' := by
            intro x hx
            dsimp [invFun]
            rw [dif_pos hx] }
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := by
        have h_cont : Continuous (fun x : ℂ => ((0 : ℂ), x)) :=
          continuous_zero.prodMk continuous_id
        exact e.open_target.preimage h_cont
      continuousOn_toFun := continuous_subtype_val.fst.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        change Continuous (fun x : target => invFun x)
        have hEq : (fun x : target => invFun x) =
            (fun x : target =>
              ⟨(x.val, (e.symm (0, x.val)).2),
                affineChartProjX_Y_invFun_prop H p hp x.val x.property⟩) := by
          funext x
          dsimp [invFun]
          rw [dif_pos x.property]
        rw [hEq]
        have h_cont1 : Continuous (fun x : target => e.symm (0, x.val)) := by
          have h_comp : Continuous (fun x : target => ((0 : ℂ), x.val)) :=
            continuous_zero.prodMk continuous_subtype_val
          have h_cont_symm : ContinuousOn e.symm e.target := e.continuousOn_invFun
          have h_sub_map : ∀ x : target, ((0 : ℂ), x.val) ∈ e.target :=
            fun x => x.property
          exact ContinuousOn.comp_continuous h_cont_symm h_comp h_sub_map
        have h_fst : Continuous (fun x : target => x.val) := continuous_subtype_val
        have h_snd : Continuous (fun x : target => (e.symm (0, x.val)).2) :=
          continuous_snd.comp h_cont1
        exact Continuous.subtype_mk (h_fst.prodMk h_snd) _
    }

def VX (p : ℂ × ℂ) : Fin 3 → ℂ := ![1, p.1, p.2]

theorem continuous_VX : Continuous VX := by
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · exact continuous_const
  · exact continuous_fst
  · exact continuous_snd

/-- Locus where the `phiX` straightening has invertible derivative. -/
def phiXDerivNonzeroLocus (H : PlaneCurveData) : Set (ℂ × ℂ) :=
  { q | (pderiv 1 H.F.val).eval (VX q) ≠ 0 }

/-- Locus where the `psiX` straightening has invertible derivative. -/
def psiXDerivNonzeroLocus (H : PlaneCurveData) : Set (ℂ × ℂ) :=
  { q | (pderiv 2 H.F.val).eval (VX q) ≠ 0 }

theorem isOpen_phiXDerivNonzeroLocus (H : PlaneCurveData) :
    IsOpen (phiXDerivNonzeroLocus H) := by
  have hcont : Continuous (fun q : ℂ × ℂ => (pderiv 1 H.F.val).eval (VX q)) :=
    (contDiff_eval (pderiv 1 H.F.val) ω).continuous.comp continuous_VX
  simpa [phiXDerivNonzeroLocus] using (isOpen_ne (x := (0 : ℂ))).preimage hcont

theorem isOpen_psiXDerivNonzeroLocus (H : PlaneCurveData) :
    IsOpen (psiXDerivNonzeroLocus H) := by
  have hcont : Continuous (fun q : ℂ × ℂ => (pderiv 2 H.F.val).eval (VX q)) :=
    (contDiff_eval (pderiv 2 H.F.val) ω).continuous.comp continuous_VX
  simpa [psiXDerivNonzeroLocus] using (isOpen_ne (x := (0 : ℂ))).preimage hcont

noncomputable def dVX : (ℂ × ℂ) →L[ℂ] (Fin 3 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun dp => ![0, dp.1, dp.2]
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp
      map_smul' := fun r x => by
        ext i
        fin_cases i <;> simp }

theorem dVX_apply (dp : ℂ × ℂ) : dVX dp = ![0, dp.1, dp.2] := rfl

theorem hasFDerivAt_VX (p : ℂ × ℂ) : HasFDerivAt VX dVX p := by
  have h_eq : (fun x => VX x - dVX x) = (fun _ => ![1, 0, 0]) := by
    ext x i
    fin_cases i <;> simp [VX, dVX_apply]
  have h_deriv : HasFDerivAt (fun x => VX x - dVX x)
      (0 : (ℂ × ℂ) →L[ℂ] (Fin 3 → ℂ)) p := by
    rw [h_eq]
    exact hasFDerivAt_const (𝕜 := ℂ) ![1, 0, 0] p
  have h_add := h_deriv.add dVX.hasFDerivAt
  simp only [zero_add] at h_add
  have h_fn : (fun x => VX x - dVX x) + ⇑dVX = VX := by
    ext x i
    fin_cases i <;> simp [VX, dVX_apply]
  rw [h_fn] at h_add
  exact h_add

/-- Smooth locus for projecting to Z (where ∂_y F ≠ 0). -/
def PlaneCurveAffineX.smoothLocusY (H : PlaneCurveData) : Set (PlaneCurveAffineX H) :=
  { p | (pderiv 1 H.F.val).eval ![1, p.val.1, p.val.2] ≠ 0 }

/-- Smooth locus for projecting to Y (where ∂_z F ≠ 0). -/
def PlaneCurveAffineX.smoothLocusZ (H : PlaneCurveData) : Set (PlaneCurveAffineX H) :=
  { p | (pderiv 2 H.F.val).eval ![1, p.val.1, p.val.2] ≠ 0 }

theorem smooth_locus_coverX (p : PlaneCurveAffineX H) :
    p ∈ PlaneCurveAffineX.smoothLocusY H ∨ p ∈ PlaneCurveAffineX.smoothLocusZ H := by
  by_contra h
  simp only [PlaneCurveAffineX.smoothLocusY, PlaneCurveAffineX.smoothLocusZ,
    Set.mem_setOf_eq, not_or, not_not] at h
  have h_y : (pderiv 1 H.F.val).eval ![1, p.val.1, p.val.2] = 0 := h.1
  have h_z : (pderiv 2 H.F.val).eval ![1, p.val.1, p.val.2] = 0 := h.2
  have h_euler := euler_homogeneous H.F.val H.d H.F.homogeneous
  have h_eval := congr_arg (fun q : MvPolynomial (Fin 3) ℂ =>
    q.eval ![1, p.val.1, p.val.2]) h_euler
  simp only [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_X] at h_eval
  have h_sum : (∑ i : Fin 3, ![1, p.val.1, p.val.2] i *
      (pderiv i H.F.val).eval ![1, p.val.1, p.val.2]) =
      ![1, p.val.1, p.val.2] 0 * (pderiv 0 H.F.val).eval ![1, p.val.1, p.val.2] +
      ![1, p.val.1, p.val.2] 1 * (pderiv 1 H.F.val).eval ![1, p.val.1, p.val.2] +
      ![1, p.val.1, p.val.2] 2 * (pderiv 2 H.F.val).eval ![1, p.val.1, p.val.2] := by
    rw [Fin.sum_univ_three]
  rw [h_sum] at h_eval
  rw [h_y, h_z] at h_eval
  simp only [mul_zero, add_zero] at h_eval
  change (1 : ℂ) * (pderiv 0 H.F.val).eval ![1, p.val.1, p.val.2] = _ at h_eval
  rw [one_mul] at h_eval
  rw [eval_nsmul] at h_eval
  have h_prop := p.property
  change H.F.val.eval ![1, p.val.1, p.val.2] = 0 at h_prop
  rw [h_prop, smul_zero] at h_eval
  have h_x : (pderiv 0 H.F.val).eval ![1, p.val.1, p.val.2] = 0 := h_eval
  have h_grad : ∀ i : Fin 3, (pderiv i H.F.val).eval ![1, p.val.1, p.val.2] = 0 := by
    intro i
    fin_cases i
    · exact h_x
    · exact h_y
    · exact h_z
  have hv : (![1, p.val.1, p.val.2] : Fin 3 → ℂ) ≠ 0 := by
    intro h_zero
    have h_x_zero : (![1, p.val.1, p.val.2] : Fin 3 → ℂ) 0 = 0 := congrFun h_zero 0
    exact one_ne_zero h_x_zero
  rcases H.h_smooth ![1, p.val.1, p.val.2] hv h_prop with ⟨i, hi⟩
  exact hi (h_grad i)

noncomputable def phiX (H : PlaneCurveData) (p : ℂ × ℂ) : ℂ × ℂ :=
  (H.F.val.eval (VX p), p.2)

theorem hasFDerivAt_phiX (H : PlaneCurveData) (p : ℂ × ℂ) :
    let a := (pderiv 1 H.F.val).eval (VX p)
    let b := (pderiv 2 H.F.val).eval (VX p)
    HasFDerivAt (phiX H) (dphi a b) p := by
  intro a b
  have h_eval := hasFDerivAt_eval H.F.val (VX p)
  have h_comp := h_eval.comp p (hasFDerivAt_VX p)
  have h_snd := (snd ℂ ℂ ℂ).hasFDerivAt (x := p)
  have h_prod := h_comp.prodMk h_snd
  have h_eq : (fderiv_poly H.F.val (VX p)).comp dVX =
      (a • fst ℂ ℂ ℂ + b • snd ℂ ℂ ℂ) := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    simp only [comp_apply, fderiv_poly, sum_apply, proj_apply, add_apply, smul_apply]
    rw [Fin.sum_univ_three]
    simp [VX, a, b, dVX_apply]
  have h_deriv_eq : ((fderiv_poly H.F.val (VX p)).comp dVX).prod (snd ℂ ℂ ℂ) =
      dphi a b := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    ext
    · simp [h_eq, dphi_apply]
    · simp [dphi_apply]
  rw [← h_deriv_eq]
  exact h_prod

theorem contDiff_phiX (H : PlaneCurveData) (n : ℕ∞ω) :
    ContDiff ℂ n (phiX H) := by
  have h_VX : ContDiff ℂ n VX := by
    refine contDiff_pi.mpr (fun i => ?_)
    fin_cases i
    · exact contDiff_const
    · exact contDiff_fst
    · exact contDiff_snd
  have h1 : ContDiff ℂ n (fun p : ℂ × ℂ => H.F.val.eval (VX p)) :=
    (contDiff_eval H.F.val n).comp h_VX
  exact h1.prodMk contDiff_snd

noncomputable def phiXLocalHomeomorph (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) := by
  let a := (pderiv 1 H.F.val).eval ![1, p.val.1, p.val.2]
  let b := (pderiv 2 H.F.val).eval ![1, p.val.1, p.val.2]
  have ha : a ≠ 0 := hp
  let e' := dphi_equiv a b ha
  have hf : HasFDerivAt (phiX H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_phiX H p.val
  exact ((contDiff_phiX H ω).contDiffAt.toOpenPartialHomeomorph (phiX H) hf
    (by simp)).restrOpen (phiXDerivNonzeroLocus H) (isOpen_phiXDerivNonzeroLocus H)

theorem phiXLocalHomeomorph_coe (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H) :
    ⇑(phiXLocalHomeomorph H p hp) = phiX H := by
  unfold phiXLocalHomeomorph
  simp

theorem phiXLocalHomeomorph_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H) :
    p.val ∈ (phiXLocalHomeomorph H p hp).source := by
  unfold phiXLocalHomeomorph
  let a := (pderiv 1 H.F.val).eval ![1, p.val.1, p.val.2]
  let b := (pderiv 2 H.F.val).eval ![1, p.val.1, p.val.2]
  have ha : a ≠ 0 := hp
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dphi_equiv a b ha
  have hf : HasFDerivAt (phiX H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_phiX H p.val
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((contDiff_phiX H ω).contDiffAt (x := p.val))
    (hf' := hf) (hn := by simp), by
      simpa [phiXDerivNonzeroLocus, VX, PlaneCurveAffineX.smoothLocusY] using hp⟩

theorem phiXLocalHomeomorph_deriv_ne_zero_of_mem_source (H : PlaneCurveData)
    (p : PlaneCurveAffineX H) (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    {q : ℂ × ℂ} (hq : q ∈ (phiXLocalHomeomorph H p hp).source) :
    (pderiv 1 H.F.val).eval (VX q) ≠ 0 := by
  unfold phiXLocalHomeomorph at hq
  exact hq.2

theorem affineChartProjZ_X_invFun_prop (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H) (z : ℂ)
    (hz : (0, z) ∈ (phiXLocalHomeomorph H p hp).target) :
    H.F.val.eval ![ 1, ((phiXLocalHomeomorph H p hp).symm (0, z)).1, z ] = 0 := by
  let e := phiXLocalHomeomorph H p hp
  have h_coe : ⇑e = phiX H := phiXLocalHomeomorph_coe H p hp
  have h_eq : phiX H (e.symm (0, z)) = (0, z) := by
    rw [← h_coe]
    exact e.right_inv hz
  have h_eq_fst : H.F.val.eval (VX (e.symm (0, z))) = 0 := congrArg Prod.fst h_eq
  have h_eq_snd : (e.symm (0, z)).2 = z := congrArg Prod.snd h_eq
  change H.F.val.eval ![ 1, (e.symm (0, z)).1, (e.symm (0, z)).2 ] = 0 at h_eq_fst
  rwa [h_eq_snd] at h_eq_fst

noncomputable def affineChartProjZ_X (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H) [Nonempty (PlaneCurveAffineX H)] :
    OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ := by
  classical
  let e := phiXLocalHomeomorph H p hp
  have h_coe : ⇑e = phiX H := phiXLocalHomeomorph_coe H p hp
  let source : Set (PlaneCurveAffineX H) := { q | q.val ∈ e.source }
  let target : Set ℂ := { z | (0, z) ∈ e.target }
  letI : DecidablePred fun z : ℂ => z ∈ target := Classical.decPred _
  let invFun : ℂ → PlaneCurveAffineX H := fun z =>
    if hz : z ∈ target then
      ⟨((e.symm (0, z)).1, z), affineChartProjZ_X_invFun_prop H p hp z hz⟩
    else Classical.choice inferInstance
  refine
    { toPartialEquiv :=
        { toFun := fun q => q.val.2
          invFun := invFun
          source := source
          target := target
          map_source' := by
            intro q hq
            change (0, q.val.2) ∈ e.target
            have hq' : q.val ∈ e.source := hq
            have h_eq := e.map_source hq'
            rw [h_coe] at h_eq
            change (H.F.val.eval ![1, q.val.1, q.val.2], q.val.2) ∈ e.target at h_eq
            have h_prop := q.property
            change H.F.val.eval ![1, q.val.1, q.val.2] = 0 at h_prop
            rwa [h_prop] at h_eq
          map_target' := by
            intro z hz
            simp only [source]
            dsimp [invFun]
            rw [dif_pos hz]
            have hz' : (0, z) ∈ e.target := hz
            have h_mem := e.map_target hz'
            have h_eq : phiX H (e.symm (0, z)) = (0, z) := by
              rw [← h_coe]
              exact e.right_inv hz'
            have h_pair : ((e.symm (0, z)).1, z) = e.symm (0, z) := by
              ext
              · rfl
              · have h_eq_snd : (e.symm (0, z)).2 = z := congrArg Prod.snd h_eq
                exact h_eq_snd.symm
            change ((e.symm (0, z)).1, z) ∈ e.source
            rw [h_pair]
            exact h_mem
          left_inv' := by
            intro q hq
            have hz : q.val.2 ∈ target := by
              change (0, q.val.2) ∈ e.target
              have hq' : q.val ∈ e.source := hq
              have h_eq := e.map_source hq'
              rw [h_coe] at h_eq
              change (H.F.val.eval ![1, q.val.1, q.val.2], q.val.2) ∈ e.target at h_eq
              have h_prop := q.property
              change H.F.val.eval ![1, q.val.1, q.val.2] = 0 at h_prop
              rwa [h_prop] at h_eq
            dsimp [invFun]
            rw [dif_pos hz]
            apply Subtype.ext
            dsimp
            have h_phi : (0, q.val.2) = phiX H q.val := by
              have h_prop := q.property
              change H.F.val.eval ![1, q.val.1, q.val.2] = 0 at h_prop
              simp [phiX, VX, h_prop]
            have h_inv : e.symm (0, q.val.2) = q.val := by
              rw [h_phi]
              rw [← h_coe]
              exact e.left_inv hq
            have h_eq_snd : (e.symm (0, q.val.2)).2 = q.val.2 :=
              congrArg Prod.snd h_inv
            have h_pair : ((e.symm (0, q.val.2)).1, q.val.2) = e.symm (0, q.val.2) := by
              ext
              · rfl
              · exact h_eq_snd.symm
            rw [h_pair]
            exact h_inv
          right_inv' := by
            intro z hz
            dsimp [invFun]
            rw [dif_pos hz] }
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := by
        have h_cont : Continuous (fun z : ℂ => ((0 : ℂ), z)) :=
          continuous_zero.prodMk continuous_id
        exact e.open_target.preimage h_cont
      continuousOn_toFun := continuous_subtype_val.snd.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        change Continuous (fun z : target => invFun z)
        have hEq : (fun z : target => invFun z) =
            (fun z : target =>
              ⟨((e.symm (0, z.val)).1, z.val),
                affineChartProjZ_X_invFun_prop H p hp z.val z.property⟩) := by
          funext z
          dsimp [invFun]
          rw [dif_pos z.property]
        rw [hEq]
        have h_cont1 : Continuous (fun z : target => e.symm (0, z.val)) := by
          have h_comp : Continuous (fun z : target => ((0 : ℂ), z.val)) :=
            continuous_zero.prodMk continuous_subtype_val
          have h_cont_symm : ContinuousOn e.symm e.target := e.continuousOn_invFun
          have h_sub_map : ∀ z : target, ((0 : ℂ), z.val) ∈ e.target :=
            fun z => z.property
          exact ContinuousOn.comp_continuous h_cont_symm h_comp h_sub_map
        have h_fst : Continuous (fun z : target => (e.symm (0, z.val)).1) :=
          continuous_fst.comp h_cont1
        have h_snd : Continuous (fun z : target => z.val) := continuous_subtype_val
        exact Continuous.subtype_mk (h_fst.prodMk h_snd) _
    }

noncomputable def psiX (H : PlaneCurveData) (p : ℂ × ℂ) : ℂ × ℂ :=
  (H.F.val.eval (VX p), p.1)

theorem hasFDerivAt_psiX (H : PlaneCurveData) (p : ℂ × ℂ) :
    let a := (pderiv 1 H.F.val).eval (VX p)
    let b := (pderiv 2 H.F.val).eval (VX p)
    HasFDerivAt (psiX H) (dpsi a b) p := by
  intro a b
  have h_eval := hasFDerivAt_eval H.F.val (VX p)
  have h_comp := h_eval.comp p (hasFDerivAt_VX p)
  have h_fst := (fst ℂ ℂ ℂ).hasFDerivAt (x := p)
  have h_prod := h_comp.prodMk h_fst
  have h_eq : (fderiv_poly H.F.val (VX p)).comp dVX =
      (a • fst ℂ ℂ ℂ + b • snd ℂ ℂ ℂ) := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    simp only [comp_apply, fderiv_poly, sum_apply, proj_apply, add_apply, smul_apply]
    rw [Fin.sum_univ_three]
    simp [VX, a, b, dVX_apply]
  have h_deriv_eq : ((fderiv_poly H.F.val (VX p)).comp dVX).prod (fst ℂ ℂ ℂ) =
      dpsi a b := by
    refine ContinuousLinearMap.ext (fun dp => ?_)
    ext
    · simp [h_eq, dpsi_apply]
    · simp [dpsi_apply]
  rw [← h_deriv_eq]
  exact h_prod

theorem contDiff_psiX (H : PlaneCurveData) (n : ℕ∞ω) :
    ContDiff ℂ n (psiX H) := by
  have h_VX : ContDiff ℂ n VX := by
    refine contDiff_pi.mpr (fun i => ?_)
    fin_cases i
    · exact contDiff_const
    · exact contDiff_fst
    · exact contDiff_snd
  have h1 : ContDiff ℂ n (fun p : ℂ × ℂ => H.F.val.eval (VX p)) :=
    (contDiff_eval H.F.val n).comp h_VX
  exact h1.prodMk contDiff_fst

noncomputable def psiXLocalHomeomorph (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) := by
  let a := (pderiv 1 H.F.val).eval ![1, p.val.1, p.val.2]
  let b := (pderiv 2 H.F.val).eval ![1, p.val.1, p.val.2]
  have hb : b ≠ 0 := hp
  let e' := dpsi_equiv a b hb
  have hf : HasFDerivAt (psiX H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_psiX H p.val
  exact ((contDiff_psiX H ω).contDiffAt.toOpenPartialHomeomorph (psiX H) hf
    (by simp)).restrOpen (psiXDerivNonzeroLocus H) (isOpen_psiXDerivNonzeroLocus H)

theorem psiXLocalHomeomorph_coe (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H) :
    ⇑(psiXLocalHomeomorph H p hp) = psiX H := by
  unfold psiXLocalHomeomorph
  simp

theorem psiXLocalHomeomorph_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H) :
    p.val ∈ (psiXLocalHomeomorph H p hp).source := by
  unfold psiXLocalHomeomorph
  let a := (pderiv 1 H.F.val).eval ![1, p.val.1, p.val.2]
  let b := (pderiv 2 H.F.val).eval ![1, p.val.1, p.val.2]
  have hb : b ≠ 0 := hp
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dpsi_equiv a b hb
  have hf : HasFDerivAt (psiX H) (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) p.val :=
    hasFDerivAt_psiX H p.val
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source
    ((contDiff_psiX H ω).contDiffAt (x := p.val))
    (hf' := hf) (hn := by simp), by
      simpa [psiXDerivNonzeroLocus, VX, PlaneCurveAffineX.smoothLocusZ] using hp⟩

theorem psiXLocalHomeomorph_deriv_ne_zero_of_mem_source (H : PlaneCurveData)
    (p : PlaneCurveAffineX H) (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    {q : ℂ × ℂ} (hq : q ∈ (psiXLocalHomeomorph H p hp).source) :
    (pderiv 2 H.F.val).eval (VX q) ≠ 0 := by
  unfold psiXLocalHomeomorph at hq
  exact hq.2

theorem affineChartProjY_X_invFun_prop (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H) (y : ℂ)
    (hy : (0, y) ∈ (psiXLocalHomeomorph H p hp).target) :
    H.F.val.eval ![ 1, y, ((psiXLocalHomeomorph H p hp).symm (0, y)).2 ] = 0 := by
  let e := psiXLocalHomeomorph H p hp
  have h_coe : ⇑e = psiX H := psiXLocalHomeomorph_coe H p hp
  have h_eq : psiX H (e.symm (0, y)) = (0, y) := by
    rw [← h_coe]
    exact e.right_inv hy
  have h_eq_fst : H.F.val.eval (VX (e.symm (0, y))) = 0 := congrArg Prod.fst h_eq
  have h_eq_snd : (e.symm (0, y)).1 = y := congrArg Prod.snd h_eq
  change H.F.val.eval ![ 1, (e.symm (0, y)).1, (e.symm (0, y)).2 ] = 0 at h_eq_fst
  rwa [h_eq_snd] at h_eq_fst

noncomputable def affineChartProjY_X (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H) [Nonempty (PlaneCurveAffineX H)] :
    OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ := by
  classical
  let e := psiXLocalHomeomorph H p hp
  have h_coe : ⇑e = psiX H := psiXLocalHomeomorph_coe H p hp
  let source : Set (PlaneCurveAffineX H) := { q | q.val ∈ e.source }
  let target : Set ℂ := { y | (0, y) ∈ e.target }
  letI : DecidablePred fun y : ℂ => y ∈ target := Classical.decPred _
  let invFun : ℂ → PlaneCurveAffineX H := fun y =>
    if hy : y ∈ target then
      ⟨(y, (e.symm (0, y)).2), affineChartProjY_X_invFun_prop H p hp y hy⟩
    else Classical.choice inferInstance
  refine
    { toPartialEquiv :=
        { toFun := fun q => q.val.1
          invFun := invFun
          source := source
          target := target
          map_source' := by
            intro q hq
            change (0, q.val.1) ∈ e.target
            have hq' : q.val ∈ e.source := hq
            have h_eq := e.map_source hq'
            rw [h_coe] at h_eq
            change (H.F.val.eval ![1, q.val.1, q.val.2], q.val.1) ∈ e.target at h_eq
            have h_prop := q.property
            change H.F.val.eval ![1, q.val.1, q.val.2] = 0 at h_prop
            rwa [h_prop] at h_eq
          map_target' := by
            intro y hy
            simp only [source]
            dsimp [invFun]
            rw [dif_pos hy]
            have hy' : (0, y) ∈ e.target := hy
            have h_mem := e.map_target hy'
            have h_eq : psiX H (e.symm (0, y)) = (0, y) := by
              rw [← h_coe]
              exact e.right_inv hy'
            have h_pair : (y, (e.symm (0, y)).2) = e.symm (0, y) := by
              ext
              · have h_eq_snd : (e.symm (0, y)).1 = y := congrArg Prod.snd h_eq
                exact h_eq_snd.symm
              · rfl
            change (y, (e.symm (0, y)).2) ∈ e.source
            rw [h_pair]
            exact h_mem
          left_inv' := by
            intro q hq
            have hy : q.val.1 ∈ target := by
              change (0, q.val.1) ∈ e.target
              have hq' : q.val ∈ e.source := hq
              have h_eq := e.map_source hq'
              rw [h_coe] at h_eq
              change (H.F.val.eval ![1, q.val.1, q.val.2], q.val.1) ∈ e.target at h_eq
              have h_prop := q.property
              change H.F.val.eval ![1, q.val.1, q.val.2] = 0 at h_prop
              rwa [h_prop] at h_eq
            dsimp [invFun]
            rw [dif_pos hy]
            apply Subtype.ext
            dsimp
            have h_psi : (0, q.val.1) = psiX H q.val := by
              have h_prop := q.property
              change H.F.val.eval ![1, q.val.1, q.val.2] = 0 at h_prop
              simp [psiX, VX, h_prop]
            have h_inv : e.symm (0, q.val.1) = q.val := by
              rw [h_psi]
              rw [← h_coe]
              exact e.left_inv hq
            have h_eq_snd : (e.symm (0, q.val.1)).1 = q.val.1 :=
              congrArg Prod.fst h_inv
            have h_pair : (q.val.1, (e.symm (0, q.val.1)).2) = e.symm (0, q.val.1) := by
              ext
              · exact h_eq_snd.symm
              · rfl
            rw [h_pair]
            exact h_inv
          right_inv' := by
            intro y hy
            dsimp [invFun]
            rw [dif_pos hy] }
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := by
        have h_cont : Continuous (fun y : ℂ => ((0 : ℂ), y)) :=
          continuous_zero.prodMk continuous_id
        exact e.open_target.preimage h_cont
      continuousOn_toFun := continuous_subtype_val.fst.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        change Continuous (fun y : target => invFun y)
        have hEq : (fun y : target => invFun y) =
            (fun y : target =>
              ⟨(y.val, (e.symm (0, y.val)).2),
                affineChartProjY_X_invFun_prop H p hp y.val y.property⟩) := by
          funext y
          dsimp [invFun]
          rw [dif_pos y.property]
        rw [hEq]
        have h_cont1 : Continuous (fun y : target => e.symm (0, y.val)) := by
          have h_comp : Continuous (fun y : target => ((0 : ℂ), y.val)) :=
            continuous_zero.prodMk continuous_subtype_val
          have h_cont_symm : ContinuousOn e.symm e.target := e.continuousOn_invFun
          have h_sub_map : ∀ y : target, ((0 : ℂ), y.val) ∈ e.target :=
            fun y => y.property
          exact ContinuousOn.comp_continuous h_cont_symm h_comp h_sub_map
        have h_fst : Continuous (fun y : target => y.val) := continuous_subtype_val
        have h_snd : Continuous (fun y : target => (e.symm (0, y.val)).2) :=
          continuous_snd.comp h_cont1
        exact Continuous.subtype_mk (h_fst.prodMk h_snd) _
    }

end Jacobians.ProjectiveCurve
