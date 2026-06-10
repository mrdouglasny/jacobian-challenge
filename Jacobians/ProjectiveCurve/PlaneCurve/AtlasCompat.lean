import Jacobians.ProjectiveCurve.PlaneCurve.Atlas

open MvPolynomial
open scoped Manifold Topology ContDiff

namespace Jacobians.ProjectiveCurve

/-- Same-kind transition compatibility for the `z = 1`, project-to-`Y` charts. -/
theorem affineChartProjY_compat_affineChartProjY (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      (((affineChartProjY H p hp).symm.trans (affineChartProjY H p' hp')) : ℂ → ℂ)
      (((affineChartProjY H p hp).symm.trans (affineChartProjY H p' hp')).source) := by
  let ep := affineChartProjY H p hp
  let ep' := affineChartProjY H p' hp'
  exact ContDiffOn.congr
    (f := fun y : ℂ => y)
    (s := (ep.symm.trans ep').source)
    contDiffOn_id
    (by
      intro y hy
      have hy0 : y ∈ ep.target := hy.1
      change ep (ep.symm y) = y
      exact ep.right_inv hy0)

/-- Same-kind transition compatibility for the `z = 1`, project-to-`X` charts. -/
theorem affineChartProjX_compat_affineChartProjX (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      (((affineChartProjX H p hp).symm.trans (affineChartProjX H p' hp')) : ℂ → ℂ)
      (((affineChartProjX H p hp).symm.trans (affineChartProjX H p' hp')).source) := by
  let ep := affineChartProjX H p hp
  let ep' := affineChartProjX H p' hp'
  exact ContDiffOn.congr
    (f := fun x : ℂ => x)
    (s := (ep.symm.trans ep').source)
    contDiffOn_id
    (by
      intro x hx
      have hx0 : x ∈ ep.target := hx.1
      change ep (ep.symm x) = x
      exact ep.right_inv hx0)

/-- Same-kind transition compatibility for the `y = 1`, project-to-`Z` charts. -/
theorem affineChartProjZ_Y_compat_affineChartProjZ_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H) :
    ContDiffOn ℂ ω
      (((affineChartProjZ_Y H p hp).symm.trans (affineChartProjZ_Y H p' hp')) : ℂ → ℂ)
      (((affineChartProjZ_Y H p hp).symm.trans (affineChartProjZ_Y H p' hp')).source) := by
  let ep := affineChartProjZ_Y H p hp
  let ep' := affineChartProjZ_Y H p' hp'
  exact ContDiffOn.congr
    (f := fun z : ℂ => z)
    (s := (ep.symm.trans ep').source)
    contDiffOn_id
    (by
      intro z hz
      have hz0 : z ∈ ep.target := hz.1
      change ep (ep.symm z) = z
      exact ep.right_inv hz0)

/-- Same-kind transition compatibility for the `y = 1`, project-to-`X` charts. -/
theorem affineChartProjX_Y_compat_affineChartProjX_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H) :
    ContDiffOn ℂ ω
      (((affineChartProjX_Y H p hp).symm.trans (affineChartProjX_Y H p' hp')) : ℂ → ℂ)
      (((affineChartProjX_Y H p hp).symm.trans (affineChartProjX_Y H p' hp')).source) := by
  let ep := affineChartProjX_Y H p hp
  let ep' := affineChartProjX_Y H p' hp'
  exact ContDiffOn.congr
    (f := fun x : ℂ => x)
    (s := (ep.symm.trans ep').source)
    contDiffOn_id
    (by
      intro x hx
      have hx0 : x ∈ ep.target := hx.1
      change ep (ep.symm x) = x
      exact ep.right_inv hx0)

/-- Same-kind transition compatibility for the `x = 1`, project-to-`Z` charts. -/
theorem affineChartProjZ_X_compat_affineChartProjZ_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H) :
    ContDiffOn ℂ ω
      (((affineChartProjZ_X H p hp).symm.trans (affineChartProjZ_X H p' hp')) : ℂ → ℂ)
      (((affineChartProjZ_X H p hp).symm.trans (affineChartProjZ_X H p' hp')).source) := by
  let ep := affineChartProjZ_X H p hp
  let ep' := affineChartProjZ_X H p' hp'
  exact ContDiffOn.congr
    (f := fun z : ℂ => z)
    (s := (ep.symm.trans ep').source)
    contDiffOn_id
    (by
      intro z hz
      have hz0 : z ∈ ep.target := hz.1
      change ep (ep.symm z) = z
      exact ep.right_inv hz0)

/-- Same-kind transition compatibility for the `x = 1`, project-to-`Y` charts. -/
theorem affineChartProjY_X_compat_affineChartProjY_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H) :
    ContDiffOn ℂ ω
      (((affineChartProjY_X H p hp).symm.trans (affineChartProjY_X H p' hp')) : ℂ → ℂ)
      (((affineChartProjY_X H p hp).symm.trans (affineChartProjY_X H p' hp')).source) := by
  let ep := affineChartProjY_X H p hp
  let ep' := affineChartProjY_X H p' hp'
  exact ContDiffOn.congr
    (f := fun y : ℂ => y)
    (s := (ep.symm.trans ep').source)
    contDiffOn_id
    (by
      intro y hy
      have hy0 : y ∈ ep.target := hy.1
      change ep (ep.symm y) = y
      exact ep.right_inv hy0)


/-- Mixed transition formula in the `z = 1` patch, from project-to-`Y` to
project-to-`X`. -/
theorem affineChartProjY_trans_affineChartProjX_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY H p hp).symm.trans
      (affineChartProjX H p' hp')).source)) :
    (((affineChartProjY H p hp).symm.trans (affineChartProjX H p' hp')) y) =
      ((phiLocalHomeomorph H p hp).symm (0, y)).1 := by
  have hy0 : y ∈ (affineChartProjY H p hp).target := hy.1
  have hy0' : (0, y) ∈ (phiLocalHomeomorph H p hp).target := by
    simpa [affineChartProjY] using hy0
  change ((affineChartProjY H p hp).symm y).val.1 =
    ((phiLocalHomeomorph H p hp).symm (0, y)).1
  dsimp [affineChartProjY]
  rw [dif_pos hy0']

/-- The restricted `z = 1`, project-to-`Y` IFT inverse is analytic on its target. -/
theorem phiLocalHomeomorph_contDiffOn_symm (H : PlaneCurveData)
    (p : PlaneCurveAffine H) (hp : p ∈ PlaneCurveAffine.smoothLocusX H) :
    ContDiffOn ℂ ω (phiLocalHomeomorph H p hp).symm
      (phiLocalHomeomorph H p hp).target := by
  let e := phiLocalHomeomorph H p hp
  refine e.open_target.contDiffOn_iff.mpr ?_
  intro a ha
  have hsrc : e.symm a ∈ e.source := e.map_target ha
  have hderiv :
      (pderiv 0 H.F.val).eval (V (e.symm a)) ≠ 0 :=
    phiLocalHomeomorph_deriv_ne_zero_of_mem_source H p hp hsrc
  let a0 := (pderiv 0 H.F.val).eval (V (e.symm a))
  let b0 := (pderiv 1 H.F.val).eval (V (e.symm a))
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dphi_equiv a0 b0 hderiv
  have hf' : HasFDerivAt e (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = phi H by
      simpa [e] using phiLocalHomeomorph_coe H p hp]
    simpa [e', a0, b0] using hasFDerivAt_phi H (e.symm a)
  have hf : ContDiffAt ℂ ω e (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = phi H by
      simpa [e] using phiLocalHomeomorph_coe H p hp]
    exact (contDiff_phi H ω).contDiffAt
  exact e.contDiffAt_symm ha hf' hf

/-- Mixed transition compatibility in the `z = 1` patch, from project-to-`Y` to
project-to-`X`. -/
theorem affineChartProjY_compat_affineChartProjX (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      (((affineChartProjY H p hp).symm.trans (affineChartProjX H p' hp')) : ℂ → ℂ)
      (((affineChartProjY H p hp).symm.trans (affineChartProjX H p' hp')).source) := by
  let e := phiLocalHomeomorph H p hp
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    phiLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun y : ℂ => ((0 : ℂ), y))
      (((affineChartProjY H p hp).symm.trans (affineChartProjX H p' hp')).source) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => ((0 : ℂ), y))
      (((affineChartProjY H p hp).symm.trans (affineChartProjX H p' hp')).source)
      e.target := by
    intro y hy
    simpa [affineChartProjY, e] using hy.1
  refine ContDiffOn.congr ((hsymm.comp hline hmaps).fst) ?_
  intro y hy
  simpa [e] using affineChartProjY_trans_affineChartProjX_apply H p p' hp hp' hy


/-- Mixed transition formula in the `z = 1` patch, from project-to-`X` to
project-to-`Y`. -/
theorem affineChartProjX_trans_affineChartProjY_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX H p hp).symm.trans
      (affineChartProjY H p' hp')).source)) :
    (((affineChartProjX H p hp).symm.trans (affineChartProjY H p' hp')) x) =
      ((psiLocalHomeomorph H p hp).symm (0, x)).2 := by
  have hx0 : x ∈ (affineChartProjX H p hp).target := hx.1
  have hx0' : (0, x) ∈ (psiLocalHomeomorph H p hp).target := by
    simpa [affineChartProjX] using hx0
  change ((affineChartProjX H p hp).symm x).val.2 =
    ((psiLocalHomeomorph H p hp).symm (0, x)).2
  dsimp [affineChartProjX]
  rw [dif_pos hx0']

/-- The restricted `z = 1`, project-to-`X` IFT inverse is analytic on its target. -/
theorem psiLocalHomeomorph_contDiffOn_symm (H : PlaneCurveData)
    (p : PlaneCurveAffine H) (hp : p ∈ PlaneCurveAffine.smoothLocusY H) :
    ContDiffOn ℂ ω (psiLocalHomeomorph H p hp).symm
      (psiLocalHomeomorph H p hp).target := by
  let e := psiLocalHomeomorph H p hp
  refine e.open_target.contDiffOn_iff.mpr ?_
  intro a ha
  have hsrc : e.symm a ∈ e.source := e.map_target ha
  have hderiv :
      (pderiv 1 H.F.val).eval (V (e.symm a)) ≠ 0 :=
    psiLocalHomeomorph_deriv_ne_zero_of_mem_source H p hp hsrc
  let a0 := (pderiv 0 H.F.val).eval (V (e.symm a))
  let b0 := (pderiv 1 H.F.val).eval (V (e.symm a))
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dpsi_equiv a0 b0 hderiv
  have hf' : HasFDerivAt e (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = psi H by
      simpa [e] using psiLocalHomeomorph_coe H p hp]
    simpa [e', a0, b0] using hasFDerivAt_psi H (e.symm a)
  have hf : ContDiffAt ℂ ω e (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = psi H by
      simpa [e] using psiLocalHomeomorph_coe H p hp]
    exact (contDiff_psi H ω).contDiffAt
  exact e.contDiffAt_symm ha hf' hf

/-- Mixed transition compatibility in the `z = 1` patch, from project-to-`X` to
project-to-`Y`. -/
theorem affineChartProjX_compat_affineChartProjY (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      (((affineChartProjX H p hp).symm.trans (affineChartProjY H p' hp')) : ℂ → ℂ)
      (((affineChartProjX H p hp).symm.trans (affineChartProjY H p' hp')).source) := by
  let e := psiLocalHomeomorph H p hp
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    psiLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun x : ℂ => ((0 : ℂ), x))
      (((affineChartProjX H p hp).symm.trans (affineChartProjY H p' hp')).source) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => ((0 : ℂ), x))
      (((affineChartProjX H p hp).symm.trans (affineChartProjY H p' hp')).source)
      e.target := by
    intro x hx
    simpa [affineChartProjX, e] using hx.1
  refine ContDiffOn.congr ((hsymm.comp hline hmaps).snd) ?_
  intro x hx
  simpa [e] using affineChartProjX_trans_affineChartProjY_apply H p p' hp hp' hx

/-- Mixed transition formula in the `y = 1` patch, from project-to-`Z` to
project-to-`X`. -/
theorem affineChartProjZ_Y_trans_affineChartProjX_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_Y H p hp).symm.trans
      (affineChartProjX_Y H p' hp')).source)) :
    (((affineChartProjZ_Y H p hp).symm.trans (affineChartProjX_Y H p' hp')) z) =
      ((phiYLocalHomeomorph H p hp).symm (0, z)).1 := by
  have hz0 : z ∈ (affineChartProjZ_Y H p hp).target := hz.1
  have hz0' : (0, z) ∈ (phiYLocalHomeomorph H p hp).target := by
    simpa [affineChartProjZ_Y] using hz0
  change ((affineChartProjZ_Y H p hp).symm z).val.1 =
    ((phiYLocalHomeomorph H p hp).symm (0, z)).1
  dsimp [affineChartProjZ_Y]
  rw [dif_pos hz0']

/-- The restricted `y = 1`, project-to-`Z` IFT inverse is analytic on its target. -/
theorem phiYLocalHomeomorph_contDiffOn_symm (H : PlaneCurveData)
    (p : PlaneCurveAffineY H) (hp : p ∈ PlaneCurveAffineY.smoothLocusX H) :
    ContDiffOn ℂ ω (phiYLocalHomeomorph H p hp).symm
      (phiYLocalHomeomorph H p hp).target := by
  let e := phiYLocalHomeomorph H p hp
  refine e.open_target.contDiffOn_iff.mpr ?_
  intro a ha
  have hsrc : e.symm a ∈ e.source := e.map_target ha
  have hderiv :
      (pderiv 0 H.F.val).eval (VY (e.symm a)) ≠ 0 :=
    phiYLocalHomeomorph_deriv_ne_zero_of_mem_source H p hp hsrc
  let a0 := (pderiv 0 H.F.val).eval (VY (e.symm a))
  let b0 := (pderiv 2 H.F.val).eval (VY (e.symm a))
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dphi_equiv a0 b0 hderiv
  have hf' : HasFDerivAt e (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = phiY H by
      simpa [e] using phiYLocalHomeomorph_coe H p hp]
    simpa [e', a0, b0] using hasFDerivAt_phiY H (e.symm a)
  have hf : ContDiffAt ℂ ω e (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = phiY H by
      simpa [e] using phiYLocalHomeomorph_coe H p hp]
    exact (contDiff_phiY H ω).contDiffAt
  exact e.contDiffAt_symm ha hf' hf

/-- Mixed transition compatibility in the `y = 1` patch, from project-to-`Z` to
project-to-`X`. -/
theorem affineChartProjZ_Y_compat_affineChartProjX_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H) :
    ContDiffOn ℂ ω
      (((affineChartProjZ_Y H p hp).symm.trans (affineChartProjX_Y H p' hp')) : ℂ → ℂ)
      (((affineChartProjZ_Y H p hp).symm.trans (affineChartProjX_Y H p' hp')).source) := by
  let e := phiYLocalHomeomorph H p hp
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    phiYLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun z : ℂ => ((0 : ℂ), z))
      (((affineChartProjZ_Y H p hp).symm.trans (affineChartProjX_Y H p' hp')).source) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun z : ℂ => ((0 : ℂ), z))
      (((affineChartProjZ_Y H p hp).symm.trans (affineChartProjX_Y H p' hp')).source)
      e.target := by
    intro z hz
    simpa [affineChartProjZ_Y, e] using hz.1
  refine ContDiffOn.congr ((hsymm.comp hline hmaps).fst) ?_
  intro z hz
  simpa [e] using affineChartProjZ_Y_trans_affineChartProjX_Y_apply H p p' hp hp' hz

/-- Mixed transition formula in the `y = 1` patch, from project-to-`X` to
project-to-`Z`. -/
theorem affineChartProjX_Y_trans_affineChartProjZ_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX_Y H p hp).symm.trans
      (affineChartProjZ_Y H p' hp')).source)) :
    (((affineChartProjX_Y H p hp).symm.trans (affineChartProjZ_Y H p' hp')) x) =
      ((psiYLocalHomeomorph H p hp).symm (0, x)).2 := by
  have hx0 : x ∈ (affineChartProjX_Y H p hp).target := hx.1
  have hx0' : (0, x) ∈ (psiYLocalHomeomorph H p hp).target := by
    simpa [affineChartProjX_Y] using hx0
  change ((affineChartProjX_Y H p hp).symm x).val.2 =
    ((psiYLocalHomeomorph H p hp).symm (0, x)).2
  dsimp [affineChartProjX_Y]
  rw [dif_pos hx0']

/-- The restricted `y = 1`, project-to-`X` IFT inverse is analytic on its target. -/
theorem psiYLocalHomeomorph_contDiffOn_symm (H : PlaneCurveData)
    (p : PlaneCurveAffineY H) (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H) :
    ContDiffOn ℂ ω (psiYLocalHomeomorph H p hp).symm
      (psiYLocalHomeomorph H p hp).target := by
  let e := psiYLocalHomeomorph H p hp
  refine e.open_target.contDiffOn_iff.mpr ?_
  intro a ha
  have hsrc : e.symm a ∈ e.source := e.map_target ha
  have hderiv :
      (pderiv 2 H.F.val).eval (VY (e.symm a)) ≠ 0 :=
    psiYLocalHomeomorph_deriv_ne_zero_of_mem_source H p hp hsrc
  let a0 := (pderiv 0 H.F.val).eval (VY (e.symm a))
  let b0 := (pderiv 2 H.F.val).eval (VY (e.symm a))
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dpsi_equiv a0 b0 hderiv
  have hf' : HasFDerivAt e (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = psiY H by
      simpa [e] using psiYLocalHomeomorph_coe H p hp]
    simpa [e', a0, b0] using hasFDerivAt_psiY H (e.symm a)
  have hf : ContDiffAt ℂ ω e (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = psiY H by
      simpa [e] using psiYLocalHomeomorph_coe H p hp]
    exact (contDiff_psiY H ω).contDiffAt
  exact e.contDiffAt_symm ha hf' hf

/-- Mixed transition compatibility in the `y = 1` patch, from project-to-`X` to
project-to-`Z`. -/
theorem affineChartProjX_Y_compat_affineChartProjZ_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H) :
    ContDiffOn ℂ ω
      (((affineChartProjX_Y H p hp).symm.trans (affineChartProjZ_Y H p' hp')) : ℂ → ℂ)
      (((affineChartProjX_Y H p hp).symm.trans (affineChartProjZ_Y H p' hp')).source) := by
  let e := psiYLocalHomeomorph H p hp
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    psiYLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun x : ℂ => ((0 : ℂ), x))
      (((affineChartProjX_Y H p hp).symm.trans (affineChartProjZ_Y H p' hp')).source) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => ((0 : ℂ), x))
      (((affineChartProjX_Y H p hp).symm.trans (affineChartProjZ_Y H p' hp')).source)
      e.target := by
    intro x hx
    simpa [affineChartProjX_Y, e] using hx.1
  refine ContDiffOn.congr ((hsymm.comp hline hmaps).snd) ?_
  intro x hx
  simpa [e] using affineChartProjX_Y_trans_affineChartProjZ_Y_apply H p p' hp hp' hx

/-- Mixed transition formula in the `x = 1` patch, from project-to-`Z` to
project-to-`Y`. -/
theorem affineChartProjZ_X_trans_affineChartProjY_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_X H p hp).symm.trans
      (affineChartProjY_X H p' hp')).source)) :
    (((affineChartProjZ_X H p hp).symm.trans (affineChartProjY_X H p' hp')) z) =
      ((phiXLocalHomeomorph H p hp).symm (0, z)).1 := by
  have hz0 : z ∈ (affineChartProjZ_X H p hp).target := hz.1
  have hz0' : (0, z) ∈ (phiXLocalHomeomorph H p hp).target := by
    simpa [affineChartProjZ_X] using hz0
  change ((affineChartProjZ_X H p hp).symm z).val.1 =
    ((phiXLocalHomeomorph H p hp).symm (0, z)).1
  dsimp [affineChartProjZ_X]
  rw [dif_pos hz0']

/-- The restricted `x = 1`, project-to-`Z` IFT inverse is analytic on its target. -/
theorem phiXLocalHomeomorph_contDiffOn_symm (H : PlaneCurveData)
    (p : PlaneCurveAffineX H) (hp : p ∈ PlaneCurveAffineX.smoothLocusY H) :
    ContDiffOn ℂ ω (phiXLocalHomeomorph H p hp).symm
      (phiXLocalHomeomorph H p hp).target := by
  let e := phiXLocalHomeomorph H p hp
  refine e.open_target.contDiffOn_iff.mpr ?_
  intro a ha
  have hsrc : e.symm a ∈ e.source := e.map_target ha
  have hderiv :
      (pderiv 1 H.F.val).eval (VX (e.symm a)) ≠ 0 :=
    phiXLocalHomeomorph_deriv_ne_zero_of_mem_source H p hp hsrc
  let a0 := (pderiv 1 H.F.val).eval (VX (e.symm a))
  let b0 := (pderiv 2 H.F.val).eval (VX (e.symm a))
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dphi_equiv a0 b0 hderiv
  have hf' : HasFDerivAt e (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = phiX H by
      simpa [e] using phiXLocalHomeomorph_coe H p hp]
    simpa [e', a0, b0] using hasFDerivAt_phiX H (e.symm a)
  have hf : ContDiffAt ℂ ω e (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = phiX H by
      simpa [e] using phiXLocalHomeomorph_coe H p hp]
    exact (contDiff_phiX H ω).contDiffAt
  exact e.contDiffAt_symm ha hf' hf

/-- Mixed transition compatibility in the `x = 1` patch, from project-to-`Z` to
project-to-`Y`. -/
theorem affineChartProjZ_X_compat_affineChartProjY_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H) :
    ContDiffOn ℂ ω
      (((affineChartProjZ_X H p hp).symm.trans (affineChartProjY_X H p' hp')) : ℂ → ℂ)
      (((affineChartProjZ_X H p hp).symm.trans (affineChartProjY_X H p' hp')).source) := by
  let e := phiXLocalHomeomorph H p hp
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    phiXLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun z : ℂ => ((0 : ℂ), z))
      (((affineChartProjZ_X H p hp).symm.trans (affineChartProjY_X H p' hp')).source) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun z : ℂ => ((0 : ℂ), z))
      (((affineChartProjZ_X H p hp).symm.trans (affineChartProjY_X H p' hp')).source)
      e.target := by
    intro z hz
    simpa [affineChartProjZ_X, e] using hz.1
  refine ContDiffOn.congr ((hsymm.comp hline hmaps).fst) ?_
  intro z hz
  simpa [e] using affineChartProjZ_X_trans_affineChartProjY_X_apply H p p' hp hp' hz

/-- Mixed transition formula in the `x = 1` patch, from project-to-`Y` to
project-to-`Z`. -/
theorem affineChartProjY_X_trans_affineChartProjZ_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY_X H p hp).symm.trans
      (affineChartProjZ_X H p' hp')).source)) :
    (((affineChartProjY_X H p hp).symm.trans (affineChartProjZ_X H p' hp')) y) =
      ((psiXLocalHomeomorph H p hp).symm (0, y)).2 := by
  have hy0 : y ∈ (affineChartProjY_X H p hp).target := hy.1
  have hy0' : (0, y) ∈ (psiXLocalHomeomorph H p hp).target := by
    simpa [affineChartProjY_X] using hy0
  change ((affineChartProjY_X H p hp).symm y).val.2 =
    ((psiXLocalHomeomorph H p hp).symm (0, y)).2
  dsimp [affineChartProjY_X]
  rw [dif_pos hy0']

/-- The restricted `x = 1`, project-to-`Y` IFT inverse is analytic on its target. -/
theorem psiXLocalHomeomorph_contDiffOn_symm (H : PlaneCurveData)
    (p : PlaneCurveAffineX H) (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H) :
    ContDiffOn ℂ ω (psiXLocalHomeomorph H p hp).symm
      (psiXLocalHomeomorph H p hp).target := by
  let e := psiXLocalHomeomorph H p hp
  refine e.open_target.contDiffOn_iff.mpr ?_
  intro a ha
  have hsrc : e.symm a ∈ e.source := e.map_target ha
  have hderiv :
      (pderiv 2 H.F.val).eval (VX (e.symm a)) ≠ 0 :=
    psiXLocalHomeomorph_deriv_ne_zero_of_mem_source H p hp hsrc
  let a0 := (pderiv 1 H.F.val).eval (VX (e.symm a))
  let b0 := (pderiv 2 H.F.val).eval (VX (e.symm a))
  let e' : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) := dpsi_equiv a0 b0 hderiv
  have hf' : HasFDerivAt e (e' : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = psiX H by
      simpa [e] using psiXLocalHomeomorph_coe H p hp]
    simpa [e', a0, b0] using hasFDerivAt_psiX H (e.symm a)
  have hf : ContDiffAt ℂ ω e (e.symm a) := by
    rw [show (e : ℂ × ℂ → ℂ × ℂ) = psiX H by
      simpa [e] using psiXLocalHomeomorph_coe H p hp]
    exact (contDiff_psiX H ω).contDiffAt
  exact e.contDiffAt_symm ha hf' hf

/-- Mixed transition compatibility in the `x = 1` patch, from project-to-`Y` to
project-to-`Z`. -/
theorem affineChartProjY_X_compat_affineChartProjZ_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H) :
    ContDiffOn ℂ ω
      (((affineChartProjY_X H p hp).symm.trans (affineChartProjZ_X H p' hp')) : ℂ → ℂ)
      (((affineChartProjY_X H p hp).symm.trans (affineChartProjZ_X H p' hp')).source) := by
  let e := psiXLocalHomeomorph H p hp
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    psiXLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun y : ℂ => ((0 : ℂ), y))
      (((affineChartProjY_X H p hp).symm.trans (affineChartProjZ_X H p' hp')).source) :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => ((0 : ℂ), y))
      (((affineChartProjY_X H p hp).symm.trans (affineChartProjZ_X H p' hp')).source)
      e.target := by
    intro y hy
    simpa [affineChartProjY_X, e] using hy.1
  refine ContDiffOn.congr ((hsymm.comp hline hmaps).snd) ?_
  intro y hy
  simpa [e] using affineChartProjY_X_trans_affineChartProjZ_X_apply H p p' hp hp' hy

end Jacobians.ProjectiveCurve
