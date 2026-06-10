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

/-! ### Cross-patch coordinate algebra -/

theorem affineChartProjY_symm_apply_fst (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffine H) (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    {y : ℂ} (hy : y ∈ (affineChartProjY H p hp).target) :
    ((affineChartProjY H p hp).symm y).val.1 =
      ((phiLocalHomeomorph H p hp).symm (0, y)).1 := by
  have hy' : (0, y) ∈ (phiLocalHomeomorph H p hp).target := by
    simpa [affineChartProjY] using hy
  dsimp [affineChartProjY]
  rw [dif_pos hy']

theorem affineChartProjY_symm_apply_snd (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffine H) (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    {y : ℂ} (hy : y ∈ (affineChartProjY H p hp).target) :
    ((affineChartProjY H p hp).symm y).val.2 = y := by
  have hy' : (0, y) ∈ (phiLocalHomeomorph H p hp).target := by
    simpa [affineChartProjY] using hy
  dsimp [affineChartProjY]
  rw [dif_pos hy']

theorem affineChartProjX_symm_apply_fst (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffine H) (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    {x : ℂ} (hx : x ∈ (affineChartProjX H p hp).target) :
    ((affineChartProjX H p hp).symm x).val.1 = x := by
  have hx' : (0, x) ∈ (psiLocalHomeomorph H p hp).target := by
    simpa [affineChartProjX] using hx
  dsimp [affineChartProjX]
  rw [dif_pos hx']

theorem affineChartProjX_symm_apply_snd (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffine H) (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    {x : ℂ} (hx : x ∈ (affineChartProjX H p hp).target) :
    ((affineChartProjX H p hp).symm x).val.2 =
      ((psiLocalHomeomorph H p hp).symm (0, x)).2 := by
  have hx' : (0, x) ∈ (psiLocalHomeomorph H p hp).target := by
    simpa [affineChartProjX] using hx
  dsimp [affineChartProjX]
  rw [dif_pos hx']

theorem affineChartProjZ_Y_symm_apply_fst (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineY H) (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    {z : ℂ} (hz : z ∈ (affineChartProjZ_Y H p hp).target) :
    ((affineChartProjZ_Y H p hp).symm z).val.1 =
      ((phiYLocalHomeomorph H p hp).symm (0, z)).1 := by
  have hz' : (0, z) ∈ (phiYLocalHomeomorph H p hp).target := by
    simpa [affineChartProjZ_Y] using hz
  dsimp [affineChartProjZ_Y]
  rw [dif_pos hz']

theorem affineChartProjZ_Y_symm_apply_snd (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineY H) (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    {z : ℂ} (hz : z ∈ (affineChartProjZ_Y H p hp).target) :
    ((affineChartProjZ_Y H p hp).symm z).val.2 = z := by
  have hz' : (0, z) ∈ (phiYLocalHomeomorph H p hp).target := by
    simpa [affineChartProjZ_Y] using hz
  dsimp [affineChartProjZ_Y]
  rw [dif_pos hz']

theorem affineChartProjX_Y_symm_apply_fst (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineY H) (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    {x : ℂ} (hx : x ∈ (affineChartProjX_Y H p hp).target) :
    ((affineChartProjX_Y H p hp).symm x).val.1 = x := by
  have hx' : (0, x) ∈ (psiYLocalHomeomorph H p hp).target := by
    simpa [affineChartProjX_Y] using hx
  dsimp [affineChartProjX_Y]
  rw [dif_pos hx']

theorem affineChartProjX_Y_symm_apply_snd (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineY H) (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    {x : ℂ} (hx : x ∈ (affineChartProjX_Y H p hp).target) :
    ((affineChartProjX_Y H p hp).symm x).val.2 =
      ((psiYLocalHomeomorph H p hp).symm (0, x)).2 := by
  have hx' : (0, x) ∈ (psiYLocalHomeomorph H p hp).target := by
    simpa [affineChartProjX_Y] using hx
  dsimp [affineChartProjX_Y]
  rw [dif_pos hx']

theorem affineChartProjZ_X_symm_apply_fst (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineX H) (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjZ_X H p hp).target) :
    ((affineChartProjZ_X H p hp).symm z).val.1 =
      ((phiXLocalHomeomorph H p hp).symm (0, z)).1 := by
  have hz' : (0, z) ∈ (phiXLocalHomeomorph H p hp).target := by
    simpa [affineChartProjZ_X] using hz
  dsimp [affineChartProjZ_X]
  rw [dif_pos hz']

theorem affineChartProjZ_X_symm_apply_snd (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineX H) (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    {z : ℂ} (hz : z ∈ (affineChartProjZ_X H p hp).target) :
    ((affineChartProjZ_X H p hp).symm z).val.2 = z := by
  have hz' : (0, z) ∈ (phiXLocalHomeomorph H p hp).target := by
    simpa [affineChartProjZ_X] using hz
  dsimp [affineChartProjZ_X]
  rw [dif_pos hz']

theorem affineChartProjY_X_symm_apply_fst (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineX H) (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    {y : ℂ} (hy : y ∈ (affineChartProjY_X H p hp).target) :
    ((affineChartProjY_X H p hp).symm y).val.1 = y := by
  have hy' : (0, y) ∈ (psiXLocalHomeomorph H p hp).target := by
    simpa [affineChartProjY_X] using hy
  dsimp [affineChartProjY_X]
  rw [dif_pos hy']

theorem affineChartProjY_X_symm_apply_snd (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineX H) (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    {y : ℂ} (hy : y ∈ (affineChartProjY_X H p hp).target) :
    ((affineChartProjY_X H p hp).symm y).val.2 =
      ((psiXLocalHomeomorph H p hp).symm (0, y)).2 := by
  have hy' : (0, y) ∈ (psiXLocalHomeomorph H p hp).target := by
    simpa [affineChartProjY_X] using hy
  dsimp [affineChartProjY_X]
  rw [dif_pos hy']

private lemma toPlaneCurve_eq_toPlaneCurveY_coords (H : PlaneCurveData)
    {a : PlaneCurveAffine H} {b : PlaneCurveAffineY H}
    (h : PlaneCurveAffine.toPlaneCurve H a = PlaneCurveAffineY.toPlaneCurve H b) :
    a.val.2 ≠ 0 ∧ b.val.1 = a.val.1 / a.val.2 ∧ b.val.2 = (a.val.2)⁻¹ := by
  have h_eq : (PlaneCurveAffine.toPlaneCurve H a).val =
      (PlaneCurveAffineY.toPlaneCurve H b).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffine.toPlaneCurve, PlaneCurveAffineY.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have hc1 := congr_fun hc 1
  have hc0 := congr_fun hc 0
  have hc2 := congr_fun hc 2
  change (c : ℂ) * 1 = a.val.2 at hc1
  change (c : ℂ) * b.val.1 = a.val.1 at hc0
  change (c : ℂ) * b.val.2 = 1 at hc2
  have hc_eq : (c : ℂ) = a.val.2 := by simpa using hc1
  have hy : a.val.2 ≠ 0 := by simp [← hc_eq, c.ne_zero]
  refine ⟨hy, ?_, ?_⟩
  · rw [← hc_eq]
    calc
      b.val.1 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * a.val.1 := by rw [hc0]
      _ = a.val.1 / (c : ℂ) := by rw [div_eq_mul_inv, mul_comm]
  · rw [← hc_eq]
    calc
      b.val.2 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * 1 := by rw [hc2]
      _ = (c : ℂ)⁻¹ := by rw [mul_one]

private lemma toPlaneCurveY_eq_toPlaneCurve_coords (H : PlaneCurveData)
    {a : PlaneCurveAffineY H} {b : PlaneCurveAffine H}
    (h : PlaneCurveAffineY.toPlaneCurve H a = PlaneCurveAffine.toPlaneCurve H b) :
    a.val.2 ≠ 0 ∧ b.val.1 = a.val.1 / a.val.2 ∧ b.val.2 = (a.val.2)⁻¹ := by
  have h_eq : (PlaneCurveAffineY.toPlaneCurve H a).val =
      (PlaneCurveAffine.toPlaneCurve H b).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffineY.toPlaneCurve, PlaneCurveAffine.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have hc2 := congr_fun hc 2
  have hc0 := congr_fun hc 0
  have hc1 := congr_fun hc 1
  change (c : ℂ) * 1 = a.val.2 at hc2
  change (c : ℂ) * b.val.1 = a.val.1 at hc0
  change (c : ℂ) * b.val.2 = 1 at hc1
  have hz : (c : ℂ) = a.val.2 := by simpa using hc2
  have hnz : a.val.2 ≠ 0 := by simp [← hz, c.ne_zero]
  refine ⟨hnz, ?_, ?_⟩
  · rw [← hz]
    calc
      b.val.1 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * a.val.1 := by rw [hc0]
      _ = a.val.1 / (c : ℂ) := by rw [div_eq_mul_inv, mul_comm]
  · rw [← hz]
    calc
      b.val.2 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * 1 := by rw [hc1]
      _ = (c : ℂ)⁻¹ := by rw [mul_one]

private lemma toPlaneCurve_eq_toPlaneCurveX_coords (H : PlaneCurveData)
    {a : PlaneCurveAffine H} {b : PlaneCurveAffineX H}
    (h : PlaneCurveAffine.toPlaneCurve H a = PlaneCurveAffineX.toPlaneCurve H b) :
    a.val.1 ≠ 0 ∧ b.val.1 = a.val.2 / a.val.1 ∧ b.val.2 = (a.val.1)⁻¹ := by
  have h_eq : (PlaneCurveAffine.toPlaneCurve H a).val =
      (PlaneCurveAffineX.toPlaneCurve H b).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffine.toPlaneCurve, PlaneCurveAffineX.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have hc0 := congr_fun hc 0
  have hc1 := congr_fun hc 1
  have hc2 := congr_fun hc 2
  change (c : ℂ) * 1 = a.val.1 at hc0
  change (c : ℂ) * b.val.1 = a.val.2 at hc1
  change (c : ℂ) * b.val.2 = 1 at hc2
  have hx : (c : ℂ) = a.val.1 := by simpa using hc0
  have hnz : a.val.1 ≠ 0 := by simp [← hx, c.ne_zero]
  refine ⟨hnz, ?_, ?_⟩
  · rw [← hx]
    calc
      b.val.1 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * a.val.2 := by rw [hc1]
      _ = a.val.2 / (c : ℂ) := by rw [div_eq_mul_inv, mul_comm]
  · rw [← hx]
    calc
      b.val.2 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * 1 := by rw [hc2]
      _ = (c : ℂ)⁻¹ := by rw [mul_one]

private lemma toPlaneCurveX_eq_toPlaneCurve_coords (H : PlaneCurveData)
    {a : PlaneCurveAffineX H} {b : PlaneCurveAffine H}
    (h : PlaneCurveAffineX.toPlaneCurve H a = PlaneCurveAffine.toPlaneCurve H b) :
    a.val.2 ≠ 0 ∧ b.val.1 = (a.val.2)⁻¹ ∧ b.val.2 = a.val.1 / a.val.2 := by
  have h_eq : (PlaneCurveAffineX.toPlaneCurve H a).val =
      (PlaneCurveAffine.toPlaneCurve H b).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffineX.toPlaneCurve, PlaneCurveAffine.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have hc2 := congr_fun hc 2
  have hc0 := congr_fun hc 0
  have hc1 := congr_fun hc 1
  change (c : ℂ) * 1 = a.val.2 at hc2
  change (c : ℂ) * b.val.1 = 1 at hc0
  change (c : ℂ) * b.val.2 = a.val.1 at hc1
  have hz : (c : ℂ) = a.val.2 := by simpa using hc2
  have hnz : a.val.2 ≠ 0 := by simp [← hz, c.ne_zero]
  refine ⟨hnz, ?_, ?_⟩
  · rw [← hz]
    calc
      b.val.1 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * 1 := by rw [hc0]
      _ = (c : ℂ)⁻¹ := by rw [mul_one]
  · rw [← hz]
    calc
      b.val.2 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * a.val.1 := by rw [hc1]
      _ = a.val.1 / (c : ℂ) := by rw [div_eq_mul_inv, mul_comm]

private lemma toPlaneCurveY_eq_toPlaneCurveX_coords (H : PlaneCurveData)
    {a : PlaneCurveAffineY H} {b : PlaneCurveAffineX H}
    (h : PlaneCurveAffineY.toPlaneCurve H a = PlaneCurveAffineX.toPlaneCurve H b) :
    a.val.1 ≠ 0 ∧ b.val.1 = (a.val.1)⁻¹ ∧ b.val.2 = a.val.2 / a.val.1 := by
  have h_eq : (PlaneCurveAffineY.toPlaneCurve H a).val =
      (PlaneCurveAffineX.toPlaneCurve H b).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffineY.toPlaneCurve, PlaneCurveAffineX.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have hc0 := congr_fun hc 0
  have hc1 := congr_fun hc 1
  have hc2 := congr_fun hc 2
  change (c : ℂ) * 1 = a.val.1 at hc0
  change (c : ℂ) * b.val.1 = 1 at hc1
  change (c : ℂ) * b.val.2 = a.val.2 at hc2
  have hx : (c : ℂ) = a.val.1 := by simpa using hc0
  have hnz : a.val.1 ≠ 0 := by simp [← hx, c.ne_zero]
  refine ⟨hnz, ?_, ?_⟩
  · rw [← hx]
    calc
      b.val.1 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * 1 := by rw [hc1]
      _ = (c : ℂ)⁻¹ := by rw [mul_one]
  · rw [← hx]
    calc
      b.val.2 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * a.val.2 := by rw [hc2]
      _ = a.val.2 / (c : ℂ) := by rw [div_eq_mul_inv, mul_comm]

private lemma toPlaneCurveX_eq_toPlaneCurveY_coords (H : PlaneCurveData)
    {a : PlaneCurveAffineX H} {b : PlaneCurveAffineY H}
    (h : PlaneCurveAffineX.toPlaneCurve H a = PlaneCurveAffineY.toPlaneCurve H b) :
    a.val.1 ≠ 0 ∧ b.val.1 = (a.val.1)⁻¹ ∧ b.val.2 = a.val.2 / a.val.1 := by
  have h_eq : (PlaneCurveAffineX.toPlaneCurve H a).val =
      (PlaneCurveAffineY.toPlaneCurve H b).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffineX.toPlaneCurve, PlaneCurveAffineY.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have hc1 := congr_fun hc 1
  have hc0 := congr_fun hc 0
  have hc2 := congr_fun hc 2
  change (c : ℂ) * 1 = a.val.1 at hc1
  change (c : ℂ) * b.val.1 = 1 at hc0
  change (c : ℂ) * b.val.2 = a.val.2 at hc2
  have hy : (c : ℂ) = a.val.1 := by simpa using hc1
  have hnz : a.val.1 ≠ 0 := by simp [← hy, c.ne_zero]
  refine ⟨hnz, ?_, ?_⟩
  · rw [← hy]
    calc
      b.val.1 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.1) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * 1 := by rw [hc0]
      _ = (c : ℂ)⁻¹ := by rw [mul_one]
  · rw [← hy]
    calc
      b.val.2 = (c : ℂ)⁻¹ * ((c : ℂ) * b.val.2) := by
        rw [← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
      _ = (c : ℂ)⁻¹ * a.val.2 := by rw [hc2]
      _ = a.val.2 / (c : ℂ) := by rw [div_eq_mul_inv, mul_comm]

/-! ### Cross-patch transitions: `z = 1` to `y = 1` -/

private lemma z_to_y_lift_source_data (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (eZ : OpenPartialHomeomorph (PlaneCurveAffine H) ℂ)
    (eY : OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
      (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source) :
    w ∈ eZ.target ∧
      ∃ b : PlaneCurveAffineY H, b ∈ eY.source ∧
        PlaneCurveAffineY.toPlaneCurve H b =
          PlaneCurveAffine.toPlaneCurve H (eZ.symm w) := by
  constructor
  · simpa [OpenPartialHomeomorph.lift_openEmbedding_target] using hw.1
  · have hws := hw.2
    simpa [OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply] using hws

private lemma z_to_y_overlap_y_ne_zero (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (eZ : OpenPartialHomeomorph (PlaneCurveAffine H) ℂ)
    (eY : OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
      (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source) :
    (eZ.symm w).val.2 ≠ 0 := by
  rcases (z_to_y_lift_source_data H eZ eY hw).2 with ⟨b, _hb_src, hb_eq⟩
  exact (toPlaneCurve_eq_toPlaneCurveY_coords H hb_eq.symm).1

/-- Cross-patch transition formula from the `z = 1`, project-to-`Y` chart to
the `y = 1`, project-to-`Z` chart. -/
theorem affineChartProjY_lift_trans_affineChartProjZ_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjZ_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H))).source) :
    (((affineChartProjY H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjZ_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)) y) = y⁻¹ := by
  let eZ := affineChartProjY H p hp
  let eY := affineChartProjZ_Y H p' hp'
  rcases z_to_y_lift_source_data H eZ eY hy with ⟨hy_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurve_eq_toPlaneCurveY_coords H hb_eq.symm
  have hy_snd : (eZ.symm y).val.2 = y :=
    affineChartProjY_symm_apply_snd H p hp hy_target
  change (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))
      (PlaneCurveAffine.toPlaneCurve H (eZ.symm y)) = y⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = y⁻¹
  rw [hcoords.2.2, hy_snd]

/-- Cross-patch compatibility from the `z = 1`, project-to-`Y` chart to the
`y = 1`, project-to-`Z` chart. -/
theorem affineChartProjY_lift_compat_affineChartProjZ_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((affineChartProjY H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjZ_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))) : ℂ → ℂ)
      (((affineChartProjY H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjZ_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))).source := by
  let eZ := affineChartProjY H p hp
  let eY := affineChartProjZ_Y H p' hp'
  let s := ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
    (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source
  have hne : ∀ y ∈ s, y ≠ 0 := by
    intro y hy
    have hy_target := (z_to_y_lift_source_data H eZ eY hy).1
    have hy_nonzero := z_to_y_overlap_y_ne_zero H eZ eY hy
    have hy_snd : (eZ.symm y).val.2 = y :=
      affineChartProjY_symm_apply_snd H p hp hy_target
    simpa [hy_snd] using hy_nonzero
  exact ContDiffOn.congr
    ((contDiffOn_id (𝕜 := ℂ) (n := ω) (s := s)).inv hne)
    (fun y hy => affineChartProjY_lift_trans_affineChartProjZ_Y_apply H p p' hp hp' hy)

/-- Cross-patch transition formula from the `z = 1`, project-to-`Y` chart to
the `y = 1`, project-to-`X` chart. -/
theorem affineChartProjY_lift_trans_affineChartProjX_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjX_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H))).source) :
    (((affineChartProjY H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjX_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)) y) =
      ((phiLocalHomeomorph H p hp).symm (0, y)).1 / y := by
  let eZ := affineChartProjY H p hp
  let eY := affineChartProjX_Y H p' hp'
  rcases z_to_y_lift_source_data H eZ eY hy with ⟨hy_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurve_eq_toPlaneCurveY_coords H hb_eq.symm
  have hy_fst : (eZ.symm y).val.1 =
      ((phiLocalHomeomorph H p hp).symm (0, y)).1 :=
    affineChartProjY_symm_apply_fst H p hp hy_target
  have hy_snd : (eZ.symm y).val.2 = y :=
    affineChartProjY_symm_apply_snd H p hp hy_target
  change (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))
      (PlaneCurveAffine.toPlaneCurve H (eZ.symm y)) =
        ((phiLocalHomeomorph H p hp).symm (0, y)).1 / y
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = ((phiLocalHomeomorph H p hp).symm (0, y)).1 / y
  rw [hcoords.2.1, hy_fst, hy_snd]

/-- Cross-patch compatibility from the `z = 1`, project-to-`Y` chart to the
`y = 1`, project-to-`X` chart. -/
theorem affineChartProjY_lift_compat_affineChartProjX_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H) :
    ContDiffOn ℂ ω
      ((((affineChartProjY H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjX_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))) : ℂ → ℂ)
      (((affineChartProjY H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjX_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))).source := by
  let eZ := affineChartProjY H p hp
  let eY := affineChartProjX_Y H p' hp'
  let s := ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
    (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source
  have hsymm : ContDiffOn ℂ ω (phiLocalHomeomorph H p hp).symm
      (phiLocalHomeomorph H p hp).target :=
    phiLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun y : ℂ => ((0 : ℂ), y)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => ((0 : ℂ), y)) s
      (phiLocalHomeomorph H p hp).target := by
    intro y hy
    have hy_target := (z_to_y_lift_source_data H eZ eY hy).1
    simpa [eZ, affineChartProjY] using hy_target
  have hbranch : ContDiffOn ℂ ω
      (fun y : ℂ => ((phiLocalHomeomorph H p hp).symm (0, y)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ y ∈ s, y ≠ 0 := by
    intro y hy
    have hy_target := (z_to_y_lift_source_data H eZ eY hy).1
    have hy_nonzero := z_to_y_overlap_y_ne_zero H eZ eY hy
    have hy_snd : (eZ.symm y).val.2 = y :=
      affineChartProjY_symm_apply_snd H p hp hy_target
    simpa [hy_snd] using hy_nonzero
  exact ContDiffOn.congr
    (hbranch.div contDiffOn_id hne)
    (fun y hy => affineChartProjY_lift_trans_affineChartProjX_Y_apply H p p' hp hp' hy)

/-- Cross-patch transition formula from the `z = 1`, project-to-`X` chart to
the `y = 1`, project-to-`Z` chart. -/
theorem affineChartProjX_lift_trans_affineChartProjZ_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjZ_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H))).source) :
    (((affineChartProjX H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjZ_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)) x) =
      (((psiLocalHomeomorph H p hp).symm (0, x)).2)⁻¹ := by
  let eZ := affineChartProjX H p hp
  let eY := affineChartProjZ_Y H p' hp'
  rcases z_to_y_lift_source_data H eZ eY hx with ⟨hx_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurve_eq_toPlaneCurveY_coords H hb_eq.symm
  have hx_snd : (eZ.symm x).val.2 =
      ((psiLocalHomeomorph H p hp).symm (0, x)).2 :=
    affineChartProjX_symm_apply_snd H p hp hx_target
  change (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))
      (PlaneCurveAffine.toPlaneCurve H (eZ.symm x)) =
        (((psiLocalHomeomorph H p hp).symm (0, x)).2)⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = (((psiLocalHomeomorph H p hp).symm (0, x)).2)⁻¹
  rw [hcoords.2.2, hx_snd]

/-- Cross-patch compatibility from the `z = 1`, project-to-`X` chart to the
`y = 1`, project-to-`Z` chart. -/
theorem affineChartProjX_lift_compat_affineChartProjZ_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((affineChartProjX H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjZ_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))) : ℂ → ℂ)
      (((affineChartProjX H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjZ_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))).source := by
  let eZ := affineChartProjX H p hp
  let eY := affineChartProjZ_Y H p' hp'
  let s := ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
    (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source
  have hsymm : ContDiffOn ℂ ω (psiLocalHomeomorph H p hp).symm
      (psiLocalHomeomorph H p hp).target :=
    psiLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun x : ℂ => ((0 : ℂ), x)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => ((0 : ℂ), x)) s
      (psiLocalHomeomorph H p hp).target := by
    intro x hx
    have hx_target := (z_to_y_lift_source_data H eZ eY hx).1
    simpa [eZ, affineChartProjX] using hx_target
  have hbranch : ContDiffOn ℂ ω
      (fun x : ℂ => ((psiLocalHomeomorph H p hp).symm (0, x)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ x ∈ s, ((psiLocalHomeomorph H p hp).symm (0, x)).2 ≠ 0 := by
    intro x hx
    have hx_target := (z_to_y_lift_source_data H eZ eY hx).1
    have hy_nonzero := z_to_y_overlap_y_ne_zero H eZ eY hx
    have hx_snd : (eZ.symm x).val.2 =
        ((psiLocalHomeomorph H p hp).symm (0, x)).2 :=
      affineChartProjX_symm_apply_snd H p hp hx_target
    simpa [hx_snd] using hy_nonzero
  exact ContDiffOn.congr
    (hbranch.inv hne)
    (fun x hx => affineChartProjX_lift_trans_affineChartProjZ_Y_apply H p p' hp hp' hx)

/-- Cross-patch transition formula from the `z = 1`, project-to-`X` chart to
the `y = 1`, project-to-`X` chart. -/
theorem affineChartProjX_lift_trans_affineChartProjX_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjX_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H))).source) :
    (((affineChartProjX H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjX_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)) x) =
      x / ((psiLocalHomeomorph H p hp).symm (0, x)).2 := by
  let eZ := affineChartProjX H p hp
  let eY := affineChartProjX_Y H p' hp'
  rcases z_to_y_lift_source_data H eZ eY hx with ⟨hx_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurve_eq_toPlaneCurveY_coords H hb_eq.symm
  have hx_fst : (eZ.symm x).val.1 = x :=
    affineChartProjX_symm_apply_fst H p hp hx_target
  have hx_snd : (eZ.symm x).val.2 =
      ((psiLocalHomeomorph H p hp).symm (0, x)).2 :=
    affineChartProjX_symm_apply_snd H p hp hx_target
  change (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))
      (PlaneCurveAffine.toPlaneCurve H (eZ.symm x)) =
        x / ((psiLocalHomeomorph H p hp).symm (0, x)).2
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = x / ((psiLocalHomeomorph H p hp).symm (0, x)).2
  rw [hcoords.2.1, hx_fst, hx_snd]

/-- Cross-patch compatibility from the `z = 1`, project-to-`X` chart to the
`y = 1`, project-to-`X` chart. -/
theorem affineChartProjX_lift_compat_affineChartProjX_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H) :
    ContDiffOn ℂ ω
      ((((affineChartProjX H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjX_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))) : ℂ → ℂ)
      (((affineChartProjX H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjX_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))).source := by
  let eZ := affineChartProjX H p hp
  let eY := affineChartProjX_Y H p' hp'
  let s := ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
    (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source
  have hsymm : ContDiffOn ℂ ω (psiLocalHomeomorph H p hp).symm
      (psiLocalHomeomorph H p hp).target :=
    psiLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun x : ℂ => ((0 : ℂ), x)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => ((0 : ℂ), x)) s
      (psiLocalHomeomorph H p hp).target := by
    intro x hx
    have hx_target := (z_to_y_lift_source_data H eZ eY hx).1
    simpa [eZ, affineChartProjX] using hx_target
  have hbranch : ContDiffOn ℂ ω
      (fun x : ℂ => ((psiLocalHomeomorph H p hp).symm (0, x)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ x ∈ s, ((psiLocalHomeomorph H p hp).symm (0, x)).2 ≠ 0 := by
    intro x hx
    have hx_target := (z_to_y_lift_source_data H eZ eY hx).1
    have hy_nonzero := z_to_y_overlap_y_ne_zero H eZ eY hx
    have hx_snd : (eZ.symm x).val.2 =
        ((psiLocalHomeomorph H p hp).symm (0, x)).2 :=
      affineChartProjX_symm_apply_snd H p hp hx_target
    simpa [hx_snd] using hy_nonzero
  exact ContDiffOn.congr
    (contDiffOn_id.div hbranch hne)
    (fun x hx => affineChartProjX_lift_trans_affineChartProjX_Y_apply H p p' hp hp' hx)

/-! ### Cross-patch transitions: `y = 1` to `z = 1` -/

private lemma y_to_z_lift_source_data (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (eY : OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ)
    (eZ : OpenPartialHomeomorph (PlaneCurveAffine H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source) :
    w ∈ eY.target ∧
      ∃ b : PlaneCurveAffine H, b ∈ eZ.source ∧
        PlaneCurveAffine.toPlaneCurve H b =
          PlaneCurveAffineY.toPlaneCurve H (eY.symm w) := by
  constructor
  · simpa [OpenPartialHomeomorph.lift_openEmbedding_target] using hw.1
  · have hws := hw.2
    simpa [OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply] using hws

private lemma y_to_z_overlap_z_ne_zero (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (eY : OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ)
    (eZ : OpenPartialHomeomorph (PlaneCurveAffine H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source) :
    (eY.symm w).val.2 ≠ 0 := by
  rcases (y_to_z_lift_source_data H eY eZ hw).2 with ⟨b, _hb_src, hb_eq⟩
  exact (toPlaneCurveY_eq_toPlaneCurve_coords H hb_eq.symm).1

/-- Cross-patch transition formula from the `y = 1`, project-to-`Z` chart to
the `z = 1`, project-to-`Y` chart. -/
theorem affineChartProjZ_Y_lift_trans_affineChartProjY_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjY H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H))).source) :
    (((affineChartProjZ_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjY H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)) z) = z⁻¹ := by
  let eY := affineChartProjZ_Y H p hp
  let eZ := affineChartProjY H p' hp'
  rcases y_to_z_lift_source_data H eY eZ hz with ⟨hz_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveY_eq_toPlaneCurve_coords H hb_eq.symm
  have hz_snd : (eY.symm z).val.2 = z :=
    affineChartProjZ_Y_symm_apply_snd H p hp hz_target
  change (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))
      (PlaneCurveAffineY.toPlaneCurve H (eY.symm z)) = z⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = z⁻¹
  rw [hcoords.2.2, hz_snd]

/-- Cross-patch compatibility from the `y = 1`, project-to-`Z` chart to the
`z = 1`, project-to-`Y` chart. -/
theorem affineChartProjZ_Y_lift_compat_affineChartProjY (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((affineChartProjZ_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjY H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))) : ℂ → ℂ)
      (((affineChartProjZ_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjY H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))).source := by
  let eY := affineChartProjZ_Y H p hp
  let eZ := affineChartProjY H p' hp'
  let s := ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
    (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source
  have hne : ∀ z ∈ s, z ≠ 0 := by
    intro z hz
    have hz_target := (y_to_z_lift_source_data H eY eZ hz).1
    have hz_nonzero := y_to_z_overlap_z_ne_zero H eY eZ hz
    have hz_snd : (eY.symm z).val.2 = z :=
      affineChartProjZ_Y_symm_apply_snd H p hp hz_target
    simpa [hz_snd] using hz_nonzero
  exact ContDiffOn.congr
    ((contDiffOn_id (𝕜 := ℂ) (n := ω) (s := s)).inv hne)
    (fun z hz => affineChartProjZ_Y_lift_trans_affineChartProjY_apply H p p' hp hp' hz)

/-- Cross-patch transition formula from the `y = 1`, project-to-`Z` chart to
the `z = 1`, project-to-`X` chart. -/
theorem affineChartProjZ_Y_lift_trans_affineChartProjX_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjX H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H))).source) :
    (((affineChartProjZ_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjX H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)) z) =
      ((phiYLocalHomeomorph H p hp).symm (0, z)).1 / z := by
  let eY := affineChartProjZ_Y H p hp
  let eZ := affineChartProjX H p' hp'
  rcases y_to_z_lift_source_data H eY eZ hz with ⟨hz_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveY_eq_toPlaneCurve_coords H hb_eq.symm
  have hz_fst : (eY.symm z).val.1 =
      ((phiYLocalHomeomorph H p hp).symm (0, z)).1 :=
    affineChartProjZ_Y_symm_apply_fst H p hp hz_target
  have hz_snd : (eY.symm z).val.2 = z :=
    affineChartProjZ_Y_symm_apply_snd H p hp hz_target
  change (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))
      (PlaneCurveAffineY.toPlaneCurve H (eY.symm z)) =
        ((phiYLocalHomeomorph H p hp).symm (0, z)).1 / z
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = ((phiYLocalHomeomorph H p hp).symm (0, z)).1 / z
  rw [hcoords.2.1, hz_fst, hz_snd]

/-- Cross-patch compatibility from the `y = 1`, project-to-`Z` chart to the
`z = 1`, project-to-`X` chart. -/
theorem affineChartProjZ_Y_lift_compat_affineChartProjX (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((affineChartProjZ_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjX H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))) : ℂ → ℂ)
      (((affineChartProjZ_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjX H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))).source := by
  let eY := affineChartProjZ_Y H p hp
  let eZ := affineChartProjX H p' hp'
  let s := ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
    (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source
  have hsymm : ContDiffOn ℂ ω (phiYLocalHomeomorph H p hp).symm
      (phiYLocalHomeomorph H p hp).target :=
    phiYLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun z : ℂ => ((0 : ℂ), z)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun z : ℂ => ((0 : ℂ), z)) s
      (phiYLocalHomeomorph H p hp).target := by
    intro z hz
    have hz_target := (y_to_z_lift_source_data H eY eZ hz).1
    simpa [eY, affineChartProjZ_Y] using hz_target
  have hbranch : ContDiffOn ℂ ω
      (fun z : ℂ => ((phiYLocalHomeomorph H p hp).symm (0, z)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ z ∈ s, z ≠ 0 := by
    intro z hz
    have hz_target := (y_to_z_lift_source_data H eY eZ hz).1
    have hz_nonzero := y_to_z_overlap_z_ne_zero H eY eZ hz
    have hz_snd : (eY.symm z).val.2 = z :=
      affineChartProjZ_Y_symm_apply_snd H p hp hz_target
    simpa [hz_snd] using hz_nonzero
  exact ContDiffOn.congr
    (hbranch.div contDiffOn_id hne)
    (fun z hz => affineChartProjZ_Y_lift_trans_affineChartProjX_apply H p p' hp hp' hz)

/-- Cross-patch transition formula from the `y = 1`, project-to-`X` chart to
the `z = 1`, project-to-`Y` chart. -/
theorem affineChartProjX_Y_lift_trans_affineChartProjY_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjY H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H))).source) :
    (((affineChartProjX_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjY H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)) x) =
      (((psiYLocalHomeomorph H p hp).symm (0, x)).2)⁻¹ := by
  let eY := affineChartProjX_Y H p hp
  let eZ := affineChartProjY H p' hp'
  rcases y_to_z_lift_source_data H eY eZ hx with ⟨hx_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveY_eq_toPlaneCurve_coords H hb_eq.symm
  have hx_snd : (eY.symm x).val.2 =
      ((psiYLocalHomeomorph H p hp).symm (0, x)).2 :=
    affineChartProjX_Y_symm_apply_snd H p hp hx_target
  change (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))
      (PlaneCurveAffineY.toPlaneCurve H (eY.symm x)) =
        (((psiYLocalHomeomorph H p hp).symm (0, x)).2)⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = (((psiYLocalHomeomorph H p hp).symm (0, x)).2)⁻¹
  rw [hcoords.2.2, hx_snd]

/-- Cross-patch compatibility from the `y = 1`, project-to-`X` chart to the
`z = 1`, project-to-`Y` chart. -/
theorem affineChartProjX_Y_lift_compat_affineChartProjY (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((affineChartProjX_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjY H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))) : ℂ → ℂ)
      (((affineChartProjX_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjY H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))).source := by
  let eY := affineChartProjX_Y H p hp
  let eZ := affineChartProjY H p' hp'
  let s := ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
    (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source
  have hsymm : ContDiffOn ℂ ω (psiYLocalHomeomorph H p hp).symm
      (psiYLocalHomeomorph H p hp).target :=
    psiYLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun x : ℂ => ((0 : ℂ), x)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => ((0 : ℂ), x)) s
      (psiYLocalHomeomorph H p hp).target := by
    intro x hx
    have hx_target := (y_to_z_lift_source_data H eY eZ hx).1
    simpa [eY, affineChartProjX_Y] using hx_target
  have hbranch : ContDiffOn ℂ ω
      (fun x : ℂ => ((psiYLocalHomeomorph H p hp).symm (0, x)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ x ∈ s, ((psiYLocalHomeomorph H p hp).symm (0, x)).2 ≠ 0 := by
    intro x hx
    have hx_target := (y_to_z_lift_source_data H eY eZ hx).1
    have hz_nonzero := y_to_z_overlap_z_ne_zero H eY eZ hx
    have hx_snd : (eY.symm x).val.2 =
        ((psiYLocalHomeomorph H p hp).symm (0, x)).2 :=
      affineChartProjX_Y_symm_apply_snd H p hp hx_target
    simpa [hx_snd] using hz_nonzero
  exact ContDiffOn.congr
    (hbranch.inv hne)
    (fun x hx => affineChartProjX_Y_lift_trans_affineChartProjY_apply H p p' hp hp' hx)

/-- Cross-patch transition formula from the `y = 1`, project-to-`X` chart to
the `z = 1`, project-to-`X` chart. -/
theorem affineChartProjX_Y_lift_trans_affineChartProjX_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjX H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H))).source) :
    (((affineChartProjX_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjX H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)) x) =
      x / ((psiYLocalHomeomorph H p hp).symm (0, x)).2 := by
  let eY := affineChartProjX_Y H p hp
  let eZ := affineChartProjX H p' hp'
  rcases y_to_z_lift_source_data H eY eZ hx with ⟨hx_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveY_eq_toPlaneCurve_coords H hb_eq.symm
  have hx_fst : (eY.symm x).val.1 = x :=
    affineChartProjX_Y_symm_apply_fst H p hp hx_target
  have hx_snd : (eY.symm x).val.2 =
      ((psiYLocalHomeomorph H p hp).symm (0, x)).2 :=
    affineChartProjX_Y_symm_apply_snd H p hp hx_target
  change (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))
      (PlaneCurveAffineY.toPlaneCurve H (eY.symm x)) =
        x / ((psiYLocalHomeomorph H p hp).symm (0, x)).2
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = x / ((psiYLocalHomeomorph H p hp).symm (0, x)).2
  rw [hcoords.2.1, hx_fst, hx_snd]

/-- Cross-patch compatibility from the `y = 1`, project-to-`X` chart to the
`z = 1`, project-to-`X` chart. -/
theorem affineChartProjX_Y_lift_compat_affineChartProjX (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((affineChartProjX_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjX H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))) : ℂ → ℂ)
      (((affineChartProjX_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjX H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))).source := by
  let eY := affineChartProjX_Y H p hp
  let eZ := affineChartProjX H p' hp'
  let s := ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
    (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source
  have hsymm : ContDiffOn ℂ ω (psiYLocalHomeomorph H p hp).symm
      (psiYLocalHomeomorph H p hp).target :=
    psiYLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun x : ℂ => ((0 : ℂ), x)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => ((0 : ℂ), x)) s
      (psiYLocalHomeomorph H p hp).target := by
    intro x hx
    have hx_target := (y_to_z_lift_source_data H eY eZ hx).1
    simpa [eY, affineChartProjX_Y] using hx_target
  have hbranch : ContDiffOn ℂ ω
      (fun x : ℂ => ((psiYLocalHomeomorph H p hp).symm (0, x)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ x ∈ s, ((psiYLocalHomeomorph H p hp).symm (0, x)).2 ≠ 0 := by
    intro x hx
    have hx_target := (y_to_z_lift_source_data H eY eZ hx).1
    have hz_nonzero := y_to_z_overlap_z_ne_zero H eY eZ hx
    have hx_snd : (eY.symm x).val.2 =
        ((psiYLocalHomeomorph H p hp).symm (0, x)).2 :=
      affineChartProjX_Y_symm_apply_snd H p hp hx_target
    simpa [hx_snd] using hz_nonzero
  exact ContDiffOn.congr
    (contDiffOn_id.div hbranch hne)
    (fun x hx => affineChartProjX_Y_lift_trans_affineChartProjX_apply H p p' hp hp' hx)

/-! ### Cross-patch transitions: `z = 1` to `x = 1` -/

private lemma z_to_x_lift_source_data (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (eZ : OpenPartialHomeomorph (PlaneCurveAffine H) ℂ)
    (eX : OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
      (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source) :
    w ∈ eZ.target ∧
      ∃ b : PlaneCurveAffineX H, b ∈ eX.source ∧
        PlaneCurveAffineX.toPlaneCurve H b =
          PlaneCurveAffine.toPlaneCurve H (eZ.symm w) := by
  constructor
  · simpa [OpenPartialHomeomorph.lift_openEmbedding_target] using hw.1
  · have hws := hw.2
    simpa [OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply] using hws

private lemma z_to_x_overlap_x_ne_zero (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (eZ : OpenPartialHomeomorph (PlaneCurveAffine H) ℂ)
    (eX : OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
      (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source) :
    (eZ.symm w).val.1 ≠ 0 := by
  rcases (z_to_x_lift_source_data H eZ eX hw).2 with ⟨b, _hb_src, hb_eq⟩
  exact (toPlaneCurve_eq_toPlaneCurveX_coords H hb_eq.symm).1

/-- Cross-patch transition formula from the `z = 1`, project-to-`X` chart to
the `x = 1`, project-to-`Z` chart. -/
theorem affineChartProjX_lift_trans_affineChartProjZ_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjZ_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H))).source) :
    (((affineChartProjX H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjZ_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)) x) = x⁻¹ := by
  let eZ := affineChartProjX H p hp
  let eX := affineChartProjZ_X H p' hp'
  rcases z_to_x_lift_source_data H eZ eX hx with ⟨hx_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurve_eq_toPlaneCurveX_coords H hb_eq.symm
  have hx_fst : (eZ.symm x).val.1 = x :=
    affineChartProjX_symm_apply_fst H p hp hx_target
  change (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))
      (PlaneCurveAffine.toPlaneCurve H (eZ.symm x)) = x⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = x⁻¹
  rw [hcoords.2.2, hx_fst]

/-- Cross-patch compatibility from the `z = 1`, project-to-`X` chart to the
`x = 1`, project-to-`Z` chart. -/
theorem affineChartProjX_lift_compat_affineChartProjZ_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((affineChartProjX H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjZ_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))) : ℂ → ℂ)
      (((affineChartProjX H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjZ_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))).source := by
  let eZ := affineChartProjX H p hp
  let eX := affineChartProjZ_X H p' hp'
  let s := ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
    (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source
  have hne : ∀ x ∈ s, x ≠ 0 := by
    intro x hx
    have hx_target := (z_to_x_lift_source_data H eZ eX hx).1
    have hx_nonzero := z_to_x_overlap_x_ne_zero H eZ eX hx
    have hx_fst : (eZ.symm x).val.1 = x :=
      affineChartProjX_symm_apply_fst H p hp hx_target
    simpa [hx_fst] using hx_nonzero
  exact ContDiffOn.congr
    ((contDiffOn_id (𝕜 := ℂ) (n := ω) (s := s)).inv hne)
    (fun x hx => affineChartProjX_lift_trans_affineChartProjZ_X_apply H p p' hp hp' hx)

/-- Cross-patch transition formula from the `z = 1`, project-to-`X` chart to
the `x = 1`, project-to-`Y` chart. -/
theorem affineChartProjX_lift_trans_affineChartProjY_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjY_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H))).source) :
    (((affineChartProjX H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjY_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)) x) =
      ((psiLocalHomeomorph H p hp).symm (0, x)).2 / x := by
  let eZ := affineChartProjX H p hp
  let eX := affineChartProjY_X H p' hp'
  rcases z_to_x_lift_source_data H eZ eX hx with ⟨hx_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurve_eq_toPlaneCurveX_coords H hb_eq.symm
  have hx_fst : (eZ.symm x).val.1 = x :=
    affineChartProjX_symm_apply_fst H p hp hx_target
  have hx_snd : (eZ.symm x).val.2 =
      ((psiLocalHomeomorph H p hp).symm (0, x)).2 :=
    affineChartProjX_symm_apply_snd H p hp hx_target
  change (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))
      (PlaneCurveAffine.toPlaneCurve H (eZ.symm x)) =
        ((psiLocalHomeomorph H p hp).symm (0, x)).2 / x
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = ((psiLocalHomeomorph H p hp).symm (0, x)).2 / x
  rw [hcoords.2.1, hx_snd, hx_fst]

/-- Cross-patch compatibility from the `z = 1`, project-to-`X` chart to the
`x = 1`, project-to-`Y` chart. -/
theorem affineChartProjX_lift_compat_affineChartProjY_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H) :
    ContDiffOn ℂ ω
      ((((affineChartProjX H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjY_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))) : ℂ → ℂ)
      (((affineChartProjX H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjY_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))).source := by
  let eZ := affineChartProjX H p hp
  let eX := affineChartProjY_X H p' hp'
  let s := ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
    (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source
  have hsymm : ContDiffOn ℂ ω (psiLocalHomeomorph H p hp).symm
      (psiLocalHomeomorph H p hp).target :=
    psiLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun x : ℂ => ((0 : ℂ), x)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => ((0 : ℂ), x)) s
      (psiLocalHomeomorph H p hp).target := by
    intro x hx
    have hx_target := (z_to_x_lift_source_data H eZ eX hx).1
    simpa [eZ, affineChartProjX] using hx_target
  have hbranch : ContDiffOn ℂ ω
      (fun x : ℂ => ((psiLocalHomeomorph H p hp).symm (0, x)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ x ∈ s, x ≠ 0 := by
    intro x hx
    have hx_target := (z_to_x_lift_source_data H eZ eX hx).1
    have hx_nonzero := z_to_x_overlap_x_ne_zero H eZ eX hx
    have hx_fst : (eZ.symm x).val.1 = x :=
      affineChartProjX_symm_apply_fst H p hp hx_target
    simpa [hx_fst] using hx_nonzero
  exact ContDiffOn.congr
    (hbranch.div contDiffOn_id hne)
    (fun x hx => affineChartProjX_lift_trans_affineChartProjY_X_apply H p p' hp hp' hx)

/-- Cross-patch transition formula from the `z = 1`, project-to-`Y` chart to
the `x = 1`, project-to-`Z` chart. -/
theorem affineChartProjY_lift_trans_affineChartProjZ_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjZ_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H))).source) :
    (((affineChartProjY H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjZ_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)) y) =
      (((phiLocalHomeomorph H p hp).symm (0, y)).1)⁻¹ := by
  let eZ := affineChartProjY H p hp
  let eX := affineChartProjZ_X H p' hp'
  rcases z_to_x_lift_source_data H eZ eX hy with ⟨hy_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurve_eq_toPlaneCurveX_coords H hb_eq.symm
  have hy_fst : (eZ.symm y).val.1 =
      ((phiLocalHomeomorph H p hp).symm (0, y)).1 :=
    affineChartProjY_symm_apply_fst H p hp hy_target
  change (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))
      (PlaneCurveAffine.toPlaneCurve H (eZ.symm y)) =
        (((phiLocalHomeomorph H p hp).symm (0, y)).1)⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = (((phiLocalHomeomorph H p hp).symm (0, y)).1)⁻¹
  rw [hcoords.2.2, hy_fst]

/-- Cross-patch compatibility from the `z = 1`, project-to-`Y` chart to the
`x = 1`, project-to-`Z` chart. -/
theorem affineChartProjY_lift_compat_affineChartProjZ_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((affineChartProjY H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjZ_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))) : ℂ → ℂ)
      (((affineChartProjY H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjZ_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))).source := by
  let eZ := affineChartProjY H p hp
  let eX := affineChartProjZ_X H p' hp'
  let s := ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
    (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source
  have hsymm : ContDiffOn ℂ ω (phiLocalHomeomorph H p hp).symm
      (phiLocalHomeomorph H p hp).target :=
    phiLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun y : ℂ => ((0 : ℂ), y)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => ((0 : ℂ), y)) s
      (phiLocalHomeomorph H p hp).target := by
    intro y hy
    have hy_target := (z_to_x_lift_source_data H eZ eX hy).1
    simpa [eZ, affineChartProjY] using hy_target
  have hbranch : ContDiffOn ℂ ω
      (fun y : ℂ => ((phiLocalHomeomorph H p hp).symm (0, y)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ y ∈ s, ((phiLocalHomeomorph H p hp).symm (0, y)).1 ≠ 0 := by
    intro y hy
    have hy_target := (z_to_x_lift_source_data H eZ eX hy).1
    have hx_nonzero := z_to_x_overlap_x_ne_zero H eZ eX hy
    have hy_fst : (eZ.symm y).val.1 =
        ((phiLocalHomeomorph H p hp).symm (0, y)).1 :=
      affineChartProjY_symm_apply_fst H p hp hy_target
    simpa [hy_fst] using hx_nonzero
  exact ContDiffOn.congr
    (hbranch.inv hne)
    (fun y hy => affineChartProjY_lift_trans_affineChartProjZ_X_apply H p p' hp hp' hy)

/-- Cross-patch transition formula from the `z = 1`, project-to-`Y` chart to
the `x = 1`, project-to-`Y` chart. -/
theorem affineChartProjY_lift_trans_affineChartProjY_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjY_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H))).source) :
    (((affineChartProjY H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)).symm.trans
      ((affineChartProjY_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)) y) =
      y / ((phiLocalHomeomorph H p hp).symm (0, y)).1 := by
  let eZ := affineChartProjY H p hp
  let eX := affineChartProjY_X H p' hp'
  rcases z_to_x_lift_source_data H eZ eX hy with ⟨hy_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurve_eq_toPlaneCurveX_coords H hb_eq.symm
  have hy_fst : (eZ.symm y).val.1 =
      ((phiLocalHomeomorph H p hp).symm (0, y)).1 :=
    affineChartProjY_symm_apply_fst H p hp hy_target
  have hy_snd : (eZ.symm y).val.2 = y :=
    affineChartProjY_symm_apply_snd H p hp hy_target
  change (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))
      (PlaneCurveAffine.toPlaneCurve H (eZ.symm y)) =
        y / ((phiLocalHomeomorph H p hp).symm (0, y)).1
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = y / ((phiLocalHomeomorph H p hp).symm (0, y)).1
  rw [hcoords.2.1, hy_snd, hy_fst]

/-- Cross-patch compatibility from the `z = 1`, project-to-`Y` chart to the
`x = 1`, project-to-`Y` chart. -/
theorem affineChartProjY_lift_compat_affineChartProjY_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffine H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H) :
    ContDiffOn ℂ ω
      ((((affineChartProjY H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjY_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))) : ℂ → ℂ)
      (((affineChartProjY H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H)).symm.trans
        ((affineChartProjY_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))).source := by
  let eZ := affineChartProjY H p hp
  let eX := affineChartProjY_X H p' hp'
  let s := ((eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)).symm.trans
    (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source
  have hsymm : ContDiffOn ℂ ω (phiLocalHomeomorph H p hp).symm
      (phiLocalHomeomorph H p hp).target :=
    phiLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun y : ℂ => ((0 : ℂ), y)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => ((0 : ℂ), y)) s
      (phiLocalHomeomorph H p hp).target := by
    intro y hy
    have hy_target := (z_to_x_lift_source_data H eZ eX hy).1
    simpa [eZ, affineChartProjY] using hy_target
  have hbranch : ContDiffOn ℂ ω
      (fun y : ℂ => ((phiLocalHomeomorph H p hp).symm (0, y)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ y ∈ s, ((phiLocalHomeomorph H p hp).symm (0, y)).1 ≠ 0 := by
    intro y hy
    have hy_target := (z_to_x_lift_source_data H eZ eX hy).1
    have hx_nonzero := z_to_x_overlap_x_ne_zero H eZ eX hy
    have hy_fst : (eZ.symm y).val.1 =
        ((phiLocalHomeomorph H p hp).symm (0, y)).1 :=
      affineChartProjY_symm_apply_fst H p hp hy_target
    simpa [hy_fst] using hx_nonzero
  exact ContDiffOn.congr
    (contDiffOn_id.div hbranch hne)
    (fun y hy => affineChartProjY_lift_trans_affineChartProjY_X_apply H p p' hp hp' hy)

/-! ### Cross-patch transitions: `x = 1` to `z = 1` -/

private lemma x_to_z_lift_source_data (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (eX : OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ)
    (eZ : OpenPartialHomeomorph (PlaneCurveAffine H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source) :
    w ∈ eX.target ∧
      ∃ b : PlaneCurveAffine H, b ∈ eZ.source ∧
        PlaneCurveAffine.toPlaneCurve H b =
          PlaneCurveAffineX.toPlaneCurve H (eX.symm w) := by
  constructor
  · simpa [OpenPartialHomeomorph.lift_openEmbedding_target] using hw.1
  · have hws := hw.2
    simpa [OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply] using hws

private lemma x_to_z_overlap_z_ne_zero (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (eX : OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ)
    (eZ : OpenPartialHomeomorph (PlaneCurveAffine H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source) :
    (eX.symm w).val.2 ≠ 0 := by
  rcases (x_to_z_lift_source_data H eX eZ hw).2 with ⟨b, _hb_src, hb_eq⟩
  exact (toPlaneCurveX_eq_toPlaneCurve_coords H hb_eq.symm).1

/-- Cross-patch transition formula from the `x = 1`, project-to-`Z` chart to
the `z = 1`, project-to-`X` chart. -/
theorem affineChartProjZ_X_lift_trans_affineChartProjX_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjX H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H))).source) :
    (((affineChartProjZ_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjX H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)) z) = z⁻¹ := by
  let eX := affineChartProjZ_X H p hp
  let eZ := affineChartProjX H p' hp'
  rcases x_to_z_lift_source_data H eX eZ hz with ⟨hz_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveX_eq_toPlaneCurve_coords H hb_eq.symm
  have hz_snd : (eX.symm z).val.2 = z :=
    affineChartProjZ_X_symm_apply_snd H p hp hz_target
  change (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))
      (PlaneCurveAffineX.toPlaneCurve H (eX.symm z)) = z⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = z⁻¹
  rw [hcoords.2.1, hz_snd]

/-- Cross-patch compatibility from the `x = 1`, project-to-`Z` chart to the
`z = 1`, project-to-`X` chart. -/
theorem affineChartProjZ_X_lift_compat_affineChartProjX (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((affineChartProjZ_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjX H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))) : ℂ → ℂ)
      (((affineChartProjZ_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjX H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))).source := by
  let eX := affineChartProjZ_X H p hp
  let eZ := affineChartProjX H p' hp'
  let s := ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
    (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source
  have hne : ∀ z ∈ s, z ≠ 0 := by
    intro z hz
    have hz_target := (x_to_z_lift_source_data H eX eZ hz).1
    have hz_nonzero := x_to_z_overlap_z_ne_zero H eX eZ hz
    have hz_snd : (eX.symm z).val.2 = z :=
      affineChartProjZ_X_symm_apply_snd H p hp hz_target
    simpa [hz_snd] using hz_nonzero
  exact ContDiffOn.congr
    ((contDiffOn_id (𝕜 := ℂ) (n := ω) (s := s)).inv hne)
    (fun z hz => affineChartProjZ_X_lift_trans_affineChartProjX_apply H p p' hp hp' hz)

/-- Cross-patch transition formula from the `x = 1`, project-to-`Z` chart to
the `z = 1`, project-to-`Y` chart. -/
theorem affineChartProjZ_X_lift_trans_affineChartProjY_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjY H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H))).source) :
    (((affineChartProjZ_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjY H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)) z) =
      ((phiXLocalHomeomorph H p hp).symm (0, z)).1 / z := by
  let eX := affineChartProjZ_X H p hp
  let eZ := affineChartProjY H p' hp'
  rcases x_to_z_lift_source_data H eX eZ hz with ⟨hz_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveX_eq_toPlaneCurve_coords H hb_eq.symm
  have hz_fst : (eX.symm z).val.1 =
      ((phiXLocalHomeomorph H p hp).symm (0, z)).1 :=
    affineChartProjZ_X_symm_apply_fst H p hp hz_target
  have hz_snd : (eX.symm z).val.2 = z :=
    affineChartProjZ_X_symm_apply_snd H p hp hz_target
  change (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))
      (PlaneCurveAffineX.toPlaneCurve H (eX.symm z)) =
        ((phiXLocalHomeomorph H p hp).symm (0, z)).1 / z
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = ((phiXLocalHomeomorph H p hp).symm (0, z)).1 / z
  rw [hcoords.2.2, hz_fst, hz_snd]

/-- Cross-patch compatibility from the `x = 1`, project-to-`Z` chart to the
`z = 1`, project-to-`Y` chart. -/
theorem affineChartProjZ_X_lift_compat_affineChartProjY (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((affineChartProjZ_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjY H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))) : ℂ → ℂ)
      (((affineChartProjZ_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjY H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))).source := by
  let eX := affineChartProjZ_X H p hp
  let eZ := affineChartProjY H p' hp'
  let s := ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
    (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source
  have hsymm : ContDiffOn ℂ ω (phiXLocalHomeomorph H p hp).symm
      (phiXLocalHomeomorph H p hp).target :=
    phiXLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun z : ℂ => ((0 : ℂ), z)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun z : ℂ => ((0 : ℂ), z)) s
      (phiXLocalHomeomorph H p hp).target := by
    intro z hz
    have hz_target := (x_to_z_lift_source_data H eX eZ hz).1
    simpa [eX, affineChartProjZ_X] using hz_target
  have hbranch : ContDiffOn ℂ ω
      (fun z : ℂ => ((phiXLocalHomeomorph H p hp).symm (0, z)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ z ∈ s, z ≠ 0 := by
    intro z hz
    have hz_target := (x_to_z_lift_source_data H eX eZ hz).1
    have hz_nonzero := x_to_z_overlap_z_ne_zero H eX eZ hz
    have hz_snd : (eX.symm z).val.2 = z :=
      affineChartProjZ_X_symm_apply_snd H p hp hz_target
    simpa [hz_snd] using hz_nonzero
  exact ContDiffOn.congr
    (hbranch.div contDiffOn_id hne)
    (fun z hz => affineChartProjZ_X_lift_trans_affineChartProjY_apply H p p' hp hp' hz)

/-- Cross-patch transition formula from the `x = 1`, project-to-`Y` chart to
the `z = 1`, project-to-`X` chart. -/
theorem affineChartProjY_X_lift_trans_affineChartProjX_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjX H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H))).source) :
    (((affineChartProjY_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjX H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)) y) =
      (((psiXLocalHomeomorph H p hp).symm (0, y)).2)⁻¹ := by
  let eX := affineChartProjY_X H p hp
  let eZ := affineChartProjX H p' hp'
  rcases x_to_z_lift_source_data H eX eZ hy with ⟨hy_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveX_eq_toPlaneCurve_coords H hb_eq.symm
  have hy_snd : (eX.symm y).val.2 =
      ((psiXLocalHomeomorph H p hp).symm (0, y)).2 :=
    affineChartProjY_X_symm_apply_snd H p hp hy_target
  change (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))
      (PlaneCurveAffineX.toPlaneCurve H (eX.symm y)) =
        (((psiXLocalHomeomorph H p hp).symm (0, y)).2)⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = (((psiXLocalHomeomorph H p hp).symm (0, y)).2)⁻¹
  rw [hcoords.2.1, hy_snd]

/-- Cross-patch compatibility from the `x = 1`, project-to-`Y` chart to the
`z = 1`, project-to-`X` chart. -/
theorem affineChartProjY_X_lift_compat_affineChartProjX (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((affineChartProjY_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjX H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))) : ℂ → ℂ)
      (((affineChartProjY_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjX H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))).source := by
  let eX := affineChartProjY_X H p hp
  let eZ := affineChartProjX H p' hp'
  let s := ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
    (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source
  have hsymm : ContDiffOn ℂ ω (psiXLocalHomeomorph H p hp).symm
      (psiXLocalHomeomorph H p hp).target :=
    psiXLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun y : ℂ => ((0 : ℂ), y)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => ((0 : ℂ), y)) s
      (psiXLocalHomeomorph H p hp).target := by
    intro y hy
    have hy_target := (x_to_z_lift_source_data H eX eZ hy).1
    simpa [eX, affineChartProjY_X] using hy_target
  have hbranch : ContDiffOn ℂ ω
      (fun y : ℂ => ((psiXLocalHomeomorph H p hp).symm (0, y)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ y ∈ s, ((psiXLocalHomeomorph H p hp).symm (0, y)).2 ≠ 0 := by
    intro y hy
    have hy_target := (x_to_z_lift_source_data H eX eZ hy).1
    have hz_nonzero := x_to_z_overlap_z_ne_zero H eX eZ hy
    have hy_snd : (eX.symm y).val.2 =
        ((psiXLocalHomeomorph H p hp).symm (0, y)).2 :=
      affineChartProjY_X_symm_apply_snd H p hp hy_target
    simpa [hy_snd] using hz_nonzero
  exact ContDiffOn.congr
    (hbranch.inv hne)
    (fun y hy => affineChartProjY_X_lift_trans_affineChartProjX_apply H p p' hp hp' hy)

/-- Cross-patch transition formula from the `x = 1`, project-to-`Y` chart to
the `z = 1`, project-to-`Y` chart. -/
theorem affineChartProjY_X_lift_trans_affineChartProjY_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjY H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H))).source) :
    (((affineChartProjY_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjY H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurve H)) y) =
      y / ((psiXLocalHomeomorph H p hp).symm (0, y)).2 := by
  let eX := affineChartProjY_X H p hp
  let eZ := affineChartProjY H p' hp'
  rcases x_to_z_lift_source_data H eX eZ hy with ⟨hy_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveX_eq_toPlaneCurve_coords H hb_eq.symm
  have hy_fst : (eX.symm y).val.1 = y :=
    affineChartProjY_X_symm_apply_fst H p hp hy_target
  have hy_snd : (eX.symm y).val.2 =
      ((psiXLocalHomeomorph H p hp).symm (0, y)).2 :=
    affineChartProjY_X_symm_apply_snd H p hp hy_target
  change (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))
      (PlaneCurveAffineX.toPlaneCurve H (eX.symm y)) =
        y / ((psiXLocalHomeomorph H p hp).symm (0, y)).2
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = y / ((psiXLocalHomeomorph H p hp).symm (0, y)).2
  rw [hcoords.2.2, hy_fst, hy_snd]

/-- Cross-patch compatibility from the `x = 1`, project-to-`Y` chart to the
`z = 1`, project-to-`Y` chart. -/
theorem affineChartProjY_X_lift_compat_affineChartProjY (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffine H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((affineChartProjY_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjY H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))) : ℂ → ℂ)
      (((affineChartProjY_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjY H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurve H))).source := by
  let eX := affineChartProjY_X H p hp
  let eZ := affineChartProjY H p' hp'
  let s := ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
    (eZ.lift_openEmbedding (isOpenEmbedding_toPlaneCurve H))).source
  have hsymm : ContDiffOn ℂ ω (psiXLocalHomeomorph H p hp).symm
      (psiXLocalHomeomorph H p hp).target :=
    psiXLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun y : ℂ => ((0 : ℂ), y)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => ((0 : ℂ), y)) s
      (psiXLocalHomeomorph H p hp).target := by
    intro y hy
    have hy_target := (x_to_z_lift_source_data H eX eZ hy).1
    simpa [eX, affineChartProjY_X] using hy_target
  have hbranch : ContDiffOn ℂ ω
      (fun y : ℂ => ((psiXLocalHomeomorph H p hp).symm (0, y)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ y ∈ s, ((psiXLocalHomeomorph H p hp).symm (0, y)).2 ≠ 0 := by
    intro y hy
    have hy_target := (x_to_z_lift_source_data H eX eZ hy).1
    have hz_nonzero := x_to_z_overlap_z_ne_zero H eX eZ hy
    have hy_snd : (eX.symm y).val.2 =
        ((psiXLocalHomeomorph H p hp).symm (0, y)).2 :=
      affineChartProjY_X_symm_apply_snd H p hp hy_target
    simpa [hy_snd] using hz_nonzero
  exact ContDiffOn.congr
    (contDiffOn_id.div hbranch hne)
    (fun y hy => affineChartProjY_X_lift_trans_affineChartProjY_apply H p p' hp hp' hy)

/-! ### Cross-patch transitions: `y = 1` to `x = 1` -/

private lemma y_to_x_lift_source_data (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (eY : OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ)
    (eX : OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source) :
    w ∈ eY.target ∧
      ∃ b : PlaneCurveAffineX H, b ∈ eX.source ∧
        PlaneCurveAffineX.toPlaneCurve H b =
          PlaneCurveAffineY.toPlaneCurve H (eY.symm w) := by
  constructor
  · simpa [OpenPartialHomeomorph.lift_openEmbedding_target] using hw.1
  · have hws := hw.2
    simpa [OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply] using hws

private lemma y_to_x_overlap_x_ne_zero (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (eY : OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ)
    (eX : OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source) :
    (eY.symm w).val.1 ≠ 0 := by
  rcases (y_to_x_lift_source_data H eY eX hw).2 with ⟨b, _hb_src, hb_eq⟩
  exact (toPlaneCurveY_eq_toPlaneCurveX_coords H hb_eq.symm).1

/-- Cross-patch transition formula from the `y = 1`, project-to-`X` chart to
the `x = 1`, project-to-`Y` chart. -/
theorem affineChartProjX_Y_lift_trans_affineChartProjY_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjY_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H))).source) :
    (((affineChartProjX_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjY_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)) x) = x⁻¹ := by
  let eY := affineChartProjX_Y H p hp
  let eX := affineChartProjY_X H p' hp'
  rcases y_to_x_lift_source_data H eY eX hx with ⟨hx_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveY_eq_toPlaneCurveX_coords H hb_eq.symm
  have hx_fst : (eY.symm x).val.1 = x :=
    affineChartProjX_Y_symm_apply_fst H p hp hx_target
  change (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))
      (PlaneCurveAffineY.toPlaneCurve H (eY.symm x)) = x⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = x⁻¹
  rw [hcoords.2.1, hx_fst]

/-- Cross-patch compatibility from the `y = 1`, project-to-`X` chart to the
`x = 1`, project-to-`Y` chart. -/
theorem affineChartProjX_Y_lift_compat_affineChartProjY_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H) :
    ContDiffOn ℂ ω
      ((((affineChartProjX_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjY_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))) : ℂ → ℂ)
      (((affineChartProjX_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjY_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))).source := by
  let eY := affineChartProjX_Y H p hp
  let eX := affineChartProjY_X H p' hp'
  let s := ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
    (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source
  have hne : ∀ x ∈ s, x ≠ 0 := by
    intro x hx
    have hx_target := (y_to_x_lift_source_data H eY eX hx).1
    have hx_nonzero := y_to_x_overlap_x_ne_zero H eY eX hx
    have hx_fst : (eY.symm x).val.1 = x :=
      affineChartProjX_Y_symm_apply_fst H p hp hx_target
    simpa [hx_fst] using hx_nonzero
  exact ContDiffOn.congr
    ((contDiffOn_id (𝕜 := ℂ) (n := ω) (s := s)).inv hne)
    (fun x hx => affineChartProjX_Y_lift_trans_affineChartProjY_X_apply H p p' hp hp' hx)

/-- Cross-patch transition formula from the `y = 1`, project-to-`X` chart to
the `x = 1`, project-to-`Z` chart. -/
theorem affineChartProjX_Y_lift_trans_affineChartProjZ_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H)
    {x : ℂ}
    (hx : x ∈ (((affineChartProjX_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjZ_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H))).source) :
    (((affineChartProjX_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjZ_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)) x) =
      ((psiYLocalHomeomorph H p hp).symm (0, x)).2 / x := by
  let eY := affineChartProjX_Y H p hp
  let eX := affineChartProjZ_X H p' hp'
  rcases y_to_x_lift_source_data H eY eX hx with ⟨hx_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveY_eq_toPlaneCurveX_coords H hb_eq.symm
  have hx_fst : (eY.symm x).val.1 = x :=
    affineChartProjX_Y_symm_apply_fst H p hp hx_target
  have hx_snd : (eY.symm x).val.2 =
      ((psiYLocalHomeomorph H p hp).symm (0, x)).2 :=
    affineChartProjX_Y_symm_apply_snd H p hp hx_target
  change (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))
      (PlaneCurveAffineY.toPlaneCurve H (eY.symm x)) =
        ((psiYLocalHomeomorph H p hp).symm (0, x)).2 / x
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = ((psiYLocalHomeomorph H p hp).symm (0, x)).2 / x
  rw [hcoords.2.2, hx_snd, hx_fst]

/-- Cross-patch compatibility from the `y = 1`, project-to-`X` chart to the
`x = 1`, project-to-`Z` chart. -/
theorem affineChartProjX_Y_lift_compat_affineChartProjZ_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((affineChartProjX_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjZ_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))) : ℂ → ℂ)
      (((affineChartProjX_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjZ_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))).source := by
  let eY := affineChartProjX_Y H p hp
  let eX := affineChartProjZ_X H p' hp'
  let s := ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
    (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source
  have hsymm : ContDiffOn ℂ ω (psiYLocalHomeomorph H p hp).symm
      (psiYLocalHomeomorph H p hp).target :=
    psiYLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun x : ℂ => ((0 : ℂ), x)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => ((0 : ℂ), x)) s
      (psiYLocalHomeomorph H p hp).target := by
    intro x hx
    have hx_target := (y_to_x_lift_source_data H eY eX hx).1
    simpa [eY, affineChartProjX_Y] using hx_target
  have hbranch : ContDiffOn ℂ ω
      (fun x : ℂ => ((psiYLocalHomeomorph H p hp).symm (0, x)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ x ∈ s, x ≠ 0 := by
    intro x hx
    have hx_target := (y_to_x_lift_source_data H eY eX hx).1
    have hx_nonzero := y_to_x_overlap_x_ne_zero H eY eX hx
    have hx_fst : (eY.symm x).val.1 = x :=
      affineChartProjX_Y_symm_apply_fst H p hp hx_target
    simpa [hx_fst] using hx_nonzero
  exact ContDiffOn.congr
    (hbranch.div contDiffOn_id hne)
    (fun x hx => affineChartProjX_Y_lift_trans_affineChartProjZ_X_apply H p p' hp hp' hx)

/-- Cross-patch transition formula from the `y = 1`, project-to-`Z` chart to
the `x = 1`, project-to-`Y` chart. -/
theorem affineChartProjZ_Y_lift_trans_affineChartProjY_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjY_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H))).source) :
    (((affineChartProjZ_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjY_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)) z) =
      (((phiYLocalHomeomorph H p hp).symm (0, z)).1)⁻¹ := by
  let eY := affineChartProjZ_Y H p hp
  let eX := affineChartProjY_X H p' hp'
  rcases y_to_x_lift_source_data H eY eX hz with ⟨hz_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveY_eq_toPlaneCurveX_coords H hb_eq.symm
  have hz_fst : (eY.symm z).val.1 =
      ((phiYLocalHomeomorph H p hp).symm (0, z)).1 :=
    affineChartProjZ_Y_symm_apply_fst H p hp hz_target
  change (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))
      (PlaneCurveAffineY.toPlaneCurve H (eY.symm z)) =
        (((phiYLocalHomeomorph H p hp).symm (0, z)).1)⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = (((phiYLocalHomeomorph H p hp).symm (0, z)).1)⁻¹
  rw [hcoords.2.1, hz_fst]

/-- Cross-patch compatibility from the `y = 1`, project-to-`Z` chart to the
`x = 1`, project-to-`Y` chart. -/
theorem affineChartProjZ_Y_lift_compat_affineChartProjY_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusZ H) :
    ContDiffOn ℂ ω
      ((((affineChartProjZ_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjY_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))) : ℂ → ℂ)
      (((affineChartProjZ_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjY_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))).source := by
  let eY := affineChartProjZ_Y H p hp
  let eX := affineChartProjY_X H p' hp'
  let s := ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
    (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source
  have hsymm : ContDiffOn ℂ ω (phiYLocalHomeomorph H p hp).symm
      (phiYLocalHomeomorph H p hp).target :=
    phiYLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun z : ℂ => ((0 : ℂ), z)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun z : ℂ => ((0 : ℂ), z)) s
      (phiYLocalHomeomorph H p hp).target := by
    intro z hz
    have hz_target := (y_to_x_lift_source_data H eY eX hz).1
    simpa [eY, affineChartProjZ_Y] using hz_target
  have hbranch : ContDiffOn ℂ ω
      (fun z : ℂ => ((phiYLocalHomeomorph H p hp).symm (0, z)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ z ∈ s, ((phiYLocalHomeomorph H p hp).symm (0, z)).1 ≠ 0 := by
    intro z hz
    have hz_target := (y_to_x_lift_source_data H eY eX hz).1
    have hx_nonzero := y_to_x_overlap_x_ne_zero H eY eX hz
    have hz_fst : (eY.symm z).val.1 =
        ((phiYLocalHomeomorph H p hp).symm (0, z)).1 :=
      affineChartProjZ_Y_symm_apply_fst H p hp hz_target
    simpa [hz_fst] using hx_nonzero
  exact ContDiffOn.congr
    (hbranch.inv hne)
    (fun z hz => affineChartProjZ_Y_lift_trans_affineChartProjY_X_apply H p p' hp hp' hz)

/-- Cross-patch transition formula from the `y = 1`, project-to-`Z` chart to
the `x = 1`, project-to-`Z` chart. -/
theorem affineChartProjZ_Y_lift_trans_affineChartProjZ_X_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjZ_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H))).source) :
    (((affineChartProjZ_Y H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)).symm.trans
      ((affineChartProjZ_X H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)) z) =
      z / ((phiYLocalHomeomorph H p hp).symm (0, z)).1 := by
  let eY := affineChartProjZ_Y H p hp
  let eX := affineChartProjZ_X H p' hp'
  rcases y_to_x_lift_source_data H eY eX hz with ⟨hz_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveY_eq_toPlaneCurveX_coords H hb_eq.symm
  have hz_fst : (eY.symm z).val.1 =
      ((phiYLocalHomeomorph H p hp).symm (0, z)).1 :=
    affineChartProjZ_Y_symm_apply_fst H p hp hz_target
  have hz_snd : (eY.symm z).val.2 = z :=
    affineChartProjZ_Y_symm_apply_snd H p hp hz_target
  change (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))
      (PlaneCurveAffineY.toPlaneCurve H (eY.symm z)) =
        z / ((phiYLocalHomeomorph H p hp).symm (0, z)).1
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = z / ((phiYLocalHomeomorph H p hp).symm (0, z)).1
  rw [hcoords.2.2, hz_snd, hz_fst]

/-- Cross-patch compatibility from the `y = 1`, project-to-`Z` chart to the
`x = 1`, project-to-`Z` chart. -/
theorem affineChartProjZ_Y_lift_compat_affineChartProjZ_X (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H)
    (hp' : p' ∈ PlaneCurveAffineX.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((affineChartProjZ_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjZ_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))) : ℂ → ℂ)
      (((affineChartProjZ_Y H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H)).symm.trans
        ((affineChartProjZ_X H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H))).source := by
  let eY := affineChartProjZ_Y H p hp
  let eX := affineChartProjZ_X H p' hp'
  let s := ((eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)).symm.trans
    (eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H))).source
  have hsymm : ContDiffOn ℂ ω (phiYLocalHomeomorph H p hp).symm
      (phiYLocalHomeomorph H p hp).target :=
    phiYLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun z : ℂ => ((0 : ℂ), z)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun z : ℂ => ((0 : ℂ), z)) s
      (phiYLocalHomeomorph H p hp).target := by
    intro z hz
    have hz_target := (y_to_x_lift_source_data H eY eX hz).1
    simpa [eY, affineChartProjZ_Y] using hz_target
  have hbranch : ContDiffOn ℂ ω
      (fun z : ℂ => ((phiYLocalHomeomorph H p hp).symm (0, z)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ z ∈ s, ((phiYLocalHomeomorph H p hp).symm (0, z)).1 ≠ 0 := by
    intro z hz
    have hz_target := (y_to_x_lift_source_data H eY eX hz).1
    have hx_nonzero := y_to_x_overlap_x_ne_zero H eY eX hz
    have hz_fst : (eY.symm z).val.1 =
        ((phiYLocalHomeomorph H p hp).symm (0, z)).1 :=
      affineChartProjZ_Y_symm_apply_fst H p hp hz_target
    simpa [hz_fst] using hx_nonzero
  exact ContDiffOn.congr
    (contDiffOn_id.div hbranch hne)
    (fun z hz => affineChartProjZ_Y_lift_trans_affineChartProjZ_X_apply H p p' hp hp' hz)

/-! ### Cross-patch transitions: `x = 1` to `y = 1` -/

private lemma x_to_y_lift_source_data (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (eX : OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ)
    (eY : OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source) :
    w ∈ eX.target ∧
      ∃ b : PlaneCurveAffineY H, b ∈ eY.source ∧
        PlaneCurveAffineY.toPlaneCurve H b =
          PlaneCurveAffineX.toPlaneCurve H (eX.symm w) := by
  constructor
  · simpa [OpenPartialHomeomorph.lift_openEmbedding_target] using hw.1
  · have hws := hw.2
    simpa [OpenPartialHomeomorph.lift_openEmbedding_source,
      OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply] using hws

private lemma x_to_y_overlap_y_ne_zero (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (eX : OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ)
    (eY : OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ)
    {w : ℂ}
    (hw : w ∈ ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source) :
    (eX.symm w).val.1 ≠ 0 := by
  rcases (x_to_y_lift_source_data H eX eY hw).2 with ⟨b, _hb_src, hb_eq⟩
  exact (toPlaneCurveX_eq_toPlaneCurveY_coords H hb_eq.symm).1

/-- Cross-patch transition formula from the `x = 1`, project-to-`Y` chart to
the `y = 1`, project-to-`X` chart. -/
theorem affineChartProjY_X_lift_trans_affineChartProjX_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjX_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H))).source) :
    (((affineChartProjY_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjX_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)) y) = y⁻¹ := by
  let eX := affineChartProjY_X H p hp
  let eY := affineChartProjX_Y H p' hp'
  rcases x_to_y_lift_source_data H eX eY hy with ⟨hy_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveX_eq_toPlaneCurveY_coords H hb_eq.symm
  have hy_fst : (eX.symm y).val.1 = y :=
    affineChartProjY_X_symm_apply_fst H p hp hy_target
  change (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))
      (PlaneCurveAffineX.toPlaneCurve H (eX.symm y)) = y⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = y⁻¹
  rw [hcoords.2.1, hy_fst]

/-- Cross-patch compatibility from the `x = 1`, project-to-`Y` chart to the
`y = 1`, project-to-`X` chart. -/
theorem affineChartProjY_X_lift_compat_affineChartProjX_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H) :
    ContDiffOn ℂ ω
      ((((affineChartProjY_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjX_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))) : ℂ → ℂ)
      (((affineChartProjY_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjX_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))).source := by
  let eX := affineChartProjY_X H p hp
  let eY := affineChartProjX_Y H p' hp'
  let s := ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
    (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source
  have hne : ∀ y ∈ s, y ≠ 0 := by
    intro y hy
    have hy_target := (x_to_y_lift_source_data H eX eY hy).1
    have hy_nonzero := x_to_y_overlap_y_ne_zero H eX eY hy
    have hy_fst : (eX.symm y).val.1 = y :=
      affineChartProjY_X_symm_apply_fst H p hp hy_target
    simpa [hy_fst] using hy_nonzero
  exact ContDiffOn.congr
    ((contDiffOn_id (𝕜 := ℂ) (n := ω) (s := s)).inv hne)
    (fun y hy => affineChartProjY_X_lift_trans_affineChartProjX_Y_apply H p p' hp hp' hy)

/-- Cross-patch transition formula from the `x = 1`, project-to-`Y` chart to
the `y = 1`, project-to-`Z` chart. -/
theorem affineChartProjY_X_lift_trans_affineChartProjZ_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H)
    {y : ℂ}
    (hy : y ∈ (((affineChartProjY_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjZ_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H))).source) :
    (((affineChartProjY_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjZ_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)) y) =
      ((psiXLocalHomeomorph H p hp).symm (0, y)).2 / y := by
  let eX := affineChartProjY_X H p hp
  let eY := affineChartProjZ_Y H p' hp'
  rcases x_to_y_lift_source_data H eX eY hy with ⟨hy_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveX_eq_toPlaneCurveY_coords H hb_eq.symm
  have hy_fst : (eX.symm y).val.1 = y :=
    affineChartProjY_X_symm_apply_fst H p hp hy_target
  have hy_snd : (eX.symm y).val.2 =
      ((psiXLocalHomeomorph H p hp).symm (0, y)).2 :=
    affineChartProjY_X_symm_apply_snd H p hp hy_target
  change (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))
      (PlaneCurveAffineX.toPlaneCurve H (eX.symm y)) =
        ((psiXLocalHomeomorph H p hp).symm (0, y)).2 / y
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = ((psiXLocalHomeomorph H p hp).symm (0, y)).2 / y
  rw [hcoords.2.2, hy_snd, hy_fst]

/-- Cross-patch compatibility from the `x = 1`, project-to-`Y` chart to the
`y = 1`, project-to-`Z` chart. -/
theorem affineChartProjY_X_lift_compat_affineChartProjZ_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((affineChartProjY_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjZ_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))) : ℂ → ℂ)
      (((affineChartProjY_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjZ_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))).source := by
  let eX := affineChartProjY_X H p hp
  let eY := affineChartProjZ_Y H p' hp'
  let s := ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
    (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source
  have hsymm : ContDiffOn ℂ ω (psiXLocalHomeomorph H p hp).symm
      (psiXLocalHomeomorph H p hp).target :=
    psiXLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun y : ℂ => ((0 : ℂ), y)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => ((0 : ℂ), y)) s
      (psiXLocalHomeomorph H p hp).target := by
    intro y hy
    have hy_target := (x_to_y_lift_source_data H eX eY hy).1
    simpa [eX, affineChartProjY_X] using hy_target
  have hbranch : ContDiffOn ℂ ω
      (fun y : ℂ => ((psiXLocalHomeomorph H p hp).symm (0, y)).2) s :=
    (hsymm.comp hline hmaps).snd
  have hne : ∀ y ∈ s, y ≠ 0 := by
    intro y hy
    have hy_target := (x_to_y_lift_source_data H eX eY hy).1
    have hy_nonzero := x_to_y_overlap_y_ne_zero H eX eY hy
    have hy_fst : (eX.symm y).val.1 = y :=
      affineChartProjY_X_symm_apply_fst H p hp hy_target
    simpa [hy_fst] using hy_nonzero
  exact ContDiffOn.congr
    (hbranch.div contDiffOn_id hne)
    (fun y hy => affineChartProjY_X_lift_trans_affineChartProjZ_Y_apply H p p' hp hp' hy)

/-- Cross-patch transition formula from the `x = 1`, project-to-`Z` chart to
the `y = 1`, project-to-`X` chart. -/
theorem affineChartProjZ_X_lift_trans_affineChartProjX_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjX_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H))).source) :
    (((affineChartProjZ_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjX_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)) z) =
      (((phiXLocalHomeomorph H p hp).symm (0, z)).1)⁻¹ := by
  let eX := affineChartProjZ_X H p hp
  let eY := affineChartProjX_Y H p' hp'
  rcases x_to_y_lift_source_data H eX eY hz with ⟨hz_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveX_eq_toPlaneCurveY_coords H hb_eq.symm
  have hz_fst : (eX.symm z).val.1 =
      ((phiXLocalHomeomorph H p hp).symm (0, z)).1 :=
    affineChartProjZ_X_symm_apply_fst H p hp hz_target
  change (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))
      (PlaneCurveAffineX.toPlaneCurve H (eX.symm z)) =
        (((phiXLocalHomeomorph H p hp).symm (0, z)).1)⁻¹
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.1 = (((phiXLocalHomeomorph H p hp).symm (0, z)).1)⁻¹
  rw [hcoords.2.1, hz_fst]

/-- Cross-patch compatibility from the `x = 1`, project-to-`Z` chart to the
`y = 1`, project-to-`X` chart. -/
theorem affineChartProjZ_X_lift_compat_affineChartProjX_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusZ H) :
    ContDiffOn ℂ ω
      ((((affineChartProjZ_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjX_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))) : ℂ → ℂ)
      (((affineChartProjZ_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjX_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))).source := by
  let eX := affineChartProjZ_X H p hp
  let eY := affineChartProjX_Y H p' hp'
  let s := ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
    (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source
  have hsymm : ContDiffOn ℂ ω (phiXLocalHomeomorph H p hp).symm
      (phiXLocalHomeomorph H p hp).target :=
    phiXLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun z : ℂ => ((0 : ℂ), z)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun z : ℂ => ((0 : ℂ), z)) s
      (phiXLocalHomeomorph H p hp).target := by
    intro z hz
    have hz_target := (x_to_y_lift_source_data H eX eY hz).1
    simpa [eX, affineChartProjZ_X] using hz_target
  have hbranch : ContDiffOn ℂ ω
      (fun z : ℂ => ((phiXLocalHomeomorph H p hp).symm (0, z)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ z ∈ s, ((phiXLocalHomeomorph H p hp).symm (0, z)).1 ≠ 0 := by
    intro z hz
    have hz_target := (x_to_y_lift_source_data H eX eY hz).1
    have hy_nonzero := x_to_y_overlap_y_ne_zero H eX eY hz
    have hz_fst : (eX.symm z).val.1 =
        ((phiXLocalHomeomorph H p hp).symm (0, z)).1 :=
      affineChartProjZ_X_symm_apply_fst H p hp hz_target
    simpa [hz_fst] using hy_nonzero
  exact ContDiffOn.congr
    (hbranch.inv hne)
    (fun z hz => affineChartProjZ_X_lift_trans_affineChartProjX_Y_apply H p p' hp hp' hz)

/-- Cross-patch transition formula from the `x = 1`, project-to-`Z` chart to
the `y = 1`, project-to-`Z` chart. -/
theorem affineChartProjZ_X_lift_trans_affineChartProjZ_Y_apply (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H)
    {z : ℂ}
    (hz : z ∈ (((affineChartProjZ_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjZ_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H))).source) :
    (((affineChartProjZ_X H p hp).lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveX H)).symm.trans
      ((affineChartProjZ_Y H p' hp').lift_openEmbedding
      (isOpenEmbedding_toPlaneCurveY H)) z) =
      z / ((phiXLocalHomeomorph H p hp).symm (0, z)).1 := by
  let eX := affineChartProjZ_X H p hp
  let eY := affineChartProjZ_Y H p' hp'
  rcases x_to_y_lift_source_data H eX eY hz with ⟨hz_target, b, _hb_src, hb_eq⟩
  have hcoords := toPlaneCurveX_eq_toPlaneCurveY_coords H hb_eq.symm
  have hz_fst : (eX.symm z).val.1 =
      ((phiXLocalHomeomorph H p hp).symm (0, z)).1 :=
    affineChartProjZ_X_symm_apply_fst H p hp hz_target
  have hz_snd : (eX.symm z).val.2 = z :=
    affineChartProjZ_X_symm_apply_snd H p hp hz_target
  change (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))
      (PlaneCurveAffineX.toPlaneCurve H (eX.symm z)) =
        z / ((phiXLocalHomeomorph H p hp).symm (0, z)).1
  rw [← hb_eq]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  change b.val.2 = z / ((phiXLocalHomeomorph H p hp).symm (0, z)).1
  rw [hcoords.2.2, hz_snd, hz_fst]

/-- Cross-patch compatibility from the `x = 1`, project-to-`Z` chart to the
`y = 1`, project-to-`Z` chart. -/
theorem affineChartProjZ_X_lift_compat_affineChartProjZ_Y (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H)
    (hp' : p' ∈ PlaneCurveAffineY.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((affineChartProjZ_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjZ_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))) : ℂ → ℂ)
      (((affineChartProjZ_X H p hp).lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveX H)).symm.trans
        ((affineChartProjZ_Y H p' hp').lift_openEmbedding
        (isOpenEmbedding_toPlaneCurveY H))).source := by
  let eX := affineChartProjZ_X H p hp
  let eY := affineChartProjZ_Y H p' hp'
  let s := ((eX.lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)).symm.trans
    (eY.lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H))).source
  have hsymm : ContDiffOn ℂ ω (phiXLocalHomeomorph H p hp).symm
      (phiXLocalHomeomorph H p hp).target :=
    phiXLocalHomeomorph_contDiffOn_symm H p hp
  have hline : ContDiffOn ℂ ω (fun z : ℂ => ((0 : ℂ), z)) s :=
    (contDiff_const.prodMk contDiff_id).contDiffOn
  have hmaps : Set.MapsTo (fun z : ℂ => ((0 : ℂ), z)) s
      (phiXLocalHomeomorph H p hp).target := by
    intro z hz
    have hz_target := (x_to_y_lift_source_data H eX eY hz).1
    simpa [eX, affineChartProjZ_X] using hz_target
  have hbranch : ContDiffOn ℂ ω
      (fun z : ℂ => ((phiXLocalHomeomorph H p hp).symm (0, z)).1) s :=
    (hsymm.comp hline hmaps).fst
  have hne : ∀ z ∈ s, ((phiXLocalHomeomorph H p hp).symm (0, z)).1 ≠ 0 := by
    intro z hz
    have hz_target := (x_to_y_lift_source_data H eX eY hz).1
    have hy_nonzero := x_to_y_overlap_y_ne_zero H eX eY hz
    have hz_fst : (eX.symm z).val.1 =
        ((phiXLocalHomeomorph H p hp).symm (0, z)).1 :=
      affineChartProjZ_X_symm_apply_fst H p hp hz_target
    simpa [hz_fst] using hy_nonzero
  exact ContDiffOn.congr
    (contDiffOn_id.div hbranch hne)
    (fun z hz => affineChartProjZ_X_lift_trans_affineChartProjZ_Y_apply H p p' hp hp' hz)

/-! ### Cross-patch compatibility for preferred lifted patch charts -/

/-- Cross-patch compatibility from the preferred `z = 1` lifted chart to the
preferred `y = 1` lifted chart. -/
theorem centralLiftChart_compat_yLiftChart (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineY H) :
    ContDiffOn ℂ ω
      (((centralLiftChart H p).symm.trans (yLiftChart H p')) : ℂ → ℂ)
      ((centralLiftChart H p).symm.trans (yLiftChart H p')).source := by
  classical
  unfold centralLiftChart yLiftChart PlaneCurveAffine.prefChart PlaneCurveAffineY.prefChart
  split_ifs with hp hp'
  · exact affineChartProjY_lift_compat_affineChartProjZ_Y H p p' hp hp'
  · exact affineChartProjY_lift_compat_affineChartProjX_Y H p p' hp _
  · exact affineChartProjX_lift_compat_affineChartProjZ_Y H p p' _ _
  · exact affineChartProjX_lift_compat_affineChartProjX_Y H p p' _ _

/-- Cross-patch compatibility from the preferred `y = 1` lifted chart to the
preferred `z = 1` lifted chart. -/
theorem yLiftChart_compat_centralLiftChart (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffine H) :
    ContDiffOn ℂ ω
      (((yLiftChart H p).symm.trans (centralLiftChart H p')) : ℂ → ℂ)
      ((yLiftChart H p).symm.trans (centralLiftChart H p')).source := by
  classical
  unfold yLiftChart centralLiftChart PlaneCurveAffineY.prefChart PlaneCurveAffine.prefChart
  split_ifs with hp hp'
  · exact affineChartProjZ_Y_lift_compat_affineChartProjY H p p' hp hp'
  · exact affineChartProjZ_Y_lift_compat_affineChartProjX H p p' hp _
  · exact affineChartProjX_Y_lift_compat_affineChartProjY H p p' _ _
  · exact affineChartProjX_Y_lift_compat_affineChartProjX H p p' _ _

/-- Cross-patch compatibility from the preferred `z = 1` lifted chart to the
preferred `x = 1` lifted chart. -/
theorem centralLiftChart_compat_xLiftChart (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffine H) (p' : PlaneCurveAffineX H) :
    ContDiffOn ℂ ω
      (((centralLiftChart H p).symm.trans (xLiftChart H p')) : ℂ → ℂ)
      ((centralLiftChart H p).symm.trans (xLiftChart H p')).source := by
  classical
  unfold centralLiftChart xLiftChart PlaneCurveAffine.prefChart PlaneCurveAffineX.prefChart
  split_ifs with hp hp'
  · exact affineChartProjY_lift_compat_affineChartProjZ_X H p p' hp hp'
  · exact affineChartProjY_lift_compat_affineChartProjY_X H p p' hp _
  · exact affineChartProjX_lift_compat_affineChartProjZ_X H p p' _ _
  · exact affineChartProjX_lift_compat_affineChartProjY_X H p p' _ _

/-- Cross-patch compatibility from the preferred `x = 1` lifted chart to the
preferred `z = 1` lifted chart. -/
theorem xLiftChart_compat_centralLiftChart (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffine H) :
    ContDiffOn ℂ ω
      (((xLiftChart H p).symm.trans (centralLiftChart H p')) : ℂ → ℂ)
      ((xLiftChart H p).symm.trans (centralLiftChart H p')).source := by
  classical
  unfold xLiftChart centralLiftChart PlaneCurveAffineX.prefChart PlaneCurveAffine.prefChart
  split_ifs with hp hp'
  · exact affineChartProjZ_X_lift_compat_affineChartProjY H p p' hp hp'
  · exact affineChartProjZ_X_lift_compat_affineChartProjX H p p' hp _
  · exact affineChartProjY_X_lift_compat_affineChartProjY H p p' _ _
  · exact affineChartProjY_X_lift_compat_affineChartProjX H p p' _ _

/-- Cross-patch compatibility from the preferred `y = 1` lifted chart to the
preferred `x = 1` lifted chart. -/
theorem yLiftChart_compat_xLiftChart (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)] [Nonempty (PlaneCurveAffineX H)]
    (p : PlaneCurveAffineY H) (p' : PlaneCurveAffineX H) :
    ContDiffOn ℂ ω
      (((yLiftChart H p).symm.trans (xLiftChart H p')) : ℂ → ℂ)
      ((yLiftChart H p).symm.trans (xLiftChart H p')).source := by
  classical
  unfold yLiftChart xLiftChart PlaneCurveAffineY.prefChart PlaneCurveAffineX.prefChart
  split_ifs with hp hp'
  · exact affineChartProjZ_Y_lift_compat_affineChartProjZ_X H p p' hp hp'
  · exact affineChartProjZ_Y_lift_compat_affineChartProjY_X H p p' hp _
  · exact affineChartProjX_Y_lift_compat_affineChartProjZ_X H p p' _ _
  · exact affineChartProjX_Y_lift_compat_affineChartProjY_X H p p' _ _

/-- Cross-patch compatibility from the preferred `x = 1` lifted chart to the
preferred `y = 1` lifted chart. -/
theorem xLiftChart_compat_yLiftChart (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)] [Nonempty (PlaneCurveAffineY H)]
    (p : PlaneCurveAffineX H) (p' : PlaneCurveAffineY H) :
    ContDiffOn ℂ ω
      (((xLiftChart H p).symm.trans (yLiftChart H p')) : ℂ → ℂ)
      ((xLiftChart H p).symm.trans (yLiftChart H p')).source := by
  classical
  unfold xLiftChart yLiftChart PlaneCurveAffineX.prefChart PlaneCurveAffineY.prefChart
  split_ifs with hp hp'
  · exact affineChartProjZ_X_lift_compat_affineChartProjZ_Y H p p' hp hp'
  · exact affineChartProjZ_X_lift_compat_affineChartProjX_Y H p p' hp _
  · exact affineChartProjY_X_lift_compat_affineChartProjZ_Y H p p' _ _
  · exact affineChartProjY_X_lift_compat_affineChartProjX_Y H p p' _ _

/-! ### Diagonal compatibility for preferred lifted patch charts -/

/-- Same-patch compatibility for preferred lifted charts in the `z = 1` patch. -/
theorem centralLiftChart_compat_centralLiftChart (H : PlaneCurveData)
    (p p' : PlaneCurveAffine H) :
    ContDiffOn ℂ ω
      (((centralLiftChart H p).symm.trans (centralLiftChart H p')) : ℂ → ℂ)
      ((centralLiftChart H p).symm.trans (centralLiftChart H p')).source := by
  classical
  unfold centralLiftChart PlaneCurveAffine.prefChart
  split_ifs with hp hp'
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjY_compat_affineChartProjY H p p' hp hp'
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjY_compat_affineChartProjX H p p' hp _
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjX_compat_affineChartProjY H p p' _ _
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjX_compat_affineChartProjX H p p' _ _

/-- Same-patch compatibility for preferred lifted charts in the `y = 1` patch. -/
theorem yLiftChart_compat_yLiftChart (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineY H)]
    (p p' : PlaneCurveAffineY H) :
    ContDiffOn ℂ ω
      (((yLiftChart H p).symm.trans (yLiftChart H p')) : ℂ → ℂ)
      ((yLiftChart H p).symm.trans (yLiftChart H p')).source := by
  classical
  unfold yLiftChart PlaneCurveAffineY.prefChart
  split_ifs with hp hp'
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjZ_Y_compat_affineChartProjZ_Y H p p' hp hp'
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjZ_Y_compat_affineChartProjX_Y H p p' hp _
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjX_Y_compat_affineChartProjZ_Y H p p' _ _
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjX_Y_compat_affineChartProjX_Y H p p' _ _

/-- Same-patch compatibility for preferred lifted charts in the `x = 1` patch. -/
theorem xLiftChart_compat_xLiftChart (H : PlaneCurveData)
    [Nonempty (PlaneCurveAffineX H)]
    (p p' : PlaneCurveAffineX H) :
    ContDiffOn ℂ ω
      (((xLiftChart H p).symm.trans (xLiftChart H p')) : ℂ → ℂ)
      ((xLiftChart H p).symm.trans (xLiftChart H p')).source := by
  classical
  unfold xLiftChart PlaneCurveAffineX.prefChart
  split_ifs with hp hp'
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjZ_X_compat_affineChartProjZ_X H p p' hp hp'
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjZ_X_compat_affineChartProjY_X H p p' hp _
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjY_X_compat_affineChartProjZ_X H p p' _ _
  · simpa only [OpenPartialHomeomorph.lift_openEmbedding_trans] using
      affineChartProjY_X_compat_affineChartProjY_X H p p' _ _

/-! ### Charted-space compatibility and manifold instance -/

/-- The preferred chart at any two points of a plane curve has an analytic transition. -/
theorem PlaneCurve.chartAt_compat (H : PlaneCurveData) (q q' : PlaneCurve H) :
    ContDiffOn ℂ ω
      (((chartAt H q).symm.trans (chartAt H q')) : ℂ → ℂ)
      ((chartAt H q).symm.trans (chartAt H q')).source := by
  classical
  by_cases hq2 : q.val.rep 2 ≠ 0
  · let p : PlaneCurveAffine H := PlaneCurveAffine.projZ_inv H ⟨q, by
      rw [range_toPlaneCurve_eq_U2 H]
      exact mem_U_of_rep_ne_zero q.val 2 hq2⟩
    have hq : chartAt H q = centralLiftChart H p := by
      simp [chartAt, hq2, p]
    by_cases hq'2 : q'.val.rep 2 ≠ 0
    · let p' : PlaneCurveAffine H := PlaneCurveAffine.projZ_inv H ⟨q', by
        rw [range_toPlaneCurve_eq_U2 H]
        exact mem_U_of_rep_ne_zero q'.val 2 hq'2⟩
      have hq' : chartAt H q' = centralLiftChart H p' := by
        simp [chartAt, hq'2, p']
      simpa [hq, hq'] using centralLiftChart_compat_centralLiftChart H p p'
    · by_cases hq'1 : q'.val.rep 1 ≠ 0
      · let p' : PlaneCurveAffineY H := PlaneCurveAffineY.projY_inv H ⟨q', by
          rw [range_toPlaneCurveY_eq_U1 H]
          exact mem_U_of_rep_ne_zero q'.val 1 hq'1⟩
        haveI : Nonempty (PlaneCurveAffineY H) := ⟨p'⟩
        have hq' : chartAt H q' = yLiftChart H p' := by
          simp [chartAt, hq'2, hq'1, p']
        simpa [hq, hq'] using centralLiftChart_compat_yLiftChart H p p'
      · have hq'0 : q'.val.rep 0 ≠ 0 := by
          have h_nz := Projectivization.rep_nonzero q'.val
          intro h_zero
          apply h_nz
          ext i
          fin_cases i
          · exact h_zero
          · exact not_not.mp hq'1
          · exact not_not.mp hq'2
        let p' : PlaneCurveAffineX H := PlaneCurveAffineX.projX_inv H ⟨q', by
          rw [range_toPlaneCurveX_eq_U0 H]
          exact mem_U_of_rep_ne_zero q'.val 0 hq'0⟩
        haveI : Nonempty (PlaneCurveAffineX H) := ⟨p'⟩
        have hq' : chartAt H q' = xLiftChart H p' := by
          simp [chartAt, hq'2, hq'1, p']
        simpa [hq, hq'] using centralLiftChart_compat_xLiftChart H p p'
  · by_cases hq1 : q.val.rep 1 ≠ 0
    · let p : PlaneCurveAffineY H := PlaneCurveAffineY.projY_inv H ⟨q, by
        rw [range_toPlaneCurveY_eq_U1 H]
        exact mem_U_of_rep_ne_zero q.val 1 hq1⟩
      haveI : Nonempty (PlaneCurveAffineY H) := ⟨p⟩
      have hq : chartAt H q = yLiftChart H p := by
        simp [chartAt, hq2, hq1, p]
      by_cases hq'2 : q'.val.rep 2 ≠ 0
      · let p' : PlaneCurveAffine H := PlaneCurveAffine.projZ_inv H ⟨q', by
          rw [range_toPlaneCurve_eq_U2 H]
          exact mem_U_of_rep_ne_zero q'.val 2 hq'2⟩
        have hq' : chartAt H q' = centralLiftChart H p' := by
          simp [chartAt, hq'2, p']
        simpa [hq, hq'] using yLiftChart_compat_centralLiftChart H p p'
      · by_cases hq'1 : q'.val.rep 1 ≠ 0
        · let p' : PlaneCurveAffineY H := PlaneCurveAffineY.projY_inv H ⟨q', by
            rw [range_toPlaneCurveY_eq_U1 H]
            exact mem_U_of_rep_ne_zero q'.val 1 hq'1⟩
          have hq' : chartAt H q' = yLiftChart H p' := by
            simp [chartAt, hq'2, hq'1, p']
          simpa [hq, hq'] using yLiftChart_compat_yLiftChart H p p'
        · have hq'0 : q'.val.rep 0 ≠ 0 := by
            have h_nz := Projectivization.rep_nonzero q'.val
            intro h_zero
            apply h_nz
            ext i
            fin_cases i
            · exact h_zero
            · exact not_not.mp hq'1
            · exact not_not.mp hq'2
          let p' : PlaneCurveAffineX H := PlaneCurveAffineX.projX_inv H ⟨q', by
            rw [range_toPlaneCurveX_eq_U0 H]
            exact mem_U_of_rep_ne_zero q'.val 0 hq'0⟩
          haveI : Nonempty (PlaneCurveAffineX H) := ⟨p'⟩
          have hq' : chartAt H q' = xLiftChart H p' := by
            simp [chartAt, hq'2, hq'1, p']
          simpa [hq, hq'] using yLiftChart_compat_xLiftChart H p p'
    · have hq0 : q.val.rep 0 ≠ 0 := by
        have h_nz := Projectivization.rep_nonzero q.val
        intro h_zero
        apply h_nz
        ext i
        fin_cases i
        · exact h_zero
        · exact not_not.mp hq1
        · exact not_not.mp hq2
      let p : PlaneCurveAffineX H := PlaneCurveAffineX.projX_inv H ⟨q, by
        rw [range_toPlaneCurveX_eq_U0 H]
        exact mem_U_of_rep_ne_zero q.val 0 hq0⟩
      haveI : Nonempty (PlaneCurveAffineX H) := ⟨p⟩
      have hq : chartAt H q = xLiftChart H p := by
        simp [chartAt, hq2, hq1, p]
      by_cases hq'2 : q'.val.rep 2 ≠ 0
      · let p' : PlaneCurveAffine H := PlaneCurveAffine.projZ_inv H ⟨q', by
          rw [range_toPlaneCurve_eq_U2 H]
          exact mem_U_of_rep_ne_zero q'.val 2 hq'2⟩
        have hq' : chartAt H q' = centralLiftChart H p' := by
          simp [chartAt, hq'2, p']
        simpa [hq, hq'] using xLiftChart_compat_centralLiftChart H p p'
      · by_cases hq'1 : q'.val.rep 1 ≠ 0
        · let p' : PlaneCurveAffineY H := PlaneCurveAffineY.projY_inv H ⟨q', by
            rw [range_toPlaneCurveY_eq_U1 H]
            exact mem_U_of_rep_ne_zero q'.val 1 hq'1⟩
          haveI : Nonempty (PlaneCurveAffineY H) := ⟨p'⟩
          have hq' : chartAt H q' = yLiftChart H p' := by
            simp [chartAt, hq'2, hq'1, p']
          simpa [hq, hq'] using xLiftChart_compat_yLiftChart H p p'
        · have hq'0 : q'.val.rep 0 ≠ 0 := by
            have h_nz := Projectivization.rep_nonzero q'.val
            intro h_zero
            apply h_nz
            ext i
            fin_cases i
            · exact h_zero
            · exact not_not.mp hq'1
            · exact not_not.mp hq'2
          let p' : PlaneCurveAffineX H := PlaneCurveAffineX.projX_inv H ⟨q', by
            rw [range_toPlaneCurveX_eq_U0 H]
            exact mem_U_of_rep_ne_zero q'.val 0 hq'0⟩
          have hq' : chartAt H q' = xLiftChart H p' := by
            simp [chartAt, hq'2, hq'1, p']
          simpa [hq, hq'] using xLiftChart_compat_xLiftChart H p p'

/-- The analytic manifold structure on a smooth projective plane curve. -/
noncomputable instance PlaneCurve.instIsManifold (H : PlaneCurveData) :
    IsManifold 𝓘(ℂ, ℂ) ω (PlaneCurve H) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨q, rfl⟩
  rcases he' with ⟨q', rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.preimage_id, id_eq, Set.inter_univ, Set.univ_inter] using
    PlaneCurve.chartAt_compat H q q'

end Jacobians.ProjectiveCurve
