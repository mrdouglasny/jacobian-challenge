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

end Jacobians.ProjectiveCurve
