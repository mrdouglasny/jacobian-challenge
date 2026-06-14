/-
# Linearity of the developing value in the holomorphic one-form

The developing value `developingValue x₀ form γ` is `ℂ`-linear in `form`
for a fixed path `γ`. The chosen chart-ball subdivision depends only on the
path, so additivity / scalar-multiplication reduce, cell by cell, to the
corresponding statement for the chart-local primitive endpoint difference
`developingIncrement`. Two primitives of the same coefficient on a ball that
agree at the centre coincide (`Metric.ball` is open and preconnected), so the
chart primitive is additive / homogeneous up to the additive constant that
cancels in the endpoint difference.

These lemmas supply the `ℂ`-linearity needed to re-found the period map on the
axiom-free developing-value homomorphism (`loopDevValH1Hom`).
-/
import Submission.Jacobians.RiemannSurface.DevelopingMap

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## Differentiability of the chart-ball primitive on its ball -/

/-- The chart-ball primitive is differentiable on its ball. -/
theorem pathChartBallPrimitive_differentiableOn (form : HolomorphicOneForm X)
    (B : PathChartBall X) :
    DifferentiableOn ℂ (pathChartBallPrimitive form B) (Metric.ball B.c B.r) :=
  fun z hz =>
    (pathChartBallPrimitive_hasDerivAt form B z hz).differentiableAt.differentiableWithinAt

/-- The chart-ball primitive's derivative equals the coefficient on its ball. -/
theorem pathChartBallPrimitive_deriv (form : HolomorphicOneForm X)
    (B : PathChartBall X) {z : ℂ} (hz : z ∈ Metric.ball B.c B.r) :
    deriv (pathChartBallPrimitive form B) z = form.coeff B.p z :=
  (pathChartBallPrimitive_hasDerivAt form B z hz).deriv

/-! ## Additivity / homogeneity of the chart-ball primitive on its ball -/

/-- On its ball, the chart-local primitive of a sum of one-forms equals the
sum of the chart-local primitives. Both sides are primitives of the same
coefficient `(form₁ + form₂).coeff` and vanish at the centre `B.c`, so they
agree on the open, preconnected ball. -/
theorem pathChartBallPrimitive_add (form₁ form₂ : HolomorphicOneForm X)
    (B : PathChartBall X) {z : ℂ} (hz : z ∈ Metric.ball B.c B.r) :
    pathChartBallPrimitive (form₁ + form₂) B z =
      pathChartBallPrimitive form₁ B z + pathChartBallPrimitive form₂ B z := by
  have hc : B.c ∈ Metric.ball B.c B.r := by
    rcases (Metric.nonempty_ball).1 ⟨z, hz⟩ with hr
    exact Metric.mem_ball_self hr
  refine Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
    (pathChartBallPrimitive_differentiableOn (form₁ + form₂) B)
    ((pathChartBallPrimitive_differentiableOn form₁ B).add
      (pathChartBallPrimitive_differentiableOn form₂ B))
    ?_ hc ?_ hz
  · intro w hw
    rw [pathChartBallPrimitive_deriv (form₁ + form₂) B hw,
      deriv_add ((pathChartBallPrimitive_differentiableOn form₁ B w hw).differentiableAt
          (Metric.isOpen_ball.mem_nhds hw))
        ((pathChartBallPrimitive_differentiableOn form₂ B w hw).differentiableAt
          (Metric.isOpen_ball.mem_nhds hw)),
      pathChartBallPrimitive_deriv form₁ B hw, pathChartBallPrimitive_deriv form₂ B hw]
    simp [HolomorphicOneForm.coeff_add]
  · rw [Pi.add_apply, pathChartBallPrimitive_value, pathChartBallPrimitive_value,
      pathChartBallPrimitive_value, add_zero]

/-- On its ball, the chart-local primitive of a scalar multiple of a one-form
equals the scalar multiple of the chart-local primitive. -/
theorem pathChartBallPrimitive_smul (a : ℂ) (form : HolomorphicOneForm X)
    (B : PathChartBall X) {z : ℂ} (hz : z ∈ Metric.ball B.c B.r) :
    pathChartBallPrimitive (a • form) B z =
      a • pathChartBallPrimitive form B z := by
  have hc : B.c ∈ Metric.ball B.c B.r := by
    rcases (Metric.nonempty_ball).1 ⟨z, hz⟩ with hr
    exact Metric.mem_ball_self hr
  refine Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
    (pathChartBallPrimitive_differentiableOn (a • form) B)
    ((pathChartBallPrimitive_differentiableOn form B).const_smul a)
    ?_ hc ?_ hz
  · intro w hw
    rw [pathChartBallPrimitive_deriv (a • form) B hw,
      deriv_const_smul a ((pathChartBallPrimitive_differentiableOn form B w hw).differentiableAt
        (Metric.isOpen_ball.mem_nhds hw)),
      pathChartBallPrimitive_deriv form B hw]
    simp [HolomorphicOneForm.coeff_smul]
  · rw [Pi.smul_apply, pathChartBallPrimitive_value, pathChartBallPrimitive_value,
      smul_zero]

/-! ## Additivity / homogeneity of the developing increment -/

/-- The developing increment of a sum of one-forms over one subdivision cell is
the sum of the increments: the endpoints lie in the cell's ball, where the
primitives are additive. -/
theorem developingIncrement_add (form₁ form₂ : HolomorphicOneForm X)
    {γ : C(unitInterval, X)} (S : PathChartBallSubdivision γ) (i : Fin S.n) :
    developingIncrement (form₁ + form₂) γ S i =
      developingIncrement form₁ γ S i + developingIncrement form₂ γ S i := by
  simp only [developingIncrement]
  rw [pathChartBallPrimitive_add form₁ form₂ _ (S.right_coord_mem_ball i),
    pathChartBallPrimitive_add form₁ form₂ _ (S.left_coord_mem_ball i)]
  ring

/-- The developing increment of a scalar multiple of a one-form over one
subdivision cell is the scalar multiple of the increment. -/
theorem developingIncrement_smul (a : ℂ) (form : HolomorphicOneForm X)
    {γ : C(unitInterval, X)} (S : PathChartBallSubdivision γ) (i : Fin S.n) :
    developingIncrement (a • form) γ S i = a • developingIncrement form γ S i := by
  simp only [developingIncrement]
  rw [pathChartBallPrimitive_smul a form _ (S.right_coord_mem_ball i),
    pathChartBallPrimitive_smul a form _ (S.left_coord_mem_ball i)]
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_sub]

/-! ## Additivity / homogeneity of the developing value -/

/-- The developing value of a sum of one-forms equals the sum of developing
values: the chosen subdivision is the same for all forms (it depends only on
the path), and the increments are additive cell by cell. -/
theorem developingValueOfSubdivision_add (form₁ form₂ : HolomorphicOneForm X)
    {γ : C(unitInterval, X)} (S : PathChartBallSubdivision γ) :
    developingValueOfSubdivision (form₁ + form₂) γ S =
      developingValueOfSubdivision form₁ γ S +
        developingValueOfSubdivision form₂ γ S := by
  unfold developingValueOfSubdivision
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => developingIncrement_add form₁ form₂ S i)

theorem developingValueOfSubdivision_smul (a : ℂ) (form : HolomorphicOneForm X)
    {γ : C(unitInterval, X)} (S : PathChartBallSubdivision γ) :
    developingValueOfSubdivision (a • form) γ S =
      a • developingValueOfSubdivision form γ S := by
  unfold developingValueOfSubdivision
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => developingIncrement_smul a form S i)

/-- **Additivity of the developing value in the form.** -/
theorem developingValue_add (x₀ : X) (form₁ form₂ : HolomorphicOneForm X)
    (γ : C(unitInterval, X)) :
    developingValue x₀ (form₁ + form₂) γ =
      developingValue x₀ form₁ γ + developingValue x₀ form₂ γ :=
  developingValueOfSubdivision_add form₁ form₂ (chosenPathChartBallSubdivision γ)

/-- **Homogeneity of the developing value in the form.** -/
theorem developingValue_smul (x₀ : X) (a : ℂ) (form : HolomorphicOneForm X)
    (γ : C(unitInterval, X)) :
    developingValue x₀ (a • form) γ = a • developingValue x₀ form γ :=
  developingValueOfSubdivision_smul a form (chosenPathChartBallSubdivision γ)

/-- The developing value of the zero form vanishes. -/
theorem developingValue_zero (x₀ : X) (γ : C(unitInterval, X)) :
    developingValue x₀ (0 : HolomorphicOneForm X) γ = 0 := by
  have h := developingValue_smul x₀ 0 (0 : HolomorphicOneForm X) γ
  simpa using h

end Jacobians.RiemannSurface
