import Jacobians.RiemannSurface.DevelopingMap

/-!
# Algebra of the developing value

Path-level algebra for the choice-based `developingValue`.
-/

noncomputable section

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The basepoint argument of `developingValue` is definitionally ignored. -/
theorem developingValue_basepoint_indep (x₀ x₁ : X) (form : HolomorphicOneForm X)
    (γ : C(unitInterval, X)) :
    developingValue x₀ form γ = developingValue x₁ form γ := by
  rfl

/-- A3: the developing value of a constant path is zero. -/
theorem devVal_refl (x₀ : X) (form : HolomorphicOneForm X) (x : X) :
    developingValue x₀ form ((Path.refl x : Path x x) : C(unitInterval, X)) = 0 := by
  classical
  let z : ℂ := (extChartAt 𝓘(ℂ) x) x
  have hz_target : z ∈ (extChartAt 𝓘(ℂ) x).target := by
    simp [z]
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    (Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := 𝓘(ℂ)) x)) z hz_target
  let B : PathChartBall X :=
    { p := x, c := z, r := r, ball_subset_target := hr_sub }
  refine developingValue_eq_zero_of_loop_in_pathChartBall
    (x₀ := x₀) (form := form)
    (γ := ((Path.refl x : Path x x) : C(unitInterval, X))) B ?_ ?_
  · simp
  · intro u
    constructor
    · simp [B]
    · exact (show (extChartAt 𝓘(ℂ) B.p)
          (((Path.refl x : Path x x) : C(unitInterval, X)) u) ∈ Metric.ball B.c B.r by
        simpa [B, z] using (Metric.mem_ball_self (x := z) hr_pos))

end Jacobians.RiemannSurface
