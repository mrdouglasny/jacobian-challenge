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

private noncomputable def reversePathChartBallSubdivision {a b : X} (γ : Path a b)
    (S : PathChartBallSubdivision ((γ : Path a b) : C(unitInterval, X))) :
    PathChartBallSubdivision ((γ.symm : Path b a) : C(unitInterval, X)) where
  n := S.n
  t := fun i => unitInterval.symm (S.t i.rev)
  cellBall := fun i => S.cellBall i.rev
  zero_eq := by
    simp [S.one_eq]
  one_eq := by
    simp [S.zero_eq]
  monotone_t := by
    intro i j hij
    rw [unitInterval.symm_le_symm]
    exact S.monotone_t ((Fin.rev_le_rev (i := j) (j := i)).2 hij)
  cell_subset := by
    intro i u hu
    have hleft : S.t i.rev.castSucc ≤ unitInterval.symm u := by
      exact (unitInterval.le_symm_comm (i := u) (j := S.t i.rev.castSucc)).1
        (by simpa [Fin.rev_succ] using hu.2)
    have hright : unitInterval.symm u ≤ S.t i.rev.succ := by
      exact (unitInterval.symm_le_comm (i := S.t i.rev.succ) (j := u)).1
        (by simpa [Fin.rev_castSucc] using hu.1)
    have hmem :
        unitInterval.symm u ∈
          Set.Icc (S.t i.rev.castSucc) (S.t i.rev.succ) :=
      ⟨hleft, hright⟩
    have hbase := S.cell_subset i.rev hmem
    simpa [pathChartBallSet, Path.symm_apply, Function.comp_def] using hbase

private theorem developingIncrement_reversePathChartBallSubdivision {a b : X}
    (form : HolomorphicOneForm X) (γ : Path a b)
    (S : PathChartBallSubdivision ((γ : Path a b) : C(unitInterval, X)))
    (i : Fin S.n) :
    developingIncrement form ((γ.symm : Path b a) : C(unitInterval, X))
        (reversePathChartBallSubdivision γ S) i =
      -developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i.rev := by
  unfold developingIncrement reversePathChartBallSubdivision
  simp [Path.symm_apply, Fin.rev_castSucc, Fin.rev_succ]

private theorem developingValueOfSubdivision_reversePathChartBallSubdivision {a b : X}
    (form : HolomorphicOneForm X) (γ : Path a b)
    (S : PathChartBallSubdivision ((γ : Path a b) : C(unitInterval, X))) :
    developingValueOfSubdivision form ((γ.symm : Path b a) : C(unitInterval, X))
        (reversePathChartBallSubdivision γ S) =
      -developingValueOfSubdivision form ((γ : Path a b) : C(unitInterval, X)) S := by
  classical
  unfold developingValueOfSubdivision
  calc
    (∑ i : Fin S.n,
        developingIncrement form ((γ.symm : Path b a) : C(unitInterval, X))
          (reversePathChartBallSubdivision γ S) i) =
        ∑ i : Fin S.n,
          -developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i.rev := by
          exact Finset.sum_congr rfl (fun i _ =>
            developingIncrement_reversePathChartBallSubdivision form γ S i)
    _ = ∑ i : Fin S.n,
          -developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i := by
          exact Fintype.sum_bijective Fin.rev Fin.rev_bijective
            (fun i : Fin S.n =>
              -developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i.rev)
            (fun i : Fin S.n =>
              -developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i)
            (fun i => by simp)
    _ = -∑ i : Fin S.n,
          developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i := by
          rw [Finset.sum_neg_distrib]

/-- A1: reversing a path negates the developing value. -/
theorem devVal_symm {a b : X} (x₀ : X) (form : HolomorphicOneForm X)
    (γ : Path a b) :
    developingValue x₀ form ((γ.symm : Path b a) : C(unitInterval, X)) =
      -developingValue x₀ form ((γ : Path a b) : C(unitInterval, X)) := by
  classical
  let S : PathChartBallSubdivision ((γ : Path a b) : C(unitInterval, X)) :=
    chosenPathChartBallSubdivision ((γ : Path a b) : C(unitInterval, X))
  let R : PathChartBallSubdivision ((γ.symm : Path b a) : C(unitInterval, X)) :=
    reversePathChartBallSubdivision γ S
  have hsymm :
      developingValue x₀ form ((γ.symm : Path b a) : C(unitInterval, X)) =
        developingValueOfSubdivision form ((γ.symm : Path b a) : C(unitInterval, X)) R :=
    developingValue_eq_developingValueOfSubdivision x₀ form
      ((γ.symm : Path b a) : C(unitInterval, X)) R
  have hγ :
      developingValue x₀ form ((γ : Path a b) : C(unitInterval, X)) =
        developingValueOfSubdivision form ((γ : Path a b) : C(unitInterval, X)) S :=
    developingValue_eq_developingValueOfSubdivision x₀ form
      ((γ : Path a b) : C(unitInterval, X)) S
  calc
    developingValue x₀ form ((γ.symm : Path b a) : C(unitInterval, X)) =
        developingValueOfSubdivision form ((γ.symm : Path b a) : C(unitInterval, X)) R := hsymm
    _ = -developingValueOfSubdivision form ((γ : Path a b) : C(unitInterval, X)) S := by
      simpa [R] using developingValueOfSubdivision_reversePathChartBallSubdivision form γ S
    _ = -developingValue x₀ form ((γ : Path a b) : C(unitInterval, X)) := by
      rw [hγ]

end Jacobians.RiemannSurface
