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

private def scaleL (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by
    obtain ⟨h0, h1⟩ := t.prop
    constructor <;> linarith⟩

private def scaleR (t : unitInterval) : unitInterval :=
  ⟨((t : ℝ) + 1) / 2, by
    obtain ⟨h0, h1⟩ := t.prop
    constructor <;> linarith⟩

private def unitHalf : unitInterval :=
  ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

@[simp] private theorem scaleL_coe (t : unitInterval) :
    ((scaleL t : unitInterval) : ℝ) = (t : ℝ) / 2 :=
  rfl

@[simp] private theorem scaleR_coe (t : unitInterval) :
    ((scaleR t : unitInterval) : ℝ) = ((t : ℝ) + 1) / 2 :=
  rfl

@[simp] private theorem unitHalf_coe :
    ((unitHalf : unitInterval) : ℝ) = (1 / 2 : ℝ) :=
  rfl

@[simp] private theorem scaleL_zero : scaleL (0 : unitInterval) = 0 := by
  ext
  norm_num [scaleL]

@[simp] private theorem scaleL_one : scaleL (1 : unitInterval) = unitHalf := by
  ext
  norm_num [scaleL, unitHalf]

@[simp] private theorem scaleR_zero : scaleR (0 : unitInterval) = unitHalf := by
  ext
  norm_num [scaleR, unitHalf]

@[simp] private theorem scaleR_one : scaleR (1 : unitInterval) = 1 := by
  ext
  norm_num [scaleR]

private theorem scaleL_le_half (t : unitInterval) : scaleL t ≤ unitHalf := by
  change ((t : ℝ) / 2) ≤ (1 / 2 : ℝ)
  linarith [t.2.2]

private theorem half_le_scaleR (t : unitInterval) : unitHalf ≤ scaleR t := by
  change (1 / 2 : ℝ) ≤ ((t : ℝ) + 1) / 2
  linarith [t.2.1]

private theorem scaleL_mono {u v : unitInterval} (h : u ≤ v) : scaleL u ≤ scaleL v := by
  change ((u : ℝ) / 2) ≤ ((v : ℝ) / 2)
  have h' : (u : ℝ) ≤ (v : ℝ) := h
  linarith

private theorem scaleR_mono {u v : unitInterval} (h : u ≤ v) : scaleR u ≤ scaleR v := by
  change (((u : ℝ) + 1) / 2) ≤ (((v : ℝ) + 1) / 2)
  have h' : (u : ℝ) ≤ (v : ℝ) := h
  linarith

private theorem pathChartBallSubdivision_n_pos {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) : 0 < S.n := by
  by_contra hpos
  have hn : S.n = 0 := Nat.eq_zero_of_not_pos hpos
  have hidx : (0 : Fin (S.n + 1)) = Fin.last S.n := by
    ext
    simp [hn]
  have h01 : (0 : unitInterval) = 1 := by
    calc
      (0 : unitInterval) = S.t 0 := S.zero_eq.symm
      _ = S.t (Fin.last S.n) := by rw [hidx]
      _ = 1 := S.one_eq
  have hreal : (0 : ℝ) = 1 := by
    have h := congrArg (fun t : unitInterval => (t : ℝ)) h01
    simpa using h
  norm_num at hreal

private def transSubdivisionT {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X))) :
    Fin (S₁.n + S₂.n + 1) → unitInterval := fun i =>
  if h : i.val ≤ S₁.n then
    scaleL (S₁.t ⟨i.val, by omega⟩)
  else
    scaleR (S₂.t ⟨i.val - S₁.n, by omega⟩)

private noncomputable def transSubdivisionCellBall {a b c : X}
    (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X))) :
    Fin (S₁.n + S₂.n) → PathChartBall X := fun i =>
  if h : i.val < S₁.n then
    S₁.cellBall ⟨i.val, by omega⟩
  else
    S₂.cellBall ⟨i.val - S₁.n, by omega⟩

private theorem transSubdivisionT_mono {a b c : X}
    (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X))) :
    Monotone (transSubdivisionT γ₁ γ₂ S₁ S₂) := by
  intro i j hij
  unfold transSubdivisionT
  by_cases hi : i.val ≤ S₁.n
  · by_cases hj : j.val ≤ S₁.n
    · simp [hi, hj]
      exact scaleL_mono
        (S₁.monotone_t (Fin.mk_le_mk.mpr (Fin.val_le_of_le hij)))
    · simp [hi, hj]
      exact (scaleL_le_half _).trans (half_le_scaleR _)
  · by_cases hj : j.val ≤ S₁.n
    · have hij_val : i.val ≤ j.val := Fin.val_le_of_le hij
      omega
    · simp [hi, hj]
      have hij_val : i.val ≤ j.val := Fin.val_le_of_le hij
      have hsub : i.val - S₁.n ≤ j.val - S₁.n := by
        omega
      exact scaleR_mono
        (S₂.monotone_t (Fin.mk_le_mk.mpr hsub))

private theorem transSubdivision_cell_subset {a b c : X}
    (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X))) :
    ∀ i : Fin (S₁.n + S₂.n),
      Set.Icc ((transSubdivisionT γ₁ γ₂ S₁ S₂) i.castSucc)
          ((transSubdivisionT γ₁ γ₂ S₁ S₂) i.succ) ⊆
        pathChartBallSet (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X)))
          (transSubdivisionCellBall γ₁ γ₂ S₁ S₂ i) := by
  intro i u hu
  by_cases hi : i.val < S₁.n
  · let i₁ : Fin S₁.n := ⟨i.val, hi⟩
    have hleft₀ : i.val ≤ S₁.n := Nat.le_of_lt hi
    have hu_left :
        ((S₁.t i₁.castSucc : unitInterval) : ℝ) / 2 ≤ (u : ℝ) := by
      simpa [transSubdivisionT, hleft₀, i₁] using hu.1
    have hu_right :
        (u : ℝ) ≤ ((S₁.t i₁.succ : unitInterval) : ℝ) / 2 := by
      simpa [transSubdivisionT, hi, i₁, Fin.val_succ] using hu.2
    have hu_half : (u : ℝ) ≤ 1 / 2 := by
      linarith [(S₁.t i₁.succ).2.2, hu_right]
    let v : unitInterval := ⟨2 * (u : ℝ), by
      constructor
      · linarith [u.2.1]
      · linarith [hu_half]⟩
    have hvI : v ∈ Set.Icc (S₁.t i₁.castSucc) (S₁.t i₁.succ) := by
      constructor
      · change ((S₁.t i₁.castSucc : unitInterval) : ℝ) ≤ 2 * (u : ℝ)
        linarith [hu_left]
      · change 2 * (u : ℝ) ≤ ((S₁.t i₁.succ : unitInterval) : ℝ)
        linarith [hu_right]
    have hbase := S₁.cell_subset i₁ hvI
    have hγ : ((γ₁.trans γ₂ : Path a c) u) = γ₁ v := by
      have h := Path.extend_trans_of_le_half γ₁ γ₂ (t := (u : ℝ)) hu_half
      rw [Path.extend_apply _ u.2, Path.extend_apply _ v.2] at h
      simpa [v] using h
    simpa [pathChartBallSet, transSubdivisionCellBall, hi, i₁, hγ] using hbase
  · let j : Fin S₂.n := ⟨i.val - S₁.n, by omega⟩
    have hidx_right :
        (⟨i.val + 1 - S₁.n, by omega⟩ : Fin (S₂.n + 1)) = j.succ := by
      ext
      change i.val + 1 - S₁.n = i.val - S₁.n + 1
      omega
    have hraw_right : u ≤ scaleR (S₂.t ⟨i.val + 1 - S₁.n, by omega⟩) := by
      simpa [transSubdivisionT, hi, Fin.val_succ] using hu.2
    have hright_scaled : u ≤ scaleR (S₂.t j.succ) := by
      simpa [hidx_right] using hraw_right
    have hu_right :
        (u : ℝ) ≤ (((S₂.t j.succ : unitInterval) : ℝ) + 1) / 2 := by
      simpa using hright_scaled
    have hu_left_s₂ :
        ((S₂.t j.castSucc : unitInterval) : ℝ) ≤ 2 * (u : ℝ) - 1 := by
      by_cases hleft₀ : i.val ≤ S₁.n
      · have hival : i.val = S₁.n := by
          omega
        have hidx₁ :
            (⟨i.val, by omega⟩ : Fin (S₁.n + 1)) = Fin.last S₁.n := by
          ext
          simp [hival]
        have hraw : scaleL (S₁.t (Fin.last S₁.n)) ≤ u := by
          simpa [transSubdivisionT, hleft₀, hidx₁] using hu.1
        have hu_mid_interval : unitHalf ≤ u := by
          simpa [S₁.one_eq] using hraw
        have hu_mid : (1 / 2 : ℝ) ≤ (u : ℝ) := by
          exact hu_mid_interval
        have hidx₂ : j.castSucc = (0 : Fin (S₂.n + 1)) := by
          ext
          simp [j, hival]
        have hz : ((S₂.t j.castSucc : unitInterval) : ℝ) = 0 := by
          rw [hidx₂, S₂.zero_eq]
          rfl
        linarith
      · have hidx_left :
            (⟨i.val - S₁.n, by omega⟩ : Fin (S₂.n + 1)) = j.castSucc := by
          ext
          simp [j]
        have hraw : scaleR (S₂.t ⟨i.val - S₁.n, by omega⟩) ≤ u := by
          simpa [transSubdivisionT, hleft₀] using hu.1
        have hraw' : scaleR (S₂.t j.castSucc) ≤ u := by
          simpa [hidx_left] using hraw
        change (((S₂.t j.castSucc : unitInterval) : ℝ) + 1) / 2 ≤ (u : ℝ) at hraw'
        linarith
    have hu_half : (1 / 2 : ℝ) ≤ (u : ℝ) := by
      linarith [(S₂.t j.castSucc).2.1, hu_left_s₂]
    let v : unitInterval := ⟨2 * (u : ℝ) - 1, by
      constructor
      · linarith [hu_half]
      · linarith [u.2.2]⟩
    have hvI : v ∈ Set.Icc (S₂.t j.castSucc) (S₂.t j.succ) := by
      constructor
      · change ((S₂.t j.castSucc : unitInterval) : ℝ) ≤ 2 * (u : ℝ) - 1
        exact hu_left_s₂
      · change 2 * (u : ℝ) - 1 ≤ ((S₂.t j.succ : unitInterval) : ℝ)
        linarith [hu_right]
    have hbase := S₂.cell_subset j hvI
    have hγ : ((γ₁.trans γ₂ : Path a c) u) = γ₂ v := by
      have h := Path.extend_trans_of_half_le γ₁ γ₂ (t := (u : ℝ)) hu_half
      rw [Path.extend_apply _ u.2, Path.extend_apply _ v.2] at h
      simpa [v] using h
    simpa [pathChartBallSet, transSubdivisionCellBall, hi, j, hγ] using hbase

private noncomputable def S_trans {a b c : X}
    (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X))) :
    PathChartBallSubdivision (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X))) where
  n := S₁.n + S₂.n
  t := transSubdivisionT γ₁ γ₂ S₁ S₂
  cellBall := transSubdivisionCellBall γ₁ γ₂ S₁ S₂
  zero_eq := by
    simp [transSubdivisionT, S₁.zero_eq]
  one_eq := by
    have hS₂ : 0 < S₂.n := pathChartBallSubdivision_n_pos S₂
    have hS₂_ne : S₂.n ≠ 0 := Nat.ne_of_gt hS₂
    have hidx : (⟨S₂.n, by omega⟩ : Fin (S₂.n + 1)) = Fin.last S₂.n := by
      ext
      simp
    simp [transSubdivisionT, Fin.val_last, hS₂_ne, hidx, S₂.one_eq]
  monotone_t := transSubdivisionT_mono γ₁ γ₂ S₁ S₂
  cell_subset := transSubdivision_cell_subset γ₁ γ₂ S₁ S₂

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
