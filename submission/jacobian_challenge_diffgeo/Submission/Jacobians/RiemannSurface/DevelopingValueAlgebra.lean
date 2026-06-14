import Submission.Jacobians.RiemannSurface.DevelopingMap

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

private theorem trans_apply_scaleL {a b c : X}
    (γ₁ : Path a b) (γ₂ : Path b c) (u : unitInterval) :
    (γ₁.trans γ₂ : Path a c) (scaleL u) = γ₁ u := by
  have hhalf : ((scaleL u : unitInterval) : ℝ) ≤ 1 / 2 := by
    exact scaleL_le_half u
  have h := Path.extend_trans_of_le_half γ₁ γ₂ (t := (scaleL u : ℝ)) hhalf
  have hscale : 2 * ((scaleL u : unitInterval) : ℝ) = (u : ℝ) := by
    simp [scaleL]
    ring
  rw [hscale, Path.extend_apply _ u.2] at h
  rw [Path.extend_apply _ (scaleL u).2] at h
  simpa [hscale] using h

private theorem trans_apply_scaleR {a b c : X}
    (γ₁ : Path a b) (γ₂ : Path b c) (u : unitInterval) :
    (γ₁.trans γ₂ : Path a c) (scaleR u) = γ₂ u := by
  have hhalf : (1 / 2 : ℝ) ≤ (scaleR u : unitInterval) := by
    exact half_le_scaleR u
  have h := Path.extend_trans_of_half_le γ₁ γ₂ (t := (scaleR u : ℝ)) hhalf
  have hscale : 2 * ((scaleR u : unitInterval) : ℝ) - 1 = (u : ℝ) := by
    simp [scaleR]
    ring
  rw [hscale, Path.extend_apply _ u.2] at h
  rw [Path.extend_apply _ (scaleR u).2] at h
  simpa [hscale] using h

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

private theorem devInc_castAdd {a b c : X}
    (form : HolomorphicOneForm X) (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X)))
    (i : Fin S₁.n) :
    developingIncrement form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X)))
        (S_trans γ₁ γ₂ S₁ S₂) (Fin.castAdd S₂.n i) =
      developingIncrement form ((γ₁ : Path a b) : C(unitInterval, X)) S₁ i := by
  have hcell : (Fin.castAdd S₂.n i).val < S₁.n := by
    exact i.isLt
  have hleft : (Fin.castAdd S₂.n i).castSucc.val ≤ S₁.n := by
    exact Nat.le_of_lt i.isLt
  have hright : (Fin.castAdd S₂.n i).succ.val ≤ S₁.n := by
    simpa [Fin.val_succ] using Nat.succ_le_of_lt i.isLt
  have hidx_left_fin :
      (⟨(Fin.castAdd S₂.n i).castSucc.val, by omega⟩ : Fin (S₁.n + 1)) =
        i.castSucc := by
    ext
    rfl
  have hidx_left :
      S₁.t ⟨(Fin.castAdd S₂.n i).castSucc.val, by omega⟩ = S₁.t i.castSucc := by
    exact congrArg S₁.t hidx_left_fin
  have hidx_right_fin :
      (⟨(Fin.castAdd S₂.n i).succ.val, by omega⟩ : Fin (S₁.n + 1)) =
        i.succ := by
    ext
    simp [Fin.val_succ]
  have hidx_right :
      S₁.t ⟨(Fin.castAdd S₂.n i).succ.val, by omega⟩ = S₁.t i.succ := by
    exact congrArg S₁.t hidx_right_fin
  have hidx_left' :
      S₁.t (⟨i.val, by omega⟩ : Fin (S₁.n + 1)) = S₁.t i.castSucc := by
    have hfin : (⟨i.val, by omega⟩ : Fin (S₁.n + 1)) = i.castSucc := by
      ext
      rfl
    exact congrArg S₁.t hfin
  have hidx_right' :
      S₁.t (⟨i.val + 1, by omega⟩ : Fin (S₁.n + 1)) = S₁.t i.succ := by
    congr
  unfold developingIncrement
  simp [S_trans, transSubdivisionT, transSubdivisionCellBall, trans_apply_scaleL,
    hidx_left', hidx_right']

private theorem developingIncrement_trans_right_zero {a b c : X}
    (form : HolomorphicOneForm X) (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X)))
    (hS₂ : 0 < S₂.n) :
    developingIncrement form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X)))
        (S_trans γ₁ γ₂ S₁ S₂)
        (Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)) =
      developingIncrement form ((γ₂ : Path b c) : C(unitInterval, X)) S₂
        (⟨0, hS₂⟩ : Fin S₂.n) := by
  have hcell :
      ¬ (Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).val < S₁.n := by
    simp
  have hleft :
      (Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).castSucc.val ≤ S₁.n := by
    simp
  have hright :
      ¬ (Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).succ.val ≤ S₁.n := by
    simp
  have hidx_cell :
      (⟨(Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).val - S₁.n,
          by omega⟩ : Fin S₂.n) = ⟨0, hS₂⟩ := by
    ext
    simp
  have hidx_left_fin :
      (⟨(Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).castSucc.val,
          by omega⟩ : Fin (S₁.n + 1)) = Fin.last S₁.n := by
    ext
    simp
  have hidx_left :
      S₁.t ⟨(Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).castSucc.val,
          by omega⟩ = S₁.t (Fin.last S₁.n) := by
    exact congrArg S₁.t hidx_left_fin
  have hidx_right_fin :
      (⟨(Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).succ.val - S₁.n,
          by omega⟩ : Fin (S₂.n + 1)) = (⟨0, hS₂⟩ : Fin S₂.n).succ := by
    ext
    simp
  have hidx_right :
      S₂.t ⟨(Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).succ.val - S₁.n,
          by omega⟩ = S₂.t (⟨0, hS₂⟩ : Fin S₂.n).succ := by
    exact congrArg S₂.t hidx_right_fin
  have hleft_path :
      γ₁ (S₁.t ⟨(Fin.natAdd S₁.n (⟨0, hS₂⟩ : Fin S₂.n)).castSucc.val,
          by omega⟩) = b := by
    rw [hidx_left, S₁.one_eq]
    exact γ₁.target
  have hleft_path' :
      γ₁ (S₁.t (⟨S₁.n, by omega⟩ : Fin (S₁.n + 1))) = b := by
    have hlast : (⟨S₁.n, by omega⟩ : Fin (S₁.n + 1)) = Fin.last S₁.n := by
      ext
      simp
    rw [hlast, S₁.one_eq]
    exact γ₁.target
  have hright_path' :
      γ₂ (S₂.t (0 : Fin (S₂.n + 1))) = b := by
    rw [S₂.zero_eq]
    exact γ₂.source
  unfold developingIncrement
  simp [S_trans, transSubdivisionT, transSubdivisionCellBall, trans_apply_scaleL,
    trans_apply_scaleR, hleft_path', hright_path']

private theorem developingIncrement_trans_right_pos {a b c : X}
    (form : HolomorphicOneForm X) (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X)))
    (j : Fin S₂.n) (hj : j.val ≠ 0) :
    developingIncrement form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X)))
        (S_trans γ₁ γ₂ S₁ S₂) (Fin.natAdd S₁.n j) =
      developingIncrement form ((γ₂ : Path b c) : C(unitInterval, X)) S₂ j := by
  have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj
  have hcell : ¬ (Fin.natAdd S₁.n j).val < S₁.n := by
    simp
  have hleft : ¬ (Fin.natAdd S₁.n j).castSucc.val ≤ S₁.n := by
    simp
    omega
  have hright : ¬ (Fin.natAdd S₁.n j).succ.val ≤ S₁.n := by
    simp [Fin.val_succ]
  have hidx_cell :
      (⟨(Fin.natAdd S₁.n j).val - S₁.n, by omega⟩ : Fin S₂.n) = j := by
    ext
    simp
  have hidx_left_fin :
      (⟨(Fin.natAdd S₁.n j).castSucc.val - S₁.n,
          by omega⟩ : Fin (S₂.n + 1)) = j.castSucc := by
    ext
    change S₁.n + j.val - S₁.n = j.val
    omega
  have hidx_left :
      S₂.t ⟨(Fin.natAdd S₁.n j).castSucc.val - S₁.n,
          by omega⟩ = S₂.t j.castSucc := by
    exact congrArg S₂.t hidx_left_fin
  have hidx_right_fin :
      (⟨(Fin.natAdd S₁.n j).succ.val - S₁.n,
          by omega⟩ : Fin (S₂.n + 1)) = j.succ := by
    ext
    change S₁.n + j.val + 1 - S₁.n = j.val + 1
    omega
  have hidx_right :
      S₂.t ⟨(Fin.natAdd S₁.n j).succ.val - S₁.n,
          by omega⟩ = S₂.t j.succ := by
    exact congrArg S₂.t hidx_right_fin
  have hidx_left' :
      S₂.t (⟨j.val, by omega⟩ : Fin (S₂.n + 1)) = S₂.t j.castSucc := by
    have hfin : (⟨j.val, by omega⟩ : Fin (S₂.n + 1)) = j.castSucc := by
      ext
      rfl
    exact congrArg S₂.t hfin
  have hidx_right' :
      S₂.t (⟨S₁.n + j.val + 1 - S₁.n, by omega⟩ : Fin (S₂.n + 1)) =
        S₂.t j.succ := by
    have hfin :
        (⟨S₁.n + j.val + 1 - S₁.n, by omega⟩ : Fin (S₂.n + 1)) = j.succ := by
      ext
      simp [Fin.val_succ]
      omega
    exact congrArg S₂.t hfin
  unfold developingIncrement
  simp [S_trans, transSubdivisionT, transSubdivisionCellBall, trans_apply_scaleR, hj,
    hidx_left', hidx_right']

private theorem devInc_natAdd {a b c : X}
    (form : HolomorphicOneForm X) (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X)))
    (j : Fin S₂.n) :
    developingIncrement form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X)))
        (S_trans γ₁ γ₂ S₁ S₂) (Fin.natAdd S₁.n j) =
      developingIncrement form ((γ₂ : Path b c) : C(unitInterval, X)) S₂ j := by
  by_cases hj : j.val = 0
  · have hS₂ : 0 < S₂.n := by omega
    have hj' : j = (⟨0, hS₂⟩ : Fin S₂.n) := by
      ext
      exact hj
    subst j
    exact developingIncrement_trans_right_zero form γ₁ γ₂ S₁ S₂ hS₂
  · exact developingIncrement_trans_right_pos form γ₁ γ₂ S₁ S₂ j hj

private theorem developingValueOfSubdivision_trans {a b c : X}
    (form : HolomorphicOneForm X) (γ₁ : Path a b) (γ₂ : Path b c)
    (S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)))
    (S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X))) :
    developingValueOfSubdivision form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X)))
        (S_trans γ₁ γ₂ S₁ S₂) =
      developingValueOfSubdivision form ((γ₁ : Path a b) : C(unitInterval, X)) S₁ +
        developingValueOfSubdivision form ((γ₂ : Path b c) : C(unitInterval, X)) S₂ := by
  classical
  unfold developingValueOfSubdivision
  change (∑ i : Fin (S₁.n + S₂.n),
      developingIncrement form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X)))
        (S_trans γ₁ γ₂ S₁ S₂) i) =
    (∑ i : Fin S₁.n,
      developingIncrement form ((γ₁ : Path a b) : C(unitInterval, X)) S₁ i) +
    (∑ i : Fin S₂.n,
      developingIncrement form ((γ₂ : Path b c) : C(unitInterval, X)) S₂ i)
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ =>
      devInc_castAdd form γ₁ γ₂ S₁ S₂ i)
  · exact Finset.sum_congr rfl (fun j _ =>
      devInc_natAdd form γ₁ γ₂ S₁ S₂ j)

/-- A2: the developing value of a concatenated path is the sum of the values. -/
theorem devVal_trans {a b c : X} (x₀ : X) (form : HolomorphicOneForm X)
    (γ₁ : Path a b) (γ₂ : Path b c) :
    developingValue x₀ form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X))) =
      developingValue x₀ form ((γ₁ : Path a b) : C(unitInterval, X)) +
        developingValue x₀ form ((γ₂ : Path b c) : C(unitInterval, X)) := by
  classical
  let S₁ : PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)) :=
    chosenPathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X))
  let S₂ : PathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X)) :=
    chosenPathChartBallSubdivision ((γ₂ : Path b c) : C(unitInterval, X))
  let S : PathChartBallSubdivision (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X))) :=
    S_trans γ₁ γ₂ S₁ S₂
  have htrans :
      developingValue x₀ form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X))) =
        developingValueOfSubdivision form
          (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X))) S :=
    developingValue_eq_developingValueOfSubdivision x₀ form
      (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X))) S
  have hγ₁ :
      developingValue x₀ form ((γ₁ : Path a b) : C(unitInterval, X)) =
        developingValueOfSubdivision form ((γ₁ : Path a b) : C(unitInterval, X)) S₁ :=
    developingValue_eq_developingValueOfSubdivision x₀ form
      ((γ₁ : Path a b) : C(unitInterval, X)) S₁
  have hγ₂ :
      developingValue x₀ form ((γ₂ : Path b c) : C(unitInterval, X)) =
        developingValueOfSubdivision form ((γ₂ : Path b c) : C(unitInterval, X)) S₂ :=
    developingValue_eq_developingValueOfSubdivision x₀ form
      ((γ₂ : Path b c) : C(unitInterval, X)) S₂
  calc
    developingValue x₀ form (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X))) =
        developingValueOfSubdivision form
          (((γ₁.trans γ₂ : Path a c) : C(unitInterval, X))) S := htrans
    _ = developingValueOfSubdivision form ((γ₁ : Path a b) : C(unitInterval, X)) S₁ +
        developingValueOfSubdivision form ((γ₂ : Path b c) : C(unitInterval, X)) S₂ := by
      simpa [S] using developingValueOfSubdivision_trans form γ₁ γ₂ S₁ S₂
    _ = developingValue x₀ form ((γ₁ : Path a b) : C(unitInterval, X)) +
        developingValue x₀ form ((γ₂ : Path b c) : C(unitInterval, X)) := by
      rw [← hγ₁, ← hγ₂]

private theorem developingValue_subpath_eq_increment {a b : X}
    (x₀ : X) (form : HolomorphicOneForm X) (γ : Path a b)
    (S : PathChartBallSubdivision ((γ : Path a b) : C(unitInterval, X)))
    (i : Fin S.n) :
    developingValue x₀ form
        (((γ.subpath (S.t i.castSucc) (S.t i.succ) :
            Path (γ (S.t i.castSucc)) (γ (S.t i.succ))) : C(unitInterval, X))) =
      developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i := by
  classical
  let δ : Path (γ (S.t i.castSucc)) (γ (S.t i.succ)) :=
    γ.subpath (S.t i.castSucc) (S.t i.succ)
  let τ : Fin (1 + 1) → unitInterval := fun j =>
    if j = (0 : Fin (1 + 1)) then 0 else 1
  let Sseg : PathChartBallSubdivision ((δ : Path (γ (S.t i.castSucc))
      (γ (S.t i.succ))) : C(unitInterval, X)) :=
    { n := 1
      t := τ
      cellBall := fun _ => S.cellBall i
      zero_eq := by
        simp [τ]
      one_eq := by
        simp [τ, Fin.last]
      monotone_t := by
        intro j k hjk
        fin_cases j <;> fin_cases k <;> simp [τ] at hjk ⊢
      cell_subset := by
        intro j u _hu
        have hle : S.t i.castSucc ≤ S.t i.succ :=
          S.monotone_t (Fin.castSucc_le_succ i)
        have huI : Set.Icc.convexComb (S.t i.castSucc) (S.t i.succ) u ∈
            Set.Icc (S.t i.castSucc) (S.t i.succ) :=
          ⟨Set.Icc.le_convexComb hle u, Set.Icc.convexComb_le hle u⟩
        have hbase := S.cell_subset i huI
        simpa [pathChartBallSet, δ, Path.subpath] using hbase }
  have hdev :
      developingValue x₀ form
          (((γ.subpath (S.t i.castSucc) (S.t i.succ) :
              Path (γ (S.t i.castSucc)) (γ (S.t i.succ))) : C(unitInterval, X))) =
        developingValueOfSubdivision form ((δ : Path (γ (S.t i.castSucc))
          (γ (S.t i.succ))) : C(unitInterval, X)) Sseg := by
    simpa [δ] using
      developingValue_eq_developingValueOfSubdivision x₀ form
        ((δ : Path (γ (S.t i.castSucc)) (γ (S.t i.succ))) :
          C(unitInterval, X)) Sseg
  have hsub :
      developingValueOfSubdivision form ((δ : Path (γ (S.t i.castSucc))
          (γ (S.t i.succ))) : C(unitInterval, X)) Sseg =
        developingIncrement form ((δ : Path (γ (S.t i.castSucc))
          (γ (S.t i.succ))) : C(unitInterval, X)) Sseg 0 := by
    simp [developingValueOfSubdivision, Sseg]
  have hinc :
      developingIncrement form ((δ : Path (γ (S.t i.castSucc))
          (γ (S.t i.succ))) : C(unitInterval, X)) Sseg 0 =
        developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i := by
    unfold developingIncrement
    simp [Sseg, τ, δ, Path.subpath]
  calc
    developingValue x₀ form
        (((γ.subpath (S.t i.castSucc) (S.t i.succ) :
            Path (γ (S.t i.castSucc)) (γ (S.t i.succ))) : C(unitInterval, X))) =
        developingValueOfSubdivision form ((δ : Path (γ (S.t i.castSucc))
          (γ (S.t i.succ))) : C(unitInterval, X)) Sseg := hdev
    _ = developingIncrement form ((δ : Path (γ (S.t i.castSucc))
          (γ (S.t i.succ))) : C(unitInterval, X)) Sseg 0 := hsub
    _ = developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S i := hinc

/-- A4: the developing value is the sum of the developing values on subdivision segments. -/
theorem devVal_subdivision {a b : X} (x₀ : X) (form : HolomorphicOneForm X)
    (γ : Path a b)
    (S : PathChartBallSubdivision ((γ : Path a b) : C(unitInterval, X))) :
    developingValue x₀ form ((γ : Path a b) : C(unitInterval, X)) =
      ∑ i : Fin S.n,
        developingValue x₀ form
          (((γ.subpath (S.t i.castSucc) (S.t i.succ) :
              Path (γ (S.t i.castSucc)) (γ (S.t i.succ))) : C(unitInterval, X))) := by
  classical
  have hdev :
      developingValue x₀ form ((γ : Path a b) : C(unitInterval, X)) =
        developingValueOfSubdivision form ((γ : Path a b) : C(unitInterval, X)) S :=
    developingValue_eq_developingValueOfSubdivision x₀ form
      ((γ : Path a b) : C(unitInterval, X)) S
  calc
    developingValue x₀ form ((γ : Path a b) : C(unitInterval, X)) =
        developingValueOfSubdivision form ((γ : Path a b) : C(unitInterval, X)) S := hdev
    _ = ∑ i : Fin S.n,
        developingValue x₀ form
          (((γ.subpath (S.t i.castSucc) (S.t i.succ) :
              Path (γ (S.t i.castSucc)) (γ (S.t i.succ))) : C(unitInterval, X))) := by
      unfold developingValueOfSubdivision
      exact Finset.sum_congr rfl (fun i _ =>
        (developingValue_subpath_eq_increment x₀ form γ S i).symm)

/-- A5: a chart-contained cell boundary has equal sums of opposite developing values. -/
theorem devVal_cell_eq {p q r s : X} (x₀ : X) (form : HolomorphicOneForm X)
    (B : Path p q) (R : Path q s) (T : Path r s) (L : Path p r)
    (Bl : PathChartBall X)
    (himage : ∀ u : unitInterval,
      u ∈ pathChartBallSet
        ((((B.trans R).trans T.symm).trans L.symm : Path p p) : C(unitInterval, X)) Bl) :
    developingValue x₀ form ((B : Path p q) : C(unitInterval, X)) +
        developingValue x₀ form ((R : Path q s) : C(unitInterval, X)) =
      developingValue x₀ form ((T : Path r s) : C(unitInterval, X)) +
        developingValue x₀ form ((L : Path p r) : C(unitInterval, X)) := by
  classical
  let loop : Path p p := ((B.trans R).trans T.symm).trans L.symm
  have hloop : ((loop : Path p p) : C(unitInterval, X)) (0 : unitInterval) =
      ((loop : Path p p) : C(unitInterval, X)) (1 : unitInterval) := by
    simp [loop]
  have hzero :
      developingValue x₀ form ((loop : Path p p) : C(unitInterval, X)) = 0 := by
    simpa [loop] using
      developingValue_eq_zero_of_loop_in_pathChartBall
        (x₀ := x₀) (form := form)
        (γ := ((loop : Path p p) : C(unitInterval, X))) Bl hloop
        (by simpa [loop] using himage)
  have hsplit :
      developingValue x₀ form ((loop : Path p p) : C(unitInterval, X)) =
        ((developingValue x₀ form ((B : Path p q) : C(unitInterval, X)) +
            developingValue x₀ form ((R : Path q s) : C(unitInterval, X))) +
          -developingValue x₀ form ((T : Path r s) : C(unitInterval, X))) +
          -developingValue x₀ form ((L : Path p r) : C(unitInterval, X)) := by
    simp only [loop]
    rw [devVal_trans x₀ form ((B.trans R).trans T.symm) L.symm]
    rw [devVal_trans x₀ form (B.trans R) T.symm]
    rw [devVal_trans x₀ form B R]
    rw [devVal_symm x₀ form T]
    rw [devVal_symm x₀ form L]
  have hsum :
      ((developingValue x₀ form ((B : Path p q) : C(unitInterval, X)) +
          developingValue x₀ form ((R : Path q s) : C(unitInterval, X))) +
        -developingValue x₀ form ((T : Path r s) : C(unitInterval, X))) +
        -developingValue x₀ form ((L : Path p r) : C(unitInterval, X)) = 0 := by
    rw [← hsplit, hzero]
  calc
    developingValue x₀ form ((B : Path p q) : C(unitInterval, X)) +
        developingValue x₀ form ((R : Path q s) : C(unitInterval, X)) =
        (developingValue x₀ form ((T : Path r s) : C(unitInterval, X)) +
          developingValue x₀ form ((L : Path p r) : C(unitInterval, X))) +
          (((developingValue x₀ form ((B : Path p q) : C(unitInterval, X)) +
              developingValue x₀ form ((R : Path q s) : C(unitInterval, X))) +
            -developingValue x₀ form ((T : Path r s) : C(unitInterval, X))) +
            -developingValue x₀ form ((L : Path p r) : C(unitInterval, X))) := by
          abel
    _ = developingValue x₀ form ((T : Path r s) : C(unitInterval, X)) +
        developingValue x₀ form ((L : Path p r) : C(unitInterval, X)) := by
      rw [hsum]
      abel

end Jacobians.RiemannSurface
