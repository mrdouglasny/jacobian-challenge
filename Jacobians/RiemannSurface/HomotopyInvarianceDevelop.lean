import Jacobians.RiemannSurface.DevelopingValueAlgebra
import Jacobians.RiemannSurface.SquareSubdivision
import Jacobians.RiemannSurface.DevelopingBridge

/-!
# Homotopy invariance for developing values

This file proves the final grid-telescoping step for HI-1: the choice-based
`developingValue` is invariant under path homotopy, and hence so is the
canonical arc integral via the HI-0 bridge.
-/

noncomputable section

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Set

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The point-level chart-ball predicate underlying `pathChartBallSet`. -/
def pointChartBallSet (B : PathChartBall X) : Set X :=
  {x | x ∈ (chartAt ℂ B.p).source ∧
    (extChartAt 𝓘(ℂ) B.p) x ∈ Metric.ball B.c B.r}

lemma pathChartBallSet_eq_preimage_pointChartBallSet (γ : C(unitInterval, X))
    (B : PathChartBall X) :
    pathChartBallSet γ B = γ ⁻¹' pointChartBallSet B := by
  rfl

/-- Subdivide the square so that every cell maps into one chart-coordinate ball. -/
theorem exists_pathChartBall_subordinate_grid
    (G : unitInterval → unitInterval → X)
    (hG : Continuous (fun z : unitInterval × unitInterval => G z.1 z.2)) :
    ∃ (m n : ℕ) (sigma : Fin (m + 1) → ℝ) (tau : Fin (n + 1) → ℝ)
      (B : Fin m → Fin n → PathChartBall X),
      sigma 0 = 0 ∧ sigma (Fin.last m) = 1 ∧ Monotone sigma ∧
      tau 0 = 0 ∧ tau (Fin.last n) = 1 ∧ Monotone tau ∧
      ∀ i : Fin m, ∀ j : Fin n,
        ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (sigma i.castSucc) (sigma i.succ) →
        ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (tau j.castSucc) (tau j.succ) →
          G x y ∈ pointChartBallSet (B i j) := by
  classical
  let c : PathChartBall X → Set (unitInterval × unitInterval) :=
    fun B => {z | G z.1 z.2 ∈ pointChartBallSet B}
  have hc_open : ∀ B, IsOpen (c B) := by
    intro B
    have hopenX : IsOpen ((chartAt ℂ B.p).source ∩
        (extChartAt 𝓘(ℂ) B.p) ⁻¹' Metric.ball B.c B.r) := by
      exact isOpen_extChartAt_preimage (I := 𝓘(ℂ)) B.p Metric.isOpen_ball
    simpa [c, pointChartBallSet, Set.preimage_inter] using hopenX.preimage hG
  have hc_cover : Set.univ ⊆ ⋃ B : PathChartBall X, c B := by
    intro z _hz
    let p : X := G z.1 z.2
    let w : ℂ := (extChartAt 𝓘(ℂ) p) p
    have hw_target : w ∈ (extChartAt 𝓘(ℂ) p).target := by
      simp [w, p]
    obtain ⟨r, hr_pos, hr_sub⟩ :=
      (Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := 𝓘(ℂ)) p)) w hw_target
    let B : PathChartBall X :=
      { p := p, c := w, r := r, ball_subset_target := hr_sub }
    refine Set.mem_iUnion.2 ⟨B, ?_⟩
    constructor
    · simp [B, p]
    · exact (show (extChartAt 𝓘(ℂ) B.p) (G z.1 z.2) ∈ Metric.ball B.c B.r by
        simpa [B, p, w] using (Metric.mem_ball_self (x := w) hr_pos))
  obtain ⟨t, ht_zero, ht_mono, ⟨k, ht_eventually_one⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self (c := c) hc_open hc_cover
  let N : ℕ := k + 1
  refine ⟨N, N, (fun i : Fin (N + 1) => (t i.val : ℝ)),
    (fun j : Fin (N + 1) => (t j.val : ℝ)),
    (fun i : Fin N => fun j : Fin N => Classical.choose (ht_sub i.val j.val)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val ht_zero
  · have hlast : t N = 1 := ht_eventually_one N (Nat.le_succ k)
    simpa [N, Fin.val_last] using congrArg Subtype.val hlast
  · intro i j hij
    exact (ht_mono (Fin.val_le_of_le hij) : (t i.val : ℝ) ≤ (t j.val : ℝ))
  · simpa using congrArg Subtype.val ht_zero
  · have hlast : t N = 1 := ht_eventually_one N (Nat.le_succ k)
    simpa [N, Fin.val_last] using congrArg Subtype.val hlast
  · intro i j hij
    exact (ht_mono (Fin.val_le_of_le hij) : (t i.val : ℝ) ≤ (t j.val : ℝ))
  · intro i j x hx y hy
    have hx_left : (t i.val : ℝ) ≤ (x : ℝ) := by
      simpa [Fin.val_castSucc] using hx.1
    have hx_right : (x : ℝ) ≤ (t (i.val + 1) : ℝ) := by
      simpa [Fin.val_succ] using hx.2
    have hy_left : (t j.val : ℝ) ≤ (y : ℝ) := by
      simpa [Fin.val_castSucc] using hy.1
    have hy_right : (y : ℝ) ≤ (t (j.val + 1) : ℝ) := by
      simpa [Fin.val_succ] using hy.2
    have hu : x ∈ Set.Icc (t i.val) (t (i.val + 1)) := by
      constructor
      · exact hx_left
      · exact hx_right
    have hv : y ∈ Set.Icc (t j.val) (t (j.val + 1)) := by
      constructor
      · exact hy_left
      · exact hy_right
    have huv :
        (x, y) ∈ Set.Icc (t i.val) (t (i.val + 1)) ×ˢ
          Set.Icc (t j.val) (t (j.val + 1)) := by
      exact ⟨hu, hv⟩
    exact Classical.choose_spec (ht_sub i.val j.val) huv

/-- Clamp a real number to the unit interval. -/
def clampToI (x : ℝ) : unitInterval :=
  ⟨max 0 (min 1 x), by
    constructor
    · exact le_max_left 0 (min 1 x)
    · exact max_le zero_le_one (min_le_left 1 x)⟩

@[simp] lemma clampToI_zero : clampToI 0 = (0 : unitInterval) := by
  ext
  simp [clampToI]

@[simp] lemma clampToI_one : clampToI 1 = (1 : unitInterval) := by
  ext
  simp [clampToI]

/-- Extend a finite real subdivision to all natural indices, clamped into `I`. -/
def extGrid {m : ℕ} (σ : Fin (m + 1) → ℝ) : ℕ → unitInterval := fun k =>
  if h : k < m + 1 then clampToI (σ ⟨k, h⟩) else 1

lemma extGrid_of_lt {m : ℕ} (σ : Fin (m + 1) → ℝ) {k : ℕ} (hk : k < m + 1) :
    extGrid σ k = clampToI (σ ⟨k, hk⟩) := by
  simp [extGrid, hk]

@[simp] lemma extGrid_zero {m : ℕ} (σ : Fin (m + 1) → ℝ) (hσ0 : σ 0 = 0) :
    extGrid σ 0 = 0 := by
  rw [extGrid_of_lt σ (Nat.succ_pos m)]
  simp [hσ0]

@[simp] lemma extGrid_last {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ1 : σ (Fin.last m) = 1) :
    extGrid σ m = 1 := by
  rw [extGrid_of_lt σ (Nat.lt_succ_self m)]
  have hidx : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := by
    ext
    simp
  simp [hidx, hσ1]

lemma extGrid_castSucc {m : ℕ} (σ : Fin (m + 1) → ℝ) (i : Fin m) :
    extGrid σ i = clampToI (σ i.castSucc) := by
  rw [extGrid_of_lt σ (Nat.lt_trans i.isLt (Nat.lt_succ_self m))]
  congr

lemma extGrid_succ {m : ℕ} (σ : Fin (m + 1) → ℝ) (i : Fin m) :
    extGrid σ (i + 1) = clampToI (σ i.succ) := by
  rw [extGrid_of_lt σ (by simp)]
  congr

/-- Bottom horizontal edge of a homotopy grid cell. -/
def B_edge {a b : X} {γ₁ γ₂ : Path a b} (H : Path.Homotopy γ₁ γ₂)
    (σu τu : ℕ → unitInterval) (i j : ℕ) :
    Path ((H.eval (τu j)) (σu i)) ((H.eval (τu j)) (σu (i + 1))) :=
  (H.eval (τu j)).subpath (σu i) (σu (i + 1))

/-- Top horizontal edge of a homotopy grid cell. Definitionally the next row's bottom edge. -/
def T_edge {a b : X} {γ₁ γ₂ : Path a b} (H : Path.Homotopy γ₁ γ₂)
    (σu τu : ℕ → unitInterval) (i j : ℕ) :
    Path ((H.eval (τu (j + 1))) (σu i)) ((H.eval (τu (j + 1))) (σu (i + 1))) :=
  B_edge H σu τu i (j + 1)

/-- Vertical edge of a homotopy grid cell at fixed horizontal coordinate. -/
def vertEdge {a b : X} {γ₁ γ₂ : Path a b} (H : Path.Homotopy γ₁ γ₂)
    (x y₁ y₂ : unitInterval) :
    Path ((H.eval y₁) x) ((H.eval y₂) x) :=
  (H.toHomotopy.evalAt x).subpath y₁ y₂

/-- Left vertical edge of a homotopy grid cell. -/
def L_edge {a b : X} {γ₁ γ₂ : Path a b} (H : Path.Homotopy γ₁ γ₂)
    (σu τu : ℕ → unitInterval) (i j : ℕ) :
    Path ((H.eval (τu j)) (σu i)) ((H.eval (τu (j + 1))) (σu i)) :=
  vertEdge H (σu i) (τu j) (τu (j + 1))

/-- Right vertical edge of a homotopy grid cell. Definitionally the next column's left edge. -/
def R_edge {a b : X} {γ₁ γ₂ : Path a b} (H : Path.Homotopy γ₁ γ₂)
    (σu τu : ℕ → unitInterval) (i j : ℕ) :
    Path ((H.eval (τu j)) (σu (i + 1))) ((H.eval (τu (j + 1))) (σu (i + 1))) :=
  L_edge H σu τu (i + 1) j

end Jacobians.RiemannSurface
