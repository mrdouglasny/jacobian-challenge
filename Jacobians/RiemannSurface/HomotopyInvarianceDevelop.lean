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
open scoped BigOperators
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
      0 < m ∧ 0 < n ∧
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
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.succ_pos k
  · exact Nat.succ_pos k
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

lemma clampToI_coe_of_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (clampToI x : ℝ) = x := by
  simp [clampToI, hx.1, hx.2]

lemma grid_value_mem_Icc {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (k : Fin (m + 1)) :
    σ k ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · calc
      (0 : ℝ) = σ 0 := hσ0.symm
      _ ≤ σ k := hσmono (Fin.zero_le k)
  · calc
      σ k ≤ σ (Fin.last m) := hσmono (Fin.le_last k)
      _ = 1 := hσ1

lemma extGrid_coe_of_lt {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    {k : ℕ} (hk : k < m + 1) :
    (extGrid σ k : ℝ) = σ ⟨k, hk⟩ := by
  rw [extGrid_of_lt σ hk]
  exact clampToI_coe_of_Icc (grid_value_mem_Icc σ hσ0 hσ1 hσmono ⟨k, hk⟩)

lemma extGrid_coe_castSucc {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (i : Fin m) :
    (extGrid σ i : ℝ) = σ i.castSucc := by
  rw [extGrid_coe_of_lt σ hσ0 hσ1 hσmono
    (Nat.lt_trans i.isLt (Nat.lt_succ_self m))]
  congr

lemma extGrid_coe_succ {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (i : Fin m) :
    (extGrid σ (i + 1) : ℝ) = σ i.succ := by
  rw [extGrid_coe_of_lt σ hσ0 hσ1 hσmono (by simp)]
  congr

lemma extGrid_castSucc_le_succ {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (i : Fin m) :
    extGrid σ i ≤ extGrid σ (i + 1) := by
  change (extGrid σ i : ℝ) ≤ (extGrid σ (i + 1) : ℝ)
  rw [extGrid_coe_castSucc σ hσ0 hσ1 hσmono i,
    extGrid_coe_succ σ hσ0 hσ1 hσmono i]
  exact hσmono (Fin.castSucc_le_succ i)

lemma extGrid_fin_monotone {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ) :
    Monotone (fun k : Fin (m + 1) => extGrid σ k.val) := by
  intro i j hij
  change (extGrid σ i.val : ℝ) ≤ (extGrid σ j.val : ℝ)
  rw [extGrid_coe_of_lt σ hσ0 hσ1 hσmono i.isLt,
    extGrid_coe_of_lt σ hσ0 hσ1 hσmono j.isLt]
  exact hσmono hij

lemma extGrid_left_mem_real_Icc {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (i : Fin m) :
    (extGrid σ i : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) := by
  constructor
  · rw [extGrid_coe_castSucc σ hσ0 hσ1 hσmono i]
  · calc
      (extGrid σ i : ℝ) = σ i.castSucc :=
        extGrid_coe_castSucc σ hσ0 hσ1 hσmono i
      _ ≤ σ i.succ := hσmono (Fin.castSucc_le_succ i)

lemma extGrid_right_mem_real_Icc {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (i : Fin m) :
    (extGrid σ (i + 1) : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) := by
  constructor
  · calc
      σ i.castSucc ≤ σ i.succ := hσmono (Fin.castSucc_le_succ i)
      _ = (extGrid σ (i + 1) : ℝ) :=
        (extGrid_coe_succ σ hσ0 hσ1 hσmono i).symm
  · rw [extGrid_coe_succ σ hσ0 hσ1 hσmono i]

lemma extGrid_convex_mem_real_Icc {m : ℕ} (σ : Fin (m + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (i : Fin m) (u : unitInterval) :
    ((Set.Icc.convexComb (extGrid σ i) (extGrid σ (i + 1)) u : unitInterval) : ℝ) ∈
      Set.Icc (σ i.castSucc) (σ i.succ) := by
  have hle : extGrid σ i ≤ extGrid σ (i + 1) :=
    extGrid_castSucc_le_succ σ hσ0 hσ1 hσmono i
  let x : unitInterval := Set.Icc.convexComb (extGrid σ i) (extGrid σ (i + 1)) u
  have hx : x ∈ Set.Icc (extGrid σ i) (extGrid σ (i + 1)) :=
    ⟨Set.Icc.le_convexComb hle u, Set.Icc.convexComb_le hle u⟩
  constructor
  · calc
      σ i.castSucc = (extGrid σ i : ℝ) :=
        (extGrid_coe_castSucc σ hσ0 hσ1 hσmono i).symm
      _ ≤ (x : ℝ) := hx.1
  · calc
      (x : ℝ) ≤ (extGrid σ (i + 1) : ℝ) := hx.2
      _ = σ i.succ := extGrid_coe_succ σ hσ0 hσ1 hσmono i

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

noncomputable def devBVal {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X) (H : Path.Homotopy γ₁ γ₂)
    (σu τu : ℕ → unitInterval) (i j : ℕ) : ℂ :=
  developingValue x₀ form
    (((B_edge H σu τu i j :
      Path ((H.eval (τu j)) (σu i)) ((H.eval (τu j)) (σu (i + 1)))) :
      C(unitInterval, X)))

noncomputable def devTVal {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X) (H : Path.Homotopy γ₁ γ₂)
    (σu τu : ℕ → unitInterval) (i j : ℕ) : ℂ :=
  developingValue x₀ form
    (((T_edge H σu τu i j :
      Path ((H.eval (τu (j + 1))) (σu i)) ((H.eval (τu (j + 1))) (σu (i + 1)))) :
      C(unitInterval, X)))

noncomputable def devLVal {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X) (H : Path.Homotopy γ₁ γ₂)
    (σu τu : ℕ → unitInterval) (i j : ℕ) : ℂ :=
  developingValue x₀ form
    (((L_edge H σu τu i j :
      Path ((H.eval (τu j)) (σu i)) ((H.eval (τu (j + 1))) (σu i))) :
      C(unitInterval, X)))

/-- The oriented boundary loop of one homotopy grid cell. -/
def cellLoop {a b : X} {γ₁ γ₂ : Path a b} (H : Path.Homotopy γ₁ γ₂)
    (σu τu : ℕ → unitInterval) (i j : ℕ) :
    Path ((H.eval (τu j)) (σu i)) ((H.eval (τu j)) (σu i)) :=
  (((B_edge H σu τu i j).trans (R_edge H σu τu i j)).trans
    (T_edge H σu τu i j).symm).trans (L_edge H σu τu i j).symm

private lemma B_edge_mem_pointChartBallSet {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j))
    (i : Fin m) (j : Fin n) (u : unitInterval) :
    B_edge H (extGrid σ) (extGrid τ) i.val j.val u ∈ pointChartBallSet (Bcell i j) := by
  let x : unitInterval := Set.Icc.convexComb (extGrid σ i) (extGrid σ (i + 1)) u
  have hx : (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) :=
    extGrid_convex_mem_real_Icc σ hσ0 hσ1 hσmono i u
  have hy : ((extGrid τ j : unitInterval) : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) :=
    extGrid_left_mem_real_Icc τ hτ0 hτ1 hτmono j
  have h := hcell i j x hx (extGrid τ j) hy
  simpa [B_edge, Path.subpath, x] using h

private lemma T_edge_mem_pointChartBallSet {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j))
    (i : Fin m) (j : Fin n) (u : unitInterval) :
    T_edge H (extGrid σ) (extGrid τ) i.val j.val u ∈ pointChartBallSet (Bcell i j) := by
  let x : unitInterval := Set.Icc.convexComb (extGrid σ i) (extGrid σ (i + 1)) u
  have hx : (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) :=
    extGrid_convex_mem_real_Icc σ hσ0 hσ1 hσmono i u
  have hy : ((extGrid τ (j + 1) : unitInterval) : ℝ) ∈
      Set.Icc (τ j.castSucc) (τ j.succ) :=
    extGrid_right_mem_real_Icc τ hτ0 hτ1 hτmono j
  have h := hcell i j x hx (extGrid τ (j + 1)) hy
  simpa [T_edge, B_edge, Path.subpath, x] using h

private lemma L_edge_mem_pointChartBallSet {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j))
    (i : Fin m) (j : Fin n) (u : unitInterval) :
    L_edge H (extGrid σ) (extGrid τ) i.val j.val u ∈ pointChartBallSet (Bcell i j) := by
  let y : unitInterval := Set.Icc.convexComb (extGrid τ j) (extGrid τ (j + 1)) u
  have hx : ((extGrid σ i : unitInterval) : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) :=
    extGrid_left_mem_real_Icc σ hσ0 hσ1 hσmono i
  have hy : (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) :=
    extGrid_convex_mem_real_Icc τ hτ0 hτ1 hτmono j u
  have h := hcell i j (extGrid σ i) hx y hy
  simpa [L_edge, vertEdge, Path.subpath, y] using h

private lemma R_edge_mem_pointChartBallSet {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j))
    (i : Fin m) (j : Fin n) (u : unitInterval) :
    R_edge H (extGrid σ) (extGrid τ) i.val j.val u ∈ pointChartBallSet (Bcell i j) := by
  let y : unitInterval := Set.Icc.convexComb (extGrid τ j) (extGrid τ (j + 1)) u
  have hx : ((extGrid σ (i + 1) : unitInterval) : ℝ) ∈
      Set.Icc (σ i.castSucc) (σ i.succ) :=
    extGrid_right_mem_real_Icc σ hσ0 hσ1 hσmono i
  have hy : (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) :=
    extGrid_convex_mem_real_Icc τ hτ0 hτ1 hτmono j u
  have h := hcell i j (extGrid σ (i + 1)) hx y hy
  simpa [R_edge, L_edge, vertEdge, Path.subpath, y] using h

lemma cellLoop_mem_pathChartBallSet {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j))
    (i : Fin m) (j : Fin n) :
    ∀ u : unitInterval,
      u ∈ pathChartBallSet
        ((cellLoop H (extGrid σ) (extGrid τ) i.val j.val :
          Path ((H.eval (extGrid τ j)) (extGrid σ i))
            ((H.eval (extGrid τ j)) (extGrid σ i))) : C(unitInterval, X))
        (Bcell i j) := by
  intro u
  rw [pathChartBallSet_eq_preimage_pointChartBallSet]
  change cellLoop H (extGrid σ) (extGrid τ) i.val j.val u ∈ pointChartBallSet (Bcell i j)
  unfold cellLoop
  have hmem :
      cellLoop H (extGrid σ) (extGrid τ) i.val j.val u ∈
        Set.range (cellLoop H (extGrid σ) (extGrid τ) i.val j.val) := ⟨u, rfl⟩
  rw [cellLoop, Path.trans_range, Path.trans_range, Path.trans_range,
    Path.symm_range, Path.symm_range] at hmem
  rcases hmem with hprev | hL
  · rcases hprev with hBR | hT
    · rcases hBR with hB | hR
      · rcases hB with ⟨v, hv⟩
        rw [← hv]
        exact B_edge_mem_pointChartBallSet H σ τ hσ0 hσ1 hσmono hτ0 hτ1 hτmono
          Bcell hcell i j v
      · rcases hR with ⟨v, hv⟩
        rw [← hv]
        exact R_edge_mem_pointChartBallSet H σ τ hσ0 hσ1 hσmono hτ0 hτ1 hτmono
          Bcell hcell i j v
    · rcases hT with ⟨v, hv⟩
      rw [← hv]
      exact T_edge_mem_pointChartBallSet H σ τ hσ0 hσ1 hσmono hτ0 hτ1 hτmono
        Bcell hcell i j v
  · rcases hL with ⟨v, hv⟩
    rw [← hv]
    exact L_edge_mem_pointChartBallSet H σ τ hσ0 hσ1 hσmono hτ0 hτ1 hτmono
      Bcell hcell i j v

lemma devVal_cell_rearrange {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X)
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j))
    (i : Fin m) (j : Fin n) :
    developingValue x₀ form
        (((B_edge H (extGrid σ) (extGrid τ) i.val j.val) :
          Path ((H.eval (extGrid τ j)) (extGrid σ i))
            ((H.eval (extGrid τ j)) (extGrid σ (i + 1)))) :
          C(unitInterval, X)) -
      developingValue x₀ form
        (((T_edge H (extGrid σ) (extGrid τ) i.val j.val) :
          Path ((H.eval (extGrid τ (j + 1))) (extGrid σ i))
            ((H.eval (extGrid τ (j + 1))) (extGrid σ (i + 1)))) :
          C(unitInterval, X)) =
      developingValue x₀ form
        (((L_edge H (extGrid σ) (extGrid τ) i.val j.val) :
          Path ((H.eval (extGrid τ j)) (extGrid σ i))
            ((H.eval (extGrid τ (j + 1))) (extGrid σ i))) :
          C(unitInterval, X)) -
      developingValue x₀ form
        (((L_edge H (extGrid σ) (extGrid τ) (i.val + 1) j.val) :
          Path ((H.eval (extGrid τ j)) (extGrid σ (i.val + 1)))
            ((H.eval (extGrid τ (j + 1))) (extGrid σ (i.val + 1)))) :
          C(unitInterval, X)) := by
  have hboundary :=
    cellLoop_mem_pathChartBallSet H σ τ hσ0 hσ1 hσmono hτ0 hτ1 hτmono
      Bcell hcell i j
  have hcell_eq :=
    devVal_cell_eq (x₀ := x₀) (form := form)
      (B := B_edge H (extGrid σ) (extGrid τ) i.val j.val)
      (R := R_edge H (extGrid σ) (extGrid τ) i.val j.val)
      (T := T_edge H (extGrid σ) (extGrid τ) i.val j.val)
      (L := L_edge H (extGrid σ) (extGrid τ) i.val j.val)
      (Bl := Bcell i j)
      (by simpa [cellLoop] using hboundary)
  let dB : ℂ := developingValue x₀ form
    (((B_edge H (extGrid σ) (extGrid τ) i.val j.val) :
      Path ((H.eval (extGrid τ j)) (extGrid σ i))
        ((H.eval (extGrid τ j)) (extGrid σ (i + 1)))) :
      C(unitInterval, X))
  let dR : ℂ := developingValue x₀ form
    (((R_edge H (extGrid σ) (extGrid τ) i.val j.val) :
      Path ((H.eval (extGrid τ j)) (extGrid σ (i + 1)))
        ((H.eval (extGrid τ (j + 1))) (extGrid σ (i + 1)))) :
      C(unitInterval, X))
  let dT : ℂ := developingValue x₀ form
    (((T_edge H (extGrid σ) (extGrid τ) i.val j.val) :
      Path ((H.eval (extGrid τ (j + 1))) (extGrid σ i))
        ((H.eval (extGrid τ (j + 1))) (extGrid σ (i + 1)))) :
      C(unitInterval, X))
  let dL : ℂ := developingValue x₀ form
    (((L_edge H (extGrid σ) (extGrid τ) i.val j.val) :
      Path ((H.eval (extGrid τ j)) (extGrid σ i))
        ((H.eval (extGrid τ (j + 1))) (extGrid σ i))) :
      C(unitInterval, X))
  have hmove : dB - dT = dL - dR := by
    have h := hcell_eq
    change dB + dR = dT + dL at h
    calc
      dB - dT = (dB + dR) - dR - dT := by abel
      _ = (dT + dL) - dR - dT := by rw [h]
      _ = dL - dR := by abel
  simpa [dB, dR, dT, dL, R_edge] using hmove

lemma devVal_cell_rearrange_nat {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X)
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j))
    (i j : ℕ) (hi : i < m) (hj : j < n) :
    devBVal x₀ form H (extGrid σ) (extGrid τ) i j -
      devTVal x₀ form H (extGrid σ) (extGrid τ) i j =
    devLVal x₀ form H (extGrid σ) (extGrid τ) i j -
      devLVal x₀ form H (extGrid σ) (extGrid τ) (i + 1) j := by
  let ii : Fin m := ⟨i, hi⟩
  let jj : Fin n := ⟨j, hj⟩
  simpa [devBVal, devTVal, devLVal, ii, jj] using
    devVal_cell_rearrange x₀ form H σ τ hσ0 hσ1 hσmono hτ0 hτ1 hτmono
      Bcell hcell ii jj

/-- A path whose image is propositionally constant has zero developing value. -/
lemma devVal_const_image_zero {a b : X} (x₀ : X) (form : HolomorphicOneForm X)
    (γ : Path a b) (x : X) (hγ : ∀ u : unitInterval, γ u = x) :
    developingValue x₀ form ((γ : Path a b) : C(unitInterval, X)) = 0 := by
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
    (γ := ((γ : Path a b) : C(unitInterval, X))) B ?_ ?_
  · change γ (0 : unitInterval) = γ (1 : unitInterval)
    rw [hγ 0, hγ 1]
  · intro u
    constructor
    · simp [B, hγ u]
    · exact (show (extChartAt 𝓘(ℂ) B.p)
          (((γ : Path a b) : C(unitInterval, X)) u) ∈ Metric.ball B.c B.r by
        simpa [B, z, hγ u] using (Metric.mem_ball_self (x := z) hr_pos))

lemma devVal_vertEdge_const_left {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X) (H : Path.Homotopy γ₁ γ₂)
    (y₁ y₂ : unitInterval) :
    developingValue x₀ form
      (((vertEdge H (0 : unitInterval) y₁ y₂ :
          Path ((H.eval y₁) (0 : unitInterval)) ((H.eval y₂) (0 : unitInterval))) :
        C(unitInterval, X))) = 0 := by
  refine devVal_const_image_zero x₀ form (vertEdge H (0 : unitInterval) y₁ y₂) a ?_
  intro u
  change H (Set.Icc.convexComb y₁ y₂ u, (0 : unitInterval)) = a
  exact Path.Homotopy.source H (Set.Icc.convexComb y₁ y₂ u)

lemma devVal_vertEdge_const_right {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X) (H : Path.Homotopy γ₁ γ₂)
    (y₁ y₂ : unitInterval) :
    developingValue x₀ form
      (((vertEdge H (1 : unitInterval) y₁ y₂ :
          Path ((H.eval y₁) (1 : unitInterval)) ((H.eval y₂) (1 : unitInterval))) :
        C(unitInterval, X))) = 0 := by
  refine devVal_const_image_zero x₀ form (vertEdge H (1 : unitInterval) y₁ y₂) b ?_
  intro u
  change H (Set.Icc.convexComb y₁ y₂ u, (1 : unitInterval)) = b
  exact Path.Homotopy.target H (Set.Icc.convexComb y₁ y₂ u)

lemma row_sum_eq {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X)
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j))
    (j : Fin n) :
    (∑ i ∈ Finset.range m, devBVal x₀ form H (extGrid σ) (extGrid τ) i j.val) =
      ∑ i ∈ Finset.range m, devTVal x₀ form H (extGrid σ) (extGrid τ) i j.val := by
  classical
  have hsum :
      (∑ i ∈ Finset.range m,
        (devBVal x₀ form H (extGrid σ) (extGrid τ) i j.val -
          devTVal x₀ form H (extGrid σ) (extGrid τ) i j.val)) =
      ∑ i ∈ Finset.range m,
        (devLVal x₀ form H (extGrid σ) (extGrid τ) i j.val -
          devLVal x₀ form H (extGrid σ) (extGrid τ) (i + 1) j.val) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact devVal_cell_rearrange_nat x₀ form H σ τ hσ0 hσ1 hσmono
      hτ0 hτ1 hτmono Bcell hcell i j.val (Finset.mem_range.mp hi) j.isLt
  have hL0 : devLVal x₀ form H (extGrid σ) (extGrid τ) 0 j.val = 0 := by
    change developingValue x₀ form
      (((vertEdge H (extGrid σ 0) (extGrid τ j.val) (extGrid τ (j.val + 1)) :
        Path ((H.eval (extGrid τ j.val)) (extGrid σ 0))
          ((H.eval (extGrid τ (j.val + 1))) (extGrid σ 0))) :
        C(unitInterval, X))) = 0
    rw [extGrid_zero σ hσ0]
    exact
      devVal_vertEdge_const_left x₀ form H (extGrid τ j.val) (extGrid τ (j.val + 1))
  have hLm : devLVal x₀ form H (extGrid σ) (extGrid τ) m j.val = 0 := by
    change developingValue x₀ form
      (((vertEdge H (extGrid σ m) (extGrid τ j.val) (extGrid τ (j.val + 1)) :
        Path ((H.eval (extGrid τ j.val)) (extGrid σ m))
          ((H.eval (extGrid τ (j.val + 1))) (extGrid σ m))) :
        C(unitInterval, X))) = 0
    rw [extGrid_last σ hσ1]
    exact
      devVal_vertEdge_const_right x₀ form H (extGrid τ j.val) (extGrid τ (j.val + 1))
  have hsub :
      (∑ i ∈ Finset.range m, devBVal x₀ form H (extGrid σ) (extGrid τ) i j.val) -
        (∑ i ∈ Finset.range m, devTVal x₀ form H (extGrid σ) (extGrid τ) i j.val) = 0 := by
    calc
      (∑ i ∈ Finset.range m, devBVal x₀ form H (extGrid σ) (extGrid τ) i j.val) -
          (∑ i ∈ Finset.range m, devTVal x₀ form H (extGrid σ) (extGrid τ) i j.val) =
          ∑ i ∈ Finset.range m,
            (devBVal x₀ form H (extGrid σ) (extGrid τ) i j.val -
              devTVal x₀ form H (extGrid σ) (extGrid τ) i j.val) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ i ∈ Finset.range m,
            (devLVal x₀ form H (extGrid σ) (extGrid τ) i j.val -
              devLVal x₀ form H (extGrid σ) (extGrid τ) (i + 1) j.val) := hsum
      _ = devLVal x₀ form H (extGrid σ) (extGrid τ) 0 j.val -
            devLVal x₀ form H (extGrid σ) (extGrid τ) m j.val := by
            simpa using
              (Finset.sum_range_sub'
                (fun i => devLVal x₀ form H (extGrid σ) (extGrid τ) i j.val) m)
      _ = 0 := by
            rw [hL0, hLm, sub_self]
  exact sub_eq_zero.mp hsub

lemma col_sum_eq {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (x₀ : X) (form : HolomorphicOneForm X)
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j)) :
    (∑ i ∈ Finset.range m, devBVal x₀ form H (extGrid σ) (extGrid τ) i 0) =
      ∑ i ∈ Finset.range m, devBVal x₀ form H (extGrid σ) (extGrid τ) i n := by
  classical
  let f : ℕ → ℂ := fun j =>
    ∑ i ∈ Finset.range m, devBVal x₀ form H (extGrid σ) (extGrid τ) i j
  have hstep : ∀ j : ℕ, j < n → f j = f (j + 1) := by
    intro j hj
    let jj : Fin n := ⟨j, hj⟩
    have hrow := row_sum_eq x₀ form H σ τ hσ0 hσ1 hσmono hτ0 hτ1 hτmono
      Bcell hcell jj
    simpa [f, devTVal, T_edge, devBVal, jj] using hrow
  have hsumzero : (∑ j ∈ Finset.range n, (f j - f (j + 1))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [hstep j (Finset.mem_range.mp hj), sub_self]
  have hsub : f 0 - f n = 0 := by
    calc
      f 0 - f n = ∑ j ∈ Finset.range n, (f j - f (j + 1)) := by
        simpa using (Finset.sum_range_sub' f n).symm
      _ = 0 := hsumzero
  exact sub_eq_zero.mp hsub

/-- The last cell index below the top edge of a positive vertical grid. -/
def lastCell (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩

private lemma lastCell_succ {n : ℕ} (hn : 0 < n) :
    (lastCell n hn).succ = Fin.last n := by
  ext
  simp [lastCell]
  omega

private noncomputable def bottomRowSubdivision {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (hτ0 : τ 0 = 0) (_hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (hn : 0 < n)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j)) :
    PathChartBallSubdivision ((γ₁ : Path a b) : C(unitInterval, X)) where
  n := m
  t := fun k : Fin (m + 1) => extGrid σ k.val
  cellBall := fun i : Fin m => Bcell i ⟨0, hn⟩
  zero_eq := extGrid_zero σ hσ0
  one_eq := extGrid_last σ hσ1
  monotone_t := extGrid_fin_monotone σ hσ0 hσ1 hσmono
  cell_subset := by
    intro i u hu
    rw [pathChartBallSet_eq_preimage_pointChartBallSet]
    change γ₁ u ∈ pointChartBallSet (Bcell i ⟨0, hn⟩)
    have hx : (u : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) := by
      constructor
      · calc
          σ i.castSucc = (extGrid σ i : ℝ) :=
            (extGrid_coe_castSucc σ hσ0 hσ1 hσmono i).symm
          _ ≤ (u : ℝ) := hu.1
      · calc
          (u : ℝ) ≤ (extGrid σ (i + 1) : ℝ) := hu.2
          _ = σ i.succ := extGrid_coe_succ σ hσ0 hσ1 hσmono i
    have hy : ((0 : unitInterval) : ℝ) ∈
        Set.Icc (τ (⟨0, hn⟩ : Fin n).castSucc) (τ (⟨0, hn⟩ : Fin n).succ) := by
      constructor
      · simp [hτ0]
      · calc
          (0 : ℝ) = τ 0 := hτ0.symm
          _ ≤ τ (⟨0, hn⟩ : Fin n).succ :=
            hτmono (Fin.zero_le _)
    have h := hcell i ⟨0, hn⟩ u hx 0 hy
    simp at h ⊢
    exact h

private noncomputable def topRowSubdivision {m n : ℕ} {a b : X} {γ₁ γ₂ : Path a b}
    (H : Path.Homotopy γ₁ γ₂) (σ : Fin (m + 1) → ℝ) (τ : Fin (n + 1) → ℝ)
    (hσ0 : σ 0 = 0) (hσ1 : σ (Fin.last m) = 1) (hσmono : Monotone σ)
    (_hτ0 : τ 0 = 0) (hτ1 : τ (Fin.last n) = 1) (hτmono : Monotone τ)
    (hn : 0 < n)
    (Bcell : Fin m → Fin n → PathChartBall X)
    (hcell : ∀ i : Fin m, ∀ j : Fin n,
      ∀ x : unitInterval, (x : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) →
      ∀ y : unitInterval, (y : ℝ) ∈ Set.Icc (τ j.castSucc) (τ j.succ) →
        (H.eval y) x ∈ pointChartBallSet (Bcell i j)) :
    PathChartBallSubdivision ((γ₂ : Path a b) : C(unitInterval, X)) where
  n := m
  t := fun k : Fin (m + 1) => extGrid σ k.val
  cellBall := fun i : Fin m => Bcell i (lastCell n hn)
  zero_eq := extGrid_zero σ hσ0
  one_eq := extGrid_last σ hσ1
  monotone_t := extGrid_fin_monotone σ hσ0 hσ1 hσmono
  cell_subset := by
    intro i u hu
    rw [pathChartBallSet_eq_preimage_pointChartBallSet]
    change γ₂ u ∈ pointChartBallSet (Bcell i (lastCell n hn))
    have hx : (u : ℝ) ∈ Set.Icc (σ i.castSucc) (σ i.succ) := by
      constructor
      · calc
          σ i.castSucc = (extGrid σ i : ℝ) :=
            (extGrid_coe_castSucc σ hσ0 hσ1 hσmono i).symm
          _ ≤ (u : ℝ) := hu.1
      · calc
          (u : ℝ) ≤ (extGrid σ (i + 1) : ℝ) := hu.2
          _ = σ i.succ := extGrid_coe_succ σ hσ0 hσ1 hσmono i
    have hy : ((1 : unitInterval) : ℝ) ∈
        Set.Icc (τ (lastCell n hn).castSucc) (τ (lastCell n hn).succ) := by
      constructor
      · calc
          τ (lastCell n hn).castSucc ≤ τ (Fin.last n) :=
            hτmono (Fin.le_last _)
          _ = 1 := hτ1
      · rw [lastCell_succ hn, hτ1]
        exact le_rfl
    have h := hcell i (lastCell n hn) u hx 1 hy
    simpa using h

end Jacobians.RiemannSurface
