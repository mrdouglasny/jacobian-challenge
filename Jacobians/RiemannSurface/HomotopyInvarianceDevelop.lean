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
