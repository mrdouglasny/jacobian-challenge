/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- Implementation: independent Codex (GPT-5.4) pass, 2026-06-12, maintainer-validated;
-- mirrors the closed-loop proof at Bridge/KirovDolbeaultPeriods.lean (cell-FTC subdivision).

import Submission.Jacobians.Bridge.KirovDolbeaultPeriods

/-!
# Open-path developing value vs Kirov-Dolbeault line integral

This is the open-path analogue of
`Jacobians.Bridge.developingValue_eq_lineIntegral_of_isClosedSmoothLoop`.
The proof is the same chart-ball subdivision argument, but uses the endpoints
carried by `IsSmoothPath` instead of closing the restricted path into a loop.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory

namespace Jacobians.Bridge

open Jacobians.RiemannSurface

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The continuous-map restriction of an open smooth path `γ : ℝ → Y` to the
unit interval. -/
def smoothPathToContinuousMap (γ : ℝ → Y) (hγ : Continuous γ) : C(unitInterval, Y) :=
  ⟨fun u => γ (u : ℝ), hγ.comp continuous_subtype_val⟩

/-- The `Path` view of an open smooth path. -/
def smoothPathToPath {x y : Y} (γ : ℝ → Y)
    (hγ : _root_.Jacobians.IsSmoothPath x y γ) : Path x y where
  toFun u := γ (u : ℝ)
  continuous_toFun := hγ.cont.comp continuous_subtype_val
  source' := by simpa using hγ.start
  target' := by simpa using hγ.finish

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] in
@[simp] theorem smoothPathToPath_coe {x y : Y} (γ : ℝ → Y)
    (hγ : _root_.Jacobians.IsSmoothPath x y γ) :
    ((smoothPathToPath γ hγ : Path x y) : C(unitInterval, Y)) =
      smoothPathToContinuousMap γ hγ.cont := rfl

/-- **Developing value = moving-chart line integral** for an open `C¹` path
(the port's `IsSmoothPath`): subdivide by chart balls, apply the cell FTC on
each cell, and compare with the developing increments. -/
theorem developingValue_eq_lineIntegral_of_isSmoothPath
    (form : HolomorphicOneForm Y) {x y : Y} (γ : ℝ → Y)
    (hγ : _root_.Jacobians.IsSmoothPath x y γ) (x₀ : Y) :
    developingValue x₀ form
        ((smoothPathToPath γ hγ : Path x y) : C(unitInterval, Y)) =
      Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form) γ := by
  classical
  set γc : C(unitInterval, Y) := smoothPathToContinuousMap γ hγ.cont with hγc_def
  set S := chosenPathChartBallSubdivision γc with hS_def
  set f : ℝ → ℂ := fun t =>
    (bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t) with hf_def
  -- Global integrability of the moving-chart integrand from `velCont`.
  have hint01 : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    have h := _root_.Jacobians.intervalIntegrable_form_pathSpeed_of_velContinuous
      (bridgeKDFormEquiv form) γ hγ.velCont
    exact h
  -- The subdivision points as a real-valued sequence.
  set A : ℕ → ℝ := fun k => (S.t ⟨min k S.n, by omega⟩ : ℝ) with hA_def
  have hA_mono : ∀ j k, j ≤ k → A j ≤ A k := by
    intro j k hjk
    exact S.monotone_t (by simp [Fin.le_def]; omega)
  have hA_mem : ∀ k, A k ∈ Set.Icc (0 : ℝ) 1 := fun k => (S.t _).2
  have hA0 : A 0 = 0 := by
    have : (⟨min 0 S.n, by omega⟩ : Fin (S.n + 1)) = 0 := by
      ext; simp
    rw [hA_def]
    simp only [this, S.zero_eq]
    rfl
  have hAn : A S.n = 1 := by
    have : (⟨min S.n S.n, by omega⟩ : Fin (S.n + 1)) = Fin.last S.n := by
      ext; simp
    rw [hA_def]
    simp only [this, S.one_eq]
    rfl
  -- Cell-wise integrability.
  have hint_cell :
      ∀ k < S.n, IntervalIntegrable f MeasureTheory.volume (A k) (A (k + 1)) := by
    intro k hk
    refine hint01.mono_set ?_
    rw [Set.uIcc_of_le (hA_mono k (k + 1) (by omega)), Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc (hA_mem k).1 (hA_mem (k + 1)).2
  -- Per-cell FTC.
  have hcell : ∀ i : Fin S.n,
      (∫ t in A i.val..A (i.val + 1), f t) = developingIncrement form γc S i := by
    intro i
    have h1 : (⟨min i.val S.n, by omega⟩ : Fin (S.n + 1)) = i.castSucc := by
      ext
      simp
    have h2 : (⟨min (i.val + 1) S.n, by omega⟩ : Fin (S.n + 1)) = i.succ := by
      ext
      simp
    have hAi : A i.val = (S.t i.castSucc : ℝ) := by
      simp only [hA_def, h1]
    have hAi1 : A (i.val + 1) = (S.t i.succ : ℝ) := by
      simp only [hA_def, h2]
    set a : ℝ := (S.t i.castSucc : ℝ)
    set b : ℝ := (S.t i.succ : ℝ)
    have hab : a ≤ b := S.monotone_t (Fin.castSucc_le_succ i)
    have h01 : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc (S.t i.castSucc).2.1 (S.t i.succ).2.2
    have hmem : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt ℂ (S.cellBall i).p).source ∧
        (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ t) ∈
          Metric.ball (S.cellBall i).c (S.cellBall i).r := by
      intro t ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := h01 ht
      set u : unitInterval := ⟨t, ht01⟩ with hu_def
      have hu_cell : u ∈ Set.Icc (S.t i.castSucc) (S.t i.succ) := by
        constructor
        · exact Subtype.coe_le_coe.mp ht.1
        · exact Subtype.coe_le_coe.mp ht.2
      have huB := S.cell_subset i hu_cell
      exact huB
    have hdiff : ∀ t ∈ Set.Icc a b,
        DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t := by
      intro t ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := h01 ht
      exact hγ.diff t (by rwa [Set.uIcc_of_le zero_le_one])
    have hintab : IntervalIntegrable f MeasureTheory.volume a b := by
      have := hint_cell i.val i.isLt
      rwa [hAi, hAi1] at this
    have hFTC := lineIntegral_cell_eq_primitive_sub form (S.cellBall i) γ hab
      hγ.cont hdiff hmem hintab
    rw [hAi, hAi1]
    rw [hFTC]
    rfl
  -- Assemble: developing value = sum of increments = sum of cell integrals
  -- = the full line integral.
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := MeasureTheory.volume) (a := A) (f := f) hint_cell
  calc developingValue x₀ form ((smoothPathToPath γ hγ : Path x y) : C(unitInterval, Y))
      = developingValue x₀ form γc := by
        rw [smoothPathToPath_coe, hγc_def]
    _ = developingValueOfSubdivision form γc S :=
        developingValue_eq_developingValueOfSubdivision x₀ form γc S
    _ = ∑ i : Fin S.n, developingIncrement form γc S i := rfl
    _ = ∑ i : Fin S.n, ∫ t in A i.val..A (i.val + 1), f t := by
        refine Finset.sum_congr rfl (fun i _ => (hcell i).symm)
    _ = ∑ k ∈ Finset.range S.n, ∫ t in A k..A (k + 1), f t :=
        Fin.sum_univ_eq_sum_range (fun k => ∫ t in A k..A (k + 1), f t) S.n
    _ = ∫ t in A 0..A S.n, f t := hsum
    _ = ∫ t in (0 : ℝ)..1, f t := by rw [hA0, hAn]
    _ = Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form) γ := rfl

/-- Port-facing form of the open-path comparison. -/
theorem developingValue_eq_port_lineIntegral_of_isSmoothPath
    (form : HolomorphicOneForm Y) {x y : Y} (γ : ℝ → Y)
    (hγ : _root_.Jacobians.IsSmoothPath x y γ) (x₀ : Y) :
    developingValue x₀ form
        ((smoothPathToPath γ hγ : Path x y) : C(unitInterval, Y)) =
      _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) γ := by
  rw [port_lineIntegral_bridgeKD]
  exact developingValue_eq_lineIntegral_of_isSmoothPath form γ hγ x₀

end Jacobians.Bridge
