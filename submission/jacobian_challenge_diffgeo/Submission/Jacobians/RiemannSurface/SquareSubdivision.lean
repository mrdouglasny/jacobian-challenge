/-
Chart-subordinate square subdivisions for homotopies.

This is the two-dimensional analogue of the chart-subordinate interval
partition in `ChartPartition.lean`.  The proof pulls the chart-source cover
back to `unitInterval × unitInterval` and uses Mathlib's product version of
the Lebesgue-number subdivision lemma.  We then read the eventually-`1`
monotone sequence as a finite uniform grid in both coordinates.
-/
import Submission.Jacobians.RiemannSurface.AnalyticArc

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Subdivide the unit square so that every closed grid cell maps into the
source of a single chart.

The same finite `unitInterval` subdivision is used in both coordinates.  This
is enough for the rectangular-grid statement and keeps the proof close to
Mathlib's product interval-cover lemma. -/
theorem exists_chart_subordinate_grid
    (F : ℝ → ℝ → X) (hF : Continuous (fun z : ℝ × ℝ => F z.1 z.2)) :
    ∃ (m n : ℕ) (sigma : Fin (m + 1) → ℝ) (tau : Fin (n + 1) → ℝ)
      (p : Fin m → Fin n → X),
      sigma 0 = 0 ∧ sigma (Fin.last m) = 1 ∧ Monotone sigma ∧
      tau 0 = 0 ∧ tau (Fin.last n) = 1 ∧ Monotone tau ∧
      ∀ i : Fin m, ∀ j : Fin n,
        ∀ x ∈ Set.Icc (sigma i.castSucc) (sigma i.succ),
        ∀ y ∈ Set.Icc (tau j.castSucc) (tau j.succ),
          F x y ∈ (chartAt ℂ (p i j)).source := by
  classical
  let c : X → Set (unitInterval × unitInterval) :=
    fun q => {z | F (z.1 : ℝ) (z.2 : ℝ) ∈ (chartAt ℂ q).source}
  have hc_open : ∀ q, IsOpen (c q) := by
    intro q
    have hsub :
        Continuous (fun z : unitInterval × unitInterval => ((z.1 : ℝ), (z.2 : ℝ))) := by
      fun_prop
    exact (chartAt ℂ q).open_source.preimage (hF.comp hsub)
  have hc_cover : Set.univ ⊆ ⋃ q, c q := by
    intro z _hz
    refine Set.mem_iUnion.2 ⟨F (z.1 : ℝ) (z.2 : ℝ), ?_⟩
    exact mem_chart_source ℂ (F (z.1 : ℝ) (z.2 : ℝ))
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
    have hx_left : (t i.val : ℝ) ≤ x := by
      simpa [Fin.val_castSucc] using hx.1
    have hx_right : x ≤ (t (i.val + 1) : ℝ) := by
      simpa [Fin.val_succ] using hx.2
    have hy_left : (t j.val : ℝ) ≤ y := by
      simpa [Fin.val_castSucc] using hy.1
    have hy_right : y ≤ (t (j.val + 1) : ℝ) := by
      simpa [Fin.val_succ] using hy.2
    let u : unitInterval :=
      ⟨x, ⟨(t i.val).2.1.trans hx_left, hx_right.trans (t (i.val + 1)).2.2⟩⟩
    let v : unitInterval :=
      ⟨y, ⟨(t j.val).2.1.trans hy_left, hy_right.trans (t (j.val + 1)).2.2⟩⟩
    have hu : u ∈ Set.Icc (t i.val) (t (i.val + 1)) := by
      constructor
      · exact hx_left
      · exact hx_right
    have hv : v ∈ Set.Icc (t j.val) (t (j.val + 1)) := by
      constructor
      · exact hy_left
      · exact hy_right
    have huv :
        (u, v) ∈ Set.Icc (t i.val) (t (i.val + 1)) ×ˢ
          Set.Icc (t j.val) (t (j.val + 1)) := by
      exact ⟨hu, hv⟩
    exact Classical.choose_spec (ht_sub i.val j.val) huv

end Jacobians.RiemannSurface
