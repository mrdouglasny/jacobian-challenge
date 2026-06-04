/-
Chart-subordinate partitions for analytic arcs.

This is the first subdivision lemma needed to globalize the chart-local
path-integral construction.  It is purely topological: continuity of the
arc and the chart-source open cover of the manifold suffice.
-/
import Jacobians.RiemannSurface.AnalyticArc

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Subdivide the unit interval so that each closed subinterval of an analytic arc
is contained in the source of a single chart.

The centers `p i` are chosen from the chart-source cover after applying the
Lebesgue-number partition lemma to the pullback cover on `unitInterval`. -/
theorem exists_chart_subordinate_partition (γ : AnalyticArc X) :
    ∃ (n : ℕ) (t : Fin (n + 1) → ℝ) (p : Fin n → X),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ i : Fin n, ∀ s ∈ Set.Icc (t i.castSucc) (t i.succ),
        γ.extend s ∈ (chartAt ℂ (p i)).source := by
  classical
  let c : X → Set unitInterval :=
    fun x => {u | γ.extend (u : ℝ) ∈ (chartAt ℂ x).source}
  have hc_open : ∀ x, IsOpen (c x) := by
    intro x
    exact (chartAt ℂ x).open_source.preimage
      (γ.continuous'.comp continuous_subtype_val)
  have hc_cover : Set.univ ⊆ ⋃ x, c x := by
    intro u _
    refine Set.mem_iUnion.2 ⟨γ.extend (u : ℝ), ?_⟩
    exact mem_chart_source ℂ (γ.extend (u : ℝ))
  obtain ⟨τ, hτ_zero, hτ_mono, ⟨m, hτ_eventually_one⟩, hτ_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (c := c) hc_open hc_cover
  refine ⟨m + 1, (fun i : Fin ((m + 1) + 1) => (τ i.val : ℝ)),
    (fun i : Fin (m + 1) => Classical.choose (hτ_sub i.val)), ?_, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hτ_zero
  · have hlast : τ (m + 1) = 1 := hτ_eventually_one (m + 1) (Nat.le_succ m)
    simpa [Fin.val_last] using congrArg Subtype.val hlast
  · intro i j hij
    exact (hτ_mono (Fin.val_le_of_le hij) : (τ i.val : ℝ) ≤ (τ j.val : ℝ))
  · intro i s hs
    have hleft : (τ i.val : ℝ) ≤ s := by
      simpa [Fin.val_castSucc] using hs.1
    have hright : s ≤ (τ (i.val + 1) : ℝ) := by
      simpa [Fin.val_succ] using hs.2
    let u : unitInterval := ⟨s, ⟨(τ i.val).2.1.trans hleft, hright.trans (τ (i.val + 1)).2.2⟩⟩
    have hu : u ∈ Set.Icc (τ i.val) (τ (i.val + 1)) := by
      constructor
      · exact hleft
      · exact hright
    exact Classical.choose_spec (hτ_sub i.val) hu

end Jacobians.RiemannSurface
