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

private lemma no_mem_between_orderEmb_succ (Pset : Finset ℝ) {m : ℕ}
    (hcard : Pset.card = m + 1) (i : Fin m) {x : ℝ}
    (hx : x ∈ Pset)
    (hbetween : Pset.orderEmbOfFin hcard i.castSucc < x ∧
      x < Pset.orderEmbOfFin hcard i.succ) : False := by
  have hxrange : x ∈ Set.range (Pset.orderEmbOfFin hcard) := by
    simpa [Finset.range_orderEmbOfFin Pset hcard] using hx
  rcases hxrange with ⟨j, rfl⟩
  have hleft : i.castSucc < j :=
    ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hbetween.1
  have hright : j < i.succ :=
    ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hbetween.2
  have hleft_nat : i.val < j.val := by
    simpa [Fin.lt_def, Fin.val_castSucc] using hleft
  have hright_nat : j.val < i.val + 1 := by
    simpa [Fin.lt_def, Fin.val_succ] using hright
  omega

private lemma exists_l0_cell_of_refined_cell {n0 m : ℕ}
    {t : Fin (n0 + 1) → ℝ} {Pset : Finset ℝ} (hzero : t 0 = 0)
    (hlast : t (Fin.last n0) = 1)
    (hPbase : ∀ j : Fin (n0 + 1), t j ∈ Pset)
    (hPsubset : ↑Pset ⊆ Set.Icc (0 : ℝ) 1)
    (hcard : Pset.card = m + 1) (i : Fin m) :
    ∃ j : Fin n0,
      Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
          (Pset.orderEmbOfFin hcard i.succ) ⊆
        Set.Icc (t j.castSucc) (t j.succ) := by
  classical
  let a : ℝ := Pset.orderEmbOfFin hcard i.castSucc
  let b : ℝ := Pset.orderEmbOfFin hcard i.succ
  have ha_mem : a ∈ Pset := by
    simp [a]
  have hb_mem : b ∈ Pset := by
    simp [b]
  have ha0 : 0 ≤ a := (hPsubset ha_mem).1
  have hb1 : b ≤ 1 := (hPsubset hb_mem).2
  have hab_idx : i.castSucc < i.succ := by
    simp [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  have hab : a < b := by
    exact (Pset.orderEmbOfFin hcard).strictMono hab_idx
  have hno_between : ∀ {x : ℝ}, x ∈ Pset → ¬ (a < x ∧ x < b) := by
    intro x hx hxbetween
    exact no_mem_between_orderEmb_succ Pset hcard i hx (by simpa [a, b] using hxbetween)
  let J : Finset (Fin (n0 + 1)) := Finset.univ.filter (fun k => t k ≤ a)
  have hJ_nonempty : J.Nonempty := by
    refine ⟨0, ?_⟩
    simp [J, hzero, ha0]
  let k : Fin (n0 + 1) := J.max' hJ_nonempty
  have hk_mem : k ∈ J := Finset.max'_mem J hJ_nonempty
  have hk_t_le : t k ≤ a := (Finset.mem_filter.mp hk_mem).2
  have hk_not_last : k ≠ Fin.last n0 := by
    intro hk_last
    have hk_eq_one : t k = 1 := by
      simpa [hk_last] using hlast
    have hone_le_a : (1 : ℝ) ≤ a := by
      simpa [hk_eq_one] using hk_t_le
    exact (lt_irrefl a) ((hab.trans_le hb1).trans_le hone_le_a)
  have hk_val_lt : k.val < n0 := by
    have hk_val_le : k.val ≤ n0 := by omega
    have hk_val_ne : k.val ≠ n0 := by
      intro hval
      apply hk_not_last
      exact Fin.ext hval
    omega
  let j : Fin n0 := ⟨k.val, hk_val_lt⟩
  have hjk : j.castSucc = k := by
    exact Fin.ext (by simp [j])
  have hleft : t j.castSucc ≤ a := by
    simpa [hjk] using hk_t_le
  have hright : b ≤ t j.succ := by
    by_contra hbnot
    have ht_succ_lt_b : t j.succ < b := lt_of_not_ge hbnot
    have hsucc_not_le_a : ¬ t j.succ ≤ a := by
      intro hsucc_le_a
      have hsucc_memJ : j.succ ∈ J := by
        simp [J, hsucc_le_a]
      have hsucc_le_k : j.succ ≤ k := Finset.le_max' J (j.succ) hsucc_memJ
      have hsucc_val_le : (j.succ).val ≤ k.val := Fin.val_le_of_le hsucc_le_k
      have hsucc_val_le' := hsucc_val_le
      simp [j] at hsucc_val_le'
    have ha_lt_tsucc : a < t j.succ := lt_of_not_ge hsucc_not_le_a
    exact hno_between (hPbase j.succ) ⟨ha_lt_tsucc, ht_succ_lt_b⟩
  refine ⟨j, ?_⟩
  intro u hu
  exact ⟨hleft.trans hu.1, hu.2.trans hright⟩

private lemma exists_partition_gap_of_refined_cell {m : ℕ} {part Pset : Finset ℝ}
    (hpart_subset : part ⊆ Pset) (hPsubset : ↑Pset ⊆ Set.Icc (0 : ℝ) 1)
    (hzero : (0 : ℝ) ∈ part) (hone : (1 : ℝ) ∈ part)
    (hcard : Pset.card = m + 1) (i : Fin m) :
    ∃ s ∈ part, ∃ t ∈ part,
      s < t ∧
        Set.Ioo (Pset.orderEmbOfFin hcard i.castSucc)
            (Pset.orderEmbOfFin hcard i.succ) ⊆ Set.Ioo s t ∧
        ∀ r ∈ part, r ∈ Set.Ioo s t → False := by
  classical
  let a : ℝ := Pset.orderEmbOfFin hcard i.castSucc
  let b : ℝ := Pset.orderEmbOfFin hcard i.succ
  have ha_mem : a ∈ Pset := by simp [a]
  have hb_mem : b ∈ Pset := by simp [b]
  have ha0 : 0 ≤ a := (hPsubset ha_mem).1
  have hb1 : b ≤ 1 := (hPsubset hb_mem).2
  have hab_idx : i.castSucc < i.succ := by
    simp [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  have hab : a < b := (Pset.orderEmbOfFin hcard).strictMono hab_idx
  have hno_between : ∀ {x : ℝ}, x ∈ Pset → ¬ (a < x ∧ x < b) := by
    intro x hx hxbetween
    exact no_mem_between_orderEmb_succ Pset hcard i hx (by simpa [a, b] using hxbetween)
  let left : Finset ℝ := part.filter (fun r => r ≤ a)
  have hleft_nonempty : left.Nonempty := by
    refine ⟨0, ?_⟩
    simp [left, hzero, ha0]
  let s : ℝ := left.max' hleft_nonempty
  have hs_mem_left : s ∈ left := Finset.max'_mem left hleft_nonempty
  have hs_part : s ∈ part := (Finset.mem_filter.mp hs_mem_left).1
  have hs_le_a : s ≤ a := (Finset.mem_filter.mp hs_mem_left).2
  let right : Finset ℝ := part.filter (fun r => b ≤ r)
  have hright_nonempty : right.Nonempty := by
    refine ⟨1, ?_⟩
    simp [right, hone, hb1]
  let t : ℝ := right.min' hright_nonempty
  have ht_mem_right : t ∈ right := Finset.min'_mem right hright_nonempty
  have ht_part : t ∈ part := (Finset.mem_filter.mp ht_mem_right).1
  have hb_le_t : b ≤ t := (Finset.mem_filter.mp ht_mem_right).2
  have hst : s < t := hs_le_a.trans_lt (hab.trans_le hb_le_t)
  refine ⟨s, hs_part, t, ht_part, hst, ?_, ?_⟩
  · intro u hu
    exact ⟨hs_le_a.trans_lt hu.1, hu.2.trans_le hb_le_t⟩
  · intro r hr_part hrst
    by_cases hra : r ≤ a
    · have hr_left : r ∈ left := by
        simp [left, hr_part, hra]
      have hr_le_s : r ≤ s := Finset.le_max' left r hr_left
      exact (not_lt_of_ge hr_le_s) hrst.1
    · have ha_lt_r : a < r := lt_of_not_ge hra
      by_cases hbr : b ≤ r
      · have hr_right : r ∈ right := by
          simp [right, hr_part, hbr]
        have ht_le_r : t ≤ r := Finset.min'_le right r hr_right
        exact (not_lt_of_ge ht_le_r) hrst.2
      · have hr_lt_b : r < b := lt_of_not_ge hbr
        exact hno_between (hpart_subset hr_part) ⟨ha_lt_r, hr_lt_b⟩

/-- Refine an L0 chart-subordinate partition by the analytic partition points.

The returned cells are still chart-subordinate, and each open cell is contained
in a single open gap between two adjacent points of `gamma.partition`.  Internally
the proof uses the sorted union of the L0 breakpoints and `gamma.partition`; for
the chosen `s < t`, the helper above also proves there is no partition point in
`Set.Ioo s t`. -/
theorem exists_good_partition (gamma : AnalyticArc X) :
    ∃ (n : Nat) (tau : Fin (n + 1) → ℝ) (p : Fin n → X),
      tau 0 = 0 ∧ tau (Fin.last n) = 1 ∧ Monotone tau ∧
      (∀ i : Fin n, ∀ u ∈ Set.Icc (tau i.castSucc) (tau i.succ),
        gamma.extend u ∈ (chartAt ℂ (p i)).source) ∧
      (∀ i : Fin n, ∃ s ∈ gamma.partition, ∃ t ∈ gamma.partition,
        s < t ∧ Set.Ioo (tau i.castSucc) (tau i.succ) ⊆ Set.Ioo s t) := by
  classical
  obtain ⟨n0, t0, p0, ht_zero, ht_last, ht_mono, hmem⟩ :=
    exists_chart_subordinate_partition gamma
  let base : Finset ℝ := Finset.image t0 Finset.univ
  let Pset : Finset ℝ := base ∪ gamma.partition
  have hbase_mem : ∀ j : Fin (n0 + 1), t0 j ∈ Pset := by
    intro j
    simp [Pset, base]
  have hpart_subset : gamma.partition ⊆ Pset := by
    intro x hx
    simp [Pset, hx]
  have hbase_subset : ↑base ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    constructor
    · have h0j : (0 : Fin (n0 + 1)) ≤ j := Fin.zero_le j
      have := ht_mono h0j
      simpa [ht_zero] using this
    · have hjlast : j ≤ Fin.last n0 := Fin.le_last j
      have := ht_mono hjlast
      simpa [ht_last] using this
  have hPsubset : ↑Pset ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxbase | hxpart
    · exact hbase_subset hxbase
    · exact gamma.partition_subset hxpart
  have hzeroP : (0 : ℝ) ∈ Pset := hpart_subset gamma.zero_mem
  have honeP : (1 : ℝ) ∈ Pset := hpart_subset gamma.one_mem
  have hP_nonempty : Pset.Nonempty := ⟨0, hzeroP⟩
  have hcard_pos : 0 < Pset.card := Finset.card_pos.mpr hP_nonempty
  let n : Nat := Pset.card - 1
  have hcard : Pset.card = n + 1 := by
    have hsucc := Nat.succ_pred_eq_of_pos hcard_pos
    simpa [n, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using hsucc.symm
  let tau : Fin (n + 1) → ℝ := fun i => Pset.orderEmbOfFin hcard i
  have hcell : ∀ i : Fin n,
      ∃ j : Fin n0,
        Set.Icc (tau i.castSucc) (tau i.succ) ⊆
          Set.Icc (t0 j.castSucc) (t0 j.succ) := by
    intro i
    simpa [tau] using
      exists_l0_cell_of_refined_cell (t := t0) ht_zero ht_last hbase_mem hPsubset
        hcard i
  let cell : Fin n → Fin n0 := fun i => Classical.choose (hcell i)
  let p : Fin n → X := fun i => p0 (cell i)
  refine ⟨n, tau, p, ?_, ?_, ?_, ?_, ?_⟩
  · change Pset.orderEmbOfFin hcard 0 = 0
    have hz : 0 < n + 1 := Nat.succ_pos n
    calc
      Pset.orderEmbOfFin hcard 0 =
          Pset.min' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
        simpa using Finset.orderEmbOfFin_zero (s := Pset) hcard hz
      _ = 0 := by
        exact (Finset.min'_eq_iff Pset _ 0).2
          ⟨hzeroP, fun x hx => (hPsubset hx).1⟩
  · change Pset.orderEmbOfFin hcard (Fin.last n) = 1
    have hz : 0 < n + 1 := Nat.succ_pos n
    calc
      Pset.orderEmbOfFin hcard (Fin.last n) =
          Pset.max' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
        simpa [Fin.last, Nat.succ_eq_add_one] using
          Finset.orderEmbOfFin_last (s := Pset) hcard hz
      _ = 1 := by
        exact (Finset.max'_eq_iff Pset _ 1).2
          ⟨honeP, fun x hx => (hPsubset hx).2⟩
  · exact (Pset.orderEmbOfFin hcard).monotone
  · intro i u hu
    have hsub : Set.Icc (tau i.castSucc) (tau i.succ) ⊆
        Set.Icc (t0 (cell i).castSucc) (t0 (cell i).succ) :=
      Classical.choose_spec (hcell i)
    exact hmem (cell i) u (hsub hu)
  · intro i
    rcases exists_partition_gap_of_refined_cell (part := gamma.partition) (Pset := Pset)
        hpart_subset hPsubset gamma.zero_mem gamma.one_mem hcard i with
      ⟨s, hs, t, ht, hst, hsub, _hconsecutive⟩
    exact ⟨s, hs, t, ht, hst, by simpa [tau] using hsub⟩

end Jacobians.RiemannSurface
