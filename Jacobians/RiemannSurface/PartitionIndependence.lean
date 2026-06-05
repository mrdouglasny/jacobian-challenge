/-
Good-partition independence for the multi-chart integral along an analytic arc.
-/
import Jacobians.RiemannSurface.SegmentAdjacency
import Jacobians.RiemannSurface.SegmentCenterIndependence

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- A chart-subordinate partition whose open cells lie in analytic partition
gaps of the arc. -/
structure GoodPartition (γ : AnalyticArc X) extends ChartSubordinatePartition γ where
  gap : ∀ i : Fin n, ∃ s ∈ γ.partition, ∃ u ∈ γ.partition,
    s < u ∧ Set.Ioo (t i.castSucc) (t i.succ) ⊆ Set.Ioo s u ∧
      (∀ r ∈ γ.partition, r ∉ Set.Ioo s u)

namespace GoodPartition

/-- Good partitions exist by refining a chart-subordinate partition with the
analytic partition of the arc. -/
instance instNonempty (γ : AnalyticArc X) : Nonempty (GoodPartition γ) := by
  obtain ⟨n, tau, p, ht_zero, ht_last, ht_mono, hmem, hgap⟩ :=
    exists_good_partition γ
  exact ⟨
    { n := n
      t := tau
      p := p
      t_zero := ht_zero
      t_last := ht_last
      t_mono := ht_mono
      mem_source := hmem
      gap := hgap }⟩

end GoodPartition

/-- The ordinary-derivative integrand using the moving chart centered at
`γ.extend r`. -/
noncomputable def canonicalIntegrand (γ : AnalyticArc X)
    (form : HolomorphicOneForm X) : ℝ → ℂ :=
  fun r : ℝ =>
    form.coeff (γ.extend r)
        ((extChartAt 𝓘(ℂ) (γ.extend r)) (γ.extend r)) *
      deriv
        (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ.extend r)) (γ.extend u)) r

private lemma chartSubordinatePartition_t_mem_uIcc (γ : AnalyticArc X)
    (P : ChartSubordinatePartition γ) (j : Fin (P.n + 1)) :
    P.t j ∈ Set.uIcc (0 : ℝ) 1 := by
  refine Set.mem_uIcc_of_le ?_ ?_
  · have h0j : (0 : Fin (P.n + 1)) ≤ j := Fin.zero_le j
    have := P.t_mono h0j
    simpa [P.t_zero] using this
  · have hjlast : j ≤ Fin.last P.n := Fin.le_last j
    have := P.t_mono hjlast
    simpa [P.t_last] using this

private lemma chartSubordinatePartition_cell_intervalIntegrable
    (γ : AnalyticArc X) (P : ChartSubordinatePartition γ)
    (form : HolomorphicOneForm X)
    (hint : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume 0 1)
    (i : Fin P.n) :
    IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
      (P.t i.castSucc) (P.t i.succ) := by
  exact hint.mono_set (Set.uIcc_subset_uIcc
    (chartSubordinatePartition_t_mem_uIcc γ P i.castSucc)
    (chartSubordinatePartition_t_mem_uIcc γ P i.succ))

private lemma pathIntegralOnChartSeg_eq_canonicalIntegrand
    (γ : AnalyticArc X) (p : X) (a b : ℝ)
    (form : HolomorphicOneForm X) (hab : a ≤ b)
    {s t : ℝ} (hs : s ∈ γ.partition) (ht : t ∈ γ.partition)
    (hst : s < t) (hgap : Set.Ioo a b ⊆ Set.Ioo s t)
    (hgap_no : ∀ r ∈ γ.partition, r ∉ Set.Ioo s t)
    (hp : ∀ r ∈ Set.Ioo a b,
      γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source) :
    pathIntegralOnChartSeg γ p a b form =
      ∫ r in a..b, canonicalIntegrand γ form r := by
  let Fp : ℝ → ℂ := fun r =>
    form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
      deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r
  have h_deriv :
      pathIntegralOnChartSeg γ p a b form = ∫ r in a..b, Fp r := by
    simpa [Fp] using
      pathIntegralOnChartSeg_eq_deriv γ p a b form hab hs ht hst hgap hgap_no hp
  have h_congr :
      (∫ r in a..b, Fp r) =
        ∫ r in a..b, canonicalIntegrand γ form r := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_uIoc_iff]
    constructor
    · filter_upwards
        [Ioo_ae_eq_Ioc (a := a) (b := b) (μ := MeasureTheory.volume)]
        with r hr_eq hr
      have hro : r ∈ Set.Ioo a b := by
        change Set.Ioo a b r
        rw [hr_eq]
        exact hr
      have hdp : DifferentiableWithinAt ℝ
          (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u))
          (Set.Ioo a b) r :=
        have hrst : r ∈ Set.Ioo s t := hgap hro
        have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
          have hs01 := γ.partition_subset hs
          have ht01 := γ.partition_subset ht
          exact ⟨hs01.1.trans_lt hrst.1, hrst.2.trans_le ht01.2⟩
        have hr_notmem : r ∉ (γ.partition : Set ℝ) := by
          intro hrmem
          have hrmem' : r ∈ γ.partition := by
            simpa using hrmem
          exact (hgap_no r hrmem') hrst
        arc_chart_differentiableWithinAt γ p hr01 hr_notmem
          (hp r hro) (Set.Ioo a b)
      have hcenter := integrand_center_independent form γ p (γ.extend r)
        a b r (hp r hro) (mem_extChartAt_source (I := 𝓘(ℂ)) (γ.extend r))
        hdp hro
      simpa [Fp, canonicalIntegrand, derivWithin_of_isOpen isOpen_Ioo hro]
        using hcenter
    · filter_upwards with r hr
      have h_empty : Set.Ioc b a = (∅ : Set ℝ) :=
        Set.Ioc_eq_empty (not_lt_of_ge hab)
      rw [h_empty] at hr
      exact False.elim hr
  exact h_deriv.trans h_congr

private lemma pathIntegralOverGoodPartition_eq_canonicalIntegrand
    (γ : AnalyticArc X) (P : GoodPartition γ)
    (form : HolomorphicOneForm X)
    (hint : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume 0 1) :
    pathIntegralOverPartition γ P.toChartSubordinatePartition form =
      ∫ r in 0..1, canonicalIntegrand γ form r := by
  let Q : ChartSubordinatePartition γ := P.toChartSubordinatePartition
  have hcells : ∀ i : Fin Q.n,
      pathIntegralOnChartSeg γ (Q.p i) (Q.t i.castSucc) (Q.t i.succ) form =
        ∫ r in (Q.t i.castSucc)..(Q.t i.succ),
          canonicalIntegrand γ form r := by
    intro i
    rcases P.gap i with ⟨s, hs, t, ht, hst, hgap, hgap_no⟩
    have hab : Q.t i.castSucc ≤ Q.t i.succ :=
      Q.t_mono (Fin.castSucc_le_succ i)
    have hp : ∀ r ∈ Set.Ioo (Q.t i.castSucc) (Q.t i.succ),
        γ.extend r ∈ (extChartAt 𝓘(ℂ) (Q.p i)).source := by
      intro r hr
      have hrcc : r ∈ Set.Icc (Q.t i.castSucc) (Q.t i.succ) :=
        ⟨le_of_lt hr.1, le_of_lt hr.2⟩
      simpa [extChartAt_source] using Q.mem_source i r hrcc
    exact pathIntegralOnChartSeg_eq_canonicalIntegrand γ (Q.p i)
      (Q.t i.castSucc) (Q.t i.succ) form hab hs ht hst hgap hgap_no hp
  have hsum_cells :
      (∑ i : Fin Q.n,
          ∫ r in (Q.t i.castSucc)..(Q.t i.succ),
            canonicalIntegrand γ form r) =
        ∫ r in 0..1, canonicalIntegrand γ form r := by
    let a : ℕ → ℝ :=
      fun k => if h : k < Q.n + 1 then Q.t ⟨k, h⟩ else 0
    have hcell_hint : ∀ i : Fin Q.n,
        IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
          (Q.t i.castSucc) (Q.t i.succ) :=
      chartSubordinatePartition_cell_intervalIntegrable γ Q form hint
    have hsum :
        ∑ k ∈ Finset.range Q.n,
            ∫ r in (a k)..(a (k + 1)), canonicalIntegrand γ form r =
          ∫ r in (a 0)..(a Q.n), canonicalIntegrand γ form r := by
      refine intervalIntegral.sum_integral_adjacent_intervals
        (a := a) (n := Q.n) ?_
      intro k hk
      have hk0 : k ≤ Q.n := Nat.le_of_lt hk
      have hk1 : k < Q.n := hk
      simpa [a, hk0, hk1] using hcell_hint ⟨k, hk⟩
    have ha0 : a 0 = 0 := by
      simp [a, Q.t_zero]
    have haN : a Q.n = 1 := by
      have hfin :
          (⟨Q.n, Nat.lt_succ_self Q.n⟩ : Fin (Q.n + 1)) =
            Fin.last Q.n := by
        ext
        simp [Fin.last]
      calc
        a Q.n = Q.t ⟨Q.n, Nat.lt_succ_self Q.n⟩ := by simp [a]
        _ = Q.t (Fin.last Q.n) := by rw [hfin]
        _ = 1 := Q.t_last
    calc
      (∑ i : Fin Q.n,
          ∫ r in (Q.t i.castSucc)..(Q.t i.succ),
            canonicalIntegrand γ form r) =
          ∑ k ∈ Finset.range Q.n,
            ∫ r in (a k)..(a (k + 1)), canonicalIntegrand γ form r := by
        rw [Finset.sum_fin_eq_sum_range]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hklt : k < Q.n := by simpa using hk
        have hk0 : k ≤ Q.n := Nat.le_of_lt hklt
        have hk1 : k < Q.n := hklt
        simp [a, hk0, hk1]
      _ = ∫ r in 0..1, canonicalIntegrand γ form r := by
        simpa [ha0, haN] using hsum
  unfold pathIntegralOverPartition
  calc
    (∑ i : Fin Q.n,
        pathIntegralOnChartSeg γ (Q.p i)
          (Q.t i.castSucc) (Q.t i.succ) form) =
        ∑ i : Fin Q.n,
          ∫ r in (Q.t i.castSucc)..(Q.t i.succ),
            canonicalIntegrand γ form r := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hcells i
    _ = ∫ r in 0..1, canonicalIntegrand γ form r := hsum_cells

/-- The fixed-partition integral over a good partition is independent of the
chosen good partition.  The only analytic input retained as a hypothesis is
interval integrability of the moving-center ordinary-derivative integrand on
`[0, 1]`. -/
theorem pathIntegralOverPartition_good_indep (γ : AnalyticArc X)
    (P₁ P₂ : GoodPartition γ) (form : HolomorphicOneForm X)
    (hint : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume 0 1) :
    pathIntegralOverPartition γ P₁.toChartSubordinatePartition form =
      pathIntegralOverPartition γ P₂.toChartSubordinatePartition form := by
  rw [pathIntegralOverGoodPartition_eq_canonicalIntegrand γ P₁ form hint,
    pathIntegralOverGoodPartition_eq_canonicalIntegrand γ P₂ form hint]

end Jacobians.RiemannSurface
