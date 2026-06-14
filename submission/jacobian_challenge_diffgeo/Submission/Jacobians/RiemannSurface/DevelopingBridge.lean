import Submission.Jacobians.RiemannSurface.DevelopingMap

/-!
# Developing bridge

This file bridges the choice-based developing value to the canonical
moving-chart arc integral over an explicit chart-ball subdivision.

The explicit subdivision lemma keeps the analytic side conditions available for
reuse.  The public HI-0 bridge below discharges them from the strong analytic-arc
integrability lemmas: the selected subdivision avoids the analytic partition,
the canonical integrand is interval-integrable on `[0, 1]`, and the fixed-chart
cell integrands inherit interval integrability from the canonical integrand by
the cellwise chart-independence equality.
-/

noncomputable section

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Left endpoint of a chart-ball subdivision cell, as a real parameter. -/
def subdivisionCellLeft {γc : C(unitInterval, X)}
    (S : PathChartBallSubdivision γc) (i : Fin S.n) : ℝ :=
  (S.t i.castSucc : ℝ)

/-- Right endpoint of a chart-ball subdivision cell, as a real parameter. -/
def subdivisionCellRight {γc : C(unitInterval, X)}
    (S : PathChartBallSubdivision γc) (i : Fin S.n) : ℝ :=
  (S.t i.succ : ℝ)

/-- The ordinary-derivative fixed-chart integrand on a subdivision cell. -/
noncomputable def subdivisionFixedChartIntegrand
    (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (i : Fin S.n) : ℝ → ℂ :=
  fun r : ℝ =>
    form.coeff (S.cellBall i).p
        ((extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend r)) *
      deriv
        (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u)) r

/-- A subdivision avoids the analytic partition if no partition point lies in
the interior of any selected cell. -/
def PathChartBallSubdivisionAvoidsPartition (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ)) : Prop :=
  ∀ i : Fin S.n, ∀ r ∈
    Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
      r ∉ (γ.partition : Set ℝ)

private lemma bridge_no_mem_between_orderEmb_succ_unitInterval
    (Pset : Finset unitInterval) {m : ℕ}
    (hcard : Pset.card = m + 1) (i : Fin m) {x : unitInterval}
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

private lemma bridge_exists_subdivision_cell_of_refined_cell {γc : C(unitInterval, X)}
    (S : PathChartBallSubdivision γc) {m : ℕ} {Pset : Finset unitInterval}
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hcard : Pset.card = m + 1) (i : Fin m) :
    ∃ j : Fin S.n,
      Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
          (Pset.orderEmbOfFin hcard i.succ) ⊆
        Set.Icc (S.t j.castSucc) (S.t j.succ) := by
  classical
  let a : unitInterval := Pset.orderEmbOfFin hcard i.castSucc
  let b : unitInterval := Pset.orderEmbOfFin hcard i.succ
  have ha_mem : a ∈ Pset := by
    simp [a]
  have hb_mem : b ∈ Pset := by
    simp [b]
  have ha0 : (0 : unitInterval) ≤ a := by
    exact a.2.1
  have hb1 : b ≤ (1 : unitInterval) := by
    exact b.2.2
  have hab_idx : i.castSucc < i.succ := by
    simp [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  have hab : a < b :=
    (Pset.orderEmbOfFin hcard).strictMono hab_idx
  have hno_between : ∀ {x : unitInterval}, x ∈ Pset → ¬ (a < x ∧ x < b) := by
    intro x hx hxbetween
    exact bridge_no_mem_between_orderEmb_succ_unitInterval Pset hcard i hx
      (by simpa [a, b] using hxbetween)
  let J : Finset (Fin (S.n + 1)) := Finset.univ.filter (fun k => S.t k ≤ a)
  have hJ_nonempty : J.Nonempty := by
    refine ⟨0, ?_⟩
    simp [J, S.zero_eq, ha0]
  let k : Fin (S.n + 1) := J.max' hJ_nonempty
  have hk_mem : k ∈ J := Finset.max'_mem J hJ_nonempty
  have hk_t_le : S.t k ≤ a := (Finset.mem_filter.mp hk_mem).2
  have hk_not_last : k ≠ Fin.last S.n := by
    intro hk_last
    have hk_eq_one : S.t k = 1 := by
      simpa [hk_last] using S.one_eq
    have hone_le_a : (1 : unitInterval) ≤ a := by
      simpa [hk_eq_one] using hk_t_le
    exact (lt_irrefl a) ((hab.trans_le hb1).trans_le hone_le_a)
  have hk_val_lt : k.val < S.n := by
    have hk_val_le : k.val ≤ S.n := by omega
    have hk_val_ne : k.val ≠ S.n := by
      intro hval
      apply hk_not_last
      exact Fin.ext hval
    omega
  let j : Fin S.n := ⟨k.val, hk_val_lt⟩
  have hjk : j.castSucc = k := by
    exact Fin.ext (by simp [j])
  have hleft : S.t j.castSucc ≤ a := by
    simpa [hjk] using hk_t_le
  have hright : b ≤ S.t j.succ := by
    by_contra hbnot
    have ht_succ_lt_b : S.t j.succ < b := lt_of_not_ge hbnot
    have hsucc_not_le_a : ¬ S.t j.succ ≤ a := by
      intro hsucc_le_a
      have hsucc_memJ : j.succ ∈ J := by
        simp [J, hsucc_le_a]
      have hsucc_le_k : j.succ ≤ k := Finset.le_max' J (j.succ) hsucc_memJ
      have hsucc_val_le : (j.succ).val ≤ k.val := Fin.val_le_of_le hsucc_le_k
      have hsucc_val_le' := hsucc_val_le
      simp [j] at hsucc_val_le'
    have ha_lt_tsucc : a < S.t j.succ := lt_of_not_ge hsucc_not_le_a
    exact hno_between (hPbase j.succ) ⟨ha_lt_tsucc, ht_succ_lt_b⟩
  refine ⟨j, ?_⟩
  intro u hu
  exact ⟨hleft.trans hu.1, hu.2.trans hright⟩

private lemma bridge_orderEmb_zero_eq_of_mem {m : ℕ} {Pset : Finset unitInterval}
    (hcard : Pset.card = m + 1) (hzeroP : (0 : unitInterval) ∈ Pset) :
    Pset.orderEmbOfFin hcard 0 = 0 := by
  have hz : 0 < m + 1 := Nat.succ_pos m
  calc
    Pset.orderEmbOfFin hcard 0 =
        Pset.min' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
      simpa using Finset.orderEmbOfFin_zero (s := Pset) hcard hz
    _ = 0 := by
      exact (Finset.min'_eq_iff Pset _ 0).2
        ⟨hzeroP, fun x _hx => (show (0 : unitInterval) ≤ x from x.2.1)⟩

private lemma bridge_orderEmb_last_eq_of_mem {m : ℕ} {Pset : Finset unitInterval}
    (hcard : Pset.card = m + 1) (honeP : (1 : unitInterval) ∈ Pset) :
    Pset.orderEmbOfFin hcard (Fin.last m) = 1 := by
  have hz : 0 < m + 1 := Nat.succ_pos m
  calc
    Pset.orderEmbOfFin hcard (Fin.last m) =
        Pset.max' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
      simpa [Fin.last, Nat.succ_eq_add_one] using
        Finset.orderEmbOfFin_last (s := Pset) hcard hz
    _ = 1 := by
      exact (Finset.max'_eq_iff Pset _ 1).2
        ⟨honeP, fun x _hx => (show x ≤ (1 : unitInterval) from x.2.2)⟩

private noncomputable def bridgeSubdivisionRefinedByFinset {γc : C(unitInterval, X)}
    (S : PathChartBallSubdivision γc) (Pset : Finset unitInterval)
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hzeroP : (0 : unitInterval) ∈ Pset) (honeP : (1 : unitInterval) ∈ Pset)
    {m : ℕ} (hcard : Pset.card = m + 1) : PathChartBallSubdivision γc := by
  classical
  let cell : Fin m → Fin S.n := fun i =>
    Classical.choose (bridge_exists_subdivision_cell_of_refined_cell S hPbase hcard i)
  refine
    { n := m
      t := fun i : Fin (m + 1) => Pset.orderEmbOfFin hcard i
      cellBall := fun i : Fin m => S.cellBall (cell i)
      zero_eq := ?_
      one_eq := ?_
      monotone_t := ?_
      cell_subset := ?_ }
  · exact bridge_orderEmb_zero_eq_of_mem hcard hzeroP
  · exact bridge_orderEmb_last_eq_of_mem hcard honeP
  · exact (Pset.orderEmbOfFin hcard).monotone
  · intro i u hu
    have hsub : Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
          (Pset.orderEmbOfFin hcard i.succ) ⊆
        Set.Icc (S.t (cell i).castSucc) (S.t (cell i).succ) :=
      Classical.choose_spec (bridge_exists_subdivision_cell_of_refined_cell S hPbase hcard i)
    exact S.cell_subset (cell i) (hsub hu)

private noncomputable def analyticPartitionUnitInterval (γ : AnalyticArc X) :
    Finset unitInterval :=
  γ.partition.attach.image fun r => (⟨r.1, γ.partition_subset r.2⟩ : unitInterval)

private lemma analyticPartitionUnitInterval_mem (γ : AnalyticArc X) {r : ℝ}
    (hr : r ∈ γ.partition) :
    (⟨r, γ.partition_subset hr⟩ : unitInterval) ∈
      analyticPartitionUnitInterval γ := by
  classical
  refine Finset.mem_image.mpr ?_
  exact ⟨⟨r, hr⟩, by simp⟩

/-- Every analytic arc admits a chart-ball subdivision whose open cells avoid
the analytic partition.  Start with any chart-ball subdivision, then refine its
finite breakpoint set by adjoining the finitely many analytic partition points. -/
theorem exists_partition_avoiding_subdivision (γ : AnalyticArc X) :
    ∃ S : PathChartBallSubdivision (analyticArcToContinuousMap γ),
      PathChartBallSubdivisionAvoidsPartition γ S := by
  classical
  obtain ⟨S₀⟩ := exists_pathChartBallSubdivision (analyticArcToContinuousMap γ)
  let baseS : Finset unitInterval := Finset.image S₀.t Finset.univ
  let partP : Finset unitInterval := analyticPartitionUnitInterval γ
  let Pset : Finset unitInterval := baseS ∪ partP
  have hSbase : ∀ j : Fin (S₀.n + 1), S₀.t j ∈ Pset := by
    intro j
    simp [Pset, baseS]
  have hzeroP : (0 : unitInterval) ∈ Pset := by
    have h : S₀.t 0 ∈ Pset := hSbase 0
    simpa [S₀.zero_eq] using h
  have honeP : (1 : unitInterval) ∈ Pset := by
    have h : S₀.t (Fin.last S₀.n) ∈ Pset := hSbase (Fin.last S₀.n)
    simpa [S₀.one_eq] using h
  have hP_nonempty : Pset.Nonempty := ⟨0, hzeroP⟩
  have hcard_pos : 0 < Pset.card := Finset.card_pos.mpr hP_nonempty
  let m : ℕ := Pset.card - 1
  have hcard : Pset.card = m + 1 := by
    have hsucc := Nat.succ_pred_eq_of_pos hcard_pos
    simpa [m, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using hsucc.symm
  let S : PathChartBallSubdivision (analyticArcToContinuousMap γ) :=
    bridgeSubdivisionRefinedByFinset S₀ Pset hSbase hzeroP honeP hcard
  refine ⟨S, ?_⟩
  intro i r hr hrpart
  have hrpart_fin : r ∈ γ.partition := by
    simpa using hrpart
  let x : unitInterval := ⟨r, γ.partition_subset hrpart_fin⟩
  have hx_part : x ∈ partP := by
    simpa [x, partP] using analyticPartitionUnitInterval_mem γ hrpart_fin
  have hxP : x ∈ Pset := by
    simp [Pset, hx_part]
  have hbetween : Pset.orderEmbOfFin hcard i.castSucc < x ∧
      x < Pset.orderEmbOfFin hcard i.succ := by
    constructor
    · change ((Pset.orderEmbOfFin hcard i.castSucc : unitInterval) : ℝ) < (x : ℝ)
      simpa [S, bridgeSubdivisionRefinedByFinset, subdivisionCellLeft, x] using hr.1
    · change (x : ℝ) < ((Pset.orderEmbOfFin hcard i.succ : unitInterval) : ℝ)
      simpa [S, bridgeSubdivisionRefinedByFinset, subdivisionCellRight, x] using hr.2
  exact bridge_no_mem_between_orderEmb_succ_unitInterval Pset hcard i hxP hbetween

private lemma subdivisionCell_left_le_right {γc : C(unitInterval, X)}
    (S : PathChartBallSubdivision γc) (i : Fin S.n) :
    subdivisionCellLeft S i ≤ subdivisionCellRight S i := by
  exact S.monotone_t (Fin.castSucc_le_succ i)

private lemma subdivisionCell_mem_uIcc {γc : C(unitInterval, X)}
    (S : PathChartBallSubdivision γc) (j : Fin (S.n + 1)) :
    (S.t j : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
  exact Set.mem_uIcc_of_le (S.t j).2.1 (S.t j).2.2

private lemma subdivisionCell_source_of_mem_Icc
    (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (i : Fin S.n) {r : ℝ}
    (hr : r ∈ Set.Icc (subdivisionCellLeft S i) (subdivisionCellRight S i)) :
    γ.extend r ∈ (extChartAt 𝓘(ℂ) (S.cellBall i).p).source := by
  let u : unitInterval :=
    ⟨r, ⟨(S.t i.castSucc).2.1.trans hr.1, hr.2.trans (S.t i.succ).2.2⟩⟩
  have hu_cell : u ∈ Set.Icc (S.t i.castSucc) (S.t i.succ) := by
    constructor
    · exact hr.1
    · exact hr.2
  have hu := S.cell_subset i hu_cell
  simpa [u, analyticArcToContinuousMap_apply, extChartAt_source] using hu.1

private lemma subdivisionCell_coord_mem_ball_of_mem_Icc
    (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (i : Fin S.n) {r : ℝ}
    (hr : r ∈ Set.Icc (subdivisionCellLeft S i) (subdivisionCellRight S i)) :
    (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend r) ∈
      Metric.ball (S.cellBall i).c (S.cellBall i).r := by
  let u : unitInterval :=
    ⟨r, ⟨(S.t i.castSucc).2.1.trans hr.1, hr.2.trans (S.t i.succ).2.2⟩⟩
  have hu_cell : u ∈ Set.Icc (S.t i.castSucc) (S.t i.succ) := by
    constructor
    · exact hr.1
    · exact hr.2
  have hu := S.cell_subset i hu_cell
  simpa [u, analyticArcToContinuousMap_apply] using hu.2

private lemma subdivisionFixedChartIntegrand_eq_canonicalIntegrand_of_mem_Ioo
    (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (i : Fin S.n)
    (havoid : ∀ r ∈
      Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
        r ∉ (γ.partition : Set ℝ))
    {r : ℝ}
    (hr : r ∈ Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i)) :
    subdivisionFixedChartIntegrand form γ S i r =
      canonicalIntegrand γ form r := by
  have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨(S.t i.castSucc).2.1.trans_lt hr.1,
      hr.2.trans_le (S.t i.succ).2.2⟩
  have hp : γ.extend r ∈ (extChartAt 𝓘(ℂ) (S.cellBall i).p).source := by
    exact subdivisionCell_source_of_mem_Icc γ S i
      ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  have hdp : DifferentiableWithinAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u))
      (Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i)) r :=
    arc_chart_differentiableWithinAt γ (S.cellBall i).p
      hr01 (havoid r hr) hp
      (Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i))
  have hcenter := integrand_center_independent form γ (S.cellBall i).p
    (γ.extend r) (subdivisionCellLeft S i) (subdivisionCellRight S i) r
    hp (mem_extChartAt_source (I := 𝓘(ℂ)) (γ.extend r)) hdp hr
  simpa [subdivisionFixedChartIntegrand, canonicalIntegrand,
    derivWithin_of_isOpen isOpen_Ioo hr] using hcenter

private lemma subdivisionFixedChartIntegrand_eq_canonicalIntegrand_ae_of_cell
    (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (i : Fin S.n)
    (havoid : ∀ r ∈
      Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
        r ∉ (γ.partition : Set ℝ)) :
    subdivisionFixedChartIntegrand form γ S i
      =ᵐ[MeasureTheory.volume.restrict
        (Set.uIoc (subdivisionCellLeft S i) (subdivisionCellRight S i))]
      canonicalIntegrand γ form := by
  have hle : subdivisionCellLeft S i ≤ subdivisionCellRight S i :=
    subdivisionCell_left_le_right S i
  rw [Filter.EventuallyEq]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
  rw [MeasureTheory.ae_uIoc_iff]
  constructor
  · filter_upwards
      [Ioo_ae_eq_Ioc
        (a := subdivisionCellLeft S i) (b := subdivisionCellRight S i)
        (μ := MeasureTheory.volume)]
      with r hr_eq hr
    exact subdivisionFixedChartIntegrand_eq_canonicalIntegrand_of_mem_Ioo
      form γ S i havoid (by
        change Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i) r
        rw [hr_eq]
        exact hr)
  · filter_upwards with r hr
    have h_empty :
        Set.Ioc (subdivisionCellRight S i) (subdivisionCellLeft S i) =
          (∅ : Set ℝ) :=
      Set.Ioc_eq_empty (not_lt_of_ge hle)
    rw [h_empty] at hr
    exact False.elim hr

private lemma subdivisionFixedChartIntegrand_intervalIntegrable_of_cell
    (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (i : Fin S.n)
    (havoid : ∀ r ∈
      Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
        r ∉ (γ.partition : Set ℝ))
    (hcanonical_integrable : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume (0 : ℝ) 1) :
    IntervalIntegrable (subdivisionFixedChartIntegrand form γ S i)
      MeasureTheory.volume (subdivisionCellLeft S i)
        (subdivisionCellRight S i) := by
  have hcanonical_cell :
      IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
        (subdivisionCellLeft S i) (subdivisionCellRight S i) :=
    hcanonical_integrable.mono_set (Set.uIcc_subset_uIcc
      (subdivisionCell_mem_uIcc S i.castSucc)
      (subdivisionCell_mem_uIcc S i.succ))
  exact hcanonical_cell.congr_ae
    (subdivisionFixedChartIntegrand_eq_canonicalIntegrand_ae_of_cell
      form γ S i havoid).symm

/-- A chart-ball primitive endpoint increment equals the fixed-chart interval
integral over the same cell, assuming the right-derivative and integrability
side conditions needed by the interval FTC. -/
theorem developingIncrement_eq_fixedChart_intervalIntegral_of_hasDeriv_right
    (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (i : Fin S.n)
    (hchart_hasDeriv_right : ∀ r ∈
      Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
        HasDerivWithinAt
          (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u))
          (deriv
            (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u)) r)
          (Set.Ioi r) r)
    (hintegrable : IntervalIntegrable
      (subdivisionFixedChartIntegrand form γ S i) MeasureTheory.volume
      (subdivisionCellLeft S i) (subdivisionCellRight S i)) :
    developingIncrement form (analyticArcToContinuousMap γ) S i =
      ∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
        subdivisionFixedChartIntegrand form γ S i r := by
  let B : PathChartBall X := S.cellBall i
  let charted : ℝ → ℂ := fun r => (extChartAt 𝓘(ℂ) B.p) (γ.extend r)
  let fixedIntegrand : ℝ → ℂ :=
    fun r => form.coeff B.p (charted r) * deriv charted r
  let g : ℂ → ℂ := pathChartBallPrimitive form B
  have hab : subdivisionCellLeft S i ≤ subdivisionCellRight S i :=
    subdivisionCell_left_le_right S i
  have hcharted_cont : ContinuousOn charted
      (Set.Icc (subdivisionCellLeft S i) (subdivisionCellRight S i)) := by
    have hsource : ∀ r ∈
        Set.Icc (subdivisionCellLeft S i) (subdivisionCellRight S i),
        γ.extend r ∈ (extChartAt 𝓘(ℂ) B.p).source := by
      intro r hr
      simpa [B] using subdivisionCell_source_of_mem_Icc γ S i hr
    simpa [charted] using
      (continuousOn_extChartAt (I := 𝓘(ℂ)) B.p).comp
        γ.continuous'.continuousOn hsource
  have hprimitivePath_cont : ContinuousOn (fun r : ℝ => g (charted r))
      (Set.Icc (subdivisionCellLeft S i) (subdivisionCellRight S i)) := by
    intro r hr
    have hball : charted r ∈ Metric.ball B.c B.r := by
      simpa [charted, B] using subdivisionCell_coord_mem_ball_of_mem_Icc γ S i hr
    exact (pathChartBallPrimitive_hasDerivAt form B (charted r) hball).continuousAt
      |>.comp_continuousWithinAt (hcharted_cont r hr)
  have hFTC :
      (∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
          fixedIntegrand r) =
        (fun r : ℝ => g (charted r)) (subdivisionCellRight S i) -
          (fun r : ℝ => g (charted r)) (subdivisionCellLeft S i) := by
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      (f := fun r : ℝ => g (charted r)) (f' := fixedIntegrand) hab
      hprimitivePath_cont ?_ ?_
    · intro r hr
      have hrcc : r ∈
          Set.Icc (subdivisionCellLeft S i) (subdivisionCellRight S i) :=
        ⟨le_of_lt hr.1, le_of_lt hr.2⟩
      have hprim : HasDerivAt g (form.coeff B.p (charted r)) (charted r) := by
        have hball : charted r ∈ Metric.ball B.c B.r := by
          simpa [charted, B] using subdivisionCell_coord_mem_ball_of_mem_Icc γ S i hrcc
        exact pathChartBallPrimitive_hasDerivAt form B (charted r) hball
      have hchart : HasDerivWithinAt charted (deriv charted r) (Set.Ioi r) r := by
        simpa [charted, B] using hchart_hasDeriv_right r hr
      have hcomp : HasDerivWithinAt (fun u : ℝ => g (charted u))
          (deriv charted r * form.coeff B.p (charted r)) (Set.Ioi r) r := by
        simpa [Function.comp_def, smul_eq_mul] using
          hprim.scomp_hasDerivWithinAt (x := r) hchart
      simpa [fixedIntegrand, mul_comm] using hcomp
    · simpa [fixedIntegrand, charted, B, subdivisionFixedChartIntegrand] using
        hintegrable
  simpa [developingIncrement, analyticArcToContinuousMap_apply, B, charted,
    fixedIntegrand, g, subdivisionCellLeft, subdivisionCellRight,
    subdivisionFixedChartIntegrand] using hFTC.symm

/-- If a cell avoids the analytic partition, its fixed-chart ordinary-derivative
integral agrees with the moving-center canonical integrand integral on that
cell. -/
theorem fixedChart_intervalIntegral_eq_canonicalIntegrand_intervalIntegral_of_cell
    (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (i : Fin S.n)
    (havoid : ∀ r ∈
      Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
        r ∉ (γ.partition : Set ℝ)) :
    (∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
        subdivisionFixedChartIntegrand form γ S i r) =
      ∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
        canonicalIntegrand γ form r := by
  have hle : subdivisionCellLeft S i ≤ subdivisionCellRight S i :=
    subdivisionCell_left_le_right S i
  have hpointwise : ∀ r ∈
      Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
      subdivisionFixedChartIntegrand form γ S i r =
        canonicalIntegrand γ form r := by
    intro r hr
    exact subdivisionFixedChartIntegrand_eq_canonicalIntegrand_of_mem_Ioo
      form γ S i havoid hr
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_uIoc_iff]
  constructor
  · filter_upwards
      [Ioo_ae_eq_Ioc
        (a := subdivisionCellLeft S i) (b := subdivisionCellRight S i)
        (μ := MeasureTheory.volume)]
      with r hr_eq hr
    exact hpointwise r (by
      change Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i) r
      rw [hr_eq]
      exact hr)
  · filter_upwards with r hr
    have h_empty :
        Set.Ioc (subdivisionCellRight S i) (subdivisionCellLeft S i) =
          (∅ : Set ℝ) :=
      Set.Ioc_eq_empty (not_lt_of_ge hle)
    rw [h_empty] at hr
    exact False.elim hr

/-- The sum of canonical integrals over the cells of a subdivision telescopes to
the canonical integral over `[0, 1]`. -/
theorem sum_canonicalIntegrand_intervalIntegral_eq_canonicalArcIntegral
    (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (hintegrable : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume (0 : ℝ) 1) :
    (∑ i : Fin S.n,
        ∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
          canonicalIntegrand γ form r) =
      canonicalArcIntegral γ form := by
  let a : ℕ → ℝ :=
    fun k => if h : k < S.n + 1 then (S.t ⟨k, h⟩ : ℝ) else 0
  have hcell_hint : ∀ i : Fin S.n,
      IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
        (subdivisionCellLeft S i) (subdivisionCellRight S i) := by
    intro i
    exact hintegrable.mono_set (Set.uIcc_subset_uIcc
      (subdivisionCell_mem_uIcc S i.castSucc)
      (subdivisionCell_mem_uIcc S i.succ))
  have hsum :
      ∑ k ∈ Finset.range S.n,
          ∫ r in (a k)..(a (k + 1)), canonicalIntegrand γ form r =
        ∫ r in (a 0)..(a S.n), canonicalIntegrand γ form r := by
    refine intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (n := S.n) ?_
    intro k hk
    have hk_le : k ≤ S.n := Nat.le_of_lt hk
    simpa [a, subdivisionCellLeft, subdivisionCellRight, hk_le, hk]
      using hcell_hint ⟨k, hk⟩
  have ha0 : a 0 = 0 := by
    have h0 : 0 < S.n + 1 := Nat.succ_pos S.n
    simpa [a, h0] using congrArg Subtype.val S.zero_eq
  have haN : a S.n = 1 := by
    have hN : S.n < S.n + 1 := Nat.lt_succ_self S.n
    have hfin : (⟨S.n, hN⟩ : Fin (S.n + 1)) = Fin.last S.n := by
      ext
      simp [Fin.last]
    calc
      a S.n = (S.t ⟨S.n, hN⟩ : ℝ) := by simp [a]
      _ = (S.t (Fin.last S.n) : ℝ) := by rw [hfin]
      _ = 1 := by simpa using congrArg Subtype.val S.one_eq
  calc
    (∑ i : Fin S.n,
        ∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
          canonicalIntegrand γ form r) =
        ∑ k ∈ Finset.range S.n,
          ∫ r in (a k)..(a (k + 1)), canonicalIntegrand γ form r := by
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hklt : k < S.n := by simpa using hk
      have hk_le : k ≤ S.n := Nat.le_of_lt hklt
      simp [a, subdivisionCellLeft, subdivisionCellRight, hklt, hk_le]
    _ = ∫ r in (0 : ℝ)..1, canonicalIntegrand γ form r := by
      simpa [ha0, haN] using hsum
    _ = canonicalArcIntegral γ form := by
      rfl

/-- Bridge over an explicit subdivision, with the local fixed-chart FTC and the
fixed-to-canonical cell comparison supplied by the preceding lemmas. -/
theorem developingValue_analyticArcToContinuousMap_eq_canonicalArcIntegral_of_subdivision
    (x₀ : X) (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (hchart_hasDeriv_right : ∀ i : Fin S.n, ∀ r ∈
      Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
        HasDerivWithinAt
          (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u))
          (deriv
            (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u)) r)
          (Set.Ioi r) r)
    (hfixed_integrable : ∀ i : Fin S.n,
      IntervalIntegrable (subdivisionFixedChartIntegrand form γ S i)
        MeasureTheory.volume (subdivisionCellLeft S i) (subdivisionCellRight S i))
    (havoid : PathChartBallSubdivisionAvoidsPartition γ S)
    (hcanonical_integrable : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume (0 : ℝ) 1) :
    developingValue x₀ form (analyticArcToContinuousMap γ) =
      canonicalArcIntegral γ form := by
  have hcell : ∀ i : Fin S.n,
      developingIncrement form (analyticArcToContinuousMap γ) S i =
        ∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
          canonicalIntegrand γ form r := by
    intro i
    calc
      developingIncrement form (analyticArcToContinuousMap γ) S i =
          ∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
            subdivisionFixedChartIntegrand form γ S i r :=
        developingIncrement_eq_fixedChart_intervalIntegral_of_hasDeriv_right
          form γ S i (hchart_hasDeriv_right i) (hfixed_integrable i)
      _ = ∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
            canonicalIntegrand γ form r :=
        fixedChart_intervalIntegral_eq_canonicalIntegrand_intervalIntegral_of_cell
          form γ S i (havoid i)
  calc
    developingValue x₀ form (analyticArcToContinuousMap γ) =
        developingValueOfSubdivision form (analyticArcToContinuousMap γ) S :=
      developingValue_eq_developingValueOfSubdivision x₀ form
        (analyticArcToContinuousMap γ) S
    _ = ∑ i : Fin S.n,
        ∫ r in (subdivisionCellLeft S i)..(subdivisionCellRight S i),
          canonicalIntegrand γ form r := by
      unfold developingValueOfSubdivision
      exact Finset.sum_congr rfl (fun i _ => hcell i)
    _ = canonicalArcIntegral γ form :=
      sum_canonicalIntegrand_intervalIntegral_eq_canonicalArcIntegral
        form γ S hcanonical_integrable

/-- Avoiding the analytic partition gives the per-cell right-derivative
hypothesis needed by the fixed-chart FTC lemma. -/
theorem pathChartBallSubdivision_hasDeriv_right_of_partition_avoiding
    (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (havoid : PathChartBallSubdivisionAvoidsPartition γ S) :
    ∀ i : Fin S.n, ∀ r ∈
      Set.Ioo (subdivisionCellLeft S i) (subdivisionCellRight S i),
        HasDerivWithinAt
          (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u))
          (deriv
            (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u)) r)
          (Set.Ioi r) r := by
  intro i r hr
  have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
    exact ⟨(S.t i.castSucc).2.1.trans_lt hr.1,
      hr.2.trans_le (S.t i.succ).2.2⟩
  have hp : γ.extend r ∈ (extChartAt 𝓘(ℂ) (S.cellBall i).p).source := by
    exact subdivisionCell_source_of_mem_Icc γ S i
      ⟨le_of_lt hr.1, le_of_lt hr.2⟩
  have hdiffWithin : DifferentiableWithinAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u))
      Set.univ r :=
    arc_chart_differentiableWithinAt γ (S.cellBall i).p
      hr01 (havoid i r hr) hp Set.univ
  have hdiffAt : DifferentiableAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ.extend u)) r := by
    simpa [differentiableWithinAt_univ] using hdiffWithin
  exact hdiffAt.hasDerivAt.hasDerivWithinAt

/-- Main HI-0 bridge under the explicit discharge hypotheses: an avoiding
chart-ball subdivision and per-cell integrability of the fixed-chart
integrands. -/
theorem developingValue_eq_canonicalArcIntegral_of_partition_avoiding_subdivision
    (x₀ : X) (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (S : PathChartBallSubdivision (analyticArcToContinuousMap γ))
    (havoid : PathChartBallSubdivisionAvoidsPartition γ S)
    (hfixed_integrable : ∀ i : Fin S.n,
      IntervalIntegrable (subdivisionFixedChartIntegrand form γ S i)
        MeasureTheory.volume (subdivisionCellLeft S i) (subdivisionCellRight S i))
    (hcanonical_integrable : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume (0 : ℝ) 1) :
    developingValue x₀ form (analyticArcToContinuousMap γ) =
      canonicalArcIntegral γ form :=
  developingValue_analyticArcToContinuousMap_eq_canonicalArcIntegral_of_subdivision
    x₀ form γ S
    (pathChartBallSubdivision_hasDeriv_right_of_partition_avoiding γ S havoid)
    hfixed_integrable havoid hcanonical_integrable

/-- HI-0 bridge: for every analytic arc, the choice-based developing value agrees
with the canonical moving-chart arc integral.  The avoiding subdivision and both
integrability hypotheses are discharged internally. -/
theorem developingValue_eq_canonicalArcIntegral
    (x₀ : X) (form : HolomorphicOneForm X) (γ : AnalyticArc X) :
    developingValue x₀ form (analyticArcToContinuousMap γ) =
      canonicalArcIntegral γ form := by
  obtain ⟨S, havoid⟩ := exists_partition_avoiding_subdivision γ
  have hcanonical_integrable :
      IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
        (0 : ℝ) 1 :=
    analyticArc_canonicalIntegrand_intervalIntegrable γ form
  have hfixed_integrable : ∀ i : Fin S.n,
      IntervalIntegrable (subdivisionFixedChartIntegrand form γ S i)
        MeasureTheory.volume (subdivisionCellLeft S i)
          (subdivisionCellRight S i) := by
    intro i
    exact subdivisionFixedChartIntegrand_intervalIntegrable_of_cell
      form γ S i (havoid i) hcanonical_integrable
  exact developingValue_eq_canonicalArcIntegral_of_partition_avoiding_subdivision
    x₀ form γ S havoid hfixed_integrable hcanonical_integrable

end Jacobians.RiemannSurface
