import Jacobians.RiemannSurface.DevelopingMap

/-!
# Developing bridge

This file bridges the choice-based developing value to the canonical
moving-chart arc integral over an explicit chart-ball subdivision.

The analytic discharge intentionally remains explicit at the outer theorem:
the selected subdivision must avoid the analytic partition on each open cell,
and the fixed-chart integrands must be interval-integrable on the cells.
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

end Jacobians.RiemannSurface
