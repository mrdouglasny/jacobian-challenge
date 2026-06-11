/-
# The chart segment arc

For `Q` in the chart-ball neighbourhood `Bridge.chartBallSource P` of `P`, the
endpoint-flattened straight chart segment from `P` to `Q` packaged as an
`AnalyticArc`, together with its FTC evaluation: against any primitive `g` of
`form.coeff P` on the chart ball, its canonical arc integral is
`g (chart Q) - g (chart P)`.

This is the local geometric input of the B-3 period non-degeneracy engine
(`docs/planning/B3_NONDEG_ROUTE.md`); the construction mirrors
`Bridge.PathChartBallSubdivision.chartFlatPath` / `chartFlatAnalyticArc`,
de-coupled from a subdivision.
-/
import Jacobians.Bridge.BridgePathArc
import Jacobians.RiemannSurface.DevelopingMap

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.Bridge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- Membership in `chartBallSource P` puts the chart coordinate in the chosen
chart-target ball. -/
theorem coord_mem_ball_of_mem_chartBallSource {P Q : X}
    (hQ : Q ∈ chartBallSource P) :
    (chartAt ℂ P) Q ∈ Metric.ball ((chartAt ℂ P) P) (chartTargetBallRadius P) :=
  hQ.2

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The flattened chart segment from `P` toward `Q ∈ chartBallSource P` stays
in the chosen chart-target ball. -/
theorem chartSegment_flatSegment_mem_ball (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    flatSegment ((chartAt ℂ P) P) ((chartAt ℂ P) Q) t
      ∈ Metric.ball ((chartAt ℂ P) P) (chartTargetBallRadius P) :=
  segment_subset_ball (Metric.mem_ball_self (chartTargetBallRadius_pos P))
    (coord_mem_ball_of_mem_chartBallSource hQ) (flatSegment_mem_segment ht)

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The flattened chart segment stays in the chart target. -/
theorem chartSegment_flatSegment_mem_target (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    flatSegment ((chartAt ℂ P) P) ((chartAt ℂ P) Q) t ∈ (chartAt ℂ P).target :=
  chartTargetBall_subset_chart_target P
    (chartSegment_flatSegment_mem_ball P hQ ht)

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The chosen chart-target ball sits inside the `extChartAt` target (the
model is `𝓘(ℂ)`, so the extended target is the chart target). -/
theorem chartTargetBall_subset_extChartAt_target (x : X) :
    Metric.ball ((chartAt ℂ x) x) (chartTargetBallRadius x)
      ⊆ (extChartAt 𝓘(ℂ) x).target := by
  intro z hz
  rw [extChartAt_target]
  refine ⟨?_, by simp⟩
  simpa using chartTargetBall_subset_chart_target x hz

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The straight (endpoint-flattened) chart segment from `P` to a point `Q`
of its chart-ball neighbourhood, as a bundled path. -/
noncomputable def chartSegmentPath (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) : Path P Q where
  toFun s :=
    (chartAt ℂ P).symm (flatSegment ((chartAt ℂ P) P) ((chartAt ℂ P) Q) (s : ℝ))
  continuous_toFun := by
    have hflat : Continuous fun s : unitInterval =>
        flatSegment ((chartAt ℂ P) P) ((chartAt ℂ P) Q) (s : ℝ) :=
      (continuous_flatSegment _ _).comp continuous_subtype_val
    have htarget : ∀ s : unitInterval,
        flatSegment ((chartAt ℂ P) P) ((chartAt ℂ P) Q) (s : ℝ) ∈
          (chartAt ℂ P).target := fun s =>
      chartSegment_flatSegment_mem_target P hQ s.2
    exact (chartAt ℂ P).continuousOn_symm.comp_continuous hflat htarget
  source' := by
    simp [(chartAt ℂ P).left_inv (mem_chart_source ℂ P)]
  target' := by
    simpa using (chartAt ℂ P).left_inv hQ.1

omit [IsManifold 𝓘(ℂ) ω X] in
/-- On `[0, 1]`, the extended chart segment path is the chart pullback of the
flattened segment. -/
theorem chartSegmentPath_extend_eq (P : X) {Q : X} (hQ : Q ∈ chartBallSource P)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (chartSegmentPath P hQ).extend t =
      (chartAt ℂ P).symm
        (flatSegment ((chartAt ℂ P) P) ((chartAt ℂ P) Q) t) := by
  rw [Path.extend_apply _ ht]
  rfl

omit [IsManifold 𝓘(ℂ) ω X] in
/-- The chart segment path stays in the chart source. -/
theorem chartSegmentPath_extend_mem_chart_source (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (chartSegmentPath P hQ).extend t ∈ (chartAt ℂ P).source := by
  rw [chartSegmentPath_extend_eq P hQ ht]
  exact (chartAt ℂ P).map_target (chartSegment_flatSegment_mem_target P hQ ht)

omit [IsManifold 𝓘(ℂ) ω X] in
/-- In the chart at `P`, the chart segment path reads as the flattened
segment. -/
theorem chartSegmentPath_coord_eq (P : X) {Q : X} (hQ : Q ∈ chartBallSource P)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (chartAt ℂ P) ((chartSegmentPath P hQ).extend t) =
      flatSegment ((chartAt ℂ P) P) ((chartAt ℂ P) Q) t := by
  rw [chartSegmentPath_extend_eq P hQ ht]
  exact (chartAt ℂ P).right_inv (chartSegment_flatSegment_mem_target P hQ ht)

/-- The straight chart segment from `P` to `Q ∈ chartBallSource P`, packaged
as a (strongly) analytic arc with the trivial partition `{0, 1}`. -/
noncomputable def chartSegmentArc (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) : AnalyticArc X where
  extend := (chartSegmentPath P hQ).extend
  continuous' := Path.continuous_extend _
  partition := {0, 1}
  partition_subset := by
    intro r hr
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> simp
  zero_mem := by simp
  one_mem := by simp
  is_analytic_strong := by
    intro a ha b hb hab _hcons
    have ha01 : a = 0 ∨ a = 1 := by simpa using ha
    have hb01 : b = 0 ∨ b = 1 := by simpa using hb
    rcases ha01 with rfl | rfl
    · rcases hb01 with rfl | rfl
      · exact False.elim (lt_irrefl (0 : ℝ) hab)
      · refine ⟨{0, 1}, by simp, by simp, ?_, ?_⟩
        · intro r hr
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hr
          rcases hr with rfl | rfl <;> simp
        · intro s hs t ht hst _hτcons
          have hs01 : s = 0 ∨ s = 1 := by simpa using hs
          have ht01 : t = 0 ∨ t = 1 := by simpa using ht
          rcases hs01 with rfl | rfl
          · rcases ht01 with rfl | rfl
            · exact False.elim (lt_irrefl (0 : ℝ) hst)
            · refine ⟨P, Set.univ,
                flatSegment ((chartAt ℂ P) P) ((chartAt ℂ P) Q),
                isOpen_univ, ?_, ?_, ?_, ?_⟩
              · intro r _
                exact Set.mem_univ r
              · intro r _
                exact analyticAt_flatSegment _ _ r
              · intro r hr
                simpa [extChartAt_source] using
                  chartSegmentPath_extend_mem_chart_source P hQ hr.2
              · intro r hr
                rw [extChartAt_coe, modelWithCornersSelf_coe]
                simpa using chartSegmentPath_coord_eq P hQ hr.2
          · rcases ht01 with rfl | rfl
            · linarith
            · exact False.elim (lt_irrefl (1 : ℝ) hst)
    · rcases hb01 with rfl | rfl
      · linarith
      · exact False.elim (lt_irrefl (1 : ℝ) hab)

@[simp]
theorem chartSegmentArc_extend_zero (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) : (chartSegmentArc P hQ).extend 0 = P := by
  simp [chartSegmentArc]

@[simp]
theorem chartSegmentArc_extend_one (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) : (chartSegmentArc P hQ).extend 1 = Q := by
  simp [chartSegmentArc]

/-- The velocity of the flattened segment: `(6t - 6t²) • (b - a)`. -/
theorem hasDerivAt_flatSegment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a b : E) (t : ℝ) :
    HasDerivAt (flatSegment a b) ((6 * t - 6 * t ^ 2) • (b - a)) t := by
  have hf : HasDerivAt flatReparam (6 * t - 6 * t ^ 2) t :=
    hasDerivAt_flatReparam t
  have h1 : HasDerivAt (fun s : ℝ => 1 - flatReparam s)
      (-(6 * t - 6 * t ^ 2)) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).sub hf
  have hsum := (h1.smul_const a).add (hf.smul_const b)
  have hsum' : HasDerivAt (flatSegment a b)
      ((-(6 * t - 6 * t ^ 2)) • a + (6 * t - 6 * t ^ 2) • b) t := hsum
  have hval : (-(6 * t - 6 * t ^ 2)) • a + (6 * t - 6 * t ^ 2) • b =
      (6 * t - 6 * t ^ 2) • (b - a) := by
    rw [smul_sub, neg_smul]
    abel
  rw [hval] at hsum'
  exact hsum'

/-- The pointwise derivative of the flattened segment. -/
theorem deriv_flatSegment {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a b : E) (t : ℝ) :
    deriv (flatSegment a b) t = (6 * t - 6 * t ^ 2) • (b - a) :=
  (hasDerivAt_flatSegment a b t).deriv

/-- **Segment FTC.** Against any primitive `g` of `form.coeff P` on the
chosen chart-target ball at `P`, the canonical arc integral of the chart
segment from `P` to `Q` is the primitive increment between the chart
coordinates of the endpoints. -/
theorem canonicalArcIntegral_chartSegmentArc (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) (form : HolomorphicOneForm X) {g : ℂ → ℂ}
    (hg : ∀ z ∈ Metric.ball ((chartAt ℂ P) P) (chartTargetBallRadius P),
      HasDerivAt g (form.coeff P z) z) :
    canonicalArcIntegral (chartSegmentArc P hQ) form
      = g ((chartAt ℂ P) Q) - g ((chartAt ℂ P) P) := by
  set a : ℂ := (chartAt ℂ P) P with ha_def
  set b : ℂ := (chartAt ℂ P) Q with hb_def
  have hcoord : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend t) =
        flatSegment a b t := by
    intro t ht
    rw [extChartAt_coe, modelWithCornersSelf_coe]
    simpa using chartSegmentPath_coord_eq P hQ ht
  have hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (chartSegmentArc P hQ).extend t ∈ (extChartAt 𝓘(ℂ) P).source := by
    intro t ht
    simpa [extChartAt_source] using
      chartSegmentPath_extend_mem_chart_source P hQ ht
  have hball : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend t) ∈
        Metric.ball a (chartTargetBallRadius P) := by
    intro t ht
    rw [hcoord t ht]
    exact chartSegment_flatSegment_mem_ball P hQ ht
  -- the chart trace agrees with the flattened segment near interior points
  have heq_nhds : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (fun u : ℝ => (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend u))
        =ᶠ[𝓝 t] flatSegment a b := by
    intro t ht
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    exact hcoord u hu
  have hchart_right : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (fun u : ℝ => (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend u))
        (deriv
          (fun u : ℝ => (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend u)) t)
        (Set.Ioi t) t := by
    intro t ht
    have hflat : HasDerivAt (flatSegment a b)
        ((6 * t - 6 * t ^ 2) • (b - a)) t := hasDerivAt_flatSegment a b t
    have htrace : HasDerivAt
        (fun u : ℝ => (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend u))
        ((6 * t - 6 * t ^ 2) • (b - a)) t :=
      hflat.congr_of_eventuallyEq (heq_nhds t ht)
    rw [htrace.deriv]
    exact htrace.hasDerivWithinAt
  -- integrability of the fixed-chart integrand
  have hintegrable : IntervalIntegrable
      (fun t : ℝ =>
        form.coeff P ((extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend t)) *
          deriv
            (fun u : ℝ => (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend u)) t)
      MeasureTheory.volume (0 : ℝ) 1 := by
    set G : ℝ → ℂ := fun t =>
      form.coeff P (flatSegment a b t) * deriv (flatSegment a b) t with hG_def
    have hcoeff_cont : ContinuousOn (fun t : ℝ => form.coeff P (flatSegment a b t))
        (Set.Icc (0 : ℝ) 1) := by
      refine ((form.2.1 P).continuousOn.comp
        (continuous_flatSegment a b).continuousOn ?_)
      intro t ht
      exact chartTargetBall_subset_extChartAt_target P
        (chartSegment_flatSegment_mem_ball P hQ ht)
    have hderiv_cont : Continuous (deriv (flatSegment a b)) := by
      have : (deriv (flatSegment a b)) =
          fun t : ℝ => (6 * t - 6 * t ^ 2) • (b - a) := by
        funext t
        exact deriv_flatSegment a b t
      rw [this]
      fun_prop
    have hG_cont : ContinuousOn G (Set.Icc (0 : ℝ) 1) :=
      hcoeff_cont.mul hderiv_cont.continuousOn
    have hG_int : IntervalIntegrable G MeasureTheory.volume (0 : ℝ) 1 :=
      hG_cont.intervalIntegrable_of_Icc (by norm_num)
    refine hG_int.congr_ae ?_
    rw [Filter.EventuallyEq, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine MeasureTheory.ae_restrict_of_ae_eq_of_ae_restrict
      MeasureTheory.Ioo_ae_eq_Ioc ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun t ht => ?_
    have hticc : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self ht
    have hderiv_eq :
        deriv
          (fun u : ℝ => (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend u)) t =
          deriv (flatSegment a b) t :=
      Filter.EventuallyEq.deriv_eq (heq_nhds t ht)
    rw [hG_def]
    dsimp only
    rw [hcoord t hticc, hderiv_eq]
  have hmain := canonicalArcIntegral_eq_chartPrimitive_endpoint_sub
    (chartSegmentArc P hQ) form P hsource hball hg hchart_right hintegrable
  rw [hmain]
  have h1 : (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend 1) = b := by
    rw [chartSegmentArc_extend_one]
    rfl
  have h0 : (extChartAt 𝓘(ℂ) P) ((chartSegmentArc P hQ).extend 0) = a := by
    rw [chartSegmentArc_extend_zero]
    rfl
  rw [h1, h0]

end Jacobians.RiemannSurface
