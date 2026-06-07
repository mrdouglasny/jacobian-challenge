/-
Integral-level chart-center independence for a chart-local segment integral.
-/
import Jacobians.RiemannSurface.MultiChartIntegral
import Jacobians.RiemannSurface.IntegrandIndependence
import Jacobians.RiemannSurface.ArcChartDifferentiable

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The chart-local segment integral does not depend on the chart center, provided
the open segment lies in one analytic partition gap and the arc lies in both
chart sources there.

This proof uses the a.e./`uIoc` variant of the L1-c route.  When `a ≤ b`, the
pointwise integrand identity on `Set.Ioo a b` is upgraded to an a.e. identity on
`Set.uIoc a b`; the only missing point is the endpoint.  The reverse-orientation
case `b < a` is handled separately: then `Set.Ioo a b = ∅`, so both
`derivWithin` factors are zero. -/
theorem pathIntegralOnChartSeg_center_independent
    (γ : AnalyticArc X) (p q : X) (a b : ℝ) (form : HolomorphicOneForm X)
    {s t : ℝ} (hs : s ∈ γ.partition) (ht : t ∈ γ.partition) (hst : s < t)
    (hgap : Set.Ioo a b ⊆ Set.Ioo s t)
    (hgap_no : ∀ u ∈ γ.partition, u ∉ Set.Ioo s t)
    (hp : ∀ r ∈ Set.Ioo a b, γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source)
    (hq : ∀ r ∈ Set.Ioo a b, γ.extend r ∈ (extChartAt 𝓘(ℂ) q).source) :
    pathIntegralOnChartSeg γ p a b form = pathIntegralOnChartSeg γ q a b form := by
  have _hst : s < t := hst
  rcases le_or_gt a b with hab | hba
  · unfold pathIntegralOnChartSeg
    have h_pointwise : ∀ r ∈ Set.Ioo a b,
        form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
            derivWithin (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u))
              (Set.Ioo a b) r =
          form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
            derivWithin (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u))
              (Set.Ioo a b) r := by
      intro r hr
      have hdp : DifferentiableWithinAt ℝ
          (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) (Set.Ioo a b) r :=
        have hrst : r ∈ Set.Ioo s t := hgap hr
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
          (hp r hr) (Set.Ioo a b)
      exact integrand_center_independent form γ p q a b r
        (hp r hr) (hq r hr) hdp hr
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_uIoc_iff]
    constructor
    · filter_upwards
        [Ioo_ae_eq_Ioc (a := a) (b := b) (μ := MeasureTheory.volume)]
        with r hr_eq hr
      exact h_pointwise r (by
        change Set.Ioo a b r
        rw [hr_eq]
        exact hr)
    · filter_upwards with r hr
      have h_empty : Set.Ioc b a = (∅ : Set ℝ) :=
        Set.Ioc_eq_empty (not_lt_of_ge hab)
      rw [h_empty] at hr
      exact False.elim hr
  · unfold pathIntegralOnChartSeg
    have h_empty : Set.Ioo a b = (∅ : Set ℝ) :=
      Set.Ioo_eq_empty hba.not_gt
    simp [h_empty, derivWithin_zero_of_not_accPt, AccPt]

end Jacobians.RiemannSurface
