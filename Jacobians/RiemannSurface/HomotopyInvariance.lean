/-
HI-0 bridge from the canonical moving-chart arc integral to a fixed chart
when the arc lies in one chart source.
-/
import Jacobians.RiemannSurface.CanonicalArcIntegral

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- If an analytic arc lies in a single chart source over `[0, 1]`, then the
canonical moving-center arc integral is the same integral written in that fixed
chart throughout. -/
theorem canonicalArcIntegral_eq_fixedChart_integral
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) (x₀ : X)
    (hsource : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      γ.extend r ∈ (extChartAt 𝓘(ℂ) x₀).source) :
    canonicalArcIntegral γ form =
      ∫ r in (0 : ℝ)..1,
        form.coeff x₀ ((extChartAt 𝓘(ℂ) x₀) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)) r := by
  unfold canonicalArcIntegral
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_uIoc_iff]
  constructor
  · filter_upwards
      [Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume),
        γ.partition.countable_toSet.ae_notMem MeasureTheory.volume]
      with r hr_eq hr_notmem hr
    have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
      change Set.Ioo (0 : ℝ) 1 r
      rw [hr_eq]
      exact hr
    have hfixed : γ.extend r ∈ (extChartAt 𝓘(ℂ) x₀).source :=
      hsource r ⟨le_of_lt hr01.1, le_of_lt hr01.2⟩
    have hmoving : γ.extend r ∈
        (extChartAt 𝓘(ℂ) (γ.extend r)).source :=
      mem_extChartAt_source (I := 𝓘(ℂ)) (γ.extend r)
    have hdiff : DifferentiableWithinAt ℝ
        (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ.extend r)) (γ.extend u))
        (Set.Ioo (0 : ℝ) 1) r :=
      arc_chart_differentiableWithinAt γ (γ.extend r) hr01 hr_notmem
        hmoving (Set.Ioo (0 : ℝ) 1)
    have hcenter := integrand_center_independent form γ (γ.extend r) x₀
      (0 : ℝ) 1 r hmoving hfixed hdiff hr01
    simpa [canonicalIntegrand, derivWithin_of_isOpen isOpen_Ioo hr01] using hcenter
  · filter_upwards with r hr
    have h_empty : Set.Ioc (1 : ℝ) 0 = (∅ : Set ℝ) :=
      Set.Ioc_eq_empty (not_lt_of_ge (zero_le_one : (0 : ℝ) ≤ 1))
    rw [h_empty] at hr
    exact False.elim hr

end Jacobians.RiemannSurface
