/-
Developing-map primitives for chart-local increments.
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Jacobians.RiemannSurface.HomotopyInvariance

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- B0: the coefficient of a holomorphic one-form has a primitive on any
coordinate ball contained in the fixed chart target. -/
theorem coeff_isExactOn_ball (form : HolomorphicOneForm X) (x₀ : X)
    {c : ℂ} {r : ℝ}
    (hball : Metric.ball c r ⊆ (extChartAt 𝓘(ℂ) x₀).target) :
    Complex.IsExactOn (form.coeff x₀) (Metric.ball c r) := by
  have hdiff : DifferentiableOn ℂ (form.coeff x₀) (Metric.ball c r) :=
    (form.2.1 x₀).differentiableOn.mono hball
  exact hdiff.isExactOn_ball

/-- B0, pointed form: choose the chart-local primitive with a prescribed value
at an arbitrary base coordinate. -/
theorem coeff_exists_primitive_on_ball_with_value
    (form : HolomorphicOneForm X) (x₀ : X) {c xbase y : ℂ} {r : ℝ}
    (hball : Metric.ball c r ⊆ (extChartAt 𝓘(ℂ) x₀).target) :
    ∃ g : ℂ → ℂ, g xbase = y ∧
      ∀ z ∈ Metric.ball c r, HasDerivAt g (form.coeff x₀ z) z :=
  (coeff_isExactOn_ball form x₀ hball).with_val_at xbase y

/-- B1: on a single chart and a ball carrying a primitive `g` of the coefficient,
the canonical arc integral is the endpoint difference of the primitive.

The chart-path regularity hypotheses are exactly the remaining FTC side
conditions used below: right derivatives on the open interval and interval
integrability of the fixed-chart integrand. Continuity of the primitive along
the path is derived from chart continuity and the derivative hypothesis on `g`. -/
theorem canonicalArcIntegral_eq_chartPrimitive_endpoint_sub
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) (x₀ : X)
    {c : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.extend t ∈ (extChartAt 𝓘(ℂ) x₀).source)
    (hpath_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (extChartAt 𝓘(ℂ) x₀) (γ.extend t) ∈ Metric.ball c r)
    (hprimitive : ∀ z ∈ Metric.ball c r, HasDerivAt g (form.coeff x₀ z) z)
    (hchart_hasDeriv_right : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u))
        (deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)) t)
        (Set.Ioi t) t)
    (hintegrable : IntervalIntegrable
      (fun t : ℝ =>
        form.coeff x₀ ((extChartAt 𝓘(ℂ) x₀) (γ.extend t)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)) t)
      MeasureTheory.volume (0 : ℝ) 1) :
    canonicalArcIntegral γ form =
      g ((extChartAt 𝓘(ℂ) x₀) (γ.extend 1)) -
        g ((extChartAt 𝓘(ℂ) x₀) (γ.extend 0)) := by
  let charted : ℝ → ℂ := fun u => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)
  let fixedIntegrand : ℝ → ℂ := fun t => form.coeff x₀ (charted t) * deriv charted t
  have hfixed :
      canonicalArcIntegral γ form = ∫ t in (0 : ℝ)..1, fixedIntegrand t := by
    simpa [charted, fixedIntegrand] using
      canonicalArcIntegral_eq_fixedChart_integral γ form x₀ hsource
  have hFTC :
      (∫ t in (0 : ℝ)..1, fixedIntegrand t) =
        (fun t : ℝ => g (charted t)) 1 - (fun t : ℝ => g (charted t)) 0 := by
    have hcharted_cont : ContinuousOn charted (Set.Icc (0 : ℝ) 1) := by
      simpa [charted] using
        (continuousOn_extChartAt (I := 𝓘(ℂ)) x₀).comp γ.continuous'.continuousOn
          hsource
    have hprimitivePath_cont : ContinuousOn (fun t : ℝ => g (charted t))
        (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact (hprimitive (charted t) (by simpa [charted] using hpath_ball t ht)).continuousAt
        |>.comp_continuousWithinAt (hcharted_cont t ht)
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      (f := fun t : ℝ => g (charted t)) (f' := fixedIntegrand)
      (show (0 : ℝ) ≤ 1 by norm_num) ?_ ?_ ?_
    · exact hprimitivePath_cont
    · intro t ht
      have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hprim : HasDerivAt g (form.coeff x₀ (charted t)) (charted t) :=
        hprimitive (charted t) (by simpa [charted] using hpath_ball t htcc)
      have hchart : HasDerivWithinAt charted (deriv charted t) (Set.Ioi t) t := by
        simpa [charted] using hchart_hasDeriv_right t ht
      have hcomp : HasDerivWithinAt (fun u : ℝ => g (charted u))
          (deriv charted t * form.coeff x₀ (charted t)) (Set.Ioi t) t := by
        simpa [Function.comp_def, smul_eq_mul] using
          hprim.scomp_hasDerivWithinAt (x := t) hchart
      simpa [fixedIntegrand, mul_comm] using hcomp
    · simpa [charted, fixedIntegrand] using hintegrable
  calc
    canonicalArcIntegral γ form = ∫ t in (0 : ℝ)..1, fixedIntegrand t := hfixed
    _ = (fun t : ℝ => g (charted t)) 1 - (fun t : ℝ => g (charted t)) 0 := hFTC
    _ = g ((extChartAt 𝓘(ℂ) x₀) (γ.extend 1)) -
        g ((extChartAt 𝓘(ℂ) x₀) (γ.extend 0)) := by
          rfl

end Jacobians.RiemannSurface
