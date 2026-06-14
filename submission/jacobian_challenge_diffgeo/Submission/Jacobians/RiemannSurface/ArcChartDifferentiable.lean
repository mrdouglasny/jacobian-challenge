/-
Real differentiability of analytic arcs in any chart containing the point.
-/
import Submission.Jacobians.RiemannSurface.AnalyticArc
import Submission.Jacobians.RiemannSurface.IntegrandIndependence

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- An analytic arc is real-differentiable in any chart whose source contains the
point, at interior points of an analyticity partition interval. -/
theorem arc_chart_differentiableWithinAt (γ : AnalyticArc X) (p : X)
    {u : ℝ} (hu01 : u ∈ Set.Ioo (0 : ℝ) 1)
    (hunotmem : u ∉ (γ.partition : Set ℝ))
    (hp : γ.extend u ∈ (extChartAt 𝓘(ℂ) p).source) (S : Set ℝ) :
    DifferentiableWithinAt ℝ
      (fun r : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend r)) S u := by
  let q : X := γ.extend u
  let ψ : PartialEquiv X ℂ := extChartAt 𝓘(ℂ) q
  let φ : PartialEquiv X ℂ := extChartAt 𝓘(ℂ) p
  let g : ℝ → ℂ := fun r => ψ (γ.extend r)
  let T : ℂ → ℂ := φ ∘ ψ.symm
  have hq_source : γ.extend u ∈ ψ.source := by
    change γ.extend u ∈ (extChartAt 𝓘(ℂ) (γ.extend u)).source
    exact mem_extChartAt_source (γ.extend u)
  have hg_diff : DifferentiableAt ℝ g u := by
    simpa [q, ψ, g] using (γ.is_analytic u hu01 hunotmem).differentiableAt
  have hz : g u ∈ ψ.target := by
    simpa [g] using ψ.map_source hq_source
  have hsymm_z : ψ.symm (g u) = γ.extend u := by
    simpa [g] using ψ.left_inv hq_source
  have hsymm_source : ψ.symm (g u) ∈ φ.source := by
    rw [hsymm_z]
    simpa [φ] using hp
  have hT_diff_complex : DifferentiableAt ℂ T (g u) := by
    simpa [q, ψ, φ, T] using
      chartTransition_differentiableAt (p := q) (q := p) (z := g u) hz hsymm_source
  have hT_diff_real : DifferentiableAt ℝ T (g u) :=
    hT_diff_complex.restrictScalars ℝ
  have hcomp : DifferentiableAt ℝ (T ∘ g) u :=
    hT_diff_real.comp u hg_diff
  have hsource :
      ∀ᶠ r in 𝓝 u, γ.extend r ∈ ψ.source := by
    simpa [q, ψ] using
      γ.continuous'.continuousAt.eventually
        ((isOpen_extChartAt_source (I := 𝓘(ℂ)) q).mem_nhds
          (mem_extChartAt_source (I := 𝓘(ℂ)) q))
  have hlocal :
      (fun r : ℝ => φ (γ.extend r)) =ᶠ[𝓝 u] T ∘ g := by
    filter_upwards [hsource] with r hr
    have hr_chart : γ.extend r ∈ (chartAt ℂ q).source := by
      simpa [q, ψ, extChartAt_source] using hr
    change (chartAt ℂ p) (γ.extend r) =
      (chartAt ℂ p) ((chartAt ℂ q).symm ((chartAt ℂ q) (γ.extend r)))
    rw [(chartAt ℂ q).left_inv hr_chart]
  exact (hcomp.congr_of_eventuallyEq hlocal).differentiableWithinAt

end Jacobians.RiemannSurface
