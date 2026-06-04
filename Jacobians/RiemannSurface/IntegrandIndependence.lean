/-
Chart-center independence for the chart-local integrand of a holomorphic
one-form along an analytic arc.
-/
import Jacobians.RiemannSurface.MultiChartIntegral
import Jacobians.RiemannSurface.OneForm

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- Chart transitions between two `extChartAt` charts are complex differentiable at
points of the overlap. -/
private lemma chartTransition_differentiableAt {p q : X} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) p).target)
    (hq : (extChartAt 𝓘(ℂ) p).symm z ∈ (extChartAt 𝓘(ℂ) q).source) :
    DifferentiableAt ℂ ((extChartAt 𝓘(ℂ) q) ∘ (extChartAt 𝓘(ℂ) p).symm) z := by
  have hsymm_mdiff_within : MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ)
      (extChartAt 𝓘(ℂ) p).symm (Set.range (𝓘(ℂ))) z := by
    simpa using mdifferentiableWithinAt_extChartAt_symm hz
  have hsymm_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (extChartAt 𝓘(ℂ) p).symm z := by
    have hrange : (Set.range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
      ModelWithCorners.range_eq_univ _
    rw [← mdifferentiableWithinAt_univ, ← hrange]
    exact hsymm_mdiff_within
  have hchart_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (extChartAt 𝓘(ℂ) q) ((extChartAt 𝓘(ℂ) p).symm z) := by
    apply mdifferentiableAt_extChartAt
    rwa [← extChartAt_source (I := 𝓘(ℂ))]
  exact (hchart_mdiff.comp z hsymm_mdiff).differentiableAt

/-- The chart-local integrand of a holomorphic 1-form is independent of the
chosen chart center, at points where the arc lies in both chart sources. -/
theorem integrand_center_independent (form : HolomorphicOneForm X)
    (gamma : AnalyticArc X) (p q : X) (a b r : ℝ)
    (hp : gamma.extend r ∈ (extChartAt 𝓘(ℂ) p).source)
    (hq : gamma.extend r ∈ (extChartAt 𝓘(ℂ) q).source)
    (hdp : DifferentiableWithinAt ℝ
      (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (gamma.extend s)) (Set.Ioo a b) r)
    (hrmem : r ∈ Set.Ioo a b) :
    form.coeff p ((extChartAt 𝓘(ℂ) p) (gamma.extend r)) *
        derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) p) (gamma.extend s))
          (Set.Ioo a b) r =
      form.coeff q ((extChartAt 𝓘(ℂ) q) (gamma.extend r)) *
        derivWithin (fun s : ℝ => (extChartAt 𝓘(ℂ) q) (gamma.extend s))
          (Set.Ioo a b) r := by
  let gp : ℝ → ℂ := fun s => (extChartAt 𝓘(ℂ) p) (gamma.extend s)
  let gq : ℝ → ℂ := fun s => (extChartAt 𝓘(ℂ) q) (gamma.extend s)
  let z : ℂ := gp r
  let T : ℂ → ℂ := (extChartAt 𝓘(ℂ) q) ∘ (extChartAt 𝓘(ℂ) p).symm
  let d : ℂ := fderiv ℂ T z 1
  have hz : z ∈ (extChartAt 𝓘(ℂ) p).target := by
    simpa [z, gp] using (extChartAt 𝓘(ℂ) p).map_source hp
  have hsymm_z : (extChartAt 𝓘(ℂ) p).symm z = gamma.extend r := by
    simpa [z, gp] using (extChartAt 𝓘(ℂ) p).left_inv hp
  have hsymm_z_chart : (chartAt ℂ p).symm z = gamma.extend r := by
    have hp_chart : gamma.extend r ∈ (chartAt ℂ p).source := by
      simpa [extChartAt_source] using hp
    simpa [z, gp] using (chartAt ℂ p).left_inv hp_chart
  have hzq : (extChartAt 𝓘(ℂ) p).symm z ∈ (extChartAt 𝓘(ℂ) q).source := by
    rw [hsymm_z]
    exact hq
  have hcoeff : form.coeff p z =
      form.coeff q ((extChartAt 𝓘(ℂ) q) (gamma.extend r)) * d := by
    have hcocycle := form.2.2.1 p q z hz hzq
    rw [hsymm_z] at hcocycle
    simpa [HolomorphicOneForm.coeff, T, d] using hcocycle
  have hTdiff : DifferentiableAt ℂ T z :=
    chartTransition_differentiableAt (p := p) (q := q) hz hzq
  have hTderiv : HasDerivAt T d (gp r) := by
    simpa [d, z] using hTdiff.hasDerivAt
  have hgp_deriv : HasDerivWithinAt gp (derivWithin gp (Set.Ioo a b) r)
      (Set.Ioo a b) r := by
    simpa [gp] using hdp.hasDerivWithinAt
  have hcomp_deriv : HasDerivWithinAt (T ∘ gp)
      (derivWithin gp (Set.Ioo a b) r * d) (Set.Ioo a b) r := by
    simpa [smul_eq_mul] using hTderiv.scomp_hasDerivWithinAt (x := r) hgp_deriv
  have hunique : UniqueDiffWithinAt ℝ (Set.Ioo a b) r :=
    uniqueDiffWithinAt_Ioo hrmem
  have hchain : derivWithin (T ∘ gp) (Set.Ioo a b) r =
      d * derivWithin gp (Set.Ioo a b) r := by
    rw [hcomp_deriv.derivWithin hunique, mul_comm]
  have hgp_source : ∀ᶠ s in 𝓝 r, gamma.extend s ∈ (extChartAt 𝓘(ℂ) p).source :=
    gamma.continuous'.continuousAt.eventually ((isOpen_extChartAt_source p).mem_nhds hp)
  have hlocal : gq =ᶠ[𝓝 r] T ∘ gp := by
    filter_upwards [hgp_source] with s hs
    have hs_chart : gamma.extend s ∈ (chartAt ℂ p).source := by
      simpa [extChartAt_source] using hs
    change (chartAt ℂ q) (gamma.extend s) =
      (chartAt ℂ q) ((chartAt ℂ p).symm ((chartAt ℂ p) (gamma.extend s)))
    rw [(chartAt ℂ p).left_inv hs_chart]
  have hlocal_within : gq =ᶠ[𝓝[Set.Ioo a b] r] T ∘ gp :=
    hlocal.filter_mono nhdsWithin_le_nhds
  have hgq_deriv : derivWithin gq (Set.Ioo a b) r =
      d * derivWithin gp (Set.Ioo a b) r := by
    rw [hlocal_within.derivWithin_eq_of_mem hrmem, hchain]
  have hmain : form.coeff p z * derivWithin gp (Set.Ioo a b) r =
      form.coeff q ((extChartAt 𝓘(ℂ) q) (gamma.extend r)) *
        derivWithin gq (Set.Ioo a b) r := by
    calc
      form.coeff p z * derivWithin gp (Set.Ioo a b) r =
          (form.coeff q ((extChartAt 𝓘(ℂ) q) (gamma.extend r)) * d) *
            derivWithin gp (Set.Ioo a b) r := by
        rw [hcoeff]
      _ = form.coeff q ((extChartAt 𝓘(ℂ) q) (gamma.extend r)) *
          (d * derivWithin gp (Set.Ioo a b) r) := by
        rw [mul_assoc]
      _ = form.coeff q ((extChartAt 𝓘(ℂ) q) (gamma.extend r)) *
          derivWithin gq (Set.Ioo a b) r := by
        rw [hgq_deriv]
  simpa [gp, gq, z] using hmain

end Jacobians.RiemannSurface
