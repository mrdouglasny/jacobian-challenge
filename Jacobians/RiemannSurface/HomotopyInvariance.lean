/-
HI-0 bridge from the canonical moving-chart arc integral to a fixed chart
when the arc lies in one chart source.
-/
import Jacobians.RiemannSurface.CanonicalArcIntegral
import Jacobians.Bridge.ContourDeformation

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Set Filter
open Jacobians.Bridge.ContourDeformation

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The underlying Mathlib path of an analytic arc. -/
def analyticArcToPath (γ : AnalyticArc X) : Path (γ.extend 0) (γ.extend 1) where
  toFun t := γ.extend (t : ℝ)
  continuous_toFun := γ.continuous'.comp continuous_subtype_val
  source' := rfl
  target' := rfl

/-- The coordinate path obtained by reading an analytic arc in one fixed chart. -/
noncomputable def fixedChartPath (γ : AnalyticArc X) (x₀ : X)
    (hsource : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      γ.extend r ∈ (extChartAt 𝓘(ℂ) x₀).source) :
    Path ((extChartAt 𝓘(ℂ) x₀) (γ.extend 0))
      ((extChartAt 𝓘(ℂ) x₀) (γ.extend 1)) where
  toFun t := (extChartAt 𝓘(ℂ) x₀) (γ.extend (t : ℝ))
  continuous_toFun := by
    exact (continuousOn_extChartAt (I := 𝓘(ℂ)) x₀).comp_continuous
      (γ.continuous'.comp continuous_subtype_val) (fun t => hsource (t : ℝ) t.2)
  source' := rfl
  target' := rfl

private theorem arc_source_of_homotopy_left
    (γ₁ γ₂ : AnalyticArc X) (x₀ : X)
    (hstart : γ₁.extend 0 = γ₂.extend 0) (hend : γ₁.extend 1 = γ₂.extend 1)
    (F : (analyticArcToPath γ₁).Homotopy ((analyticArcToPath γ₂).cast hstart hend))
    (hFsource : ∀ z : unitInterval × unitInterval,
      F z ∈ (extChartAt 𝓘(ℂ) x₀).source) :
    ∀ r ∈ Set.Icc (0 : ℝ) 1, γ₁.extend r ∈ (extChartAt 𝓘(ℂ) x₀).source := by
  intro r hr
  have h := hFsource (0, (⟨r, hr⟩ : unitInterval))
  rw [ContinuousMap.HomotopyWith.apply_zero F (⟨r, hr⟩ : unitInterval)] at h
  simpa [analyticArcToPath] using h

private theorem arc_source_of_homotopy_right
    (γ₁ γ₂ : AnalyticArc X) (x₀ : X)
    (hstart : γ₁.extend 0 = γ₂.extend 0) (hend : γ₁.extend 1 = γ₂.extend 1)
    (F : (analyticArcToPath γ₁).Homotopy ((analyticArcToPath γ₂).cast hstart hend))
    (hFsource : ∀ z : unitInterval × unitInterval,
      F z ∈ (extChartAt 𝓘(ℂ) x₀).source) :
    ∀ r ∈ Set.Icc (0 : ℝ) 1, γ₂.extend r ∈ (extChartAt 𝓘(ℂ) x₀).source := by
  intro r hr
  have h := hFsource (1, (⟨r, hr⟩ : unitInterval))
  rw [ContinuousMap.HomotopyWith.apply_one F (⟨r, hr⟩ : unitInterval)] at h
  simpa [analyticArcToPath] using h

/-- The coordinate homotopy induced by a path homotopy whose image lies in a
single chart source. -/
noncomputable def fixedChartHomotopy
    (γ₁ γ₂ : AnalyticArc X) (x₀ : X)
    (hstart : γ₁.extend 0 = γ₂.extend 0) (hend : γ₁.extend 1 = γ₂.extend 1)
    (F : (analyticArcToPath γ₁).Homotopy ((analyticArcToPath γ₂).cast hstart hend))
    (hFsource : ∀ z : unitInterval × unitInterval,
      F z ∈ (extChartAt 𝓘(ℂ) x₀).source) :
    (fixedChartPath γ₁ x₀
      (arc_source_of_homotopy_left γ₁ γ₂ x₀ hstart hend F hFsource)).Homotopy
      ((fixedChartPath γ₂ x₀
        (arc_source_of_homotopy_right γ₁ γ₂ x₀ hstart hend F hFsource)).cast
          (congrArg (fun x => (extChartAt 𝓘(ℂ) x₀) x) hstart)
          (congrArg (fun x => (extChartAt 𝓘(ℂ) x₀) x) hend)) where
  toFun z := (extChartAt 𝓘(ℂ) x₀) (F z)
  continuous_toFun := by
    exact (continuousOn_extChartAt (I := 𝓘(ℂ)) x₀).comp_continuous
      F.continuous_toFun hFsource
  map_zero_left t := by
    rw [ContinuousMap.HomotopyWith.apply_zero F t]
    rfl
  map_one_left t := by
    rw [ContinuousMap.HomotopyWith.apply_one F t]
    rfl
  prop' t s hs := by
    rcases hs with hs | hs
    · rw [hs]
      change (extChartAt 𝓘(ℂ) x₀) (F (t, 0)) = (extChartAt 𝓘(ℂ) x₀) (γ₁.extend 0)
      rw [Path.Homotopy.source F t]
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      change (extChartAt 𝓘(ℂ) x₀) (F (t, 1)) = (extChartAt 𝓘(ℂ) x₀) (γ₁.extend 1)
      rw [Path.Homotopy.target F t]

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

private theorem fixedChart_integral_eq_curveIntegral
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) (x₀ : X)
    (hsource : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      γ.extend r ∈ (extChartAt 𝓘(ℂ) x₀).source) :
    (∫ r in (0 : ℝ)..1,
        form.coeff x₀ ((extChartAt 𝓘(ℂ) x₀) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)) r) =
      ∫ᶜ z in fixedChartPath γ x₀ hsource, holoOneForm (form.coeff x₀) z := by
  let p := fixedChartPath γ x₀ hsource
  let charted : ℝ → ℂ := fun u => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)
  have hcurve := curveIntegral_eq_intervalIntegral_deriv (holoOneForm (form.coeff x₀)) p
  rw [hcurve]
  refine (intervalIntegral.integral_congr_ae ?_).symm
  rw [MeasureTheory.ae_uIoc_iff]
  constructor
  · filter_upwards
      [Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)]
      with r hr_eq hr
    have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
      change Set.Ioo (0 : ℝ) 1 r
      rw [hr_eq]
      exact hr
    have hrcc : r ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hr01.1, le_of_lt hr01.2⟩
    have hev : p.extend =ᶠ[𝓝 r] charted := by
      filter_upwards [(isOpen_Ioo.mem_nhds hr01)] with u hu
      have hucc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
      simp [p, fixedChartPath, charted, Path.extend_apply, hucc]
    have hderiv : deriv (⇑p.extend) r = deriv charted r :=
      Filter.EventuallyEq.deriv_eq hev
    have hpval : p.extend r = charted r := by
      simp [p, fixedChartPath, charted, Path.extend_apply, hrcc]
    calc
      form.coeff x₀ (p.extend r) * deriv (⇑p.extend) r =
          form.coeff x₀ (charted r) * deriv charted r := by rw [hpval, hderiv]
      _ = form.coeff x₀ ((extChartAt 𝓘(ℂ) x₀) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)) r := by
            rfl
  · filter_upwards with r hr
    have h_empty : Set.Ioc (1 : ℝ) 0 = (∅ : Set ℝ) :=
      Set.Ioc_eq_empty (not_lt_of_ge (zero_le_one : (0 : ℝ) ≤ 1))
    rw [h_empty] at hr
    exact False.elim hr

private theorem canonicalArcIntegral_homotopy_invariant_singleChart_of_fixedChartHomotopy
    (γ₁ γ₂ : AnalyticArc X) (form : HolomorphicOneForm X) (x₀ : X)
    (hsource₁ : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      γ₁.extend r ∈ (extChartAt 𝓘(ℂ) x₀).source)
    (hsource₂ : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      γ₂.extend r ∈ (extChartAt 𝓘(ℂ) x₀).source)
    (hstart : (extChartAt 𝓘(ℂ) x₀) (γ₁.extend 0) =
      (extChartAt 𝓘(ℂ) x₀) (γ₂.extend 0))
    (hend : (extChartAt 𝓘(ℂ) x₀) (γ₁.extend 1) =
      (extChartAt 𝓘(ℂ) x₀) (γ₂.extend 1))
    (F : (fixedChartPath γ₁ x₀ hsource₁).Homotopy
      ((fixedChartPath γ₂ x₀ hsource₂).cast hstart hend))
    (hFt : ∀ a ∈ Set.Ioo (0 : unitInterval) 1,
      ∀ b ∈ Set.Ioo (0 : unitInterval) 1,
        F (a, b) ∈ (extChartAt 𝓘(ℂ) x₀).target)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (F.toHomotopy.extend xy.1) xy.2)
      (Set.Icc 0 1))
    (hωdcc : DiffContOnCl ℝ (holoOneForm (form.coeff x₀))
      (extChartAt 𝓘(ℂ) x₀).target) :
    canonicalArcIntegral γ₁ form = canonicalArcIntegral γ₂ form := by
  let p₁ := fixedChartPath γ₁ x₀ hsource₁
  let p₂ := fixedChartPath γ₂ x₀ hsource₂
  have hfixed₁ := canonicalArcIntegral_eq_fixedChart_integral γ₁ form x₀ hsource₁
  have hfixed₂ := canonicalArcIntegral_eq_fixedChart_integral γ₂ form x₀ hsource₂
  have hbridge₁ := fixedChart_integral_eq_curveIntegral γ₁ form x₀ hsource₁
  have hbridge₂ := fixedChart_integral_eq_curveIntegral γ₂ form x₀ hsource₂
  have ht : IsOpen (extChartAt 𝓘(ℂ) x₀).target :=
    isOpen_extChartAt_target (I := 𝓘(ℂ)) x₀
  have hf : DifferentiableOn ℂ (form.coeff x₀) (extChartAt 𝓘(ℂ) x₀).target :=
    (form.2.1 x₀).differentiableOn
  have hcontour := contourDeformation1D_pathHomotopy ht hf hωdcc F hFt hcontdiff
  calc
    canonicalArcIntegral γ₁ form =
        ∫ r in (0 : ℝ)..1,
          form.coeff x₀ ((extChartAt 𝓘(ℂ) x₀) (γ₁.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ₁.extend u)) r := hfixed₁
    _ = ∫ᶜ z in p₁, holoOneForm (form.coeff x₀) z := hbridge₁
    _ = ∫ᶜ z in (p₂.cast hstart hend), holoOneForm (form.coeff x₀) z := hcontour
    _ = ∫ᶜ z in p₂, holoOneForm (form.coeff x₀) z := by simp [p₂]
    _ = ∫ r in (0 : ℝ)..1,
          form.coeff x₀ ((extChartAt 𝓘(ℂ) x₀) (γ₂.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ₂.extend u)) r := hbridge₂.symm
    _ = canonicalArcIntegral γ₂ form := hfixed₂.symm

/-- Single-chart homotopy invariance of the canonical analytic-arc integral.

The additional `DiffContOnCl` and `ContDiffOn` hypotheses are the exact
regularity assumptions required by the chart-local Cauchy theorem after the
given `X`-valued homotopy is read in the fixed chart. -/
theorem canonicalArcIntegral_homotopy_invariant_singleChart
    (γ₁ γ₂ : AnalyticArc X) (form : HolomorphicOneForm X) (x₀ : X)
    (hstart : γ₁.extend 0 = γ₂.extend 0) (hend : γ₁.extend 1 = γ₂.extend 1)
    (F : (analyticArcToPath γ₁).Homotopy ((analyticArcToPath γ₂).cast hstart hend))
    (hFsource : ∀ z : unitInterval × unitInterval,
      F z ∈ (extChartAt 𝓘(ℂ) x₀).source)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one
        ((fixedChartHomotopy γ₁ γ₂ x₀ hstart hend F hFsource).toHomotopy.extend xy.1) xy.2)
      (Set.Icc 0 1))
    (hωdcc : DiffContOnCl ℝ (holoOneForm (form.coeff x₀))
      (extChartAt 𝓘(ℂ) x₀).target) :
    canonicalArcIntegral γ₁ form = canonicalArcIntegral γ₂ form := by
  let hsource₁ := arc_source_of_homotopy_left γ₁ γ₂ x₀ hstart hend F hFsource
  let hsource₂ := arc_source_of_homotopy_right γ₁ γ₂ x₀ hstart hend F hFsource
  let G := fixedChartHomotopy γ₁ γ₂ x₀ hstart hend F hFsource
  have hFt : ∀ a ∈ Set.Ioo (0 : unitInterval) 1,
      ∀ b ∈ Set.Ioo (0 : unitInterval) 1,
        G (a, b) ∈ (extChartAt 𝓘(ℂ) x₀).target := by
    intro a _ha b _hb
    exact (extChartAt 𝓘(ℂ) x₀).map_source (hFsource (a, b))
  exact canonicalArcIntegral_homotopy_invariant_singleChart_of_fixedChartHomotopy
    γ₁ γ₂ form x₀ hsource₁ hsource₂
    (congrArg (fun x => (extChartAt 𝓘(ℂ) x₀) x) hstart)
    (congrArg (fun x => (extChartAt 𝓘(ℂ) x₀) x) hend)
    G hFt hcontdiff hωdcc

end Jacobians.RiemannSurface
