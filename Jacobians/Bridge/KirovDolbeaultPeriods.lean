/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.Bridge.KirovDolbeaultTrace
import Jacobians.Bridge.KirovLineIntegral
import Jacobians.RiemannSurface.LoopLattice
import Jacobians.Axioms.PeriodLatticeBase
import KirovDolbeault.PeriodLattice

/-!
# Bridge: developing values vs the Kirov-Dolbeault port's line integrals

The keystone analytic comparison behind the lattice-comparison inclusions
between our `periodLatticeInBasis` (chart-ball developing values over `H1`)
and the Dolbeault port's `truePeriodLattice` (moving-chart `lineIntegral`s
over `IsClosedSmoothLoop`s):

* `port_lineIntegral_bridgeKD` — the port's `lineIntegral` of a bridged form
  is (definitionally) the vendored Kirov line integral of the Montel-bridged
  form, so the entire `Bridge/KirovLineIntegral.lean` chart toolbox applies.
* `lineIntegral_cell_eq_primitive_sub` — **cell FTC**: on a parameter
  interval whose image stays inside one `PathChartBall`, the port line
  integral of a bridged form equals the endpoint difference of the
  chart-ball primitive (`pathChartBallPrimitive`). This is the same local
  computation as `DevelopingBridge.lean` (HI-0), but against the port's
  moving-chart integrand instead of `canonicalIntegrand`.

Idea credit: the lattice-bridge architecture (reducing #31/#191 to the
`truePeriodLattice` ↔ `periodLatticeInBasis` comparison) follows daouid's
closed PR #191; the comparison itself is proven here rather than assumed.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory

namespace Jacobians.Bridge

open Jacobians.RiemannSurface

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The Dolbeault port's `pathSpeed` agrees definitionally with the vendored
Kirov `pathSpeed` (both are `fderiv ℝ ((chartAt (γ t)).toFun ∘ γ) t 1`). -/
theorem port_pathSpeed_eq (γ : ℝ → Y) (t : ℝ) :
    _root_.Jacobians.pathSpeed γ t = Jacobians.Vendor.Kirov.pathSpeed γ t := rfl

/-- The port's `lineIntegral` of a KD-bridged form is the vendored Kirov line
integral of the Montel-bridged form: `kdFormAlign` is the identity on the
common underlying `ContMDiffSection` type, and the two `lineIntegral`s have
identical definitions. -/
theorem port_lineIntegral_bridgeKD (form : HolomorphicOneForm Y) (γ : ℝ → Y) :
    _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) γ =
      Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form) γ := rfl

/-- **Cell FTC.** If `γ : ℝ → Y` is continuous, chart-differentiable on
`[a, b]`, and its image on `[a, b]` stays inside the chart ball `B` (source
membership + coordinates in the metric ball), then the moving-chart line
integral of the bridged form over `[a, b]` is the endpoint difference of the
chart-ball primitive of `form` on `B`. -/
theorem lineIntegral_cell_eq_primitive_sub
    (form : HolomorphicOneForm Y) (B : PathChartBall Y) (γ : ℝ → Y) {a b : ℝ}
    (hab : a ≤ b) (hcont : Continuous γ)
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)
    (hmem : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt ℂ B.p).source ∧
      (extChartAt 𝓘(ℂ) B.p) (γ t) ∈ Metric.ball B.c B.r)
    (hint : IntervalIntegrable
      (fun t => (bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t))
      MeasureTheory.volume a b) :
    ∫ t in a..b, (bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t) =
      pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) (γ b)) -
        pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) (γ a)) := by
  classical
  set p : Y := B.p
  set g : ℂ → ℂ := pathChartBallPrimitive form B with hg_def
  set u : ℝ → ℂ := fun t => (extChartAt 𝓘(ℂ, ℂ) p) (γ t) with hu_def
  -- The composite `F = g ∘ u` has the moving-chart integrand as derivative on `[a, b]`.
  have key : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => g (u s))
        ((bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨hsrc_chart, hball⟩ := hmem t ht
    have hsrc_p : γ t ∈ (extChartAt 𝓘(ℂ, ℂ) p).source := by
      rwa [extChartAt_source]
    have hsrc_self : γ t ∈ (extChartAt 𝓘(ℂ, ℂ) (γ t)).source :=
      mem_extChartAt_source (γ t)
    -- Step 1: differentiability of the fixed-chart coordinate path `u` at `t`.
    have hu_diff : DifferentiableAt ℝ u t := by
      set w := chartAt (H := ℂ) (γ t) with hw_def
      set gX : ℝ → ℂ := w.toFun ∘ γ with hgX_def
      set floc : ℂ → ℂ := fun z => (extChartAt 𝓘(ℂ, ℂ) p) (w.symm z) with hfloc_def
      have hγt_w : γ t ∈ w.source := mem_chart_source ℂ (γ t)
      have hev : ∀ᶠ s in 𝓝 t, γ s ∈ w.source :=
        (hcont.continuousAt).eventually (w.open_source.mem_nhds hγt_w)
      have h_eq : u =ᶠ[𝓝 t] floc ∘ gX := by
        filter_upwards [hev] with s hs
        simp only [hu_def, hfloc_def, hgX_def, Function.comp_apply]
        congr 1
        exact (w.left_inv hs).symm
      have hf_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (extChartAt 𝓘(ℂ, ℂ) p) (γ t) := by
        apply mdifferentiableAt_extChartAt
        rwa [← extChartAt_source (I := 𝓘(ℂ, ℂ))]
      have hf_loc_diff_ℂ : DifferentiableAt ℂ floc (gX t) := by
        have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
        rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
        convert h1 using 2
      have hf_loc_diff_ℝ : DifferentiableAt ℝ floc (gX t) :=
        hf_loc_diff_ℂ.restrictScalars ℝ
      have hgX_diff : DifferentiableAt ℝ gX t := hdiff t ht
      exact (Filter.EventuallyEq.differentiableAt_iff h_eq).mpr
        (hf_loc_diff_ℝ.comp t hgX_diff)
    -- Step 2: `u` has derivative `fderiv ℝ u t 1`, which is the chart image of `pathSpeed`.
    have hu_deriv : HasDerivAt u (fderiv ℝ u t 1) t := hu_diff.hasDerivAt
    have hspeed : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) p) (γ t)
        (Jacobians.Vendor.Kirov.pathSpeed γ t) = fderiv ℝ u t 1 := by
      have h := mfderiv_extChartAt_apply_pathSpeed (x := p) (γ := γ) (t := t)
        hcont.continuousAt (hdiff t ht) hsrc_p
      simpa [hu_def] using h
    -- Step 3: primitive has the coefficient as ℂ-derivative at `u t`.
    have hg_deriv : HasDerivAt g (form.coeff p (u t)) (u t) :=
      pathChartBallPrimitive_hasDerivAt form B (u t) hball
    -- Step 4: chain rule (scalar tower ℝ ⊆ ℂ).
    have hF : HasDerivAt (fun s => g (u s))
        ((fderiv ℝ u t 1) • form.coeff p (u t)) t :=
      hg_deriv.scomp t hu_deriv
    -- Step 5: identify the derivative with the moving-chart integrand.
    have hswap : (bridgeForm form).toFun (γ t) = BridgeForm.rawCLM form p (γ t) := by
      change BridgeForm.rawCLM form (γ t) (γ t) = BridgeForm.rawCLM form p (γ t)
      exact BridgeForm.rawCLM_swap_chart form hsrc_self hsrc_p
    have hval : (bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t) =
        form.coeff p (u t) * (fderiv ℝ u t 1) := by
      rw [hswap]
      show (form.coeff p ((extChartAt 𝓘(ℂ, ℂ) p) (γ t))) •
          ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) p) (γ t))
            (Jacobians.Vendor.Kirov.pathSpeed γ t)) =
        form.coeff p (u t) * (fderiv ℝ u t 1)
      rw [hspeed]
      rfl
    rw [hval]
    convert hF using 1
    simp [smul_eq_mul]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt key hint
  simpa [hu_def] using hFTC

end Jacobians.Bridge
