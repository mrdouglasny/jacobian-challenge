import Jacobians.Bridge.BridgePathArc
import Jacobians.RiemannSurface.CanonicalArcIntegral

/-!
# Kirov line integral agrees with the canonical arc integral

This file proves that, along the bridge path packaged as an `AnalyticArc`,
the Kirov-backed line integral and the canonical moving-chart arc integral
use the same integrand.
-/

namespace Jacobians.Bridge

open scoped Manifold ContDiff Topology
open MeasureTheory Filter
open Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

lemma bridge_kirov_integrand_eq_canonicalIntegrand
    (P0 P : X) (form : HolomorphicOneForm X) (t : ℝ) :
    (Jacobians.Bridge.bridgeForm form).toFun (bridgePath (X := X) P0 P t)
        (Jacobians.Vendor.Kirov.pathSpeed (bridgePath (X := X) P0 P) t) =
      canonicalIntegrand (bridgePathArc (X := X) P0 P) form t := by
  let y : X := bridgePath (X := X) P0 P t
  have hspeed :
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) y)
          (Jacobians.Vendor.Kirov.pathSpeed (bridgePath (X := X) P0 P) t) =
        fderiv ℝ (((extChartAt 𝓘(ℂ, ℂ) y).toFun) ∘ bridgePath (X := X) P0 P) t 1 := by
    simpa [y] using
      mfderiv_extChartAt_apply_pathSpeed (x := y)
        (γ := bridgePath (X := X) P0 P) (t := t)
        ((bridgePath_continuous (X := X) P0 P).continuousAt)
        (bridgePath_chart_differentiable (X := X) P0 P t)
        (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) y)
  change BridgeForm.rawCLM form y y
        (Jacobians.Vendor.Kirov.pathSpeed (bridgePath (X := X) P0 P) t) =
      canonicalIntegrand (bridgePathArc (X := X) P0 P) form t
  unfold BridgeForm.rawCLM
  change form.coeff y ((extChartAt 𝓘(ℂ, ℂ) y) y) •
        ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) y)
          (Jacobians.Vendor.Kirov.pathSpeed (bridgePath (X := X) P0 P) t)) =
      canonicalIntegrand (bridgePathArc (X := X) P0 P) form t
  rw [hspeed]
  change form.coeff y ((extChartAt 𝓘(ℂ, ℂ) y) y) *
        (fderiv ℝ (((extChartAt 𝓘(ℂ, ℂ) y).toFun) ∘
          bridgePath (X := X) P0 P) t 1) =
      canonicalIntegrand (bridgePathArc (X := X) P0 P) form t
  rw [fderiv_apply_one_eq_deriv]
  simp [canonicalIntegrand, y, bridgePathArc, bridgePath, Function.comp_def]

theorem kirovBackedFunctional_eq_canonicalArcIntegral
    (P0 P : X) (form : HolomorphicOneForm X) :
    kirovBackedFunctional P0 P form =
      canonicalArcIntegral (bridgePathArc P0 P) form := by
  change Jacobians.Vendor.Kirov.lineIntegral (Jacobians.Bridge.bridgeForm form)
      (bridgePath (X := X) P0 P) =
    canonicalArcIntegral (bridgePathArc P0 P) form
  unfold Jacobians.Vendor.Kirov.lineIntegral canonicalArcIntegral
  exact intervalIntegral.integral_congr fun t _ =>
    bridge_kirov_integrand_eq_canonicalIntegrand (X := X) P0 P form t

end Jacobians.Bridge
