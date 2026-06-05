import Jacobians.Bridge.KirovLineIntegral
import Jacobians.RiemannSurface.AnalyticArc

/-!
# Analytic bridge-path helpers

This file collects the analyticity facts needed to package `bridgePath` as an
`AnalyticArc`.
-/

namespace Jacobians.Bridge

open scoped Manifold ContDiff Topology
open Filter
open Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

omit [T2Space X] in
/-- Chart transitions between two `extChartAt` charts are real-analytic on their overlap. -/
lemma extChartAt_trans_analyticAt {p q : X} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) q).target)
    (hmem : (extChartAt 𝓘(ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ) p).source) :
    AnalyticAt ℝ ((extChartAt 𝓘(ℂ) p) ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
  have htransition_source :
      z ∈ ((extChartAt 𝓘(ℂ) q).symm ≫ extChartAt 𝓘(ℂ) p).source := by
    rw [PartialEquiv.trans_source]
    exact ⟨hz, hmem⟩
  have hcont :
      ContDiffWithinAt ℂ ω
        (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm)
        (Set.range ((𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) : ℂ → ℂ)) z :=
    contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) p q htransition_source
  have hcontAt :
      ContDiffAt ℂ ω
        (extChartAt 𝓘(ℂ) p ∘ (extChartAt 𝓘(ℂ) q).symm) z := by
    rw [← contDiffWithinAt_univ]
    simpa [modelWithCornersSelf_coe] using hcont
  exact hcontAt.analyticAt.restrictScalars (𝕜 := ℝ)

/-- The cubic flat reparameterization is real-analytic. -/
lemma analyticAt_flatReparam (t : ℝ) :
    AnalyticAt ℝ flatReparam t := by
  unfold flatReparam
  fun_prop

section FlatSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Flat affine segments are real-analytic. -/
lemma analyticAt_flatSegment (a b : E) (t : ℝ) :
    AnalyticAt ℝ (flatSegment a b) t := by
  unfold flatSegment
  have hφ : AnalyticAt ℝ flatReparam t := analyticAt_flatReparam t
  exact ((analyticAt_const.sub hφ).smul analyticAt_const).add (hφ.smul analyticAt_const)

end FlatSegment

end Jacobians.Bridge
