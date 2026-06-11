/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FrameTraceWallCluster

/-!
# Lemma 3.2 at infinity for the plain value trace (T lane)

The last analytic field of the residual wall `exists_frameTraceFunctionData_df`: the residue at
infinity of the value trace is the `∞`-fibre `frameRes` sum (the reciprocal-chart cluster
computation at the poles of the cover).

`valueTrace_resAtInfty_df` is currently the **single residual `sorry`** of the T lane; see the
discharge sketch in its docstring.
-/

noncomputable section

open Complex Metric Filter Topology Set
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FrameTraceWall

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.ProperMapDegreeSheets Jacobians.MultiplicityPatching
  Jacobians.MultiplicityPatchingConstruct Jacobians.MeromorphicTrace Jacobians.Dolbeault
  Jacobians.TraceResidue

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **[RESIDUAL — single named `sorry`] Lemma 3.2 at `∞` for the plain value trace.**  On a
contour enclosing all exceptional values of the `ω₀ = df` value trace, the residue at infinity
is the `∞`-fibre `frameRes` sum (over the poles of the cover).  (NOT VERIFIED — Miranda
§VIII.3, the reciprocal-chart cluster computation: over `w` large the fibre clusters at the
poles of `f`; per pole of order `e`, the reciprocal normal form `1/f̂ = ηᵉ`
(`exists_reciprocal_NF`) and the unweighted symmetric descent give `T(w) = H(1/w)` with `H`
meromorphic at `0`; the contour integral picks out `−a₁(H)`, which the branch normalization
identifies with the `frameRes` sum.) -/
theorem valueTrace_resAtInfty_df (data : CanonicalForm17Data X) (F f : MeromorphicFunction X)
    (hω : data.ω₀ = differentialForm f) (hdiv : (f.div : Divisor X) ≠ 0)
    (C : Finset ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hball : ∀ c ∈ C, c ∈ Metric.ball (0 : ℂ) ρ)
    (hoff : ∀ z : ℂ, z ∉ C → AnalyticAt ℂ (valueTrace F f) z) :
    resAtInfty (valueTrace F f) ρ
      = ∑ y ∈ fibreFinset f hdiv OnePoint.infty, frameRes data F y := by
  sorry

end Jacobians.Dolbeault.FrameTraceWall

end
