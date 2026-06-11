/-
# Loop conjugation: rebasing closed analytic arcs along a connector

The `PeriodCycleBasis` interface requires all `2g` loops to be based at one
common point `x₀`, while natural cycle constructions (e.g. hyperelliptic
branch-cut circles) are closed arcs based at construction-specific points.
`AnalyticLoop.conjugate` rebases a closed arc `γ` along a connector `σ` from
`x₀` to `γ`'s basepoint: `σ ⬝ γ ⬝ σ⁻¹`, an `AnalyticLoop` at `σ.extend 0`.

`canonicalArcIntegral_conjugate` shows the connector contributions cancel:
the conjugated loop has the same canonical period as `γ` for every
holomorphic 1-form. (Homology classes are likewise conjugation-invariant;
that statement lives with the H₁ machinery, not here.)
-/
import Jacobians.RiemannSurface.ArcAlgebra

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- The composite arc `σ ⬝ γ ⬝ σ⁻¹` of a closed arc `γ` conjugated by a
connector `σ` ending at `γ`'s basepoint. -/
noncomputable def AnalyticArc.conjugate (σ γ : AnalyticArc X)
    (hσγ : σ.extend 1 = γ.extend 0) (hγ : γ.extend 1 = γ.extend 0) :
    AnalyticArc X :=
  (σ.trans γ hσγ).trans σ.reverse (by
    simp [AnalyticArc.trans_extend_one, AnalyticArc.reverse_extend_zero, hγ, hσγ.symm])

/-- Rebase a closed analytic arc `γ` at the start point of a connector `σ`
ending at `γ`'s basepoint: the loop `σ ⬝ γ ⬝ σ⁻¹` based at `σ.extend 0`. -/
noncomputable def AnalyticLoop.conjugate (σ γ : AnalyticArc X)
    (hσγ : σ.extend 1 = γ.extend 0) (hγ : γ.extend 1 = γ.extend 0) :
    AnalyticLoop X (σ.extend 0) where
  arc := AnalyticArc.conjugate σ γ hσγ hγ
  start_eq := by
    simp [AnalyticArc.conjugate, AnalyticArc.trans_extend_zero]
  end_eq := by
    simp [AnalyticArc.conjugate, AnalyticArc.trans_extend_one,
      AnalyticArc.reverse_extend_one]

@[simp] theorem AnalyticLoop.conjugate_arc (σ γ : AnalyticArc X)
    (hσγ : σ.extend 1 = γ.extend 0) (hγ : γ.extend 1 = γ.extend 0) :
    (AnalyticLoop.conjugate σ γ hσγ hγ).arc = AnalyticArc.conjugate σ γ hσγ hγ :=
  rfl

/-- **Connector cancellation.** The canonical period of a conjugated loop
`σ ⬝ γ ⬝ σ⁻¹` equals the canonical period of the closed arc `γ`:
`∫_σ ω + ∫_γ ω − ∫_σ ω = ∫_γ ω`. -/
theorem canonicalArcIntegral_conjugate (σ γ : AnalyticArc X)
    (hσγ : σ.extend 1 = γ.extend 0) (hγ : γ.extend 1 = γ.extend 0)
    (form : HolomorphicOneForm X) :
    canonicalArcIntegral (AnalyticArc.conjugate σ γ hσγ hγ) form =
      canonicalArcIntegral γ form := by
  have hintσ := analyticArc_canonicalIntegrand_intervalIntegrable σ form
  have hintγ := analyticArc_canonicalIntegrand_intervalIntegrable γ form
  have hintσγ := analyticArc_canonicalIntegrand_intervalIntegrable (σ.trans γ hσγ) form
  have hintσrev := analyticArc_canonicalIntegrand_intervalIntegrable σ.reverse form
  unfold AnalyticArc.conjugate
  rw [canonicalArcIntegral_trans _ _ _ form hintσγ hintσrev,
    canonicalArcIntegral_trans _ _ _ form hintσ hintγ,
    canonicalArcIntegral_reverse]
  ring

end Jacobians.RiemannSurface
