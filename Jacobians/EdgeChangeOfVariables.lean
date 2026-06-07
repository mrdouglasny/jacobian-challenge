/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.LineIntegral
import Jacobians.CotangentCoeff

/-!
# Edge change-of-variables for the line integral

This is the foundational "edge change-of-variables" for the period-lattice cut-surface proof. It
relates a line integral of a holomorphic 1-form `α` along a path `cut ∘ e` in the surface `X` to a
plain `ℝ → ℂ` integral over the box edge `e`, via the manifold chain rule.

`cut : ℂ → X` is the cut chart (source `= ℂ` as a manifold over itself); `e : ℝ → ℂ` is a box edge.

For a path `e : ℝ → ℂ` into the model space `ℂ`, `pathSpeed e` (the chart-pullback velocity,
defined in `Jacobians.LineIntegral`) coincides with the ordinary derivative `deriv e`, because the
preferred chart on the self-charted space `ℂ` is the identity (`chartAt_self_eq`). The main result
then follows from the repo's chart-level chain rule `pathSpeed_comp_eq_mfderiv_of_mdiff`.

## References

Forster §§10–12; Miranda Ch. 4 §§3–4 (line integrals on Riemann surfaces).
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open MeasureTheory Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- On the self-charted model space `ℂ`, the chart pullback of a path `e : ℝ → ℂ` is `e` itself
(the preferred chart at any point is the identity, `chartAt_self_eq`). -/
theorem chart_comp_modelPath (e : ℝ → ℂ) (t : ℝ) :
    (chartAt (H := ℂ) (e t)).toFun ∘ e = e := by
  funext s
  simp

/-- **`pathSpeed` of a model-space path is its ordinary derivative.** For `e : ℝ → ℂ`, the
chart-pullback velocity `pathSpeed e t` equals `deriv e t`, since on `ℂ` the preferred chart is the
identity (so the chart pullback is `e` itself) and `fderiv ℝ e t 1 = deriv e t`. -/
theorem pathSpeed_modelPath_eq_deriv (e : ℝ → ℂ) (t : ℝ) :
    pathSpeed e t = deriv e t := by
  unfold pathSpeed
  rw [chart_comp_modelPath e t, fderiv_apply_one_eq_deriv]

/-- **Edge change-of-variables.** For the cut chart `cut : ℂ → X` (smooth) and a smooth box edge
`e : ℝ → ℂ`, the line integral of `α` along `cut ∘ e` equals the `ℝ`-integral of the pullback:
`∫_{cut∘e} α = ∫₀¹ α(cut(e t))(d cut · e'(t)) dt`. -/
theorem lineIntegral_comp_cut (cut : ℂ → X) (hcut : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cut)
    (α : HolomorphicOneForms X) (e : ℝ → ℂ) (he : ∀ t, DifferentiableAt ℝ e t)
    (he_cont : Continuous e) :
    lineIntegral α (cut ∘ e)
      = ∫ t in (0:ℝ)..1, α.toFun (cut (e t)) (mfderiv 𝓘(ℂ) 𝓘(ℂ) cut (e t) (deriv e t)) := by
  unfold lineIntegral
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  -- It suffices to show the inner tangent vectors agree.
  refine congrArg (α.toFun (cut (e t))) ?_
  -- `cut`'s manifold differentiability at `e t`.
  have hcut_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cut (e t) :=
    (hcut (e t)).mdifferentiableAt (by decide : ω ≠ 0)
  -- The chart pullback of `e` at `t` is `e`, which is differentiable.
  have he_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (e t)).toFun ∘ e) t := by
    rw [chart_comp_modelPath e t]; exact he t
  -- Chain rule: `pathSpeed (cut ∘ e) t = mfderiv cut (e t) (pathSpeed e t)`, then
  -- `pathSpeed e t = deriv e t` since `e` lands in the model space `ℂ`.
  exact (pathSpeed_comp_eq_mfderiv_of_mdiff cut e t hcut_mdiff he_cont.continuousAt he_diff).trans
    (congrArg (mfderiv 𝓘(ℂ) 𝓘(ℂ) cut (e t)) (pathSpeed_modelPath_eq_deriv e t))

end Jacobians
