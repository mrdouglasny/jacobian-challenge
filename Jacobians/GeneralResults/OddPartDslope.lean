/-
# Analytic odd-part difference quotient

A small, curve-independent complex-analysis fact used in the hyperelliptic
anti-invariance proof (route D, `docs/anti-invariance-route-decision.md`):
for `h` analytic at `0`, the difference quotient of the odd part
`w ↦ (h w − h(−w))/w` extends analytically across `0`.

This is the cancellation behind branch-point removability: on a hyperelliptic
curve the two sheets contribute `coeff = h(±√f)·(±f'/(2√f))`, whose sum is
`(f'/(2√f))·(h(√f) − h(−√f)) = (f'/2)·dslope(oddPart)(√f)` — the `1/√f`
singularity cancels because the odd part vanishes to order ≥ 1.
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Basic

namespace Jacobians.GeneralResults

open scoped Topology

/-- The odd part `w ↦ h w − h (−w)` of an analytic function is analytic at `0`
and vanishes there. -/
theorem analyticAt_oddPart {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) :
    AnalyticAt ℂ (fun w => h w - h (-w)) 0 := by
  have hneg : AnalyticAt ℂ (fun w : ℂ => h (-w)) 0 := by
    have hcomp : AnalyticAt ℂ (h ∘ fun w : ℂ => -w) 0 := by
      apply AnalyticAt.comp
      · show AnalyticAt ℂ h ((fun w : ℂ => -w) 0); simpa using hh
      · exact (analyticAt_id (𝕜 := ℂ) (z := (0 : ℂ))).neg
    simpa [Function.comp] using hcomp
  exact hh.sub hneg

/-- **Odd-part difference quotient is analytic.** For `h` analytic at `0`,
`dslope (oddPart h) 0` is analytic at `0`; for `w ≠ 0` it equals
`(h w − h (−w)) / w`. -/
theorem analyticAt_dslope_oddPart {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) :
    AnalyticAt ℂ (dslope (fun w => h w - h (-w)) 0) 0 := by
  obtain ⟨p, hp⟩ := analyticAt_oddPart hh
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- The difference-quotient value: for `w ≠ 0`,
`dslope (oddPart h) 0 w = (h w − h (−w)) / w`. -/
theorem dslope_oddPart_of_ne {h : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0) :
    dslope (fun w => h w - h (-w)) 0 w = (h w - h (-w)) / w := by
  rw [dslope_of_ne (fun w => h w - h (-w)) hw, slope_def_field]
  simp

end Jacobians.GeneralResults
