/-
# Continuous square-root branches of analytic functions are analytic

`analyticAt_of_sq_eq_analytic`: if `y : ℝ → ℂ` is continuous at `t₀`,
`y t ^ 2 = g t` near `t₀` for an analytic `g`, and `y t₀ ≠ 0`, then `y` is
real-analytic at `t₀`.

Proof: near a nonzero value `c = g t₀` there is an explicit analytic local
square-root branch `φ t = y t₀ · exp(½ log(g t / c))`; near `t₀` both `y`
and `φ` square to `g` while `y + φ` is continuous and nonzero at `t₀`
(value `2 y t₀`), so `y = φ` on a neighborhood and `y` inherits `φ`'s
analyticity. No connectedness/monodromy input is needed — this is purely
local.

Consumed by the hyperelliptic cycle constructions
(`ProjectiveCurve/Hyperelliptic/CycleLoops.lean`): a continuous branch
`y` of `√(f ∘ x)` along an analytic branch-locus-avoiding arc (e.g. the
covering-theoretic lift through `sqMap_covering`) is automatically
real-analytic, so requiring only `Continuous y` in `SqrtArcData` loses no
analytic strength.
-/
import Mathlib

namespace Jacobians.GeneralResults

open Complex
open scoped Topology

/-- A continuous, locally nonvanishing square root of a real-analytic
`ℂ`-valued function is real-analytic. -/
theorem analyticAt_of_sq_eq_analytic {g y : ℝ → ℂ} {t₀ : ℝ}
    (hg : AnalyticAt ℝ g t₀) (hy : ContinuousAt y t₀)
    (hsq : ∀ᶠ t in 𝓝 t₀, y t ^ 2 = g t) (hne : y t₀ ≠ 0) :
    AnalyticAt ℝ y t₀ := by
  have hsq0 : y t₀ ^ 2 = g t₀ := hsq.self_of_nhds
  have hg0 : g t₀ ≠ 0 := by
    rw [← hsq0]
    exact pow_ne_zero 2 hne
  set c : ℂ := g t₀ with hc
  -- the explicit local branch
  set φ : ℝ → ℂ := fun t => y t₀ * Complex.exp ((1 / 2 : ℂ) * Complex.log (g t / c))
    with hφ_def
  -- φ is analytic at t₀
  have hinner : AnalyticAt ℝ (fun t : ℝ => g t / c) t₀ := by
    simpa [div_eq_mul_inv] using hg.mul (analyticAt_const (v := c⁻¹))
  have hinner_val : (fun t : ℝ => g t / c) t₀ = 1 := by
    change g t₀ / c = 1
    rw [← hc]
    exact div_self hg0
  have hlog : AnalyticAt ℝ (fun t : ℝ => Complex.log (g t / c)) t₀ := by
    have h1 : AnalyticAt ℂ Complex.log (1 : ℂ) :=
      analyticAt_clog (by simp [Complex.slitPlane] : (1 : ℂ) ∈ Complex.slitPlane)
    exact (h1.restrictScalars (𝕜 := ℝ)).comp_of_eq hinner hinner_val
  have hφ : AnalyticAt ℝ φ t₀ := by
    have hexp : AnalyticAt ℝ
        (fun t : ℝ => Complex.exp ((1 / 2 : ℂ) * Complex.log (g t / c))) t₀ :=
      (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
        (analyticAt_const.mul hlog)
    exact analyticAt_const.mul hexp
  -- φ t₀ = y t₀
  have hφ0 : φ t₀ = y t₀ := by
    simp [hφ_def, hc]
  -- eventually g ≠ 0, hence eventually φ² = g
  have hg_ne : ∀ᶠ t in 𝓝 t₀, g t ≠ 0 :=
    hg.continuousAt.eventually_ne hg0
  have hφ_sq : ∀ᶠ t in 𝓝 t₀, φ t ^ 2 = g t := by
    filter_upwards [hg_ne] with t hgt
    have hw : g t / c ≠ 0 := div_ne_zero hgt hg0
    have : φ t ^ 2 = y t₀ ^ 2 * Complex.exp ((1 / 2 : ℂ) * Complex.log (g t / c)) ^ 2 := by
      rw [hφ_def]; ring
    rw [this, ← Complex.exp_nat_mul]
    have harg : (2 : ℕ) * ((1 / 2 : ℂ) * Complex.log (g t / c)) =
        Complex.log (g t / c) := by
      push_cast; ring
    rw [harg, Complex.exp_log hw, hsq0]
    field_simp
  -- eventually y + φ ≠ 0 (continuity, value 2·y t₀ ≠ 0)
  have hsum_cont : ContinuousAt (fun t => y t + φ t) t₀ :=
    hy.add hφ.continuousAt
  have hsum_ne : ∀ᶠ t in 𝓝 t₀, y t + φ t ≠ 0 := by
    apply hsum_cont.eventually_ne
    rw [hφ0]
    simpa [two_mul] using mul_ne_zero (two_ne_zero (α := ℂ)) hne
  -- hence eventually y = φ
  have heq : ∀ᶠ t in 𝓝 t₀, y t = φ t := by
    filter_upwards [hsq, hφ_sq, hsum_ne] with t h1 h2 h3
    have hfactor : (y t - φ t) * (y t + φ t) = 0 := by
      have hsq_eq : y t ^ 2 = φ t ^ 2 := by rw [h1, h2]
      linear_combination hsq_eq
    rcases mul_eq_zero.mp hfactor with h | h
    · linear_combination h
    · exact absurd h h3
  exact hφ.congr (heq.mono fun t ht => ht.symm)

end Jacobians.GeneralResults
