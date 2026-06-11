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

/-- **Constructive global square-root branch.** If `g : ℝ → ℂ` is analytic
and nonvanishing everywhere, then for any square root `y₀` of `g 0` there is
a continuous global branch `y` with `y² = g`, given explicitly by the
log-derivative primitive: `y t = y₀ · exp(½ ∫₀ᵗ g′/g)`.

(Proof: `L t = ∫₀ᵗ g′/g` satisfies `(g · exp(−L))′ = 0`, so
`g t = g 0 · exp(L t)` and `y = y₀ · exp(L/2)` squares to `g`.)

The closed formula is part of the conclusion so that *loop closure* of the
branch (`y 1 = y 0`) reduces to evaluating the explicit winding integral
`∫₀¹ g′/g ∈ 4πi ℤ` — the argument-principle input for the hyperelliptic
branch-cut cycles. -/
theorem exists_sqrt_branch {g : ℝ → ℂ} (hg : ∀ t, AnalyticAt ℝ g t)
    (hne : ∀ t, g t ≠ 0) {y₀ : ℂ} (hy₀ : y₀ ^ 2 = g 0) :
    ∃ y : ℝ → ℂ, Continuous y ∧ y 0 = y₀ ∧ (∀ t, y t ^ 2 = g t) ∧
      ∀ t, y t =
        y₀ * Complex.exp ((∫ s in (0 : ℝ)..t, deriv g s / g s) / 2) := by
  classical
  set q : ℝ → ℂ := fun s => deriv g s / g s with hq_def
  have hg_cont : Continuous g :=
    continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt
  have hderiv_cont : Continuous (deriv g) :=
    continuous_iff_continuousAt.mpr fun t => ((hg t).deriv).continuousAt
  have hq_cont : Continuous q := hderiv_cont.div hg_cont hne
  set L : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, q s with hL_def
  have hL : ∀ t : ℝ, HasDerivAt L (q t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hq_cont.intervalIntegrable 0 t)
      (hq_cont.stronglyMeasurableAtFilter _ _)
      hq_cont.continuousAt
  have hL0 : L 0 = 0 := intervalIntegral.integral_same
  have hLcont : Continuous L :=
    continuous_iff_continuousAt.mpr fun t => (hL t).continuousAt
  -- the conserved quantity h = g · exp(−L)
  set h : ℝ → ℂ := fun t => g t * Complex.exp (-L t) with hh_def
  have hh' : ∀ t : ℝ, HasDerivAt h 0 t := by
    intro t
    have hgd : HasDerivAt g (deriv g t) t := (hg t).differentiableAt.hasDerivAt
    have hLd : HasDerivAt (fun u => -L u) (-q t) t := (hL t).neg
    have hexp : HasDerivAt (fun u => Complex.exp (-L u))
        (Complex.exp (-L t) * -q t) t := hLd.cexp
    have hmul := hgd.mul hexp
    convert hmul using 1
    rw [hq_def]
    field_simp [hne t]
    ring
  have hh_const : ∀ t : ℝ, h t = h 0 := by
    intro t
    exact is_const_of_deriv_eq_zero
      (fun u => ((hh' u).differentiableAt : DifferentiableAt ℝ h u))
      (fun u => (hh' u).deriv) t 0
  have hg_eq : ∀ t : ℝ, g t = g 0 * Complex.exp (L t) := by
    intro t
    have h1 : g t * Complex.exp (-L t) = g 0 := by
      have h2 := hh_const t
      simp only [hh_def, hL0, neg_zero, Complex.exp_zero, mul_one] at h2
      exact h2
    calc g t = g t * (Complex.exp (-L t) * Complex.exp (L t)) := by
          rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
      _ = g 0 * Complex.exp (L t) := by rw [← mul_assoc, h1]
  refine ⟨fun t => y₀ * Complex.exp (L t / 2), ?_, ?_, ?_, fun t => rfl⟩
  · exact continuous_const.mul (Complex.continuous_exp.comp (hLcont.div_const 2))
  · simp [hL0]
  · intro t
    change (y₀ * Complex.exp (L t / 2)) ^ 2 = g t
    have hsq : (y₀ * Complex.exp (L t / 2)) ^ 2 = y₀ ^ 2 * Complex.exp (L t) := by
      have : Complex.exp (L t / 2) ^ 2 = Complex.exp (L t) := by
        rw [sq, ← Complex.exp_add]
        norm_num
      rw [mul_pow, this]
    rw [hsq, hy₀, ← hg_eq t]

end Jacobians.GeneralResults
