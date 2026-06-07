/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Discharge.Manifold.LocalNormalForm

/-! # Discharge of the disk argument-principle integral

This file proves `argumentPrinciple_disk_statement` from `LocalNormalForm.lean`,
the single irreducible analytic atom of the residue theorem. The statement is the
classical **argument principle**, specialised to a zero of order `k` at the origin
(Forster §4 / Cor. 4.25):

> For `g : ℂ → ℂ` analytic at `0` with `analyticOrderAt g 0 = k`, there is
> `ε₀ > 0` such that for all `ε ∈ (0, ε₀)`,
>   `(2πi)⁻¹ · ∫₀^{2π} (g'(εe^{iθ})/g(εe^{iθ})) · (iε e^{iθ}) dθ = k`.

## Proof outline

1. Factor `g =ᶠ[𝓝 0] (· - 0)^k • u` with `u` analytic at `0` and `u 0 ≠ 0`
   (`AnalyticAt.analyticOrderAt_eq_natCast`).
2. Choose `ε₀ > 0` so small that on `closedBall 0 ε₀`: `u` is analytic, `u ≠ 0`,
   and the factorization `g = (·)^k • u` holds pointwise.
3. On the circle `|z| = ε` (so `z ≠ 0`, `u z ≠ 0`) the log-derivative splits:
   `deriv g z / g z = k • z⁻¹ + deriv u z / u z`.
4. Convert the parametrised integral to a `circleIntegral` and split:
   `∮ deriv g/g = k · (∮ z⁻¹) + (∮ deriv u/u) = k · 2πi + 0`.
   (`circleIntegral.integral_sub_inv_of_mem_ball`, and
   `argumentPrinciple_disk_zero_case` for the `u'/u` leg.)
5. Multiply by `(2πi)⁻¹` to read off `k`.

The `k = 0` case is the zero-free disk directly (`argumentPrinciple_disk_zero_case`).

The only Mathlib `circleIntegral` content used for the `k/z` contour is
`circleIntegral.integral_sub_inv_of_mem_ball` (NOT any Dolbeault lemma), keeping
this file independent of the concurrently-developed Dolbeault / Čech stack. -/

open scoped Real
open Complex Metric Set intervalIntegral

namespace Jacobians.Discharge.MMeromorphicAt

/-- The parametrised integral appearing in `argumentPrinciple_disk_statement`
equals the `circleIntegral` of the logarithmic derivative `deriv g / g` around
`C(0, ε)`. This is a pure reparametrisation: `circleMap 0 ε θ = ε e^{iθ}` and
`deriv (circleMap 0 ε) θ = ε i e^{iθ}`, with `•` on `ℂ` being `*` and
`exp (I * θ) = exp (θ * I)` by commutativity. -/
theorem parametrized_eq_circleIntegral (g : ℂ → ℂ) (ε : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * π),
        (deriv g (ε * Complex.exp (Complex.I * θ)) /
         g (ε * Complex.exp (Complex.I * θ))) *
        (ε * Complex.I * Complex.exp (Complex.I * θ)))
      = (∮ z in C((0 : ℂ), ε), deriv g z / g z) := by
  rw [circleIntegral]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [deriv_circleMap, circleMap, zero_add, smul_eq_mul]
  rw [mul_comm Complex.I (θ : ℂ)]
  ring

/-- **The disk argument-principle integral** (`k = 0` slice, zero-free disk).

If `g` is analytic and nonzero on `closedBall 0 ε`, the parametrised integral of
the log-derivative vanishes; multiplied by `(2πi)⁻¹` it is `0 = (k : ℂ)` for
`k = 0`. -/
theorem argumentPrinciple_parametrized_zero
    {g : ℂ → ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall 0 ε))
    (hne : ∀ z ∈ Metric.closedBall (0 : ℂ) ε, g z ≠ 0) :
    (2 * π * Complex.I)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * π),
        (deriv g (ε * Complex.exp (Complex.I * θ)) /
         g (ε * Complex.exp (Complex.I * θ))) *
        (ε * Complex.I * Complex.exp (Complex.I * θ))
      = 0 := by
  rw [parametrized_eq_circleIntegral, argumentPrinciple_disk_zero_case hε hg hne, mul_zero]

/-- **The disk argument-principle integral identity** (`k ≥ 1` core).

For `g = (·)^k • u` (eventually near `0`) with `u` analytic and nonzero on
`closedBall 0 ε` (and the factorization holding pointwise on `ball 0 δ ⊇ closedBall 0 ε`),
the contour integral of the log-derivative equals `2πi · k`.

This is the analytic heart of the argument principle. -/
theorem circleIntegral_logDeriv_eq
    {g u : ℂ → ℂ} {k : ℕ} (hk : 1 ≤ k) {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ)
    (hu_an : ∀ z ∈ Metric.ball (0 : ℂ) δ, AnalyticAt ℂ u z)
    (hu_ne : ∀ z ∈ Metric.closedBall (0 : ℂ) ε, u z ≠ 0)
    (hfac : ∀ z ∈ Metric.ball (0 : ℂ) δ, g z = z ^ k • u z) :
    (∮ z in C((0 : ℂ), ε), deriv g z / g z) = 2 * π * Complex.I * (k : ℂ) := by
  -- `u` is analytic on a neighborhood of the closed ball of radius `ε`.
  have hu_anOn : AnalyticOnNhd ℂ u (Metric.closedBall 0 ε) := fun z hz =>
    hu_an z (closedBall_subset_ball hεδ hz)
  -- On the sphere `|z| = ε` the log-derivative splits as `k • z⁻¹ + deriv u z / u z`.
  have hsplit : Set.EqOn (fun z => deriv g z / g z)
      (fun z => (k : ℂ) • z⁻¹ + deriv u z / u z) (Metric.sphere (0 : ℂ) ε) := by
    intro z hz
    have hzball : z ∈ Metric.ball (0 : ℂ) δ := by
      rw [Metric.mem_sphere] at hz
      rw [Metric.mem_ball]; simpa [hz] using hεδ
    -- `z ≠ 0` (radius positive) and `u z ≠ 0`.
    have hz0 : z ≠ 0 := by
      rw [Metric.mem_sphere] at hz
      intro h; rw [h] at hz; simp at hz; exact hε.ne hz
    have hzcb : z ∈ Metric.closedBall (0 : ℂ) ε := by
      rw [Metric.mem_sphere] at hz; rw [Metric.mem_closedBall, hz]
    have huz : u z ≠ 0 := hu_ne z hzcb
    -- `deriv g z = deriv (fun w => w^k • u w) z` since `g = (·)^k • u` on the open ball.
    have hgeq : g =ᶠ[nhds z] (fun w => w ^ k • u w) := by
      filter_upwards [(Metric.isOpen_ball.eventually_mem hzball)] with w hw
      exact hfac w hw
    have hderiv_g : deriv g z = (k : ℂ) * z ^ (k - 1) * u z + z ^ k * deriv u z := by
      rw [hgeq.deriv_eq]
      have huHasDeriv : HasDerivAt u (deriv u z) z :=
        (hu_an z hzball).differentiableAt.hasDerivAt
      have hpow : HasDerivAt (fun w : ℂ => w ^ k) ((k : ℂ) * z ^ (k - 1)) z := by
        simpa using hasDerivAt_pow k z
      simp only [smul_eq_mul]
      exact (hpow.mul huHasDeriv).deriv
    -- `g z = z^k * u z ≠ 0`.
    have hgz : g z = z ^ k * u z := by rw [hfac z hzball, smul_eq_mul]
    -- the algebraic split.
    simp only [smul_eq_mul]
    rw [hderiv_g, hgz]
    have hzk : z ^ k = z * z ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      ring
    rw [hzk]; field_simp
  -- Rewrite the integral using the split.
  rw [circleIntegral.integral_congr hε.le hsplit]
  -- `z⁻¹` and `deriv u / u` are continuous on the sphere, hence circle-integrable.
  have hsphere_cb : Metric.sphere (0 : ℂ) ε ⊆ Metric.closedBall (0 : ℂ) ε :=
    Metric.sphere_subset_closedBall
  have hinv_cont : ContinuousOn (fun z : ℂ => (k : ℂ) • z⁻¹) (Metric.sphere (0 : ℂ) ε) := by
    refine (continuousOn_const).smul (ContinuousOn.inv₀ continuousOn_id ?_)
    intro z hz
    rw [Metric.mem_sphere] at hz
    intro h; rw [h] at hz; simp at hz; exact hε.ne hz
  have hquot_cont : ContinuousOn (fun z : ℂ => deriv u z / u z) (Metric.sphere (0 : ℂ) ε) := by
    have hd : AnalyticOnNhd ℂ (deriv u) (Metric.closedBall 0 ε) := hu_anOn.deriv
    refine ContinuousOn.div (hd.continuousOn.mono hsphere_cb)
      (hu_anOn.continuousOn.mono hsphere_cb) ?_
    intro z hz; exact hu_ne z (hsphere_cb hz)
  have hint_inv : CircleIntegrable (fun z : ℂ => (k : ℂ) • z⁻¹) 0 ε :=
    hinv_cont.circleIntegrable hε.le
  have hint_quot : CircleIntegrable (fun z : ℂ => deriv u z / u z) 0 ε :=
    hquot_cont.circleIntegrable hε.le
  -- Split the sum.
  rw [circleIntegral.integral_add hint_inv hint_quot]
  -- `∮ k • z⁻¹ = k • (∮ z⁻¹) = k • 2πi`; note `z⁻¹ = (z - 0)⁻¹`.
  have hinv_eval : (∮ z in C((0 : ℂ), ε), (k : ℂ) • z⁻¹) = (k : ℂ) • (2 * π * Complex.I) := by
    rw [circleIntegral.integral_smul]
    congr 1
    have : (∮ z in C((0 : ℂ), ε), (z - 0)⁻¹) = 2 * ↑π * Complex.I :=
      circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hε)
    simpa using this
  -- `∮ deriv u / u = 0` (zero-free disk for `u`).
  have hquot_eval : (∮ z in C((0 : ℂ), ε), deriv u z / u z) = 0 :=
    argumentPrinciple_disk_zero_case hε.le hu_anOn hu_ne
  rw [hinv_eval, hquot_eval, smul_eq_mul, add_zero]
  ring

/-- **The disk argument-principle integral** — full discharge of
`argumentPrinciple_disk_statement` from `LocalNormalForm.lean`.

This is the single irreducible analytic atom of the residue theorem `deg_div`.
The proof is the classical argument principle centred at `0`. -/
theorem argumentPrinciple_disk_statement_holds (k : ℕ) (g : ℂ → ℂ) :
    argumentPrinciple_disk_statement k g := by
  rintro ⟨hg, hord⟩
  -- Factor `g =ᶠ[𝓝 0] (· - 0)^k • u` with `u` analytic at `0`, `u 0 ≠ 0`.
  obtain ⟨u, hu, hu0, hueq⟩ := (hg.analyticOrderAt_eq_natCast (n := k)).mp hord
  -- `g z = z^k • u z` eventually near `0` (since `z - 0 = z`).
  have hueq' : g =ᶠ[nhds (0 : ℂ)] (fun z => z ^ k • u z) := by
    filter_upwards [hueq] with z hz using by simpa using hz
  -- Pull a radius `δ_fac` where the factorization holds pointwise.
  obtain ⟨δ_fac, hδ_fac_pos, hδ_fac⟩ :=
    eventually_nhds_iff_ball.mp hueq'
  -- `u` is analytic on a ball `δ_an`.
  obtain ⟨δ_an, hδ_an_pos, hδ_an⟩ :=
    eventually_nhds_iff_ball.mp hu.eventually_analyticAt
  -- `u ≠ 0` on a ball `δ_ne` (continuity + `u 0 ≠ 0`).
  obtain ⟨δ_ne, hδ_ne_pos, hδ_ne⟩ :=
    eventually_nhds_iff_ball.mp (hu.continuousAt.eventually_ne hu0)
  -- Choose `δ := min` of the three (positive) and `ε₀ := δ / 2 < δ`.
  set δ : ℝ := min δ_fac (min δ_an δ_ne) with hδdef
  have hδ_pos : 0 < δ := lt_min hδ_fac_pos (lt_min hδ_an_pos hδ_ne_pos)
  have hδ_le_fac : δ ≤ δ_fac := min_le_left _ _
  have hδ_le_an : δ ≤ δ_an := (min_le_right _ _).trans (min_le_left _ _)
  have hδ_le_ne : δ ≤ δ_ne := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ / 2, by positivity, fun ε hε => ?_⟩
  obtain ⟨hε_pos, hε_lt⟩ := hε
  have hεδ : ε < δ := hε_lt.trans (by linarith)
  -- Repackage the three ball facts at radius `δ`.
  have hu_an_ball : ∀ z ∈ Metric.ball (0 : ℂ) δ, AnalyticAt ℂ u z := fun z hz =>
    hδ_an z (Metric.ball_subset_ball hδ_le_an hz)
  have hfac_ball : ∀ z ∈ Metric.ball (0 : ℂ) δ, g z = z ^ k • u z := fun z hz =>
    hδ_fac z (Metric.ball_subset_ball hδ_le_fac hz)
  have hu_ne_cb : ∀ z ∈ Metric.closedBall (0 : ℂ) ε, u z ≠ 0 := fun z hz =>
    hδ_ne z (Metric.ball_subset_ball hδ_le_ne (closedBall_subset_ball hεδ hz))
  -- Reduce to the parametrization identity, then to the core contour integral.
  rw [parametrized_eq_circleIntegral]
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · -- `k = 0`: `g = u` is nonzero on the disk, the integral vanishes, and `(k:ℂ) = 0`.
    subst hk0
    have hg_anOn : AnalyticOnNhd ℂ g (Metric.closedBall 0 ε) := by
      intro z hz
      have hzb : z ∈ Metric.ball (0 : ℂ) δ := closedBall_subset_ball hεδ hz
      have : g =ᶠ[nhds z] u := by
        filter_upwards [Metric.isOpen_ball.eventually_mem hzb] with w hw
        simpa using hfac_ball w hw
      exact (hu_an_ball z hzb).congr this.symm
    have hg_ne : ∀ z ∈ Metric.closedBall (0 : ℂ) ε, g z ≠ 0 := by
      intro z hz
      have hzb : z ∈ Metric.ball (0 : ℂ) δ := closedBall_subset_ball hεδ hz
      rw [hfac_ball z hzb]; simpa using hu_ne_cb z hz
    rw [argumentPrinciple_disk_zero_case hε_pos.le hg_anOn hg_ne]
    simp
  · -- `k ≥ 1`: the core contour identity, then divide by `2πi`.
    rw [circleIntegral_logDeriv_eq hk1 hε_pos hεδ hu_an_ball hu_ne_cb hfac_ball]
    have h2pi : (2 * (π : ℝ) * Complex.I : ℂ) ≠ 0 := by
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hπ, Complex.I_ne_zero]
    field_simp

end Jacobians.Discharge.MMeromorphicAt
