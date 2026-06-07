/-
Copyright (c) 2026 Michal J Wallace. All rights reserved.
Released under the MIT license (the upstream repository LICENSE; © Michal J Wallace).
Original source: https://github.com/tangentstorm/JacobianChallenge
                 Jacobian/Periods/CurveIntegralSubpath.lean (commit 82349bc8, 2026-06-01).
Note: the upstream repo LICENSE is MIT; on full adoption, vendor the upstream
LICENSE under `vendor/wallace-jacobian-challenge/`.

Vendored (trial) into this repository on 2026-06-02 by Michael R Douglas.
Modifications relative to upstream:
- Renamespaced under `Jacobians.Vendor.Wallace.*`.
- Internal imports retargeted to the vendored module paths.
No other mathematical content was altered.
-/

import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import Mathlib.Topology.Subpath
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.CompMul

set_option linter.unusedSectionVars false

/-!
# Reparameterisation: `curveIntegral` of a `Path.subpath`

States that integrating a 1-form along a subpath `γ.subpath t₀ t₁`
agrees with the interval integral of the same integrand over the
sub-interval `[t₀, t₁]` in parameter space:

`curveIntegral ω (γ.subpath t₀ t₁) =
     ∫ t in (t₀ : ℝ)..(t₁ : ℝ),
        ω (γ.extend t) (derivWithin γ.extend (Set.Icc 0 1) t)`.

This is the change-of-variables identity for the affine
reparameterisation `s ↦ (1-s)·t₀ + s·t₁` underlying `Path.subpath`,
applied to Mathlib's `curveIntegral`.

## Strategy

For the orientation `t₀ ≤ t₁`:

1. Trivial case `t₀ = t₁`: the subpath is `Path.refl`, both sides
   are `0` (`curveIntegral_refl` and `intervalIntegral.integral_same`).

2. Strict inequality `t₀ < t₁`: by the affine reparameterisation
   `φ(s) = t₀ + (t₁ - t₀)·s`, on the open interval `s ∈ (0, 1)` the
   subpath's `extend` agrees with `γ.extend ∘ φ` on a full
   neighbourhood of `s`. Taking advantage of the fact that for
   `s ∈ Ioo 0 1` and `φ s ∈ Ioo t₀ t₁ ⊆ Ioo 0 1`, both `Icc 0 1`-derivatives
   collapse to the unrestricted `deriv`, the chain rule
   (`deriv_comp_mul_left` + `deriv_comp_const_add`) gives
   `deriv (γ.subpath ⋯).extend s = (t₁ - t₀) • deriv γ.extend (φ s)`
   without any differentiability assumption. Linearity of `ω`
   factors out the scalar.

3. The `(t₁ - t₀) •`-pulled integrand on `[0, 1]` is then
   reparameterised to `[t₀, t₁]` via
   `intervalIntegral.smul_integral_comp_add_mul`.
-/

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.flexible false
set_option linter.unusedSectionVars false

namespace Jacobians.Vendor.Wallace.Periods

open Set MeasureTheory Path Filter
open scoped unitInterval Topology

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]

section SubpathExtend

variable {a b : E}

omit [NormedSpace ℝ E] in
/--
For `s ∈ Icc 0 1`, the extended subpath agrees with the affine
reparameterisation of `γ.extend`.
-/
lemma subpath_extend_eq_extend_affine
    (γ : Path a b) (t₀ t₁ : unitInterval) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (γ.subpath t₀ t₁).extend s =
      γ.extend ((1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ)) := by
  have hrange : (1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : 0 ≤ 1 - s := by linarith [hs.2]
    have hs1 : 0 ≤ s := hs.1
    refine ⟨?_, ?_⟩
    · nlinarith [t₀.2.1, t₁.2.1]
    · nlinarith [t₀.2.2, t₁.2.2]
  rw [Path.extend_apply _ hs, Path.extend_apply _ hrange]
  -- (γ.subpath t₀ t₁) ⟨s, hs⟩ = γ (subpathAux t₀ t₁ ⟨s, hs⟩) by definition,
  -- and `subpathAux t₀ t₁ ⟨s, hs⟩` has the right val by Subtype proof-irrelevance.
  rfl

omit [NormedSpace ℝ E] in
/--
For `s ∈ (0, 1)` (strict interior), the extended subpath
eventually equals the affine reparameterisation of `γ.extend` in a
neighbourhood of `s` in ℝ.
-/
lemma subpath_extend_eventuallyEq
    (γ : Path a b) (t₀ t₁ : unitInterval) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    (γ.subpath t₀ t₁).extend =ᶠ[𝓝 s]
      fun u => γ.extend ((1 - u) * (t₀ : ℝ) + u * (t₁ : ℝ)) := by
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu using
    subpath_extend_eq_extend_affine γ t₀ t₁ ⟨le_of_lt hu.1, le_of_lt hu.2⟩

end SubpathExtend

/--
Curve integral over a `Path.subpath` reduces to the interval
integral of the original path's integrand over the sub-interval
`[t₀, t₁]`.

Stated for the orientation `t₀ ≤ t₁`; the reverse orientation
follows from `curveIntegral_symm` + `Path.symm_subpath`.
-/
theorem curveIntegral_subpath_of_le
    {a b : E} (ω : E → E →L[𝕜] F) (γ : Path a b)
    (t₀ t₁ : unitInterval) (hle : t₀ ≤ t₁) :
    curveIntegral ω (γ.subpath t₀ t₁) =
      ∫ t in (t₀ : ℝ)..(t₁ : ℝ),
        ω (γ.extend t) (derivWithin γ.extend (Set.Icc 0 1) t) := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- Trivial case t₀ = t₁: both sides are zero.
    subst heq
    rw [Path.subpath_self, curveIntegral_refl, intervalIntegral.integral_same]
  -- Strict case t₀ < t₁
  have ht_real : (t₀ : ℝ) < (t₁ : ℝ) := hlt
  have ht_diff_pos : (0 : ℝ) < (t₁ : ℝ) - (t₀ : ℝ) := sub_pos.mpr ht_real
  -- Affine reparameterisation φ
  let φ : ℝ → ℝ := fun s => (t₀ : ℝ) + ((t₁ : ℝ) - (t₀ : ℝ)) * s
  have h_affine : ∀ s : ℝ,
      (1 - s) * (t₀ : ℝ) + s * (t₁ : ℝ) = φ s := fun s => by simp [φ]; ring
  -- φ maps Ioo 0 1 into Ioo t₀ t₁
  have h_phi_Ioo : ∀ {s : ℝ}, s ∈ Set.Ioo (0 : ℝ) 1 → φ s ∈ Set.Ioo (t₀ : ℝ) (t₁ : ℝ) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · simp only [φ]; nlinarith [hs.1, ht_diff_pos]
    · simp only [φ]; nlinarith [hs.2, ht_diff_pos]
  -- For interior s, extends agree on a neighbourhood.
  have h_Icc01_in_nhds : ∀ {x : ℝ}, x ∈ Set.Ioo (0 : ℝ) 1 →
      Set.Icc (0 : ℝ) 1 ∈ 𝓝 x := fun {x} hx =>
    mem_of_superset (Ioo_mem_nhds hx.1 hx.2) Set.Ioo_subset_Icc_self
  have h_Icc01_in_nhds_t : ∀ {x : ℝ}, x ∈ Set.Ioo (t₀ : ℝ) (t₁ : ℝ) →
      Set.Icc (0 : ℝ) 1 ∈ 𝓝 x := fun {x} hx =>
    h_Icc01_in_nhds ⟨lt_of_le_of_lt t₀.2.1 hx.1, lt_of_lt_of_le hx.2 t₁.2.2⟩
  -- Key reparameterisation step.
  have key : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      curveIntegralFun ω (γ.subpath t₀ t₁) s =
        ((t₁ : ℝ) - (t₀ : ℝ)) • curveIntegralFun ω γ (φ s) := by
    intro s hs
    -- Eventual equality of γ.subpath.extend with γ.extend ∘ φ at s
    have heventEq : (γ.subpath t₀ t₁).extend =ᶠ[𝓝 s] (fun u => γ.extend (φ u)) := by
      have hev := subpath_extend_eventuallyEq γ t₀ t₁ hs
      filter_upwards [hev] with u hu
      rw [hu, h_affine]
    have hval : (γ.subpath t₀ t₁).extend s = γ.extend (φ s) := heventEq.self_of_nhds
    -- Replace derivWithin with deriv at interior points.
    have hderivWithin_subpath : derivWithin (γ.subpath t₀ t₁).extend (Set.Icc 0 1) s =
        deriv (γ.subpath t₀ t₁).extend s := derivWithin_of_mem_nhds (h_Icc01_in_nhds hs)
    have hderivWithin_at_phi : derivWithin γ.extend (Set.Icc 0 1) (φ s) =
        deriv γ.extend (φ s) := derivWithin_of_mem_nhds (h_Icc01_in_nhds_t (h_phi_Ioo hs))
    -- Eventual equality preserves deriv (since equality on 𝓝 s).
    have hderiv_subst : deriv (γ.subpath t₀ t₁).extend s =
        deriv (fun u => γ.extend (φ u)) s :=
      Filter.EventuallyEq.deriv_eq heventEq
    -- Chain rule for affine map: deriv (γ.extend ∘ φ) = (t₁-t₀) • deriv γ.extend (φ s)
    have hderiv_chain : deriv (fun u => γ.extend (φ u)) s =
        ((t₁ : ℝ) - (t₀ : ℝ)) • deriv γ.extend (φ s) := by
      have hφ : (fun u => γ.extend (φ u)) =
          (fun u => γ.extend ((t₀ : ℝ) + u)) ∘ (fun u => ((t₁ : ℝ) - (t₀ : ℝ)) * u) := by
        funext u; rfl
      rw [hφ, Function.comp_def]
      rw [deriv_comp_mul_left ((t₁ : ℝ) - (t₀ : ℝ)) (fun u => γ.extend ((t₀ : ℝ) + u)) s]
      congr 1
      rw [deriv_comp_const_add γ.extend (t₀ : ℝ)]
    -- Combine
    rw [curveIntegralFun_def, hval, hderivWithin_subpath, hderiv_subst, hderiv_chain,
        ← hderivWithin_at_phi, (ω _).map_smul_of_tower, curveIntegralFun_def]
  -- ae-version of key.
  have key_ae : (curveIntegralFun ω (γ.subpath t₀ t₁)) =ᵐ[volume.restrict (Set.uIoc (0:ℝ) 1)]
      fun s => ((t₁ : ℝ) - (t₀ : ℝ)) • curveIntegralFun ω γ (φ s) := by
    rw [Set.uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs using key s hs
  -- Bridge to intervalIntegral
  rw [curveIntegral_def]
  rw [intervalIntegral.integral_congr_ae_restrict key_ae]
  rw [intervalIntegral.integral_smul]
  -- (t₁-t₀) • ∫ s in 0..1, curveIntegralFun ω γ (φ s)
  have hsub := intervalIntegral.smul_integral_comp_add_mul
    (f := curveIntegralFun ω γ) (a := (0 : ℝ)) (b := 1)
    ((t₁ : ℝ) - (t₀ : ℝ)) (t₀ : ℝ)
  rw [show (fun s => curveIntegralFun ω γ (φ s)) =
      (fun x => curveIntegralFun ω γ ((t₀ : ℝ) + ((t₁ : ℝ) - (t₀ : ℝ)) * x)) from rfl]
  rw [hsub]
  -- Bounds rewrite: t₀ + (t₁-t₀)*0 = t₀, t₀ + (t₁-t₀)*1 = t₁
  have hlb : (t₀ : ℝ) + ((t₁ : ℝ) - (t₀ : ℝ)) * 0 = (t₀ : ℝ) := by ring
  have hub : (t₀ : ℝ) + ((t₁ : ℝ) - (t₀ : ℝ)) * 1 = (t₁ : ℝ) := by ring
  rw [hlb, hub]
  -- Final: integrand congruence via curveIntegralFun_def
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [curveIntegralFun_def]

end Jacobians.Vendor.Wallace.Periods
