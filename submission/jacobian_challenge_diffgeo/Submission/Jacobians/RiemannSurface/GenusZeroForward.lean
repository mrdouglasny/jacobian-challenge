/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Submission.Jacobians.RiemannSurface.Cohomology.RiemannRochAPI
import Submission.Jacobians.RiemannSurface.DegreeOneGenusZero

/-!
# Genus zero implies homeomorphic to the 2-sphere (forward uniformization)

Forward leg of `AX_genus_eq_zero_iff_homeo`, by the classical
Riemann–Roch pole-extraction argument (Forster §16/17; Miranda VI):

1. `h0_point_eq_two_of_genus_zero`: at genus `0`, Riemann–Roch at a point
   divisor `(p)` gives `h⁰((p)) = 2` (the dual term `h⁰(K - (p))` dies by
   negative degree, `deg K = -2`).
2. `exists_degreeOne_of_genus_zero`: `L((p))` therefore strictly contains the
   constants `L(0)`, and a non-constant element has principal divisor exactly
   `(Q₁) - (Q₂)` with `Q₁ ≠ Q₂` (degree theorem) — a degree-one function.
3. `nonempty_homeo_sphere_of_genus_eq_zero`: such a function is a
   biholomorphism `X ≃ ℙ¹` (`degreeOne_equiv_projectiveLine`), and
   `ℙ¹ ≃ₜ S²` by stereographic projection, so `X ≃ₜ S²`.

Everything is theorem-grade: the Riemann–Roch input is the keystone-backed
`riemannRoch` (standard-3), no axioms are consumed.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open OnePoint
open Jacobians.Axioms
open Jacobians.ProjectiveCurve

namespace Jacobians.RiemannSurface

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

open MeromorphicFunctionField

/-- Riemann–Roch at a point divisor on a genus-zero surface: `h⁰((p)) = 2`.
The canonical term `h⁰(K - (p))` vanishes since `deg (K - (p)) = -3 < 0`. -/
theorem h0_point_eq_two_of_genus_zero (p : X) (hg : genus X = 0) :
    h0 (FreeAbelianGroup.of p : Divisor X) = 2 := by
  have hRR := riemannRoch (FreeAbelianGroup.of p : Divisor X)
  have hdegP : Divisor.deg X (FreeAbelianGroup.of p : Divisor X) = 1 := by
    simp [Divisor.deg]
  have hKP_neg :
      Divisor.deg X (canonicalDivisor X - FreeAbelianGroup.of p) < 0 := by
    rw [map_sub, canonicalDivisor_deg, hdegP, hg]
    norm_num
  have hKP_h0 : h0 (canonicalDivisor X - FreeAbelianGroup.of p : Divisor X) = 0 := by
    unfold h0
    rw [riemannRochSpace_eq_bot_of_deg_neg' hKP_neg]
    simp
  rw [hdegP, hg, hKP_h0] at hRR
  omega

/-- At genus zero, `L((p))` strictly contains the constants `L(0)`:
there is an `F ∈ L((p))` outside `L(0)`. -/
theorem exists_mem_point_notMem_zero (p : X) (hg : genus X = 0) :
    ∃ F : MeroField X,
      F ∈ riemannRochSpace (FreeAbelianGroup.of p : Divisor X) ∧
        F ∉ riemannRochSpace (0 : Divisor X) := by
  by_contra hcon
  have hle : riemannRochSpace (FreeAbelianGroup.of p : Divisor X) ≤
      riemannRochSpace (0 : Divisor X) := by
    intro F hF
    by_contra hF0
    exact hcon ⟨F, hF, hF0⟩
  have hge : riemannRochSpace (0 : Divisor X) ≤
      riemannRochSpace (FreeAbelianGroup.of p : Divisor X) := by
    refine riemannRochSpace_mono (fun q => ?_)
    simpa using (effective_of (X := X) p q)
  have h1 : h0 (FreeAbelianGroup.of p : Divisor X) = 1 := by
    unfold h0
    rw [le_antisymm hle hge]
    exact h0_zero
  have h2 := h0_point_eq_two_of_genus_zero p hg
  omega

/-- A non-zero `MeroField` element whose principal divisor vanishes lies in
`L(0)` (all its orders are `0`). -/
theorem mem_riemannRochSpace_zero_of_divisorOf_eq_zero {F : MeroField X}
    (hF : F ≠ 0) (h0div : divisorOf hF = 0) :
    F ∈ riemannRochSpace (0 : Divisor X) := by
  intro r
  have hcoeff := coeff_divisorOf hF r
  have hcoeff0 : (orderAtField r F).untop₀ = 0 := by
    rw [h0div] at hcoeff
    simpa using hcoeff.symm
  have hfin := orderAtField_ne_top_of_ne_zero hF r
  rw [← WithTop.coe_untop₀_of_ne_top hfin, hcoeff0]
  norm_num

/-- **Degree-one function at genus zero.** On a compact Riemann surface of
genus zero there is a nonconstant meromorphic function with principal divisor
`(Q₁) - (Q₂)`, `Q₁ ≠ Q₂` — the pole-extraction input of
`degreeOne_equiv_projectiveLine`. -/
theorem exists_degreeOne_of_genus_zero (hg : genus X = 0) :
    ∃ (f : MeromorphicFunctionField X) (Q₁ Q₂ : X),
      Nonconstant f ∧ Q₁ ≠ Q₂ ∧
        divHom f =
          Multiplicative.ofAdd
            ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ :
              FreeAbelianGroup X)) := by
  classical
  obtain ⟨p⟩ := (inferInstance : Nonempty X)
  obtain ⟨F, hFP, hF0⟩ := exists_mem_point_notMem_zero p hg
  have hF : F ≠ 0 := by
    intro h
    exact hF0 (h ▸ (riemannRochSpace (0 : Divisor X)).zero_mem)
  obtain ⟨q, hdiv⟩ := divisorOf_eq_pointSub_of_mem_point hF hFP
  have hqp : q ≠ p := by
    intro h
    apply hF0
    apply mem_riemannRochSpace_zero_of_divisorOf_eq_zero hF
    rw [hdiv, h]
    simp
  -- the bridge element and its divisor
  set f : MeromorphicFunctionField X := toMF hF with hf_def
  have hdivf : MeromorphicFunctionField.divisor f =
      (FreeAbelianGroup.of q - FreeAbelianGroup.of p : Divisor X) := hdiv
  -- order computations from the divisor coefficients
  have hordq : orderAtMF q f = ((1 : ℤ) : WithTop ℤ) := by
    have hcoeff : FreeAbelianGroup.coeff q
        (MeromorphicFunctionField.divisor f : FreeAbelianGroup X) = 1 := by
      rw [hdivf]
      simp [FreeAbelianGroup.coeff, hqp]
    rw [← WithTop.coe_untop₀_of_ne_top (orderAtMF_ne_top f q),
      ← coeff_divisor f q, hcoeff]
  have hordp : orderAtMF p f = ((-1 : ℤ) : WithTop ℤ) := by
    have hcoeff : FreeAbelianGroup.coeff p
        (MeromorphicFunctionField.divisor f : FreeAbelianGroup X) = -1 := by
      rw [hdivf]
      simp [FreeAbelianGroup.coeff, hqp]
    rw [← WithTop.coe_untop₀_of_ne_top (orderAtMF_ne_top f p),
      ← coeff_divisor f p, hcoeff]
  -- nonconstancy: `toP1 f` hits `0` at `q` and `∞` at `p`
  have hnc : Nonconstant f := by
    rintro ⟨y₀, hy⟩
    have hq0 : toP1 f q = (((0 : ℂ) : ProjectiveLine)) := by
      rw [toP1_eq_zero_iff, hordq]
      exact_mod_cast zero_lt_one
    have hpinf : toP1 f p = (∞ : ProjectiveLine) := by
      rw [toP1_eq_infty_iff, hordp]
      exact_mod_cast neg_one_lt_zero
    have : (((0 : ℂ) : ProjectiveLine)) = (∞ : ProjectiveLine) := by
      rw [← hq0, hy q, ← hy p, hpinf]
    exact OnePoint.coe_ne_infty (0 : ℂ) this
  refine ⟨f, q, p, hnc, hqp, ?_⟩
  show Multiplicative.ofAdd (MeromorphicFunctionField.divisor f) = _
  rw [hdivf]

/-- **Forward leg of `AX_genus_eq_zero_iff_homeo`.** A compact Riemann
surface of genus zero is homeomorphic to the unit 2-sphere. -/
theorem nonempty_homeo_sphere_of_genus_eq_zero (hg : genus X = 0) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  obtain ⟨f, Q₁, Q₂, hf, hne, hdiv⟩ := exists_degreeOne_of_genus_zero hg
  obtain ⟨e, he, _he_symm⟩ := degreeOne_equiv_projectiveLine hf hne hdiv
  exact ⟨(e.toHomeomorphOfContinuousClosed
    he.continuous he.continuous.isClosedMap).trans ProjectiveLine.stereographic⟩

end Jacobians.RiemannSurface
