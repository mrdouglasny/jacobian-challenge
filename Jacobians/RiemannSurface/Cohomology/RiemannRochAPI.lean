/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.Cohomology.RiemannRochBase
import Jacobians.Axioms.RiemannRoch
import Jacobians.Axioms.SerreDuality
import Jacobians.RiemannSurface.Cohomology.DegreeTheorem
import Jacobians.RiemannSurface.DegreeOneGenusZero

/-!
# Riemann-Roch API in terms of the germ-quotient space `L(D)`

This file states the textbook Riemann-Roch consequences directly for the
germ-quotient definition
`riemannRochSpace D = L(D) = {f | div(f) + D >= 0}` from
`Jacobians.RiemannSurface.Cohomology.RiemannRochSpace`.

The statement anchors here are vetted against the textbook form. Some bridges
still use the axiom-level cohomology package, while the high-degree corollary is
now discharged through the negative-degree Riemann-Roch-space theorem.

References: Forster, *Lectures on Riemann Surfaces*, sections 16/17; Miranda,
Ch. VI; Mumford, *Algebraic Geometry I*, Ch. II.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Filter

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- `H⁰(O_D)` is finite-dimensional (the pin, transported across the definitional
`H0 (ofDivisor D) ≃ₗ riemannRochSpace D`). -/
instance instFiniteDimensional_H0_ofDivisor (D : Divisor X) :
    FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D)) :=
  (H0_equiv_riemannRochSpace D).some.symm.finiteDimensional

/-- `H¹(O_D)` is finite-dimensional, inherited from the Layer-3 `H1coh`
finite-dimensionality instance. -/
instance instFiniteDimensional_H1_ofDivisor (D : Divisor X) :
    FiniteDimensional ℂ (Jacobians.Axioms.H1 (LineBundle.ofDivisor D)) :=
  inferInstance

/-- Riemann-Roch in pure `L(D)` terms (Forster section 17; Miranda VI;
Mumford II.2):

`h^0(D) - h^0(K_X - D) = deg D + 1 - g`.

This is the strong form obtained from the usual `h^0(D) - h^1(D)` statement by
Serre duality, identifying `H^1(O(D))` with the dual of `H^0(O(K_X - D))`, and
then using `H0_equiv_riemannRochSpace` for both divisors. -/
theorem riemannRoch (D : Divisor X) :
    (h0 D : ℤ) - (h0 (canonicalDivisor X - D) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ) := by
  have hRR := Jacobians.Layer3.riemannRochL3 (X := X) D
  have hSerre := Jacobians.Layer3.serreDualityL3 (X := X) D
  have hRR' :
      (Module.finrank ℂ (riemannRochSpace D) : ℤ) -
          (Module.finrank ℂ (Jacobians.Layer3.H1coh D) : ℤ) =
        Divisor.deg X D + 1 - (genus X : ℤ) := by
    simpa [Jacobians.Layer3.eulerCharL3] using hRR
  rw [hSerre] at hRR'
  simpa [h0] using hRR'

/-- Holomorphic differentials have dimension the genus (Forster sections 16/17;
Miranda VI; Mumford II.2): `H^0(K_X) ~= C^g`, hence `h^0(K_X) = g`. -/
theorem h0_canonical :
    h0 (canonicalDivisor X) = genus X := by
  have h := riemannRoch (0 : Divisor X)
  rw [sub_zero, h0_zero, map_zero] at h
  omega

/-- Textbook canonical degree formula (Forster section 17; Miranda VI):
`deg K_X = 2g - 2`. The genus is a natural number in this development, so it is
cast to `Int` before forming the divisor-degree identity. -/
theorem canonicalDivisor_deg :
    Divisor.deg X (canonicalDivisor X) = 2 * (genus X : ℤ) - 2 := by
  -- Riemann–Roch at `D = K`: `h⁰(K) − h⁰(0) = deg K + 1 − g`, with `h⁰(K) = g`
  -- and `h⁰(0) = 1`, gives `deg K = 2g − 2`.
  have h := riemannRoch (canonicalDivisor X)
  simp only [sub_self, h0_zero, h0_canonical, Nat.cast_one] at h
  omega

/-- Consistency bridge to the theorem-level Riemann-Roch package.

Given the `AX_RiemannRoch` numerical theorem, the `AX_SerreDuality`
identification
`H^1(O(D)) ~= H^0(O(K_X - D))^*`, and the two comparison equivalences
`H0_equiv_riemannRochSpace`, one obtains the pure `L(D)` form stated in
`riemannRoch`. -/
theorem riemannRoch_consistent_with_AX (D : Divisor X)
    [FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D))]
    [FiniteDimensional ℂ (Jacobians.Axioms.H1 (LineBundle.ofDivisor D))]
    [FiniteDimensional ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)))]
    (_hAX :
      (Module.finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) -
        (Module.finrank ℂ (Jacobians.Axioms.H1 (LineBundle.ofDivisor D)) : ℤ) =
          Divisor.deg X D + 1 - (genus X : ℤ))
    (_hSerre :
      Nonempty
        (Jacobians.Axioms.H1 (LineBundle.ofDivisor D) ≃ₗ[ℂ]
          Module.Dual ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)))))
    (_hD : Nonempty (H0 (LineBundle.ofDivisor D) ≃ₗ[ℂ] riemannRochSpace D))
    (_hKD :
      Nonempty
        (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)) ≃ₗ[ℂ]
          riemannRochSpace (canonicalDivisor X - D))) :
    (h0 D : ℤ) - (h0 (canonicalDivisor X - D) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ) :=
  -- Now subsumed: `riemannRoch` proves this identity directly from the
  -- Layer-3-backed RR/Serre wrappers, so the explicitly supplied equivalences
  -- `hAX`/`hSerre`/`hD`/`hKD` are redundant. The theorem is retained as a stated
  -- consistency anchor.
  riemannRoch D

/-- High-degree Riemann-Roch corollary (Forster section 17; Miranda VI): if
`deg D > 2g - 2`, then `H^1(O(D)) = 0`, equivalently `L(K_X - D) = 0`, so
`h^0(D) = deg D + 1 - g`. The left side is stated over `Int` because divisor
degrees are integer-valued. -/
theorem h0_of_deg_gt (D : Divisor X) :
    2 * (genus X : ℤ) - 2 < Divisor.deg X D →
      (h0 D : ℤ) = Divisor.deg X D + 1 - (genus X : ℤ) := by
  intro hD
  have hKD_neg : Divisor.deg X (canonicalDivisor X - D) < 0 := by
    rw [map_sub, canonicalDivisor_deg]
    omega
  have hKD_bot : riemannRochSpace (canonicalDivisor X - D) = ⊥ :=
    riemannRochSpace_eq_bot_of_deg_neg' hKD_neg
  have hKD_h0 : h0 (canonicalDivisor X - D) = 0 := by
    unfold h0
    rw [hKD_bot]
    simp
  simpa [hKD_h0] using riemannRoch D

private theorem effective_deg_one_eq_of (D : Divisor X) (hD : Effective D)
    (hdeg : Divisor.deg X D = 1) : ∃ q : X, D = FreeAbelianGroup.of q := by
  classical
  let fs : X →₀ ℤ := FreeAbelianGroup.toFinsupp (D : FreeAbelianGroup X)
  let ns : X →₀ ℕ := Finsupp.mapRange Int.toNat Int.toNat_zero fs
  have hsum_ns_int : ((ns.sum (fun _ n => n) : ℕ) : ℤ) = 1 := by
    calc
      ((ns.sum (fun _ n => n) : ℕ) : ℤ)
          = fs.sum (fun _ n => (Int.toNat n : ℤ)) := by
            rw [show ns.sum (fun _ n => n) = fs.sum (fun _ n => Int.toNat n) by
              simp [ns, Finsupp.sum_mapRange_index]]
            simp
      _ = fs.sum (fun _ n => n) := by
            apply Finsupp.sum_congr
            intro q _hq
            have hnonneg : 0 ≤ fs q := by
              simpa [fs, FreeAbelianGroup.coeff] using hD q
            exact Int.toNat_of_nonneg hnonneg
      _ = 1 := by
            simpa [fs, deg_eq_sum_toFinsupp] using hdeg
  have hsum_ns : ns.sum (fun _ n => n) = 1 := by omega
  obtain ⟨q, hns⟩ := (Finsupp.sum_eq_one_iff ns).mp hsum_ns
  have hfs : fs = Finsupp.single q (1 : ℤ) := by
    ext r
    have hnat : (fs r).toNat = (Finsupp.single q (1 : ℕ)) r := by
      simpa [ns, Finsupp.mapRange_apply] using congrFun (congrArg DFunLike.coe hns) r
    by_cases hnonneg : 0 ≤ fs r
    · have hcast := congrArg (fun n : ℕ => (n : ℤ)) hnat
      by_cases hr : r = q
      · subst r
        simpa [Int.toNat_of_nonneg hnonneg] using hcast
      · simpa [Int.toNat_of_nonneg hnonneg, Finsupp.single_eq_of_ne hr] using hcast
    · have hD_r : 0 ≤ fs r := by
        simpa [fs, FreeAbelianGroup.coeff] using hD r
      omega
  refine ⟨q, ?_⟩
  calc
    D = Finsupp.toFreeAbelianGroup fs := by
      simp [fs]
    _ = Finsupp.toFreeAbelianGroup (Finsupp.single q (1 : ℤ)) := by
      rw [hfs]
    _ = FreeAbelianGroup.of q := by
      simp

private theorem divisorOf_eq_pointSub_of_mem_point {F : MeroField X} (hF : F ≠ 0) {p : X}
    (hFP : F ∈ riemannRochSpace (FreeAbelianGroup.of p : Divisor X)) :
    ∃ q : X, divisorOf hF = (FreeAbelianGroup.of q - FreeAbelianGroup.of p : Divisor X) := by
  classical
  let P : Divisor X := FreeAbelianGroup.of p
  have heff : Effective (divisorOf hF + P) :=
    effective_divisorOf_add hF hFP
  have hdeg_div : Divisor.deg X (divisorOf hF) = 0 :=
    deg_divisor_eq_zero (toMF hF)
  have hdegP : Divisor.deg X P = 1 := by
    simp [P, Divisor.deg]
  have hdegE : Divisor.deg X (divisorOf hF + P) = 1 := by
    rw [map_add, hdeg_div, hdegP, zero_add]
  obtain ⟨q, hE⟩ := effective_deg_one_eq_of (divisorOf hF + P) heff hdegE
  refine ⟨q, ?_⟩
  calc
    divisorOf hF = (divisorOf hF + P) - P := by
      abel
    _ = FreeAbelianGroup.of q - P := by
      rw [hE]
    _ = FreeAbelianGroup.of q - FreeAbelianGroup.of p := by
      simp [P]

private theorem pointSub_mem_principal_of_divisorOf_eq {F : MeroField X} (hF : F ≠ 0)
    {q p : X}
    (hdiv : divisorOf hF = (FreeAbelianGroup.of q - FreeAbelianGroup.of p : Divisor X)) :
    ((FreeAbelianGroup.of q - FreeAbelianGroup.of p : FreeAbelianGroup X) : Divisor X) ∈
      PrincipalDivisors X := by
  rw [PrincipalDivisors]
  rw [Subgroup.mem_toAddSubgroup']
  refine ⟨toMF hF, ?_⟩
  change Multiplicative.ofAdd (MeromorphicFunctionField.divisor (toMF hF)) =
    Multiplicative.ofAdd
      ((FreeAbelianGroup.of q - FreeAbelianGroup.of p : FreeAbelianGroup X) : Divisor X)
  simpa [divisorOf] using congrArg Multiplicative.ofAdd hdiv

private theorem riemannRochSpace_point_le_zero (p : X) (hg : 0 < genus X) :
    riemannRochSpace (FreeAbelianGroup.of p : Divisor X) ≤
      riemannRochSpace (0 : Divisor X) := by
  intro F hFP
  by_cases hF : F = 0
  · rw [hF]
    exact (riemannRochSpace (0 : Divisor X)).zero_mem
  · obtain ⟨q, hdiv⟩ := divisorOf_eq_pointSub_of_mem_point hF hFP
    have hprincipal :
        ((FreeAbelianGroup.of q - FreeAbelianGroup.of p : FreeAbelianGroup X) : Divisor X) ∈
          PrincipalDivisors X :=
      pointSub_mem_principal_of_divisorOf_eq hF hdiv
    have hqp : q = p := principal_imp_eq_of_genus_pos hg q p hprincipal
    have hdiv0 : divisorOf hF = 0 := by
      rw [hdiv, hqp]
      simp
    intro r
    have hcoeff := coeff_divisorOf hF r
    have hcoeff0 : (orderAtField r F).untop₀ = 0 := by
      rw [hdiv0] at hcoeff
      simpa using hcoeff.symm
    have hfin := orderAtField_ne_top_of_ne_zero hF r
    rw [← WithTop.coe_untop₀_of_ne_top hfin, hcoeff0]
    norm_num

/-- Single-point positive-genus corollary (Forster section 17; Miranda VI):
for `g > 0`, the Riemann-Roch space `L(P)` has dimension one, i.e. only
constant meromorphic functions have at most one simple pole at `P`.

This formulation uses the divisor `(P)` as `FreeAbelianGroup.of p`; the
positive-genus hypothesis excludes the genus-zero case where `h^0(P) = 2`. -/
theorem h0_point_eq_one_of_genus_pos (p : X) (hg : 0 < genus X) :
    h0 (FreeAbelianGroup.of p : Divisor X) = 1 := by
  let P : Divisor X := FreeAbelianGroup.of p
  have hP0 : riemannRochSpace P ≤ riemannRochSpace (0 : Divisor X) := by
    simpa [P] using riemannRochSpace_point_le_zero p hg
  have h0P : riemannRochSpace (0 : Divisor X) ≤ riemannRochSpace P := by
    refine riemannRochSpace_mono (fun q => ?_)
    simpa [P] using (effective_of (X := X) p q)
  have hspace : riemannRochSpace P = riemannRochSpace (0 : Divisor X) :=
    le_antisymm hP0 h0P
  change Module.finrank ℂ (riemannRochSpace P) = 1
  rw [hspace]
  exact h0_zero

end Jacobians.RiemannSurface
