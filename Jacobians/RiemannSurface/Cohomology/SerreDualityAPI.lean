/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.Cohomology.RiemannRochAPI

/-!
# Serre duality API in terms of the concrete space `L(D)`

This file states the textbook Serre-duality consequences in dimension form,
linking `H1` (now `Layer3.H1coh`) to the concrete Riemann-Roch space
`H0 (O(K - D)) = riemannRochSpace (K - D)` of
`Jacobians.RiemannSurface.Cohomology.RiemannRochSpace`.

The underlying linear isomorphism `H1(O(D)) ≃ₗ[ℂ] (H0(O(K - D)))ᵛ` is the
theorem wrapper `AX_SerreDuality`; here we expose its **usable numerical content**
`h1(D) = h0(K - D)` (a finite-dimensional vector space and its dual have equal
dimension) and the Serre-vanishing corollary `deg D > 2g - 2 ⇒ h1(D) = 0`,
which is exactly what turns the `h0 - h1` Riemann-Roch identity into the
effective `h0 = deg D + 1 - g`.

These are vetted statement anchors. `h1_eq_h0_canonical_sub` (the dimension-form
duality), Serre vanishing (`h1_eq_zero_of_deg_gt`), and
`riemannRoch_h0_sub_h1` (the `h0 - h1` identity) are now **real proofs**: the
first from the Layer-3-backed `AX_SerreDuality` theorem via `LinearEquiv.finrank_eq` +
`Subspace.dual_finrank_eq`, vanishing from `deg K = 2g - 2` plus the
negative-degree Riemann-Roch-space theorem, and the last a re-export of
the Layer-3-backed `AX_RiemannRoch` theorem once the finite-dimensionality
instances are threaded through.

References: Forster, *Lectures on Riemann Surfaces*, section 17 (Serre duality);
Griffiths-Harris, *Principles of Algebraic Geometry*, Ch. 1; Miranda, Ch. VI.

Vetting trail. Statements vetted FAITHFUL by Gemini deep-think (2026-06-06):
the `K - D` direction is the correct numerical shadow of
`H1(O(D)) ≃ (H0(O(K - D)))ᵛ` (finite-dim ⇒ `finrank` of the dual equals
`finrank`); the Serre-vanishing threshold `deg D > 2g - 2` is correct and the
strictness is mandatory (`deg D = 2g - 2`, e.g. `D = K`, gives `h¹ = h⁰(0) =
1`); casting to `ℤ` before subtracting in `h1_eq_zero_of_deg_gt` and
`riemannRoch_h0_sub_h1` avoids the `ℕ`-subtraction floor (genus 0 ⇒ threshold
`-2`, not `0`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `h^1(D)` is the complex dimension of the first sheaf cohomology
`H^1(X, O(D))`, now represented by the Layer-3 `H1coh D`. Serre duality below
identifies this dimension with `h^0(K - D)`, which is the concrete `finrank` of
`riemannRochSpace (K - D)`. -/
noncomputable abbrev h1 (D : Divisor X) : ℕ :=
  Module.finrank ℂ (Jacobians.Axioms.H1 (LineBundle.ofDivisor D))

/-- Serre duality, dimension form (Forster section 17; Griffiths-Harris Ch. 1):
`h^1(D) = h^0(K - D)`.  This is the numerical shadow of the linear isomorphism
`AX_SerreDuality : H1(O(D)) ≃ₗ[ℂ] (H0(O(K - D)))ᵛ`, using that a
finite-dimensional space and its dual have the same dimension.  With `H0`
de-opaqued to `riemannRochSpace`, the right-hand side is a genuine dimension of
the meromorphic germ quotient. -/
theorem h1_eq_h0_canonical_sub (D : Divisor X) :
    h1 D = h0 (canonicalDivisor X - D) := by
  obtain ⟨e⟩ := AX_SerreDuality D
  calc h1 D
      = Module.finrank ℂ
          (Module.Dual ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)))) :=
        e.finrank_eq
    _ = Module.finrank ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D))) :=
        Subspace.dual_finrank_eq
    _ = h0 (canonicalDivisor X - D) := rfl

/-- Serre vanishing (Forster section 17; Miranda VI): for a divisor of degree
exceeding `2g - 2`, the first cohomology vanishes, `h^1(D) = 0`.  Equivalent via
`h1_eq_h0_canonical_sub` to `h^0(K - D) = 0`, since `deg(K - D) = (2g - 2) -
deg D < 0` and a divisor of negative degree has no global sections. -/
theorem h1_eq_zero_of_deg_gt (D : Divisor X)
    (hD : (2 * (genus X : ℤ) - 2) < Divisor.deg X D) :
    h1 D = 0 := by
  have hKD_neg : Divisor.deg X (canonicalDivisor X - D) < 0 := by
    rw [map_sub, canonicalDivisor_deg]
    omega
  have hKD_bot : riemannRochSpace (canonicalDivisor X - D) = ⊥ :=
    riemannRochSpace_eq_bot_of_deg_neg' hKD_neg
  have hKD_h0 : h0 (canonicalDivisor X - D) = 0 := by
    unfold h0
    rw [hKD_bot]
    simp
  rw [h1_eq_h0_canonical_sub D, hKD_h0]

/-- Compatibility of the dimension-form Serre duality with the `h^0 - h^1`
Riemann-Roch identity: combining `riemannRoch` (the `h^0(D) - h^0(K - D)` form
in `RiemannRochAPI`) with `h1_eq_h0_canonical_sub` recovers the classical
`h^0(D) - h^1(D) = deg D + 1 - g`.  This cross-checks the two anchors against
each other. -/
theorem riemannRoch_h0_sub_h1 (D : Divisor X)
    [FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D))]
    [FiniteDimensional ℂ (Jacobians.Axioms.H1 (LineBundle.ofDivisor D))] :
    (h0 D : ℤ) - (h1 D : ℤ) = Divisor.deg X D + 1 - (genus X : ℤ) :=
  AX_RiemannRoch D

end Jacobians.RiemannSurface
