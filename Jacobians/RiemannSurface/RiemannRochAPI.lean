/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.RiemannRochSpace
import Jacobians.Axioms.RiemannRoch
import Jacobians.Axioms.SerreDuality

/-!
# Riemann-Roch API in terms of the germ-quotient space `L(D)`

This file states the textbook Riemann-Roch consequences directly for the
germ-quotient definition
`riemannRochSpace D = L(D) = {f | div(f) + D >= 0}` from
`Jacobians.RiemannSurface.RiemannRochSpace`.

All results here are vetted statement anchors. The proofs are intentionally
deferred with `sorry`; the value is in the faithful, type-correct statements.

References: Forster, *Lectures on Riemann Surfaces*, sections 16/17; Miranda,
Ch. VI; Mumford, *Algebraic Geometry I*, Ch. II.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- `h^0(D)` is the complex dimension of the concrete Riemann-Roch space
`L(D) = H^0(X, O(D))`, as in Forster sections 16/17 and Miranda VI. Its
carrier is the meromorphic germ quotient, not raw functions. The
finite-dimensionality assertion making this finrank semantically faithful is
recorded separately in `riemannRochSpace_finiteDimensional`. -/
noncomputable abbrev h0 (D : Divisor X) : ℕ :=
  Module.finrank ℂ (riemannRochSpace D)

/-- Textbook canonical degree formula (Forster section 17; Miranda VI):
`deg K_X = 2g - 2`. The genus is a natural number in this development, so it is
cast to `Int` before forming the divisor-degree identity. -/
theorem canonicalDivisor_deg :
    Divisor.deg X (canonicalDivisor X) = 2 * (genus X : ℤ) - 2 := by
  sorry

/-- Riemann-Roch in pure `L(D)` terms (Forster section 17; Miranda VI;
Mumford II.2):

`h^0(D) - h^0(K_X - D) = deg D + 1 - g`.

This is the strong form obtained from the usual `h^0(D) - h^1(D)` statement by
Serre duality, identifying `H^1(O(D))` with the dual of `H^0(O(K_X - D))`, and
then using `H0_equiv_riemannRochSpace` for both divisors. -/
theorem riemannRoch (D : Divisor X) :
    (h0 D : ℤ) - (h0 (canonicalDivisor X - D) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ) := by
  sorry

/-- Consistency bridge to the existing axiom-level Riemann-Roch package.

Given the `AX_RiemannRoch` numerical statement, the `AX_SerreDuality`
identification
`H^1(O(D)) ~= H^0(O(K_X - D))^*`, and the two comparison equivalences
`H0_equiv_riemannRochSpace`, one obtains the pure `L(D)` form stated in
`riemannRoch`. This theorem is only a statement anchor; its body is deferred. -/
theorem riemannRoch_consistent_with_AX (D : Divisor X)
    [FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D))]
    [FiniteDimensional ℂ (H1 (LineBundle.ofDivisor D))]
    [FiniteDimensional ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)))]
    (hAX :
      (Module.finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) -
        (Module.finrank ℂ (H1 (LineBundle.ofDivisor D)) : ℤ) =
          Divisor.deg X D + 1 - (genus X : ℤ))
    (hSerre :
      Nonempty
        (H1 (LineBundle.ofDivisor D) ≃ₗ[ℂ]
          Module.Dual ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)))))
    (hD : Nonempty (H0 (LineBundle.ofDivisor D) ≃ₗ[ℂ] riemannRochSpace D))
    (hKD :
      Nonempty
        (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)) ≃ₗ[ℂ]
          riemannRochSpace (canonicalDivisor X - D))) :
    (h0 D : ℤ) - (h0 (canonicalDivisor X - D) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ) := by
  sorry

/-- High-degree Riemann-Roch corollary (Forster section 17; Miranda VI): if
`deg D > 2g - 2`, then `H^1(O(D)) = 0`, equivalently `L(K_X - D) = 0`, so
`h^0(D) = deg D + 1 - g`. The left side is stated over `Int` because divisor
degrees are integer-valued. -/
theorem h0_of_deg_gt (D : Divisor X) :
    2 * (genus X : ℤ) - 2 < Divisor.deg X D →
      (h0 D : ℤ) = Divisor.deg X D + 1 - (genus X : ℤ) := by
  sorry

/-- Single-point positive-genus corollary (Forster section 17; Miranda VI):
for `g > 0`, the Riemann-Roch space `L(P)` has dimension one, i.e. only
constant meromorphic functions have at most one simple pole at `P`.

This formulation uses the divisor `(P)` as `FreeAbelianGroup.of p`; the
positive-genus hypothesis excludes the genus-zero case where `h^0(P) = 2`. -/
theorem h0_point_eq_one_of_genus_pos (p : X) (hg : 0 < genus X) :
    h0 (FreeAbelianGroup.of p : Divisor X) = 1 := by
  sorry

/-- Global holomorphic functions on a compact connected Riemann surface are
constant (Forster section 16; Miranda VI): `L(0) = C`, so `h^0(0) = 1`. -/
theorem h0_zero :
    h0 (0 : Divisor X) = 1 := by
  sorry

/-- Holomorphic differentials have dimension the genus (Forster sections 16/17;
Miranda VI; Mumford II.2): `H^0(K_X) ~= C^g`, hence `h^0(K_X) = g`. -/
theorem h0_canonical :
    h0 (canonicalDivisor X) = genus X := by
  sorry

/-- Compactness/Cartan-Serre finiteness input for the concrete
Riemann-Roch space `L(D)` (Forster section 16; Miranda VI): for every divisor
`D`, the space of meromorphic functions satisfying `div(f) + D >= 0` is
finite-dimensional over `C`. This is the finite-dimensionality theorem that
makes `h0 D = finrank C (L(D))` semantically meaningful. -/
theorem riemannRochSpace_finiteDimensional (D : Divisor X) :
    FiniteDimensional ℂ (riemannRochSpace D) := by
  sorry

end Jacobians.RiemannSurface
