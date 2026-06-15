/-
# Hyperelliptic genus — parity-dispatch theorem

Proves `genus (Hyperelliptic H) = H.genus` by supplying the odd- and
even-branch genus proofs to `Hyperelliptic.genus_eq`.

This file exists downstream of both `Hyperelliptic.lean` and the
`Extensions/Hyperelliptic{Odd,Even}.lean` genus modules to avoid the import
cycle (`HyperellipticOdd.lean` imports `Hyperelliptic.lean`).
-/
import Jacobians.ProjectiveCurve.Hyperelliptic
import Jacobians.Extensions.HyperellipticEven
import Jacobians.Extensions.HyperellipticOdd

namespace Jacobians.ProjectiveCurve

open Jacobians.Extensions.HyperellipticEven
open Jacobians.Extensions.HyperellipticOdd

/-- **Theorem for the odd-degree hyperelliptic genus formula.**
Discharges the old `AX_HyperellipticOdd_genus` axiom by calling the proved
genus theorem in `HyperellipticOdd.lean`. -/
theorem AX_HyperellipticOdd_genus (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Jacobians.RiemannSurface.genus (HyperellipticOdd H h) =
      (H.f.natDegree - 1) / 2 :=
  genus_HyperellipticOdd_eq H h

/-- The genus of `y² = f(x)` matches the combinatorial formula `⌊(deg f - 1) / 2⌋`.

Proved by parity dispatch: `Hyperelliptic H` unfolds to `HyperellipticOdd H h`
(odd degree) or `HyperellipticEvenProj H` (even degree), and the genus formula
is already proved for each branch. -/
theorem genus_Hyperelliptic_eq (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus :=
  Hyperelliptic.genus_eq H
    (fun h => AX_HyperellipticOdd_genus H h)
    (@genus_HyperellipticEven_eq H)

/-- Even-degree specialization of the hyperelliptic genus formula. For
`deg f = 2g + 2`, the genus is `g = deg(f) / 2 - 1`. -/
theorem genus_Hyperelliptic_eq_of_even
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) =
      H.f.natDegree / 2 - 1 := by
  rw [genus_Hyperelliptic_eq, HyperellipticData.genus]
  obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp h
  rw [hk]
  omega

/-- Concrete even-degree form of the hyperelliptic genus formula:
if `deg f = 2g + 2`, then the genus is `g`. -/
theorem genus_Hyperelliptic_eq_of_even_degree
    (H : HyperellipticData) (g : ℕ) (hdeg : H.f.natDegree = 2 * g + 2) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = g := by
  rw [genus_Hyperelliptic_eq, HyperellipticData.genus, hdeg]
  omega

end Jacobians.ProjectiveCurve
