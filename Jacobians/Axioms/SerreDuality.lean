/-
`AX_SerreDuality`: Serre duality for line bundles on a compact Riemann
surface.

**Statement.** For `X` compact Riemann surface and `D` a divisor,

    H¹(X, 𝒪(D)) ≅ H⁰(X, Ω¹_X ⊗ 𝒪(-D))^*

as ℂ-vector spaces (or just the dimension equation, which is what our
genus-0 proof of uniformization uses).

**Consequences.**
* For `D = [P]` and `g = 0`: `dim H¹(𝒪([P])) = dim H⁰(Ω¹ ⊗ 𝒪(-[P])) ≤
  dim H⁰(Ω¹) = 0`. Combined with Riemann-Roch this gives
  `dim H⁰(𝒪([P])) = 2`, hence a biholomorphism to ℂP¹ (genus-0
  uniformization).
* More generally, Serre duality is the input to many existence
  arguments in the theory of compact Riemann surfaces (meromorphic
  differentials with prescribed principal parts, etc.).

**Why axiomatized.** Same reason as `AX_RiemannRoch` — the sheaf-
cohomology machinery on complex manifolds isn't in Mathlib at this pin.

See `docs/formalization-plan.md` §7; discharge priority #7.
Reference: Forster Ch. II §17; Mumford Vol I §II.2.
-/
import Jacobians.Axioms.RiemannRoch

namespace Jacobians.Axioms

-- TODO (AX_SerreDuality): precise Lean statement requires the same
-- sheaf-cohomology scaffolding as AX_RiemannRoch. Declare when ready.
--
-- Target signature (sketch):
--
--   axiom AX_SerreDuality {X : Type*} [...] (D : Divisor X) :
--     Module.finrank ℂ (H1 X (Divisor.LineBundle D)) =
--     Module.finrank ℂ (H0 X (Divisor.Omega1Twist X (-D)))

end Jacobians.Axioms
