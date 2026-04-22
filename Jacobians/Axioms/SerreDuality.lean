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
-- Target signature (revised 2026-04-22 post-Gemini review): state the
-- axiom as an isomorphism, not merely a dimension equality. Equality
-- of `finrank` is silently vacuous when both modules are infinite-dim
-- (both sides are 0). The isomorphism form:
--   (a) gives dimension equality as a derived corollary,
--   (b) transfers `FiniteDimensional` across the iso in one direction,
--   (c) is the classical statement ("perfect pairing") anyway.
--
--   axiom AX_SerreDuality {X : Type*} [...] (D : Divisor X) :
--     Nonempty
--       (H1 X (Divisor.LineBundle D) ≃ₗ[ℂ]
--        Module.Dual ℂ (H0 X (Divisor.Omega1Twist X (-D))))
--
-- Or, if we want to expose the pairing itself:
--
--   axiom serrePairing {X : Type*} [...] (D : Divisor X) :
--     H1 X (Divisor.LineBundle D) →ₗ[ℂ]
--       Module.Dual ℂ (H0 X (Divisor.Omega1Twist X (-D)))
--   axiom AX_SerrePairing_bijective {X : Type*} [...] (D : Divisor X) :
--     Function.Bijective (serrePairing X D)
--
-- Either form works; pick based on how consumers use it.

end Jacobians.Axioms
