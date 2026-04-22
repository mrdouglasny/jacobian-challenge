/-
`AX_RiemannRoch`: the Riemann-Roch theorem for divisors on a compact
Riemann surface.

**Statement.** For `X` a compact Riemann surface of genus `g` and `D`
a divisor on `X`,

    dim_ℂ H⁰(X, 𝒪(D)) - dim_ℂ H¹(X, 𝒪(D)) = deg D + 1 - g.

**Consequences.**
* For `D = P` a point of degree 1 on a genus-0 surface: `dim H⁰(𝒪([P])) ≥ 2`,
  giving a meromorphic function with exactly one simple pole — hence
  a biholomorphism `X → ℂP¹`. This gives the `⇒` direction of
  `genus_eq_zero_iff_homeo` modulo `AX_SerreDuality`.

**Why axiomatized.** `H⁰`, `H¹`, `𝒪(D)`, `deg D` are all sheaf-cohomology
concepts on complex manifolds, which Mathlib does not supply at this
pin. Proving Riemann-Roch from scratch requires either sheaf cohomology
+ Čech or the analytic machinery (heat kernel / Euler characteristic
via ∂̄). Both are substantial projects on their own.

See `docs/formalization-plan.md` §7; discharge priority #8.
Reference: Mumford Vol I Ch. II §2; Forster, Lectures on Riemann
Surfaces, Ch. III.
-/
import Jacobians.RiemannSurface.Genus

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff

-- TODO (AX_RiemannRoch): precise Lean statement requires
-- `Divisor X` (sheaf-of-line-bundles) + `H^0` / `H^1` / degree function,
-- none of which are in Mathlib at the pin. Declare the axiom here once
-- the divisor-theoretic scaffolding is in place.
--
-- Target signature (revised 2026-04-22 post-Gemini review): two pitfalls
-- to avoid.
-- (1) `Module.finrank` returns `0` when the module is infinite-dim. We
--     MUST bundle `[FiniteDimensional ℂ (H0 ...)] [FiniteDimensional ℂ
--     (H1 ...)]` as hypotheses (otherwise the equation reduces to
--     `0 - 0 = deg D + 1 - g`, silently false).
-- (2) `Module.finrank` returns `ℕ`. Nat subtraction truncates, so
--     `1 - 2 = 0` as ℕ — destroying the formula when the RHS is
--     negative. Both sides must be cast to `ℤ`.
--
--   axiom AX_RiemannRoch {X : Type*} [...] (D : Divisor X)
--       [FiniteDimensional ℂ (H0 X (Divisor.LineBundle D))]
--       [FiniteDimensional ℂ (H1 X (Divisor.LineBundle D))] :
--       (Module.finrank ℂ (H0 X (Divisor.LineBundle D)) : ℤ) -
--       (Module.finrank ℂ (H1 X (Divisor.LineBundle D)) : ℤ) =
--         Divisor.deg D + 1 - (genus X : ℤ)
--
-- Alternative formulation — make the finite-dimensionality itself part
-- of the axiom's conclusion (so `H0, H1` don't each need a separate
-- FD axiom):
--
--   axiom AX_RiemannRoch {X : Type*} [...] (D : Divisor X) :
--       FiniteDimensional ℂ (H0 X (Divisor.LineBundle D)) ∧
--       FiniteDimensional ℂ (H1 X (Divisor.LineBundle D)) ∧
--       (Module.finrank ℂ (H0 X (Divisor.LineBundle D)) : ℤ) -
--       (Module.finrank ℂ (H1 X (Divisor.LineBundle D)) : ℤ) =
--         Divisor.deg D + 1 - (genus X : ℤ)

end Jacobians.Axioms
