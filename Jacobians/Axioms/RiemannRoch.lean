/-
`AX_RiemannRoch`: the Riemann-Roch theorem for divisors on a compact
Riemann surface.

**Statement (Lean, refined 2026-04-23):**
```
(finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) -
(finrank ℂ (H1 (LineBundle.ofDivisor D)) : ℤ) =
  Divisor.deg X D + 1 - (genus X : ℤ)
```

subject to `FiniteDimensional ℂ (H0 ...)` and `FiniteDimensional ℂ
(H1 ...)` — these finite-dimensionality hypotheses are standard
consequences of compactness (via Serre's finiteness theorem), but
they're not currently derivable from our axiom framework alone, so
the axiom takes them as typeclass arguments.

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

## History

- 2026-04-22 (Gemini review #1): flagged the need for `FiniteDimensional`
  hypotheses + ℤ-subtraction (else `Nat.sub` truncates and the formula
  silently fails).
- 2026-04-23 (A5 in completion plan): promoted from doc-only to real
  Lean statement using the `Divisor / LineBundle / H0 / H1` stubs from
  `RiemannSurface/LineBundle.lean`.

See `docs/formalization-plan.md` §7; `docs/completion-plan.md` workstream
A4 + A5.
Reference: Mumford Vol I Ch. II §2; Forster, Lectures on Riemann
Surfaces, Ch. III.
-/
import Jacobians.RiemannSurface.LineBundle

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Axiom (Riemann-Roch).** For a compact Riemann surface `X` and a
divisor `D` on `X` (with `H⁰(O(D))` and `H¹(O(D))` both
finite-dimensional, which holds classically by compactness):

    dim H⁰(X, 𝒪(D)) − dim H¹(X, 𝒪(D)) = deg D + 1 − g.

Both sides cast to `ℤ` to avoid `Nat`-subtraction truncation. -/
axiom AX_RiemannRoch {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X)
    [_h0fd : FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D))]
    [_h1fd : FiniteDimensional ℂ (H1 (LineBundle.ofDivisor D))] :
    (Module.finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) -
    (Module.finrank ℂ (H1 (LineBundle.ofDivisor D)) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ)

end Jacobians.Axioms
