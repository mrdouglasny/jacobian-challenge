/-
`AX_SerreDuality`: Serre duality for line bundles on a compact Riemann
surface.

**Statement (Lean, refined 2026-04-23).** For `X` a compact Riemann
surface and `D` a divisor:

    H¹(X, 𝒪(D)) ≃ₗ[ℂ] Dual ℂ (H⁰(X, 𝒪(K - D)))

where `K = canonicalDivisor X` represents the canonical sheaf `Ω¹_X`.

## Consequences

* For `D = [P]` and `g = 0`: `dim H¹(𝒪([P])) = dim H⁰(Ω¹ ⊗ 𝒪(-[P])) ≤
  dim H⁰(Ω¹) = 0`. Combined with Riemann-Roch this gives
  `dim H⁰(𝒪([P])) = 2`, hence a biholomorphism to ℂP¹ (genus-0
  uniformization).
* Plus `AX_RiemannRoch`, implies the classical numerical Riemann-Roch
  `dim L(D) - dim L(K - D) = deg D - g + 1`.

This declaration is now a theorem wrapper over the Layer-3 equivalence
`serreDuality_equiv`, after the API identifies `H1(O(D))` with `H1coh D`.

## History

- 2026-04-22 (Gemini review #1): flagged — dimension equality alone is
  silently vacuous (both sides 0 when infinite-dim); an isomorphism
  statement is strictly stronger and transfers finite-dimensionality.
- 2026-04-23 (A5 in completion plan): promoted from doc-only to real
  Lean statement via `LineBundle` / `H0` / `H1` stubs + Mathlib's
  `Module.Dual`.

See `docs/formalization-plan.md` §7; `docs/completion-plan.md` workstream
A5. Reference: Forster Ch. II §17; Mumford Vol I §II.2.
-/
import Submission.Jacobians.RiemannSurface.Cohomology.LineBundle

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Axiom (Serre duality).** For a compact Riemann surface `X` and a
divisor `D`, there is a canonical ℂ-linear isomorphism

    H¹(X, 𝒪(D)) ≃ₗ[ℂ] Dual ℂ (H⁰(X, 𝒪(K − D))),

where `K := canonicalDivisor X` represents `Ω¹_X`. The isomorphism is
"perfect pairing" shape, packaged via `Nonempty` of the equivalence
to emphasize existence rather than a canonical choice. -/
theorem AX_SerreDuality {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) :
    Nonempty
      (H1 (LineBundle.ofDivisor D) ≃ₗ[ℂ]
        Module.Dual ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)))) := by
  simpa [H0, H1] using
    (Jacobians.Layer3.serreDuality_equiv (X := X) D)

end Jacobians.Axioms
