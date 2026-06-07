/-
`AX_RiemannBilinear`: Riemann's bilinear relations for the period matrix.

**Statement.** For `X` a compact Riemann surface of positive genus `g`,
there exist a symplectic basis `b` of `H_1(X, ℤ)` (via
`AnalyticCycleBasis`) and a basis `ω` of `H⁰(X, Ω¹)` (= `HolomorphicOneForm X`)
*normalized* so that `∫_{α_i} ω_j = δ_ij`, such that the B-period
matrix `τ[i,j] := ∫_{β_i} ω_j` lies in `SiegelUpperHalfSpace g` — i.e.
`τ` is symmetric and `Im τ` is positive-definite.

This is the concrete form of **Riemann's first and second bilinear
relations**.

## Consequences

* `τ(X) ∈ SiegelUpperHalfSpace (genus X)`: the Jacobian lands as a
  principally polarized abelian variety.
* `AX_PeriodLattice` follows (the period image is a full `IsZLattice`
  in `Fin g → ℂ`): `Im τ` positive-definite forces full real rank.
* Period map injectivity follows (retired `AX_PeriodInjective` was
  already a consequence of `AX_PeriodLattice`).

## Why axiomatized

The proof is classical: integration by parts + Hodge-star positivity on
a compact Kähler manifold. Writing it requires:
(a) Actual path integration (multi-chart, homotopy-invariant) — see
    `PathIntegral.lean`.
(b) Hodge inner product on `H⁰(Ω¹)`.
(c) Riemann surface orientability (automatic from complex structure).

Each is a substantial sub-project.

## History

- 2026-04-22 (Gemini review #1): the original "universal quantification
  over all bases" draft was flagged as mathematically false — the
  `[I | τ]` form only holds for symplectic-normalized pairs.
- 2026-04-23 (A3 in completion plan): promoted from doc-only to real
  Lean statement, using `AnalyticCycleBasis`'s symplectic structure
  (A1) + `SiegelUpperHalfSpace`.

See `docs/formalization-plan.md` §7, discharge priority #4;
`docs/completion-plan.md` workstream A3.
Reference: Mumford, *Tata Lectures on Theta I*, Ch. II §2, Thm II.2.1;
Griffiths-Harris, *Principles of Algebraic Geometry*, Ch. 2 §2.
-/
import Jacobians.RiemannSurface.Periods
import Jacobians.Axioms.AnalyticCycleBasis
import Jacobians.AbelianVariety.Siegel

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface Jacobians.AbelianVariety

/-- **Axiom (Riemann's bilinear relations).** There exists a symplectic
`H_1` basis, a normalized `H⁰(Ω¹)` basis, and a Siegel-upper-half-space
matrix `τ` such that:

1. The A-periods of `ω` against the `α`-cycles of the symplectic basis
   are the identity: `∫_{α_i} ω_j = δ_ij`.
2. The B-periods against the `β`-cycles are `τ`: `∫_{β_i} ω_j = τ[i,j]`.

Since `τ ∈ SiegelUpperHalfSpace (genus X)` by the type, it is
automatically symmetric and has positive-definite imaginary part —
the content of Riemann's second bilinear relation. -/
axiom AX_RiemannBilinear {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    ∃ (b : AnalyticCycleBasis X x₀)
      (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
      (τ : SiegelUpperHalfSpace (genus X)),
      -- α-normalization: A-periods form the identity.
      (∀ i j : Fin (genus X),
        periodMap X x₀ (b.isBasis (αEmbed i)) (cω j) = if i = j then 1 else 0) ∧
      -- τ is the B-period matrix.
      (∀ i j : Fin (genus X),
        τ.val i j = periodMap X x₀ (b.isBasis (βEmbed i)) (cω j))

end Jacobians.Axioms
