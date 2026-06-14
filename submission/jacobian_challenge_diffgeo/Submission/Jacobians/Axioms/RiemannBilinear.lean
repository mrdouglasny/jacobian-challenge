/-
`AX_RiemannBilinear`: Riemann's bilinear relations for the period matrix.

**Statement.** For `X` a compact Riemann surface of positive genus `g`,
there exist a cycle basis `b` of `H_1(X, ℤ)` (via
`PeriodCycleBasis`) and a basis `ω` of `H⁰(X, Ω¹)` (= `HolomorphicOneForm X`)
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

## Now a THEOREM (Layer-3 Phase C; D1 merge 2026-06-10)

Proved in `Jacobians/Layer3/Periods.lean` (`riemannBilinear_exists`) from the
R1 (isotropy / Stokes) and R2 (Hodge positivity) **fields of the chosen
`AX_PeriodCycleBasis` witness** — the D1 merge moved the former basis-free
primitives `AX_RBR1`/`AX_RBR2` into the bundle, arc-level over its own loops
— through the axiom-free matrix engine: R2 makes the A-period matrix
invertible (normalization), R1 gives `τ = τᵀ`, and R1+R2 give `Im τ ≻ 0` —
exactly Siegel membership. R1/R2 isolate the genuine analytic content
(`∫_X ω∧η = 0` and `i∫_X ω∧ω̄ > 0` routed through the symplectic dual form
`Q`, avoiding 2-form integration); each was statement-vetted before
introduction (DT 2026-06-09 as `AX_RBR1`/`AX_RBR2`; merge DT-endorsed
2026-06-10).

## History

- 2026-04-22 (Gemini review #1): the original "universal quantification
  over all bases" draft was flagged as mathematically false — the
  `[I | τ]` form only holds for symplectic-normalized pairs.
- 2026-04-23 (A3 in completion plan): promoted from doc-only to real
  Lean statement, using `AnalyticCycleBasis`'s symplectic structure
  (A1) + `SiegelUpperHalfSpace`.
- 2026-06-10 (D1): `AnalyticCycleBasis` → `PeriodCycleBasis` in the
  existential (same shape; the structure now carries R1/R2 arc-level and
  no intersection-form field).

See `docs/formalization-plan.md` §7, discharge priority #4;
`docs/completion-plan.md` workstream A3.
Reference: Mumford, *Tata Lectures on Theta I*, Ch. II §2, Thm II.2.1;
Griffiths-Harris, *Principles of Algebraic Geometry*, Ch. 2 §2.
-/
import Submission.Jacobians.RiemannSurface.Periods
import Submission.Jacobians.Axioms.PeriodCycleBasis
import Submission.Jacobians.AbelianVariety.Siegel
import Submission.Jacobians.Layer3.Periods

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface Jacobians.AbelianVariety

/-- **Riemann's bilinear relations — THEOREM** (Layer-3 Phase C; was an
axiom). There exists an `H_1` cycle basis, a normalized `H⁰(Ω¹)` basis,
and a Siegel-upper-half-space matrix `τ` such that:

1. The A-periods of `ω` against the `α`-cycles of the cycle basis
   are the identity: `∫_{α_i} ω_j = δ_ij`.
2. The B-periods against the `β`-cycles are `τ`: `∫_{β_i} ω_j = τ[i,j]`.

Since `τ ∈ SiegelUpperHalfSpace (genus X)` by the type, it is
automatically symmetric and has positive-definite imaginary part —
the content of Riemann's second bilinear relation. Proof:
`Layer3.riemannBilinear_exists`, from the R1/R2 fields of the chosen
`AX_PeriodCycleBasis` witness. -/
theorem AX_RiemannBilinear {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    ∃ (b : PeriodCycleBasis X x₀)
      (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
      (τ : SiegelUpperHalfSpace (genus X)),
      -- α-normalization: A-periods form the identity.
      (∀ i j : Fin (genus X),
        periodMap X x₀ (b.isBasis (αEmbed i)) (cω j) = if i = j then 1 else 0) ∧
      -- τ is the B-period matrix.
      (∀ i j : Fin (genus X),
        τ.val i j = periodMap X x₀ (b.isBasis (βEmbed i)) (cω j)) :=
  Jacobians.Layer3.riemannBilinear_exists x₀

end Jacobians.Axioms
