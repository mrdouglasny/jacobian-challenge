/-
`AX_RiemannBilinear`: Riemann's bilinear relations for the period matrix.

**Statement.** For `X` a compact Riemann surface of positive genus `g`,
given a symplectic basis `α, β` of `H_1(X, ℤ)` and a normalized basis
`ω` of `H⁰(X, Ω¹)` (normalized so that `∫_{α_i} ω_j = δ_ij`), the period
matrix `τ[i,j] := ∫_{β_i} ω_j` is symmetric and its imaginary part is
positive definite.

**Consequences.**
* `τ(X) ∈ SiegelUpperHalfSpace (genus X)`, so the Jacobian lands as a
  complex torus in the moduli space of principally-polarized abelian
  varieties.
* `AX_PeriodInjective` follows: `Im τ` positive-definite ⇒ the period
  map `H_1 → (H⁰(Ω¹))^∨` is injective.
* The lattice `periodLattice X x₀ ⊂ (HolomorphicOneForm X)^∨` is full
  real rank.

**Why axiomatized.** The proof is classical integration by parts + Hodge
star positivity on a compact Kähler manifold. Writing the proof requires:
(a) actual integration of 1-forms along paths (Part B's `PathIntegral`
module, not yet built), (b) Hodge inner product on `H⁰(Ω¹)`, (c)
careful choice of symplectic basis. Each is a substantial sub-project.

See `docs/formalization-plan.md` §7; discharge priority #4.
Reference: Mumford Vol I Ch. II §2, Thm II.2.1.
-/
import Jacobians.RiemannSurface.Periods

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff

-- TODO (AX_RiemannBilinear): precise statement requires the period
-- matrix construction in `RiemannSurface/Periods.lean` which in turn
-- needs `pathIntegral` + choice of a symplectic basis of H1 and a
-- normalized basis of HolomorphicOneForm. Declare the axiom here
-- once those dependencies materialize.
--
-- Target signature (sketch):
--
--   axiom AX_RiemannBilinear
--       {X : Type*} [...] (x₀ : X)
--       (α : Basis (Fin (2 * genus X)) ℤ (H1 X x₀))  -- symplectic
--       (ω : Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
--       -- "periodMatrix in the AB normalization is in SiegelUpperHalfSpace"
--       ∃ τ : SiegelUpperHalfSpace (genus X),
--         periodMatrix X x₀ α ω = [I | τ]   -- normalized form

end Jacobians.Axioms
