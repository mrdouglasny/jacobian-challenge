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
-- matrix construction in `RiemannSurface/Periods.lean`, which in turn
-- needs `pathIntegral` + the `intersectionForm` axiom (to give
-- "symplectic basis" a formal meaning). Declare the axiom here once
-- those dependencies materialize.
--
-- Target signature (revised 2026-04-22 post-Gemini review): the
-- existentials need to cover basis choice. Universally quantifying over
-- arbitrary bases is mathematically false; the `[I | τ]` normal form
-- holds only for the symplectic-normalized pair.
--
--   axiom AX_RiemannBilinear
--       {X : Type*} [...] (x₀ : X) :
--       -- "∃ a symplectic basis of H1 and a normalized basis of Ω¹
--       --  such that the period matrix is in Siegel normal form"
--       ∃ α : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀),
--       ∃ ω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X),
--       ∃ τ : SiegelUpperHalfSpace (genus X),
--         -- α is symplectic w.r.t. the intersection form (first `genus X`
--         -- are A-cycles, last `genus X` are B-cycles with
--         -- `⟨αᵢ, βⱼ⟩ = δᵢⱼ`).
--         IsSymplecticBasis (intersectionForm x₀) α ∧
--         -- ω is the dual basis normalized by the A-periods.
--         (∀ i j, periodMap X x₀ (α (Sum.inl i)) (ω j) = if i = j then 1 else 0) ∧
--         -- B-periods give τ.
--         periodMatrix_B x₀ α ω = τ.val
--
-- Prerequisites: `IsSymplecticBasis` predicate (Mathlib has
-- `LinearMap.BilinForm.IsSymplectic`-style lemmas over PID — port the
-- statement), `periodMatrix_B` (the ⟨βⱼ, ωᵢ⟩ matrix), `Module.Basis`
-- normalization lemmas.

end Jacobians.Axioms
