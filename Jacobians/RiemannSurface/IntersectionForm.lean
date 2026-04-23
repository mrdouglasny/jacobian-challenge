/-
Symplectic intersection pairing on `H1 X x₀` + period-map injectivity.

Two things this module consumes, per the plan §4.5:

1. **Hurewicz bridge.** `H1 X x₀ = Additive (Abelianization (π₁ X x₀))` is
   already the abelianization. What's missing is the explicit map taking
   a loop (a `Path` in Mathlib terms) to its class in `H1`, so downstream
   we can write `periodMap x₀ (loopToHomology γ) ω = pathIntegral γ ω`.

2. **Intersection pairing.** On a compact oriented surface `X` of genus
   `g`, `H1 X x₀` carries a non-degenerate alternating ℤ-bilinear
   "intersection" pairing. Axiomatized as
   `Jacobians.Axioms.intersectionForm` + `AX_IntersectionForm_{alternating,
   perfect}` in `Jacobians/Axioms/IntersectionForm.lean` (added 2026-04-22
   per Gemini review; strengthened to perfect pairing on 2026-04-23).
   Needed to: (a) state Riemann's bilinear relations (`Im τ` is
   positive-definite *w.r.t. the intersection form*), (b) extract a
   symplectic basis `{α_i, β_j}`, (c) state the normalized period matrix
   `[I | τ]`.

**Historical note.** This module used to declare `AX_PeriodInjective`
(injectivity of the period map) as a standalone axiom. Gemini review #2
(2026-04-23) flagged it as **strictly redundant** given `AX_PeriodLattice`
— a `IsZLattice` in `ℝ^(2g)` forces the underlying ℤ-linear map to have
full rank, hence to be injective. No downstream Lean code used
`AX_PeriodInjective`, so it was removed rather than derived as a
theorem (the derivation would require an `IsZLattice`-rank argument
not currently set up). If injectivity is needed concretely, derive via
`AX_PeriodLattice` + rank-preservation.

See `docs/formalization-plan.md` §4.5 and
`docs/gemini-review-axioms-2.md`.
-/
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.Periods

namespace Jacobians.RiemannSurface.IntersectionForm

open scoped Manifold Topology
open scoped ContDiff

-- TODO (loopToHomology): the explicit map `Path X x₀ x₀ → H1 X x₀`
-- via `Abelianization.of ∘ FundamentalGroup.ofPath`.
-- Consumer: relating `periodMap (loopToHomology γ) ω` to `pathIntegral γ ω`
-- once PathIntegral.lean is in place.

-- Intersection pairing: declared as `Jacobians.Axioms.intersectionForm`
-- in `Jacobians/Axioms/IntersectionForm.lean`. Import from consumer
-- modules; no re-export here to keep the axiom boundary clean.

-- TODO (symplectic_basis_exists): consequence of
-- `AX_IntersectionForm_{alternating,nondeg}` + classification of
-- alternating ℤ-bilinear forms over PIDs (Mathlib-ready). Gives
-- existence of a ℤ-basis `{α_1, …, α_g, β_1, …, β_g}` of `H1` in which
-- the intersection form has matrix `[[0, I], [-I, 0]]`. Needed to
-- formally state `AX_RiemannBilinear` in `[I | τ]` normal form.

end Jacobians.RiemannSurface.IntersectionForm
