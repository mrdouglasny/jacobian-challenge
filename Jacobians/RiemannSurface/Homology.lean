/-
`H1 X x₀` — first singular homology of a based topological space, with
ℤ-coefficients, via the Hurewicz theorem.

For path-connected `X`, Hurewicz gives a canonical isomorphism
`H_1(X, ℤ) ≅ π_1(X, x₀)^{ab}`. We take the abelianization of the
fundamental group as our definition — this avoids needing singular-chain
machinery.

This is a topological definition: no complex structure on `X` is
required. It's placed in `RiemannSurface/` because that's where its
primary consumer (the period pairing) lives.

**Note on rank.** For `X` a compact oriented surface of genus `g`, `H_1(X, ℤ)`
is free abelian of rank `2g`. This fact is classical CW-topology
(simplicial presentation of the surface has standard generators
`α_i, β_i` with relation `∏ [α_i, β_i] = 1`, which abelianizes to nothing).
We do **not** prove this here — it's axiomatized later as
`AX_H1FreeRank2g` (see `docs/formalization-plan.md` §7). Attempting a
direct proof would mean formalizing the classification of compact
orientable surfaces, which is out of scope.

See `docs/formalization-plan.md` §4.3.
-/
import Mathlib

namespace Jacobians.RiemannSurface

open scoped Topology

/-- The first integral homology group of a path-connected topological
space `X`, defined via Hurewicz as the abelianization of the fundamental
group based at `x₀`.

Wrapped in `Additive` so that Mathlib's group-to-commgroup-on-abelianization
pipeline lands on an *additive* commutative group (the homology convention),
matching the additive flavor the period map lands in.

For path-connected `X`, this is independent of `x₀` up to canonical
isomorphism (path-conjugation gives the iso). -/
abbrev H1 (X : Type*) [TopologicalSpace X] (x₀ : X) : Type _ :=
  Additive (Abelianization (FundamentalGroup X x₀))

namespace H1

variable {X : Type*} [TopologicalSpace X]

-- TODO (basepoint_independence): for path-connected `X` and `x₀, x₁ : X`,
-- there's a canonical `H1 X x₀ ≃+ H1 X x₁` via path-conjugation. This is
-- used in `periodLattice X` where we show the period-image lattice is
-- basepoint-independent.

-- TODO (AX_H1FreeRank2g placeholder): for `X` compact, connected, of
-- genus `g`, `H1 X x₀` is free abelian of rank `2g`. Axiomatized; not
-- proved here. Consumer: `IntersectionForm.lean` uses the ℤ-basis to
-- set up the symplectic pairing.

-- TODO (Hurewicz bridge): concrete `loopToHomology : Path X x₀ x₀ → H1 X x₀`
-- via `Abelianization.of ∘ FundamentalGroup.ofPath`. Used to state
-- `periodMap γ ω = pathIntegral γ ω` for `γ` a loop.

end H1

end Jacobians.RiemannSurface
