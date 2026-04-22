/-
Symplectic intersection pairing on `H1 X x₀` + period-map injectivity.

Two things this module is responsible for, per the plan §4.5:

1. **Hurewicz bridge.** `H1 X x₀ = Additive (Abelianization (π₁ X x₀))` is
   already the abelianization. What's missing is the explicit map taking
   a loop (a `Path` in Mathlib terms) to its class in `H1`, so downstream
   we can write `periodMap x₀ (loopToHomology γ) ω = pathIntegral γ ω`.

2. **Intersection pairing.** On a compact oriented surface `X` of genus
   `g`, `H1 X x₀` carries a non-degenerate alternating ℤ-bilinear
   "intersection" pairing. Needed to: (a) state Riemann's bilinear
   relations (`Im τ` is positive-definite *w.r.t. the intersection form*),
   (b) extract a symplectic basis `{α_i, β_j}`, (c) state the normalized
   period matrix `[I | τ]`.

3. **Period injectivity.** For `genus X > 0`, `periodMap X x₀` is injective.
   Consequence of Riemann's bilinear relations. Axiomatized here as
   `AX_PeriodInjective`; retireable once `AX_RiemannBilinear` lands.

See `docs/formalization-plan.md` §4.5.
-/
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.Periods

namespace Jacobians.RiemannSurface.IntersectionForm

open scoped Manifold Topology
open scoped ContDiff

/-- **Axiom.** The period map `H1 X x₀ → (HolomorphicOneForm X)^∨` is
injective for `X` a compact Riemann surface.

**Status.** Classically a consequence of Riemann's first and second
bilinear relations, via `AX_RiemannBilinear`. We axiomatize it directly
for now; when `AX_RiemannBilinear` lands as a named axiom (in a later
module), this becomes a *theorem* derived from it.

See `docs/formalization-plan.md` §7; discharge-priority #1. -/
axiom AX_PeriodInjective {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Function.Injective (periodMap X x₀)

-- TODO (loopToHomology): the explicit map `Path X x₀ x₀ → H1 X x₀`
-- via `Abelianization.of ∘ FundamentalGroup.ofPath`.
-- Consumer: relating `periodMap (loopToHomology γ) ω` to `pathIntegral γ ω`
-- once PathIntegral.lean is in place.

-- TODO (intersectionPairing): define
--   `intersectionPairing X x₀ : H1 X x₀ →+ (H1 X x₀ →+ ℤ)`
-- as the algebraic intersection number. Needs orientation on `X` (which
-- we get from the complex structure). Symplectic non-degeneracy is deep
-- topology; may need to axiomatize pending surface-classification work.

-- TODO (intersectionPairing_symplectic): statement that the pairing is
-- alternating and non-degenerate. Axiomatize if the proof is too heavy.

end Jacobians.RiemannSurface.IntersectionForm
