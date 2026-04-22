/-
Symplectic intersection pairing on `H1 X x₀` + period-map injectivity.

Three things this module consumes, per the plan §4.5:

1. **Hurewicz bridge.** `H1 X x₀ = Additive (Abelianization (π₁ X x₀))` is
   already the abelianization. What's missing is the explicit map taking
   a loop (a `Path` in Mathlib terms) to its class in `H1`, so downstream
   we can write `periodMap x₀ (loopToHomology γ) ω = pathIntegral γ ω`.

2. **Intersection pairing.** On a compact oriented surface `X` of genus
   `g`, `H1 X x₀` carries a non-degenerate alternating ℤ-bilinear
   "intersection" pairing. Axiomatized as
   `Jacobians.Axioms.intersectionForm` + `AX_IntersectionForm_{alternating,
   nondeg}` in `Jacobians/Axioms/IntersectionForm.lean` (added 2026-04-22
   per Gemini review). Needed to: (a) state Riemann's bilinear relations
   (`Im τ` is positive-definite *w.r.t. the intersection form*), (b)
   extract a symplectic basis `{α_i, β_j}`, (c) state the normalized
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

**Upgrade path (flagged by Gemini 2026-04-22).** Injectivity alone is
not enough to build `Jacobian X` as a complex torus — the image of an
injective ℤ-linear map into `ℝ^(2g)` can still be dense. The Jacobian
construction needs the image to be a *ℤ-lattice* (discrete of full
real rank). The bridge construction will upgrade this to:

    axiom AX_PeriodLattice : IsZLattice ℝ (LinearMap.range (periodMap_NACG X x₀))

where `periodMap_NACG` is the post-basis-pick composite landing in the
ambient `NormedAddCommGroup` `Fin (genus X) → ℂ` (see the Jacobian
bridge design note in `docs/formalization-plan.md` §4.6). Doing that
here would require baking in the `NormedAddCommGroup` structure that
`ComplexTorus` demands, which is a Part-B-architecture decision we
defer to the bridge. See `docs/formalization-plan.md` §7; discharge
priority #1 in the revised ordering. -/
axiom AX_PeriodInjective {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Function.Injective (periodMap X x₀)

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
