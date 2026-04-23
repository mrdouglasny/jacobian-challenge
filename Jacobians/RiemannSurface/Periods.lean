/-
`periodMap X x₀` — period pairing `H1 X x₀ → (HolomorphicOneForm X)^∨`.

The natural definition is `γ ↦ (ω ↦ ∫_γ ω)`, where the integral is taken
over any loop representative of the homology class. Well-definedness on
`H1 = Abelianization (π₁)` follows from homotopy invariance of the path
integral of a holomorphic 1-form (Cauchy's theorem applied in chart-local
disks, patched via Stokes on a CW structure).

**Current status (2026-04-23):** axiom retired; `periodMap` is now a
real `def` routing through `Jacobians.RiemannSurface.loopIntegralToH1`
in `PathIntegral.lean`. `loopIntegralToH1` is the axiomatized compound
"integral along a loop, descended to H_1" — the atomic classical fact,
which retires when multi-chart `pathIntegralAnalyticArc` + homotopy
invariance land.

**Associated deep axiom:** `AX_RiemannBilinear` — the period matrix
(in any basis of `HolomorphicOneForm X`) is symmetric with positive-
definite imaginary part. See `Axioms/RiemannBilinear.lean`.

See `docs/formalization-plan.md` §4.4.
-/
import Jacobians.RiemannSurface.OneForm
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.PathIntegral

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

/-- The period pairing `H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)`.

**Definition.** Routes through `loopIntegralToH1` from
`PathIntegral.lean`, which wraps the "integral along a loop, descended
to H_1" classical object as a single axiom.

Retired from axiom to `def` (2026-04-23). -/
noncomputable def periodMap (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
  loopIntegralToH1 x₀

-- TODO (periodLattice): define
--   `periodLattice X x₀ : AddSubgroup (HolomorphicOneForm X →ₗ[ℂ] ℂ)`
-- as the range of `periodMap X x₀`. Used in `Jacobian/Construction.lean`
-- to define `Jacobian X`.

-- TODO (periodLattice_basepoint_eq): prove basepoint independence of
-- `periodLattice` via path conjugation (consumer-level fact used for
-- Jacobian basepoint independence). Equivalent to a `Function.Injective`-
-- style iso through the `fundamentalGroupMulEquivOfPathConnected`.

-- TODO (period matrix — derived): given bases of H1 (from AX_H1FreeRank2g)
-- and HolomorphicOneForm (from AX_FiniteDimOneForms), produce the period
-- matrix in SiegelUpperHalfSpace (genus X) via AX_RiemannBilinear.

end Jacobians.RiemannSurface
