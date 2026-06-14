/-
`periodMap X x₀` — period pairing `H1 X x₀ → (HolomorphicOneForm X)^∨`.

The natural definition is `γ ↦ (ω ↦ ∫_γ ω)`, where the integral is taken
over any loop representative of the homology class. Well-definedness on
`H1 = Abelianization (π₁)` follows from homotopy invariance of the path
integral of a holomorphic 1-form (Cauchy's theorem applied in chart-local
disks, patched via Stokes on a CW structure).

**Current status:** `periodMap` is a real `def` routing through
`Jacobians.RiemannSurface.loopIntegralToH1` in `LoopIntegral.lean`.
`loopIntegralToH1` is constructed from the analytic cycle basis and
canonical arc integrals.

**Associated deep axiom:** `AX_RiemannBilinear` — the period matrix
(in any basis of `HolomorphicOneForm X`) is symmetric with positive-
definite imaginary part. See `Axioms/RiemannBilinear.lean`.

See `docs/formalization-plan.md` §4.4.
-/
import Submission.Jacobians.RiemannSurface.OneForm
import Submission.Jacobians.RiemannSurface.Homology
import Submission.Jacobians.RiemannSurface.PathIntegral
import Submission.Jacobians.RiemannSurface.LoopIntegral

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff

/-- The period pairing `H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)`.

**Definition.** Routes through `loopIntegralToH1` from
`LoopIntegral.lean`. -/
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
