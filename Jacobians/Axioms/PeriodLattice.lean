/-
`AX_PeriodLattice`: the period image in basis coordinates is a full
`ℤ`-lattice in `ℂ^g`. **Now a THEOREM** (Layer-3 Phase C), together with its
discreteness companion — both proved in `Jacobians/Layer3/Periods.lean` from
the R1/R2 fields of the chosen `AX_PeriodCycleBasis` witness (D1 merge
2026-06-10; formerly the basis-free primitives `AX_RBR1`/`AX_RBR2`) through
the axiom-free period-lattice engine. The names and `instance` attributes are
kept so all downstream consumers (the Jacobian bridge) are untouched.

## Construction-level setup

`periodMap X x₀` lands in `(HolomorphicOneForm X →ₗ[ℂ] ℂ)`. The Jacobian
bridge in `Jacobians/Jacobian/Construction.lean` needs a lattice inside the
concrete ambient `Fin (genus X) → ℂ`, so `Axioms/PeriodLatticeBase.lean`
fixes a basis `b` and transports the period map into coordinates
(`periodMapInBasis`); its range `periodLatticeInBasis X x₀ b` is the lattice
used by the bridge construction.

## Proof route (Layer-3 Phase C)

Mumford, *Tata Lectures on Theta I*, Ch. II §2; Griffiths-Harris, Ch. 2 §2.
For the A-normalized form basis the lattice is exactly the `[I | τ]` column
lattice of the engine (`periodLatticeInBasis_normalized_eq`, using `τ = τᵀ`
for the row/column bridge), where `Im τ ≻ 0` comes from the witness's R2
field; an arbitrary basis is reached by `ZLattice.comap` along the
dual-coordinate change. Remaining trust: `AX_PeriodCycleBasis` alone (D1:
the intersection form is no longer in this cone).
-/
import Jacobians.Axioms.PeriodLatticeBase
import Jacobians.Layer3.Periods
import Jacobians.RiemannSurface.Path2Prototype
import Jacobians.RiemannSurface.ChartFlatHomotopyWallProof

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- In basis coordinates, the period image carries the discrete topology.
**Discharged to a theorem** (Layer-3 Phase C): proved in
`Layer3/Periods.lean` from the chosen witness's R2 field (positivity ⇒
`Im τ ≻ 0` ⇒ the engine's discrete `[I | τ]` lattice) and the
dual-coordinate-change transport. -/
theorem instPeriodLatticeDiscrete (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (periodLatticeInBasis X x₀ b) :=
  -- AXIOM-FREE (T-GEN discharged via PL approximation): routes through the
  -- unconditional `analyticLoopsGenerateH1`, not `AX_PeriodCycleBasis`.
  Jacobians.RiemannSurface.periodLatticeInBasis_discreteTopology_of_tgen x₀ b
    (Jacobians.RiemannSurface.analyticLoopsGenerateH1 x₀)

attribute [instance] instPeriodLatticeDiscrete

/-- In basis coordinates, the image of the period map is a full `ℤ`-lattice
in `Fin (genus X) → ℂ`. **Discharged to a theorem** (Layer-3 Phase C): proved
in `Layer3/Periods.lean` from the chosen witness's R1 + R2 fields through
the axiom-free period-lattice engine (`Im τ ≻ 0` ⇒ full `IsZLattice`),
transported to every form basis. -/
theorem AX_PeriodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    IsZLattice ℝ (periodLatticeInBasis X x₀ b) :=
  -- AXIOM-FREE (T-GEN discharged): full-rank lattice via the unconditional
  -- `analyticLoopsGenerateH1`, not `AX_PeriodCycleBasis`.
  Jacobians.RiemannSurface.periodLatticeInBasis_isZLattice_of_tgen x₀ b
    (Jacobians.RiemannSurface.analyticLoopsGenerateH1 x₀)

attribute [instance] AX_PeriodLattice

end Jacobians.Axioms
