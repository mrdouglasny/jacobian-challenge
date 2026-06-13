/-
# `AX_PeriodCycleBasis`-free period-lattice instances (RELOCATE)

The two global instances `instPeriodLatticeDiscrete` / `AX_PeriodLattice`
(`DiscreteTopology` / `IsZLattice` of `periodLatticeInBasis`) used to live in
`Jacobians/Axioms/PeriodLattice.lean`, proved through the Layer-3 engine from
the chosen `AX_PeriodCycleBasis` witness.

This file **relocates** them to their `AX_PeriodCycleBasis`-free T-GEN proofs
(`periodLatticeInBasis_{discreteTopology,isZLattice}_of_tgen` in
`RiemannSurface/Path2Prototype.lean`, fed the now-unconditional
`analyticLoopsGenerateH1` from `RiemannSurface/ChartFlatHomotopyWallProof.lean`).

These T-GEN proofs cannot live in `PeriodLattice.lean` itself (the analytic-loop
bridge transitively imports `LoopIntegralHom` → `Axioms.PeriodLattice`, so
importing it there would cycle). Putting the instances *here* — downstream of
the period machinery — breaks the cycle: `PeriodLattice.lean` keeps the
`periodLatticeInBasis` def (via `PeriodLatticeBase`) and stops declaring the
instances, while every instance-consumer imports this module instead.

The signatures match the originals byte-for-byte (same binders, same
`[CompactSpace X]` etc.), so downstream typeclass synthesis is unchanged.
-/
import Jacobians.Axioms.PeriodLatticeBase
import Jacobians.RiemannSurface.Path2Prototype
import Jacobians.RiemannSurface.ChartFlatHomotopyWallProof

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- In basis coordinates, the period image carries the discrete topology.
**`AX_PeriodCycleBasis`-free** (RELOCATE): proved via
`periodLatticeInBasis_discreteTopology_of_tgen` fed the unconditional
`analyticLoopsGenerateH1`. Replaces the former Layer-3/cycle-basis proof. -/
theorem instPeriodLatticeDiscrete (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (periodLatticeInBasis X x₀ b) :=
  Jacobians.RiemannSurface.periodLatticeInBasis_discreteTopology_of_tgen x₀ b
    (Jacobians.RiemannSurface.analyticLoopsGenerateH1 x₀)

attribute [instance] instPeriodLatticeDiscrete

/-- In basis coordinates, the image of the period map is a full `ℤ`-lattice
in `Fin (genus X) → ℂ`. **`AX_PeriodCycleBasis`-free** (RELOCATE): proved via
`periodLatticeInBasis_isZLattice_of_tgen` fed the unconditional
`analyticLoopsGenerateH1`. Replaces the former Layer-3/cycle-basis proof. -/
theorem AX_PeriodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    IsZLattice ℝ (periodLatticeInBasis X x₀ b) :=
  Jacobians.RiemannSurface.periodLatticeInBasis_isZLattice_of_tgen x₀ b
    (Jacobians.RiemannSurface.analyticLoopsGenerateH1 x₀)

attribute [instance] AX_PeriodLattice

end Jacobians.Axioms
