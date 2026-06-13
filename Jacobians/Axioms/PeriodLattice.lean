/-
Period-lattice setup. `periodMap X x₀` lands in
`(HolomorphicOneForm X →ₗ[ℂ] ℂ)`; the Jacobian bridge in
`Jacobians/Jacobian/Construction.lean` needs a lattice inside the concrete
ambient `Fin (genus X) → ℂ`, so `Axioms/PeriodLatticeBase.lean` fixes a basis
`b` and transports the period map into coordinates (`periodMapInBasis`); its
range `periodLatticeInBasis X x₀ b` is the lattice used by the bridge.

## Instances relocated (RELOCATE)

The two global instances `instPeriodLatticeDiscrete` / `AX_PeriodLattice`
(`DiscreteTopology` / `IsZLattice` of `periodLatticeInBasis`) used to be proved
here through the Layer-3 engine from the chosen `AX_PeriodCycleBasis` witness.
They now live in `Jacobians/Axioms/PeriodLatticeTGen.lean`, proved
`AX_PeriodCycleBasis`-free from T-GEN (the unconditional
`analyticLoopsGenerateH1`). They cannot live here: the T-GEN bridge
transitively imports `LoopIntegralHom` → this module, which would cycle.
This module keeps only the `periodLatticeInBasis` def (via `PeriodLatticeBase`).
-/
import Jacobians.Axioms.PeriodLatticeBase

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-! ## Period-lattice instances relocated (RELOCATE)

The two global instances `instPeriodLatticeDiscrete` / `AX_PeriodLattice`
(`DiscreteTopology` / `IsZLattice` of `periodLatticeInBasis`) have been
**relocated** to `Jacobians/Axioms/PeriodLatticeTGen.lean`, where they are
proved `AX_PeriodCycleBasis`-free from T-GEN (the unconditional
`analyticLoopsGenerateH1`). They cannot live here because the T-GEN bridge
transitively imports `LoopIntegralHom` → this module (an import cycle). Every
former consumer now imports `Axioms.PeriodLatticeTGen`; the signatures are
byte-identical, so downstream typeclass synthesis is unchanged. This module
keeps only the `periodLatticeInBasis` def (via `PeriodLatticeBase`). -/

end Jacobians.Axioms
