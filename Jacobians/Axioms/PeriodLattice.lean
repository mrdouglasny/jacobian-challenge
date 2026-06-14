/-
`AX_PeriodLattice`: the period image in basis coordinates is a full
`ℤ`-lattice in `ℂ^g`. **A THEOREM, axiom-free (standard-3)**, together with its
discreteness companion `instPeriodLatticeDiscrete`. The names and `instance`
attributes are kept so all downstream consumers (the Jacobian bridge) are
untouched.

## Construction-level setup

`periodMap X x₀` lands in `(HolomorphicOneForm X →ₗ[ℂ] ℂ)`. The Jacobian
bridge in `Jacobians/Jacobian/Construction.lean` needs a lattice inside the
concrete ambient `Fin (genus X) → ℂ`, so `Axioms/PeriodLatticeBase.lean`
fixes a basis `b` and transports the period map into coordinates
(`periodMapInBasis`); its range `periodLatticeInBasis X x₀ b` is the lattice
used by the bridge construction.

## Proof route (T-GEN, 2026-06-14, PR #251)

Both instances are reproved from the **unconditional T-GEN theorem**
`Jacobians.RiemannSurface.analyticLoopsGenerateH1` (PR #248) via the bridge
lemmas `periodLatticeInBasis_{discreteTopology,isZLattice}_of_tgen`
(`Path2Prototype.lean`): under T-GEN the headline lattice `periodLatticeInBasis`
equals the analytic-loop period lattice `loopPeriodLattice`, whose discreteness
(K-LITE, `discreteTopology_loopPeriodLattice`) and full-rank spanning
(`span_real_loopPeriodLattice_eq_top`) are both standard-3. **No
`AX_PeriodCycleBasis`** — that axiom is no longer in these instances' closure
(nor any Buzzard headline's; see `docs/axiom-report.txt`). The earlier Layer-3
Phase-C route through the chosen `AX_PeriodCycleBasis` witness's R1/R2 fields
(Mumford, *Tata Lectures on Theta I*, Ch. II §2; Griffiths-Harris, Ch. 2 §2) is
**superseded** and no longer the trust basis here.
-/
import Jacobians.Axioms.PeriodLatticeBase
import Jacobians.Layer3.Periods
-- T-GEN route: the two global period-lattice instances are reproved from the
-- now-unconditional T-GEN theorem (`analyticLoopsGenerateH1`), dropping
-- `AX_PeriodCycleBasis` from their bodies (and hence from every headline whose
-- only axiom dependency was these instances). The earlier import cycle is broken
-- by `LoopIntegralHom` importing `PeriodLatticeBase`.
import Jacobians.RiemannSurface.Path2Prototype
import Jacobians.RiemannSurface.ChartFlatHomotopyWallProof

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- In basis coordinates, the period image carries the discrete topology.
**Axiom-free theorem (standard-3)**: reproved from the unconditional T-GEN
theorem `analyticLoopsGenerateH1` via `periodLatticeInBasis_discreteTopology_of_tgen`
(the headline lattice equals the analytic-loop lattice `loopPeriodLattice`,
whose K-LITE discreteness is standard-3). No `AX_PeriodCycleBasis`. -/
theorem instPeriodLatticeDiscrete (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (periodLatticeInBasis X x₀ b) :=
  Jacobians.RiemannSurface.periodLatticeInBasis_discreteTopology_of_tgen x₀ b
    (Jacobians.RiemannSurface.analyticLoopsGenerateH1 x₀)

attribute [instance] instPeriodLatticeDiscrete

/-- In basis coordinates, the image of the period map is a full `ℤ`-lattice
in `Fin (genus X) → ℂ`. **Axiom-free theorem (standard-3)**: reproved from the
unconditional T-GEN theorem `analyticLoopsGenerateH1` via
`periodLatticeInBasis_isZLattice_of_tgen` (full-rank spanning
`span_real_loopPeriodLattice_eq_top` of the analytic-loop lattice). No
`AX_PeriodCycleBasis`. -/
theorem AX_PeriodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    IsZLattice ℝ (periodLatticeInBasis X x₀ b) :=
  Jacobians.RiemannSurface.periodLatticeInBasis_isZLattice_of_tgen x₀ b
    (Jacobians.RiemannSurface.analyticLoopsGenerateH1 x₀)

attribute [instance] AX_PeriodLattice

end Jacobians.Axioms
