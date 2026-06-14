/-
S2 integration probe (docs/planning/PHASE_D_BRIDGE_PLAN.md, item A3).

Imports our ENTIRE library root alongside the two Kirov-Dolbeault-port modules
the Phase-D bridges will consume. Lean errors loudly on any duplicate full
declaration name between the two libraries, so this file compiling IS the
collision check for strategy S2 (path dependency, no declaration renames:
the port keeps its upstream `Jacobians.*` namespaces; only its MODULE root
was renamed to `KirovDolbeault`).

NOT imported from the `Jacobians` root module: this is a probe, not a bridge.
The real bridge files (A4) will import only the port modules they need.
-/
import Submission.Jacobians
import Submission.KirovDolbeault.Dolbeault.CechFinitenessWiring
import Submission.KirovDolbeault.Dolbeault.CohomologicalRR

open scoped Manifold ContDiff Topology

/-! Sanity: both bridge targets are visible with their expected shapes,
and our own headline interface is still resolvable unambiguously. -/

#check @Jacobians.Dolbeault.exists_cechModel
#check @Jacobians.Dolbeault.FiniteCover.exists_skyscraperLES
#check @Jacobians.Dolbeault.FiniteCover.chi_add_single

open Jacobians Jacobians.Dolbeault in
example {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (𝔘 : FiniteCover X) (D : Divisor X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d),
      Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  exists_cechModel 𝔘 D
