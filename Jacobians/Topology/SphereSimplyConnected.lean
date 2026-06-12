/-
# `S²` is simply connected — bridge into the topology umbrella

Goal A of `docs/planning/HANDOVER_PARALLEL_ACCOUNT.md` (S2 lane): expose

```
SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
```

— π₁(S²) = 1, absent from Mathlib at our pin — in the exact shape consumed by
`Jacobians.RiemannSurface.genus_eq_zero_of_homeo_sphere`
(`Jacobians/RiemannSurface/GenusZeroBackward.lean`, PR #199), completing the
backward leg of `AX_genus_eq_zero_iff_homeo`.

The proof is the ported Kirov two-open van Kampen development
(`KirovDolbeault/SphereSimplyConnected.lean` — the `OnePoint ℂ` chart/overlap
side conditions and the transport `OnePoint ℂ ≃ₜ S²`;
`KirovDolbeault/VanKampen.lean` — Lebesgue subdivision + telescoping proof of
the abstract `TwoOpenVanKampen`, Apache 2.0, Rado Kirov). This file follows the
repo's bridge pattern (cf. `Jacobians/Bridge/`): it imports the existing
in-tree port — no new vendoring — and re-states the instance under our
namespace so downstream files need not name the port.

The companion theorem `simplyConnectedSpace_sphere` is the named-form for
explicit-hypothesis consumers such as `genus_eq_zero_of_homeo_sphere`.
-/
import KirovDolbeault.VanKampen

namespace Jacobians.Topology

/-- **The Euclidean 2-sphere `S² ⊆ ℝ³` is simply connected** (π₁(S²) = 1).
Proof: two-open Seifert–van Kampen for the chart cover of the model
`OnePoint ℂ`, transported along `OnePoint ℂ ≃ₜ S²` (Kirov port). This is the
exact hypothesis of `genus_eq_zero_of_homeo_sphere`. -/
theorem simplyConnectedSpace_sphere :
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  inferInstance

end Jacobians.Topology
