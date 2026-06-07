/-
`genus (Elliptic ω₁ ω₂ h) = 1`.

## Status (2026-04-24)

**Retired from axiom to derived theorem.** The proof is in
`Jacobians/ProjectiveCurve/Elliptic/OneForm.lean`:

- `ellipticDz` is a concrete real element of `HolomorphicOneForm
  (Elliptic ω₁ ω₂ h)` with chart-local coefficient `1` on each chart
  target (and `0` off-target via the `IsZeroOffChartTarget`
  normalisation).
- `ellipticCoeff_eq_const_on_targets` uses
  `MDifferentiable.exists_eq_const_of_compactSpace` (Mathlib's
  smooth-functions-on-compact-complex-manifold-are-constant theorem,
  the intrinsic Liouville) to show the chart-centre coefficient
  function is constant.
- `eq_smul_ellipticDz` combines this with the `IsZeroOffChartTarget`
  normalisation: on-target equality extends to full submodule
  equality.
- `genus_Elliptic_eq_one` concludes via `finrank_le_of_span_eq_top` +
  `genus_Elliptic_pos`.

This file now simply re-exports the theorem under the
historical name `AX_genus_Elliptic_eq_one` for backward compatibility
of downstream consumers. **No new axiom introduced.**

Reference: Mumford, *Tata Lectures on Theta I*, Ch. I §1; Silverman,
*The Arithmetic of Elliptic Curves*, Ch. VI §5.
-/
import Jacobians.ProjectiveCurve.Elliptic
import Jacobians.ProjectiveCurve.Elliptic.OneForm
import Jacobians.RiemannSurface.OneForm
import Jacobians.RiemannSurface.Genus

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Theorem** (formerly `AX_genus_Elliptic_eq_one` axiom, retired
2026-04-24). The genus of any elliptic curve `ℂ / (ℤω₁ + ℤω₂)` is 1.
Derived from `genus_Elliptic_eq_one` in `Elliptic/OneForm.lean`. -/
theorem AX_genus_Elliptic_eq_one (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    Jacobians.RiemannSurface.genus (Elliptic ω₁ ω₂ h) = 1 :=
  genus_Elliptic_eq_one ω₁ ω₂ h

end Jacobians.ProjectiveCurve
