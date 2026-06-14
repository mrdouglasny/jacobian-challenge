/-
`genus ProjectiveLine = 0`.

**Direct proof (axiom-free).** By definition `genus X = Module.finrank ℂ
(HolomorphicOneForm X)`, and `Line/OneForm.lean` proves
`Subsingleton (HolomorphicOneForm ProjectiveLine)` directly via Liouville
(no uniformization axiom). The `finrank` of a subsingleton module is `0`.

This **retires `AX_genus_eq_zero_iff_homeo` from the `genus ℙ¹ = 0` cell**.
The previous proof routed through that uniformization axiom; the
dependency is now inverted — `Line/OneForm.lean` proves the subsingleton
from first principles and this file derives the genus from it. The
abstract `genus_eq_zero_iff_homeo` in `Challenge.lean` still uses the
axiom; only the concrete ℙ¹ value no longer does. See
`docs/contracts/genus.md`.
-/
import Submission.Jacobians.ProjectiveCurve.Line.OneForm
import Submission.Jacobians.RiemannSurface.Genus

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- The genus of `ProjectiveLine` is zero. Axiom-free: `finrank` of the
(subsingleton) space of holomorphic 1-forms on ℙ¹, which vanishes by the
direct Liouville argument in `Line/OneForm.lean`. -/
theorem genus_projectiveLine_eq_zero :
    Jacobians.RiemannSurface.genus ProjectiveLine = 0 :=
  Module.finrank_eq_zero_of_subsingleton ℂ (HolomorphicOneForm ProjectiveLine)

end Jacobians.ProjectiveCurve
