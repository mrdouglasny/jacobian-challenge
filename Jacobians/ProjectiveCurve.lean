/-
Track 2 — concrete projective-curve models of compact Riemann surfaces.

Each module in `Jacobians/ProjectiveCurve/` defines a type `X` satisfying Buzzard's
typeclass constraints by construction, with explicit charts. These provide a rich
population of X on which Buzzard's 24 sorries can be closed without any appeal to
Riemann's existence theorem.

See `docs/formalization-plan.md` §3.5 for the design.
-/
import Jacobians.ProjectiveCurve.Charts
import Jacobians.ProjectiveCurve.Line
import Jacobians.ProjectiveCurve.Line.Genus
import Jacobians.ProjectiveCurve.Line.Witnesses
import Jacobians.ProjectiveCurve.Line.OneForm
import Jacobians.ProjectiveCurve.Elliptic
import Jacobians.ProjectiveCurve.Elliptic.Genus
import Jacobians.ProjectiveCurve.Elliptic.OneForm
import Jacobians.ProjectiveCurve.Elliptic.Witnesses
import Jacobians.ProjectiveCurve.Hyperelliptic
import Jacobians.ProjectiveCurve.Hyperelliptic.Even
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas.InfinityAffineChart
import Jacobians.ProjectiveCurve.PlaneCurve
