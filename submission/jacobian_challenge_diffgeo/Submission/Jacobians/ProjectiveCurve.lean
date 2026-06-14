/-
Track 2 — concrete projective-curve models of compact Riemann surfaces.

Each module in `Jacobians/ProjectiveCurve/` defines a type `X` satisfying Buzzard's
typeclass constraints by construction, with explicit charts. These provide a rich
population of X on which Buzzard's 24 sorries can be closed without any appeal to
Riemann's existence theorem.

See `docs/formalization-plan.md` §3.5 for the design.
-/
import Submission.Jacobians.ProjectiveCurve.Charts
import Submission.Jacobians.ProjectiveCurve.Line
import Submission.Jacobians.ProjectiveCurve.Line.Genus
import Submission.Jacobians.ProjectiveCurve.Line.Witnesses
import Submission.Jacobians.ProjectiveCurve.Line.OneForm
import Submission.Jacobians.ProjectiveCurve.Elliptic
import Submission.Jacobians.ProjectiveCurve.Elliptic.Genus
import Submission.Jacobians.ProjectiveCurve.Elliptic.OneForm
import Submission.Jacobians.ProjectiveCurve.Elliptic.Witnesses
import Submission.Jacobians.ProjectiveCurve.Elliptic.Periods
import Submission.Jacobians.ProjectiveCurve.Elliptic.OfCurveInj
import Submission.Jacobians.ProjectiveCurve.Elliptic.H1Basis
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.Even
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.OddForm
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.CycleLoops
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.CycleBasisWitness
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.BoundaryWord
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas.InfinityAffineChart
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.Form
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.LiouvilleSupport
import Submission.Jacobians.ProjectiveCurve.Hyperelliptic.Involution
import Submission.Jacobians.ProjectiveCurve.PlaneCurve
import Submission.Jacobians.ProjectiveCurve.PlaneCurve.AtlasCompat
import Submission.Jacobians.ProjectiveCurve.PlaneCurve.CrossCompat
