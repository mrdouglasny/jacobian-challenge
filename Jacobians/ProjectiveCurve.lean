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
import Jacobians.ProjectiveCurve.Elliptic
