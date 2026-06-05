/-
Part B — Riemann-surface-specific constructions.

Content is split across six submodules:

* `Jacobians.RiemannSurface.OneForm`       — `HolomorphicOneForm X`
* `Jacobians.RiemannSurface.PathIntegral`  — line integration along smooth paths
* `Jacobians.RiemannSurface.Homology`      — `H_1(X, ℤ) := Abelianization (π₁ X x₀)`
* `Jacobians.RiemannSurface.IntersectionForm` — Hurewicz + symplectic pairing
* `Jacobians.RiemannSurface.Periods`       — period pairing + period matrix in `𝔥_g`
* `Jacobians.RiemannSurface.Genus`         — `genus X := finrank ℂ (HolomorphicOneForm X)`
* `Jacobians.RiemannSurface.GenusInvariance` — biholomorphism invariance of genus

See `docs/formalization-plan.md` §4 for the design.
-/
import Jacobians.RiemannSurface.OneForm
import Jacobians.RiemannSurface.AnalyticArc
import Jacobians.RiemannSurface.ChartPartition
import Jacobians.RiemannSurface.SquareSubdivision
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.Genus
import Jacobians.RiemannSurface.GenusInvariance
import Jacobians.RiemannSurface.LineBundle
import Jacobians.RiemannSurface.MeromorphicFunctionField
import Jacobians.RiemannSurface.MeromorphicToP1
import Jacobians.RiemannSurface.DegreeOneGenusZero
import Jacobians.RiemannSurface.MultiChartIntegral
import Jacobians.RiemannSurface.IntegrandIndependence
import Jacobians.RiemannSurface.ArcChartDifferentiable
import Jacobians.RiemannSurface.SegmentCenterIndependence
import Jacobians.RiemannSurface.SegmentAdjacency
import Jacobians.RiemannSurface.PartitionIndependence
import Jacobians.RiemannSurface.CanonicalArcIntegral
import Jacobians.RiemannSurface.HomotopyInvariance
import Jacobians.RiemannSurface.DevelopingMap
import Jacobians.RiemannSurface.LoopIntegral
import Jacobians.RiemannSurface.SheafCohomologySpec
import Jacobians.RiemannSurface.Periods
import Jacobians.RiemannSurface.IntersectionForm
import Jacobians.RiemannSurface.PathIntegral
