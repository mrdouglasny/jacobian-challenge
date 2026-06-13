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
import Jacobians.RiemannSurface.Divisor
import Jacobians.RiemannSurface.Cohomology.LineBundle
import Jacobians.RiemannSurface.MeromorphicFunctionField
import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace
import Jacobians.RiemannSurface.Cohomology.Repartitions
import Jacobians.RiemannSurface.Cohomology.H1
import Jacobians.RiemannSurface.Cohomology.RiemannRochAnchor
import Jacobians.RiemannSurface.Cohomology.RiemannRochAPI
import Jacobians.RiemannSurface.Cohomology.SerreDualityAPI
import Jacobians.RiemannSurface.PluckerAPI
import Jacobians.RiemannSurface.MeromorphicToP1
import Jacobians.RiemannSurface.DegreeOneGenusZero
import Jacobians.RiemannSurface.MultiChartIntegral
import Jacobians.RiemannSurface.IntegrandIndependence
import Jacobians.RiemannSurface.ArcChartDifferentiable
import Jacobians.RiemannSurface.SegmentCenterIndependence
import Jacobians.RiemannSurface.SegmentAdjacency
import Jacobians.RiemannSurface.PartitionIndependence
import Jacobians.RiemannSurface.CanonicalArcIntegral
import Jacobians.RiemannSurface.ArcAlgebra
import Jacobians.RiemannSurface.AnalyticArcMovingChart
import Jacobians.RiemannSurface.LoopConjugation
import Jacobians.RiemannSurface.HomotopyInvariance
import Jacobians.RiemannSurface.DevelopingMap
import Jacobians.RiemannSurface.DevelopingValueAlgebra
import Jacobians.RiemannSurface.DevelopingBridge
import Jacobians.RiemannSurface.HomotopyInvarianceDevelop
import Jacobians.RiemannSurface.LoopIntegralHom
import Jacobians.RiemannSurface.LoopIntegral
import Jacobians.RiemannSurface.BilinearRelations
import Jacobians.RiemannSurface.BilinearRelationsBoundaryWord
import Jacobians.RiemannSurface.BilinearRelationsBoundaryWordInterior
import Jacobians.RiemannSurface.QuotientCoveringPi1
import Jacobians.RiemannSurface.BoundaryWordElliptic
import Jacobians.RiemannSurface.BoundaryWordPolynomial
import Jacobians.RiemannSurface.BoundaryWordEllipticPoly
import Jacobians.RiemannSurface.ChartSegmentArc
import Jacobians.RiemannSurface.AbelPlumbing
import Jacobians.RiemannSurface.AbelSupsetPlumbing
import Jacobians.RiemannSurface.AbelSupsetSections
import Jacobians.RiemannSurface.AbelSupsetPencil
import Jacobians.RiemannSurface.AbelSupsetLiouville
import Jacobians.RiemannSurface.GenusZeroBackward
import Jacobians.RiemannSurface.GenusZeroForward
import Jacobians.RiemannSurface.PeriodNondegeneracy
import Jacobians.RiemannSurface.PeriodDiscreteness
import Jacobians.RiemannSurface.PeriodDiscretenessFromR2
import Jacobians.RiemannSurface.HomologyGeneration
import Jacobians.RiemannSurface.H1Composite
import Jacobians.RiemannSurface.Cohomology.SheafCohomologySpec
import Jacobians.RiemannSurface.Periods
import Jacobians.RiemannSurface.IntersectionForm
import Jacobians.RiemannSurface.PathIntegral
