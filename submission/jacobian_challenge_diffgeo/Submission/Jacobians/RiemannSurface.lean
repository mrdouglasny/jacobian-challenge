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
import Submission.Jacobians.RiemannSurface.OneForm
import Submission.Jacobians.RiemannSurface.AnalyticArc
import Submission.Jacobians.RiemannSurface.ChartPartition
import Submission.Jacobians.RiemannSurface.SquareSubdivision
import Submission.Jacobians.RiemannSurface.Homology
import Submission.Jacobians.RiemannSurface.Genus
import Submission.Jacobians.RiemannSurface.GenusInvariance
import Submission.Jacobians.RiemannSurface.Divisor
import Submission.Jacobians.RiemannSurface.Cohomology.LineBundle
import Submission.Jacobians.RiemannSurface.MeromorphicFunctionField
import Submission.Jacobians.RiemannSurface.Cohomology.RiemannRochSpace
import Submission.Jacobians.RiemannSurface.Cohomology.Repartitions
import Submission.Jacobians.RiemannSurface.Cohomology.H1
import Submission.Jacobians.RiemannSurface.Cohomology.RiemannRochAnchor
import Submission.Jacobians.RiemannSurface.Cohomology.RiemannRochAPI
import Submission.Jacobians.RiemannSurface.Cohomology.SerreDualityAPI
import Submission.Jacobians.RiemannSurface.PluckerAPI
import Submission.Jacobians.RiemannSurface.MeromorphicToP1
import Submission.Jacobians.RiemannSurface.DegreeOneGenusZero
import Submission.Jacobians.RiemannSurface.MultiChartIntegral
import Submission.Jacobians.RiemannSurface.IntegrandIndependence
import Submission.Jacobians.RiemannSurface.ArcChartDifferentiable
import Submission.Jacobians.RiemannSurface.SegmentCenterIndependence
import Submission.Jacobians.RiemannSurface.SegmentAdjacency
import Submission.Jacobians.RiemannSurface.PartitionIndependence
import Submission.Jacobians.RiemannSurface.CanonicalArcIntegral
import Submission.Jacobians.RiemannSurface.ArcAlgebra
import Submission.Jacobians.RiemannSurface.AnalyticArcMovingChart
import Submission.Jacobians.RiemannSurface.SubintervalHomotopy
import Submission.Jacobians.RiemannSurface.SmoothAnalyticLoop
import Submission.Jacobians.RiemannSurface.TGenFinalReduction
import Submission.Jacobians.RiemannSurface.PLApproxGeneration
import Submission.Jacobians.RiemannSurface.ChartFlatHomotopyWallProof
import Submission.Jacobians.RiemannSurface.LoopConjugation
import Submission.Jacobians.RiemannSurface.HomotopyInvariance
import Submission.Jacobians.RiemannSurface.DevelopingMap
import Submission.Jacobians.RiemannSurface.DevelopingValueAlgebra
import Submission.Jacobians.RiemannSurface.DevelopingBridge
import Submission.Jacobians.RiemannSurface.HomotopyInvarianceDevelop
import Submission.Jacobians.RiemannSurface.LoopIntegralHom
import Submission.Jacobians.RiemannSurface.LoopIntegral
import Submission.Jacobians.RiemannSurface.BilinearRelations
import Submission.Jacobians.RiemannSurface.BilinearRelationsBoundaryWord
import Submission.Jacobians.RiemannSurface.BilinearRelationsBoundaryWordInterior
import Submission.Jacobians.RiemannSurface.QuotientCoveringPi1
import Submission.Jacobians.RiemannSurface.BoundaryWordElliptic
import Submission.Jacobians.RiemannSurface.BoundaryWordPolynomial
import Submission.Jacobians.RiemannSurface.BoundaryWordEllipticPoly
import Submission.Jacobians.RiemannSurface.ChartSegmentArc
import Submission.Jacobians.RiemannSurface.AbelPlumbing
import Submission.Jacobians.RiemannSurface.AbelSupsetPlumbing
import Submission.Jacobians.RiemannSurface.AbelSupsetSections
import Submission.Jacobians.RiemannSurface.AbelSupsetPencil
import Submission.Jacobians.RiemannSurface.AbelSupsetLiouville
import Submission.Jacobians.RiemannSurface.GenusZeroBackward
import Submission.Jacobians.RiemannSurface.GenusZeroForward
import Submission.Jacobians.RiemannSurface.PeriodNondegeneracy
import Submission.Jacobians.RiemannSurface.PeriodDiscreteness
import Submission.Jacobians.RiemannSurface.PeriodDiscretenessFromR2
import Submission.Jacobians.RiemannSurface.PeriodDiscretenessKirovRoute
import Submission.Jacobians.RiemannSurface.HomologyGeneration
import Submission.Jacobians.RiemannSurface.H1Composite
import Submission.Jacobians.RiemannSurface.PeriodCycleBasisOfTGen
import Submission.Jacobians.RiemannSurface.AnalyticPi1Generation
import Submission.Jacobians.RiemannSurface.Cohomology.SheafCohomologySpec
import Submission.Jacobians.RiemannSurface.Periods
import Submission.Jacobians.RiemannSurface.IntersectionForm
import Submission.Jacobians.RiemannSurface.PathIntegral
