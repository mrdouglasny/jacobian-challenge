/-
  Čech finiteness — instantiating the acyclic `exists_cechModel` via the completed disk-acyclicity.

  `CechFinitenessWiring.exists_cechModel` is the single remaining finiteness sorry (Forster 14.9):
  every finite cover `𝔘` admits a chart-disk Leray model (`DiskOverlapData` + `Coboundaries`, including
  the `leray` disk-acyclicity field) whose sup-norm `H¹` is `ℂ`-linearly isomorphic to the genuine
  germ-class `𝔘.cechH1 D`.  As scoped in `CechRefinement.lean`'s `## PLAN`, the FULL statement
  (arbitrary `𝔘`, arbitrary `D`) is blocked by STEP B — Leray cover-INDEPENDENCE (`refineH1` being an
  iso for a strictly-finer Leray refinement), a greenfield ~several-hundred-LoC piece on top of the
  proven disk ∂̄-atoms.  That is NOT what the newly-completed disk-acyclicity unblocked.

  `CechFinitenessWiring` already banks (sorry-free) the END-TO-END model assembly for the ACYCLIC case:
  `exists_cechModel_of_subsingleton` discharges `exists_cechModel 𝔘 D` whenever `𝔘.cechH1 D` is a
  SUBSINGLETON, via the trivial model `DiskOverlapData.empty.trivialCoboundaries` (whose `leray` field
  is discharged and whose `supH1 = 0`) and `LinearEquiv.ofSubsingleton`.

  THIS FILE supplies the geometric INSTANTIATION that the new disk-acyclicity makes possible
  (`exists_cechModel_of_sharedChart_zero`): for a `SharedChartCover 𝔇` at `D = 0`, the subsingleton
  hypothesis is discharged by the COMPLETED disk-acyclicity `SharedChartCover.hasGluedDbarDatum` (commit
  61484f5) — `H¹(disk, 𝒪) = 0` — so the disk `∂̄`-solvability engine is wired through the
  model-construction front door:
      `dbar_solvable_ball` ⟹ `HasGluedDbarDatum` ⟹ `H¹(disk, 𝒪) = 0` ⟹ `exists_cechModel 𝔇 0`.
  (It lives here, not in `CechFinitenessWiring`, because it needs the `GluedDbarDatum` /
  `CechFinitenessBallSolve` closure, which imports — and so cannot be imported by — `CechComplex`'s
  downstream `CechFinitenessWiring`.)

  WHY THE GENERAL `exists_cechModel` STAYS A SORRY (the exact remaining obstruction):  an arbitrary
  Leray `𝔘` is NOT a `SharedChartCover` and its `cechH1 𝔘 D` is NOT a subsingleton (for high genus /
  general `D`), so the subsingleton route does not apply.  Closing the general statement needs the
  comparison `cechH1 𝔘 D ≃ₗ supH1` for a NON-acyclic `supH1` — the genuine Montel-model comparison +
  Leray cover-independence STEP B (`CechRefinement.lean`'s `## PLAN`, `CechRefinementLeray.lean`'s
  `## SURJECTIVITY`).  The forward `germ → BddHol` cochain map is built for `D = 0`
  (`CechModelCochain`/`CechModelDatum`); the inverse, the δ-square, and STEP B are not.

  All declarations here are sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Jacobians.Dolbeault.CechFinitenessWiring
import Jacobians.Dolbeault.CechModelDifferential
import Jacobians.Dolbeault.GluedDbarDatum
import Jacobians.Dolbeault.ChartCoverDbarGlue

open scoped Manifold ContDiff Topology

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`exists_cechModel` for a shared-chart disk cover at `D = 0` (the disk-acyclicity wiring).**  For
any `SharedChartCover 𝔇` (a finite cover whose sets sit in one chart with chart-images in a fixed
ball), `exists_cechModel 𝔇.toFiniteCover 0` holds.  The subsingleton hypothesis of
`exists_cechModel_of_subsingleton` is discharged by the COMPLETED disk-acyclicity
`cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 (𝔇.hasGluedDbarDatum)` (commit 61484f5): every class of
`𝔇.toFiniteCover.cechH1 0` is `0`, so that `H¹` is a subsingleton.

This wires the newly-unblocked `leray`/disk-acyclicity piece through the model-construction front
door: the disk `∂̄`-solvability (`dbar_solvable_ball`) ⟹ `HasGluedDbarDatum` ⟹ `H¹(disk, 𝒪) = 0` ⟹ the
assembled `exists_cechModel` on the shared-chart cover (the trivial acyclic model + the
`LinearEquiv.ofSubsingleton` comparison). -/
theorem exists_cechModel_of_sharedChart_zero (𝔇 : SharedChartCover X)
    (H : HasGluedDbarDatum 𝔇) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d),
      Nonempty (𝔇.toFiniteFamily.cechH1 (0 : Divisor X) ≃ₗ[ℂ] c.supH1) := by
  haveI : Subsingleton (𝔇.toFiniteFamily.cechH1 (0 : Divisor X)) :=
    subsingleton_iff.mpr fun a b => by
      rw [cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H a,
        cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H b]
  exact exists_cechModel_of_subsingleton 𝔇.toFiniteFamily 0

/-! ### The chart-cover sup-norm `H¹` is finite-dimensional (consumes the assembled δ-complex)

This wires the cross-chart Čech δ-complex of `CechModelDifferential` (the cover/shrinking `δ⁰`/`δ¹`,
`δ²=0`, and the restriction commuting square, all PROVEN) into the abstract finiteness reduction:
given ONLY the diagnostic continuous-shrinking hypothesis `ChartCoverContinuousLeray X`, the
chart-cover sup-norm `H¹` is finite-dimensional. -/

/-- **Finiteness of the chart-cover sup-norm `H¹` from the diagnostic continuous-shrinking hypothesis.**  For the chart-cover
Čech δ-complex `chartCoverCoboundaries hleray` (all structural fields proven in `CechModelDifferential`),
the sup-norm `H¹` is finite-dimensional: the Montel restriction `ρ` is compact
(`Coboundaries.ρ_compact`, from the proven disk-Montel atom), the Leray map `(η,ξ) ↦ δη + ρξ` is
surjective (`leray_surjective`, unpacking the model's `leray = hleray`), and the abstract reduction
`finiteDimensional_h1_of_leray_compact` (Schwartz 14.8) concludes.  The ONLY non-structural input is the false-shaped continuous predicate
`hleray : ChartCoverContinuousLeray X`; the corrected target must use holomorphic shrinking cochains. -/
theorem finiteDimensional_chartCoverSupH1_of_continuousLeray (hleray : ChartCoverContinuousLeray X) :
    FiniteDimensional ℂ (chartCoverCoboundaries (X := X) hleray).supH1 :=
  (chartCoverCoboundaries hleray).finiteDimensional_supH1
    (leray_surjective _ (chartCoverCoboundaries hleray))

/-! ### The chart-cover model as a witness for `exists_cechModel` (the exact remaining gap)

`exists_cechModel 𝔘 D` asks for SOME `DiskOverlapData d` + `Coboundaries d` with `𝔘.cechH1 D ≃ₗ
c.supH1`.  The work in `CechModelDifferential` builds exactly such a `(d, c)` for the canonical chart
cover — `d = chartCoverOverlapData`, `c = chartCoverCoboundaries hleray` — with all structural fields
proven.  The reduction below makes this explicit: `exists_cechModel 𝔘 D` follows from the two precisely-
named remaining obligations, the diagnostic continuous-shrinking predicate `ChartCoverContinuousLeray X` and the comparison
`𝔘.cechH1 D ≃ₗ (chartCoverCoboundaries hleray).supH1`.  This pins down what is left and prevents the
δ-complex work from drifting away from the actual goal. -/

/-- **The chart-cover model discharges `exists_cechModel` given its two named obligations.**  For any
cover `𝔘` and divisor `D`, if there is a diagnostic continuous-shrinking witness `hleray : ChartCoverContinuousLeray
X` and a comparison `𝔘.cechH1 D ≃ₗ[ℂ] (chartCoverCoboundaries hleray).supH1`, then `exists_cechModel
𝔘 D` holds (with `d = chartCoverOverlapData`, `c = chartCoverCoboundaries hleray`).  This isolates the
EXACT remaining gap: the structural δ-complex (`δ⁰`/`δ¹`/`δ²=0`/commuting square) is proven; only
(a) a corrected holomorphic-shrinking `leray` field and (b) the germ-class↔sup-norm comparison are still owed. -/
theorem exists_cechModel_of_chartCoverContinuousLeray_comparison (𝔘 : FiniteCover X) (D : Divisor X)
    (hleray : ChartCoverContinuousLeray X)
    (e : 𝔘.cechH1 D ≃ₗ[ℂ] (chartCoverCoboundaries (X := X) hleray).supH1) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d), Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  ⟨chartCoverOverlapData, chartCoverCoboundaries hleray, ⟨e⟩⟩

end Jacobians.Dolbeault
