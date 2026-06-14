/-
# The boundary-word feed, interior form: cut data with boundary continuity only

IE-lane closing rung (`docs/planning/BW_ROUTE.md`). Mirror of
`BilinearRelationsBoundaryWord.lean` over the WEAKENED port engines
(`KirovDolbeault/InteriorEngine.lean`, BW rungs 1–5): the cut pullbacks
`h` and primitives `F` are required to be holomorphic only on the OPEN
unit-box image, and merely continuous up to the closed box. This is the
regularity a *geometric* cut chart at genus ≥ 2 can actually supply (the
C2 angle-count verdict, `docs/planning/CUTSURFACE_GAP_ANALYSIS.md`) — at
the polygon vertices the chart is continuous but not holomorphic.

Contents:

* `ArcBoundaryWordDataInterior` — the weakened comparison data;
* `.periodMatrix_symm` / `.periodGram_posDef` / `.r1_field` / `.r2_field`
  — R1/R2 proven from it via the interior engines;
* `periodCycleBasisOfBoundaryWordInterior` — assembly of a full
  `PeriodCycleBasis` witness from H₁ data + interior boundary-word data;
* `ArcBoundaryWordData.toInterior` — the closed-box data of
  `BilinearRelationsBoundaryWord.lean` restricts to interior data, so the
  interior interface is strictly weaker (every old witness still feeds it).

With this file the slit-sheet construction target is the interior data:
producing `ArcBoundaryWordDataInterior` + the H₁ inputs discharges
`AX_PeriodCycleBasis` with zero remaining Hodge analysis and no closed-box
holomorphy obligation.
-/
import Submission.Jacobians.RiemannSurface.BilinearRelationsBoundaryWord
import Submission.KirovDolbeault.InteriorEngine

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff ComplexOrder
open Jacobians.Axioms
open Jacobians.Layer3 (PeriodVector Q)
open Matrix Set Complex

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {x₀ : X}

/-- **The boundary-word comparison data, interior form**: cut pullback
coefficients `h`, primitives `F`, continuous on the closed unit-box image
and holomorphic (resp. primitive) on the open box image only, plus the two
boundary-word identities over OUR arc-period blocks. Weakening of
`ArcBoundaryWordData`: no open neighbourhood `U` of the *closed* box is
demanded, so the data is producible by a geometric cut chart at any
genus. -/
structure ArcBoundaryWordDataInterior
    (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) where
  /-- The cut pullback coefficient of the `j`-th basis form, `h_j = cut^*(ω j)`. -/
  h : Fin (genus X) → ℂ → ℂ
  /-- A primitive of `h_i` on the open box, continuous up to the boundary. -/
  F : Fin (genus X) → ℂ → ℂ
  /-- Each `h_i` is continuous on the closed box image. -/
  hhc : ∀ i, ContinuousOn (h i) (Jacobians.wCLM '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1))
  /-- Each `F_i` is continuous on the closed box image. -/
  hFc : ∀ i, ContinuousOn (F i) (Jacobians.wCLM '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1))
  /-- Each `h_i` is holomorphic on the open box image. -/
  hh : ∀ i, ∀ z ∈ Jacobians.wCLM '' (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1),
    HasDerivAt (h i) (deriv (h i) z) z
  /-- `F_i' = h_i` on the open box image. -/
  hF : ∀ i, ∀ z ∈ Jacobians.wCLM '' (Set.Ioo (0:ℝ) 1 ×ˢ Set.Ioo (0:ℝ) 1),
    HasDerivAt (F i) (h i z) z
  /-- **The R1 boundary word**: `(AᵀB − BᵀA)_{ij} = ∮_{∂box} F_i·h_j dz` over
  the arc-period blocks of the basis forms. -/
  word_R1 : ∀ i j,
    ((arcAPeriodMatrix loops fun m => cω m)ᵀ * (arcBPeriodMatrix loops fun m => cω m)
        - (arcBPeriodMatrix loops fun m => cω m)ᵀ
          * (arcAPeriodMatrix loops fun m => cω m)) i j
      = Jacobians.rectBoundaryIntegral fun z => F i z * h j z
  /-- **The R2 boundary word**: `(AᵀB̄ − BᵀĀ)_{ij} = −∮_{∂box} F̄_i·h_j dz`. -/
  word_R2 : ∀ i j,
    ((arcAPeriodMatrix loops fun m => cω m)ᵀ
          * (arcBPeriodMatrix loops fun m => cω m).map (starRingEnd ℂ)
        - (arcBPeriodMatrix loops fun m => cω m)ᵀ
          * (arcAPeriodMatrix loops fun m => cω m).map (starRingEnd ℂ)) i j
      = - Jacobians.boundaryForm (h j) (F i)
  /-- **Non-degeneracy**: a nonzero coefficient vector pulls back to a
  combination `∑ v_j·h_j` that is nonzero somewhere in the open box. -/
  nondeg : ∀ v : Fin (genus X) → ℂ, v ≠ 0 →
    ∃ p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1,
      (∑ j, v j * h j (Jacobians.wCLM p)) ≠ 0

namespace ArcBoundaryWordDataInterior

variable {loops : Fin (2 * genus X) → AnalyticLoop X x₀}
  {cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)}

/-- `F_i·h_j` is continuous on the closed box (needed by split box Cauchy). -/
theorem continuousOn_Fh (D : ArcBoundaryWordDataInterior loops cω) (i j : Fin (genus X)) :
    ContinuousOn (fun z => D.F i z * D.h j z)
      (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (0 : ℝ) 1) := by
  rw [← Jacobians.wCLM_image_closedBox]
  exact (D.hFc i).mul (D.hhc j)

/-- `F_i·h_j` is holomorphic on the open box (needed by split box Cauchy). -/
theorem differentiableOn_Fh (D : ArcBoundaryWordDataInterior loops cω) (i j : Fin (genus X)) :
    DifferentiableOn ℂ (fun z => D.F i z * D.h j z)
      (Set.Ioo (0 : ℝ) 1 ×ℂ Set.Ioo (0 : ℝ) 1) := by
  rw [← Jacobians.wCLM_image_openBox]
  intro z hz
  exact ((D.hF i z hz).differentiableAt.mul
    (D.hh j z hz).differentiableAt).differentiableWithinAt

/-- **R1 block symmetry, PROVEN** from the interior boundary word via split
Cauchy on the box (`riemann_R1_of_boundaryWord_interior`, port). -/
theorem periodMatrix_symm (D : ArcBoundaryWordDataInterior loops cω) :
    (arcAPeriodMatrix loops fun m => cω m)ᵀ * (arcBPeriodMatrix loops fun m => cω m)
      = (arcBPeriodMatrix loops fun m => cω m)ᵀ
        * (arcAPeriodMatrix loops fun m => cω m) :=
  Jacobians.riemann_R1_of_boundaryWord_interior _ _ D.h D.F D.continuousOn_Fh
    D.differentiableOn_Fh D.word_R1

/-- **R2 Gram positive-definiteness, PROVEN** from the interior conjugated
boundary word via interior Green positivity
(`riemann_R2_posDef_of_boundaryWord_interior`, port). -/
theorem periodGram_posDef (D : ArcBoundaryWordDataInterior loops cω) :
    (arcPeriodGram loops fun m => cω m).PosDef :=
  Jacobians.riemann_R2_posDef_of_boundaryWord_interior _ _ D.h D.F D.hhc D.hFc D.hh D.hF
    D.word_R2 D.nondeg

/-- **The axiom's R1 field, PROVEN** from interior boundary-word data. -/
theorem r1_field (D : ArcBoundaryWordDataInterior loops cω) (η ζ : HolomorphicOneForm X) :
    Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0 :=
  arc_R1_of_periodMatrix_symm loops cω D.periodMatrix_symm η ζ

/-- **The axiom's R2 field, PROVEN** from interior boundary-word data. -/
theorem r2_field (D : ArcBoundaryWordDataInterior loops cω) (η : HolomorphicOneForm X)
    (hη : η ≠ 0) :
    0 < (Complex.I *
        Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)).re :=
  arc_R2_of_periodGram_posDef loops cω D.periodGram_posDef η hη

end ArcBoundaryWordDataInterior

/-- **Assembly: a full `PeriodCycleBasis` witness** from the topology lane's
H₁ data and the *interior* boundary-word comparison data. Interior twin of
`periodCycleBasisOfBoundaryWord`: the slit-sheet construction may target
this weaker interface (no closed-box holomorphy) at any genus. -/
noncomputable def periodCycleBasisOfBoundaryWordInterior
    {loops : Fin (2 * genus X) → AnalyticLoop X x₀}
    {cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)}
    (isBasis : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀))
    (loops_to_basis : ∀ i, isBasis i = loopToHomology (loops i))
    (D : ArcBoundaryWordDataInterior loops cω) :
    Jacobians.Axioms.PeriodCycleBasis X x₀ where
  loops := loops
  isBasis := isBasis
  loops_to_basis := loops_to_basis
  R1 := D.r1_field
  R2 := D.r2_field

/-- **Closed-box data is interior data**: the original `ArcBoundaryWordData`
(holomorphy on an open `U` containing the closed box) restricts to
`ArcBoundaryWordDataInterior`, so the interior interface is strictly
weaker and every existing closed-box witness still feeds the new pipeline. -/
def ArcBoundaryWordData.toInterior
    {loops : Fin (2 * genus X) → AnalyticLoop X x₀}
    {cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)}
    (D : ArcBoundaryWordData loops cω) :
    ArcBoundaryWordDataInterior loops cω where
  h := D.h
  F := D.F
  hhc i z hz := ((D.hh i z (D.hbox hz)).continuousAt).continuousWithinAt
  hFc i z hz := ((D.hF i z (D.hbox hz)).continuousAt).continuousWithinAt
  hh i z hz := D.hh i z (D.hbox
    (Set.image_mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hz))
  hF i z hz := D.hF i z (D.hbox
    (Set.image_mono (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hz))
  word_R1 := D.word_R1
  word_R2 := D.word_R2
  nondeg := D.nondeg

end Jacobians.RiemannSurface
