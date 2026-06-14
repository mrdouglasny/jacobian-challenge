/-
# The boundary-word feed: from cut data to the `PeriodCycleBasis` Hodge fields

R-lane Brick 3 (`docs/planning/R1R2_ROUTE.md` §2, Layer 3). Composes the
linear/Gram collapse of `BilinearRelations.lean` with the Kirov port's
PROVEN box-level analytic engines:

* `Jacobians.riemann_R1_of_boundaryWord` (`KirovDolbeault/CutSurface.lean`,
  Cauchy on the box) and
* `Jacobians.riemann_R2_posDef_of_boundaryWord`
  (`KirovDolbeault/BoundaryWordR2.lean`, Green positivity `∬‖h_v‖² > 0`),

both sorry-free (we deliberately do NOT import the port's
`CutSurfaceRelations.lean`, whose `exists_cutSurface` is sorry'd).

`ArcBoundaryWordData` is the named comparison input of the route doc: cut
pullbacks `h`, primitives `F`, and the two boundary-word identities stated
over OUR arc-period blocks (`arcAPeriodMatrix`/`arcBPeriodMatrix`, i.e. the
chart-local `canonicalArcIntegral`s of the bundled loops). Given it:

* `ArcBoundaryWordData.r1_field` / `.r2_field` prove the axiom's R1/R2
  fields verbatim;
* `periodCycleBasisOfBoundaryWord` assembles a full `PeriodCycleBasis`
  witness from the H₁ data (topology lane) + the boundary-word data.

This makes "discharge `AX_PeriodCycleBasis`" equal to "produce the H₁ data
and the boundary-word data" — zero remaining Hodge analysis.

The two small glue lemmas (`box_reProdIm_subset` and the closed-box
differentiability of `F·h`) are adapted from Rado Kirov's
`CutSurfaceRelations.lean` (Apache 2.0, `vendor/kirov-dolbeault-port/`).

NOTE (C2 verdict, route doc §3): a *geometric* realization of this data at
genus ≥ 2 requires weakening the closed-box holomorphy hypotheses of the
port engines to interior holomorphy + boundary continuity; that is a
port-side refinement scheduled with the construction work, and does not
change the interface below.
-/
import Submission.Jacobians.RiemannSurface.BilinearRelations
import Submission.KirovDolbeault.CutSurface
import Submission.KirovDolbeault.BoundaryWordR2

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff ComplexOrder
open Jacobians.Axioms
open Jacobians.Layer3 (PeriodVector Q)
open Matrix Set Complex

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {x₀ : X}

/-- The closed complex unit box `[0,1] ×ℂ [0,1]` lies in the image-form box
neighbourhood `U`. (Adapted from Kirov's `CutSurface.box_reProdIm_subset_U`,
Apache 2.0.) -/
theorem box_reProdIm_subset {U : Set ℂ}
    (hbox : Jacobians.wCLM '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ⊆ U) :
    (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (0 : ℝ) 1) ⊆ U := by
  intro z hz
  rw [Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hz
  refine hbox ⟨(z.re, z.im), ?_, ?_⟩
  · rw [Set.mem_prod]
    exact ⟨hz.1, hz.2⟩
  · rw [Jacobians.wCLM_apply]
    exact Complex.re_add_im z

/-- **The boundary-word comparison data** for a loop family and a form basis:
cut pullback coefficients `h`, primitives `F`, a box neighbourhood `U`, and
the two boundary-word identities stated over OUR arc-period blocks. This is
the construction-specific input (route doc §0/§3) that the slit-sheet
campaign must eventually produce; everything below it is proven. -/
structure ArcBoundaryWordData (loops : Fin (2 * genus X) → AnalyticLoop X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) where
  /-- The cut pullback coefficient of the `j`-th basis form, `h_j = cut^*(ω j)`. -/
  h : Fin (genus X) → ℂ → ℂ
  /-- A primitive of `h_i` on `U`. -/
  F : Fin (genus X) → ℂ → ℂ
  /-- An open neighbourhood of the closed unit box. -/
  U : Set ℂ
  /-- The closed box (as the image of `[0,1]²` under `(x,y) ↦ x + y·I`) lies in `U`. -/
  hbox : Jacobians.wCLM '' (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ⊆ U
  /-- Each `h_i` is holomorphic on `U`. -/
  hh : ∀ i, ∀ z ∈ U, HasDerivAt (h i) (deriv (h i) z) z
  /-- `F_i' = h_i` on `U`. -/
  hF : ∀ i, ∀ z ∈ U, HasDerivAt (F i) (h i z) z
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

namespace ArcBoundaryWordData

variable {loops : Fin (2 * genus X) → AnalyticLoop X x₀}
  {cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)}

/-- `F_i·h_j` is differentiable on the closed box (restriction of the
`U`-holomorphy; needed by box Cauchy). -/
theorem differentiableOn_Fh (D : ArcBoundaryWordData loops cω) (i j : Fin (genus X)) :
    DifferentiableOn ℂ (fun z => D.F i z * D.h j z)
      (Set.uIcc (0 : ℝ) 1 ×ℂ Set.uIcc (0 : ℝ) 1) := by
  have hFd : DifferentiableOn ℂ (D.F i) D.U := fun z hz =>
    (D.hF i z hz).differentiableAt.differentiableWithinAt
  have hhd : DifferentiableOn ℂ (D.h j) D.U := fun z hz =>
    (D.hh j z hz).differentiableAt.differentiableWithinAt
  exact (hFd.mul hhd).mono (box_reProdIm_subset D.hbox)

/-- **R1 block symmetry, PROVEN** from the boundary word via Cauchy on the
box (`riemann_R1_of_boundaryWord`, port). -/
theorem periodMatrix_symm (D : ArcBoundaryWordData loops cω) :
    (arcAPeriodMatrix loops fun m => cω m)ᵀ * (arcBPeriodMatrix loops fun m => cω m)
      = (arcBPeriodMatrix loops fun m => cω m)ᵀ
        * (arcAPeriodMatrix loops fun m => cω m) :=
  Jacobians.riemann_R1_of_boundaryWord _ _ D.h D.F D.differentiableOn_Fh D.word_R1

/-- **R2 Gram positive-definiteness, PROVEN** from the conjugated boundary
word via Green positivity (`riemann_R2_posDef_of_boundaryWord`, port). -/
theorem periodGram_posDef (D : ArcBoundaryWordData loops cω) :
    (arcPeriodGram loops fun m => cω m).PosDef :=
  Jacobians.riemann_R2_posDef_of_boundaryWord _ _ D.h D.F D.U D.hbox D.hh D.hF
    D.word_R2 D.nondeg

/-- **The axiom's R1 field, PROVEN** from boundary-word data: `Q` vanishes
on the arc period vectors of every pair of holomorphic 1-forms. -/
theorem r1_field (D : ArcBoundaryWordData loops cω) (η ζ : HolomorphicOneForm X) :
    Q (arcPeriodVec loops η) (arcPeriodVec loops ζ) = 0 :=
  arc_R1_of_periodMatrix_symm loops cω D.periodMatrix_symm η ζ

/-- **The axiom's R2 field, PROVEN** from boundary-word data: the Hodge
quadratic form is strictly positive on every nonzero holomorphic 1-form. -/
theorem r2_field (D : ArcBoundaryWordData loops cω) (η : HolomorphicOneForm X)
    (hη : η ≠ 0) :
    0 < (Complex.I *
        Q (arcPeriodVec loops η) (conjArcPeriodVec loops η)).re :=
  arc_R2_of_periodGram_posDef loops cω D.periodGram_posDef η hη

end ArcBoundaryWordData

/-- **Assembly: a full `PeriodCycleBasis` witness** from the topology lane's
H₁ data (`isBasis` + the Hurewicz tie) and the boundary-word comparison
data. This is the consumption point for the future slit-sheet construction:
producing these two inputs discharges `AX_PeriodCycleBasis` with zero
remaining Hodge analysis. -/
noncomputable def periodCycleBasisOfBoundaryWord
    {loops : Fin (2 * genus X) → AnalyticLoop X x₀}
    {cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)}
    (isBasis : Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀))
    (loops_to_basis : ∀ i, isBasis i = loopToHomology (loops i))
    (D : ArcBoundaryWordData loops cω) :
    Jacobians.Axioms.PeriodCycleBasis X x₀ where
  loops := loops
  isBasis := isBasis
  loops_to_basis := loops_to_basis
  R1 := D.r1_field
  R2 := D.r2_field

end Jacobians.RiemannSurface
