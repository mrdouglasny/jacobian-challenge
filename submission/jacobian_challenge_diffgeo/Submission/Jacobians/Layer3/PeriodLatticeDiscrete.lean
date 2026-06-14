/-
# B-4/B-5 transport: the official period lattice through the loop-period engine

The dissection-free B-4/B-5 engine
(`RiemannSurface/PeriodDiscreteness.lean`) specialized to
`periodLatticeInBasis` — the lattice the Jacobian construction consumes.

These results carry `AX_PeriodCycleBasis` in their closure only because
`loopIntegralToH1` (hence `periodMapInBasis`/`periodLatticeInBasis`) is
*defined* through the chosen witness; of the witness's fields only
`loops`/`isBasis`/`loops_to_basis` are used. The Riemann bilinear relations
R1/R2 are **never touched** — unlike the Phase-C Siegel route
(`Layer3/Periods.lean`), which derives the same `DiscreteTopology`/
`IsZLattice` statements from the bundled R2 positivity. This derivation
therefore survives any future weakening of the axiom to its
lattice-geometry half.

* `choiceLoops_periodGenerating` — the chosen witness's loops discharge the
  engine's named hypothesis `PeriodGeneratingLoops`;
* `loopPeriodLattice_eq_periodLatticeInBasis` — the Forster-model lattice
  (ℤ-span of ALL closed-analytic-loop periods) IS the official lattice;
* `periodLatticeInBasis_discreteTopology_of_loopSpan` /
  `periodLatticeInBasis_isZLattice_of_loopSpan` /
  `exists_periodLatticeInBasis_basis_of_loopSpan` — the R2-free
  re-derivations of the Phase-C lattice instances.
-/
import Submission.Jacobians.RiemannSurface.PeriodDiscreteness
import Submission.Jacobians.RiemannSurface.LoopIntegralHom

namespace Jacobians.Layer3

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The developing-value period vector on homology: the axiom-free
`H1`-level period map in coordinates (`loopDevValH1Hom` componentwise). On
loop classes it returns the loop's `loopPeriodVec`
(`devValPeriodVec_loopToHomology`). -/
def devValPeriodVec (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    H1 X x₀ →ₗ[ℤ] (Fin (genus X) → ℂ) :=
  LinearMap.pi fun i => (loopDevValH1Hom x₀ (b i)).toIntLinearMap

@[simp]
theorem devValPeriodVec_loopToHomology (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (δ : AnalyticLoop X x₀) :
    devValPeriodVec x₀ b (Jacobians.Axioms.loopToHomology δ)
      = loopPeriodVec x₀ b δ := by
  funext i
  simp [devValPeriodVec, loopPeriodVec]

/-- **Axiom-free reduction of the named hypothesis to topology.** If the
`2g` loops' homology classes ℤ-generate every closed analytic loop's
homology class, they period-generate: `PeriodGeneratingLoops` follows by
pushing the span through the (axiom-free) developing-value period map.
This is the interface a future dissection/Hurewicz construction of homology
generators must satisfy — no integration, no R1/R2, no chosen witness. -/
theorem PeriodGeneratingLoops.of_homology_span {x₀ : X}
    {b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)}
    {γs : Fin (2 * genus X) → AnalyticLoop X x₀}
    (hgen : ∀ δ : AnalyticLoop X x₀, Jacobians.Axioms.loopToHomology δ ∈
      Submodule.span ℤ (Set.range fun i =>
        Jacobians.Axioms.loopToHomology (γs i))) :
    PeriodGeneratingLoops x₀ b γs := by
  intro δ
  have hmem := Submodule.mem_map_of_mem (f := devValPeriodVec x₀ b) (hgen δ)
  rw [Submodule.map_span, ← Set.range_comp] at hmem
  have himg : ⇑(devValPeriodVec x₀ b) ∘ (fun i =>
        Jacobians.Axioms.loopToHomology (γs i))
      = fun i => loopPeriodVec x₀ b (γs i) :=
    funext fun i => devValPeriodVec_loopToHomology x₀ b (γs i)
  rw [himg] at hmem
  rwa [devValPeriodVec_loopToHomology] at hmem

/-- The coordinate period vector of a closed analytic loop is the
`periodMapInBasis`-image of its homology class (developing-value bridge). -/
theorem loopPeriodVec_eq_periodMapInBasis (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (δ : AnalyticLoop X x₀) :
    loopPeriodVec x₀ b δ =
      Jacobians.Axioms.periodMapInBasis X x₀ b
        (Jacobians.Axioms.loopToHomology δ) := by
  funext i
  have h1 : Jacobians.Axioms.periodMapInBasis X x₀ b
        (Jacobians.Axioms.loopToHomology δ) i
      = loopIntegralToH1 x₀ (Jacobians.Axioms.loopToHomology δ) (b i) := by
    simp [Jacobians.Axioms.periodMapInBasis, periodMap, LinearMap.comp_apply,
      b.dualBasis_equivFun]
  rw [loopPeriodVec_apply, h1, ← loopDevValH1Hom_eq_loopIntegralToH1_apply,
    loopDevValH1Hom_loopToHomology]

/-- The range of `periodMapInBasis` is the ℤ-span of the chosen cycle-basis
loops' period vectors. -/
theorem range_periodMapInBasis_eq_span_choiceLoops (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    LinearMap.range (Jacobians.Axioms.periodMapInBasis X x₀ b)
      = Submodule.span ℤ (Set.range fun i => loopPeriodVec x₀ b
          ((Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀)).loops i)) := by
  classical
  set cb := Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀) with hcb
  rw [LinearMap.range_eq_map, ← cb.isBasis.span_eq, Submodule.map_span,
    ← Set.range_comp]
  refine congrArg (Submodule.span ℤ) (congrArg Set.range (funext fun i => ?_))
  rw [Function.comp_apply, cb.loops_to_basis i,
    ← loopPeriodVec_eq_periodMapInBasis]

/-- **The chosen `AX_PeriodCycleBasis` loops discharge the engine's named
hypothesis**: every closed analytic loop's period vector lies in the ℤ-span
of the chosen loops' period vectors. Uses only the witness's
`isBasis`/`loops_to_basis` fields — no R1/R2. -/
theorem choiceLoops_periodGenerating (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    PeriodGeneratingLoops x₀ b
      (Classical.choice (Jacobians.Axioms.AX_PeriodCycleBasis x₀)).loops := by
  intro δ
  rw [← range_periodMapInBasis_eq_span_choiceLoops x₀ b]
  exact ⟨Jacobians.Axioms.loopToHomology δ,
    (loopPeriodVec_eq_periodMapInBasis x₀ b δ).symm⟩

/-- **The Forster-model lattice is the official period lattice**: the
ℤ-span of all closed-analytic-loop period vectors equals the range of
`periodMapInBasis` over `H1`. -/
theorem loopPeriodLattice_eq_periodLatticeInBasis (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    loopPeriodLattice x₀ b = Jacobians.Axioms.periodLatticeInBasis X x₀ b := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨δ, rfl⟩
    exact ⟨Jacobians.Axioms.loopToHomology δ,
      (loopPeriodVec_eq_periodMapInBasis x₀ b δ).symm⟩
  · rw [Jacobians.Axioms.periodLatticeInBasis,
      range_periodMapInBasis_eq_span_choiceLoops x₀ b]
    exact Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact loopPeriodVec_mem_loopPeriodLattice x₀ b _)

/-- **R2-free discreteness of the period lattice** (B-4 transported): same
statement as Phase-C's `periodLatticeInBasis_discrete`, derived from the
maximum-principle nondegeneracy + the 2g rank count instead of Hodge
positivity. -/
theorem periodLatticeInBasis_discreteTopology_of_loopSpan (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (Jacobians.Axioms.periodLatticeInBasis X x₀ b) := by
  rw [← loopPeriodLattice_eq_periodLatticeInBasis x₀ b]
  exact (choiceLoops_periodGenerating x₀ b).discreteTopology

/-- **R2-free full-lattice property** (B-5 transported): same statement as
Phase-C's `periodLatticeInBasis_isZLattice`, with the spanning half coming
from the axiom-free B-3 engine. -/
theorem periodLatticeInBasis_isZLattice_of_loopSpan (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    letI := periodLatticeInBasis_discreteTopology_of_loopSpan x₀ b
    IsZLattice ℝ (Jacobians.Axioms.periodLatticeInBasis X x₀ b) := by
  letI := periodLatticeInBasis_discreteTopology_of_loopSpan x₀ b
  refine ⟨?_⟩
  rw [← loopPeriodLattice_eq_periodLatticeInBasis x₀ b]
  exact span_real_loopPeriodLattice_eq_top x₀ b

/-- **B-5 packaging for the official lattice**: a `Fin (2g)`-indexed
ℤ-basis of `periodLatticeInBasis`. -/
theorem exists_periodLatticeInBasis_basis_of_loopSpan (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Nonempty (Module.Basis (Fin (2 * genus X)) ℤ
      (Jacobians.Axioms.periodLatticeInBasis X x₀ b)) := by
  rw [← loopPeriodLattice_eq_periodLatticeInBasis x₀ b]
  exact (choiceLoops_periodGenerating x₀ b).exists_basis

end

end Jacobians.Layer3
