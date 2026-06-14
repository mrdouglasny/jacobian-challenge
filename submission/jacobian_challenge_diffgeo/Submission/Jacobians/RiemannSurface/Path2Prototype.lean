/-
# Path-2 prototype: T-GEN-conditional discreteness of the HEADLINE lattice

This is the **viability spike** for "Path 2" — the question of whether the
headline period lattice `periodLatticeInBasis` (over the *continuous*-loop
homology `H1 = Additive (Abelianization (π₁))`) can be made
`AX_PeriodCycleBasis`-free WITHOUT proving the open Whitney+Grauert
approximation walls.

## What this file proves (all standard-3, `#print axioms`-verified)

* `periodMapInBasis_eq_devValPeriodVec` — the headline coordinate period map
  IS the axiom-free developing-value period map `devValPeriodVec`
  (component identity `loopDevValH1Hom_mem_periodLatticeInBasis`'s calc,
  packaged as an equality of ℤ-linear maps).
* `periodLatticeInBasis_eq_loopPeriodLattice_of_tgen` — **under T-GEN**, the
  headline lattice equals the Forster-model analytic-loop lattice
  `loopPeriodLattice`. This is the bridge whose *reverse* direction is the
  `AX_PeriodCycleBasis`-carrying step in
  `Layer3.loopPeriodLattice_eq_periodLatticeInBasis`; here it is discharged
  by T-GEN instead.
* `periodLatticeInBasis_discreteTopology_of_tgen` /
  `periodLatticeInBasis_isZLattice_of_tgen` /
  `exists_periodLatticeInBasis_basis_of_tgen` — the headline-lattice
  ZLattice instances, derived **axiom-free** from the (already unconditional,
  standard-3) discreteness of `loopPeriodLattice` plus T-GEN.

## The finding this file certifies

The K-LITE isolated-zero / max-principle machinery is ALREADY axiom-free on
the analytic-loop lattice (`discreteTopology_loopPeriodLattice` is
standard-3). It does **not** use the cycle-basis axiom at all. The *only*
place `AX_PeriodCycleBasis` enters the headline closure is the bridge from
the analytic-loop lattice to the continuous-`H1` headline lattice, i.e. the
statement that analytic loops generate `H1` — which is exactly **T-GEN**
(`AnalyticLoopsGenerateH1`), provably equivalent (this repo's
`TGenFinalReduction.lean`) to {Whitney, Grauert} analytic approximation.

So "Path 2" collapses to T-GEN: there is no cheaper variant that re-uses the
discreteness argument on the continuous lattice, because that argument is
geometric (chart-local residues), not loop-class-dependent, and is already
done. The continuous-vs-analytic gap is purely the approximation wall.
-/
import Submission.Jacobians.Layer3.PeriodLatticeDiscrete
import Submission.Jacobians.RiemannSurface.H1Composite
import Submission.Jacobians.RiemannSurface.PeriodDiscretenessKirovRoute

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open Jacobians.RiemannSurface
open Jacobians.Layer3 (devValPeriodVec)

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The headline coordinate period map is the developing-value period map.**
`periodMapInBasis X x₀ b` and the axiom-free `devValPeriodVec x₀ b` agree as
ℤ-linear maps `H1 X x₀ →ₗ[ℤ] (Fin g → ℂ)`: componentwise both send a class
`h` to `loopDevValH1Hom x₀ (b i) h` (the calc inside
`loopDevValH1Hom_mem_periodLatticeInBasis`). Axiom-free. -/
theorem periodMapInBasis_eq_devValPeriodVec (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Jacobians.Axioms.periodMapInBasis X x₀ b = devValPeriodVec x₀ b := by
  ext h i
  calc
    Jacobians.Axioms.periodMapInBasis X x₀ b h i
        = (loopIntegralToH1 x₀ h) (b i) := by
      simp [Jacobians.Axioms.periodMapInBasis, periodMap, LinearMap.comp_apply,
        b.dualBasis_equivFun]
    _ = loopDevValH1Hom x₀ (b i) h :=
      (loopDevValH1Hom_eq_loopIntegralToH1_apply x₀ (b i) h).symm
    _ = devValPeriodVec x₀ b h i := by
      simp [devValPeriodVec]

/-- **The headline lattice is the range of the developing-value period map.**
Axiom-free corollary of `periodMapInBasis_eq_devValPeriodVec`. -/
theorem periodLatticeInBasis_eq_range_devValPeriodVec (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Jacobians.Axioms.periodLatticeInBasis X x₀ b
      = LinearMap.range (devValPeriodVec x₀ b) := by
  rw [Jacobians.Axioms.periodLatticeInBasis, periodMapInBasis_eq_devValPeriodVec]

/-- **THE PATH-2 BRIDGE, T-GEN-conditional and axiom-free.** Under T-GEN
(`AnalyticLoopsGenerateH1` — the analytic loops generate `H1`), the headline
period lattice over the continuous-loop homology equals the Forster-model
analytic-loop period lattice.

This is the same equation as
`Layer3.loopPeriodLattice_eq_periodLatticeInBasis`, but its `⊇` direction —
the one that uses `Classical.choice (AX_PeriodCycleBasis)` there — is here
discharged by `range_devValPeriodVec_eq_loopPeriodLattice` over the explicit
T-GEN hypothesis. No `AX_PeriodCycleBasis`. -/
theorem periodLatticeInBasis_eq_loopPeriodLattice_of_tgen (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (hgen : AnalyticLoopsGenerateH1 x₀) :
    Jacobians.Axioms.periodLatticeInBasis X x₀ b = loopPeriodLattice x₀ b := by
  rw [periodLatticeInBasis_eq_range_devValPeriodVec,
    range_devValPeriodVec_eq_loopPeriodLattice x₀ b hgen]

/-- **Path-2 headline (B-4), axiom-free under T-GEN.** Discreteness of the
*headline* lattice `periodLatticeInBasis`, derived from the (unconditional,
standard-3) discreteness of `loopPeriodLattice` through the T-GEN bridge —
NO `AX_PeriodCycleBasis`. Contrast
`Layer3.periodLatticeInBasis_discreteTopology_of_loopSpan`, which proves the
same statement but carries `AX_PeriodCycleBasis`. -/
theorem periodLatticeInBasis_discreteTopology_of_tgen (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (hgen : AnalyticLoopsGenerateH1 x₀) :
    DiscreteTopology (Jacobians.Axioms.periodLatticeInBasis X x₀ b) := by
  rw [periodLatticeInBasis_eq_loopPeriodLattice_of_tgen x₀ b hgen]
  exact discreteTopology_loopPeriodLattice x₀ b

/-- **Path-2 headline (B-5), axiom-free under T-GEN.** The headline lattice
is a full ℤ-lattice. -/
theorem periodLatticeInBasis_isZLattice_of_tgen (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (hgen : AnalyticLoopsGenerateH1 x₀) :
    letI := periodLatticeInBasis_discreteTopology_of_tgen x₀ b hgen
    IsZLattice ℝ (Jacobians.Axioms.periodLatticeInBasis X x₀ b) := by
  letI := periodLatticeInBasis_discreteTopology_of_tgen x₀ b hgen
  refine ⟨?_⟩
  rw [periodLatticeInBasis_eq_loopPeriodLattice_of_tgen x₀ b hgen]
  exact span_real_loopPeriodLattice_eq_top x₀ b

/-- **Path-2 packaging, axiom-free under T-GEN.** A `Fin (2g)`-indexed
ℤ-basis of the headline lattice. -/
theorem exists_periodLatticeInBasis_basis_of_tgen (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (hgen : AnalyticLoopsGenerateH1 x₀) :
    Nonempty (Module.Basis (Fin (2 * genus X)) ℤ
      (Jacobians.Axioms.periodLatticeInBasis X x₀ b)) := by
  rw [periodLatticeInBasis_eq_loopPeriodLattice_of_tgen x₀ b hgen]
  exact exists_loopPeriodLattice_basis_unconditional x₀ b

end

end Jacobians.RiemannSurface
