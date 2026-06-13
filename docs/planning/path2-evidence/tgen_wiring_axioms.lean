/-
TGEN-WIRING evidence script. Run with:
  lake env lean docs/planning/path2-evidence/tgen_wiring_axioms.lean
Captured output: tgen_wiring_axioms.out (committed alongside).

Establishes "T-GEN ⟹ Buzzard-24 standard-3" wiring: the injectivity headline
is AX_PeriodCycleBasis-free under T-GEN at the consumer level; the ContMDiff
headlines drop the axiom only via the global period-lattice instances, whose
T-GEN-conditional axiom-free replacements are signature-compatible and already
proven (Path2Prototype).
-/
import Jacobians.Challenge
import Jacobians.ChallengeTGen
import Jacobians.RiemannSurface.Path2Prototype
import Jacobians.Axioms.PeriodLattice

open Jacobians Jacobians.Axioms Jacobians.Bridge Jacobians.RiemannSurface
open scoped Manifold Topology ContDiff

/- ## (1) The four Buzzard headlines TODAY: standard-3 + AX_PeriodCycleBasis -/
#print axioms Jacobian.ofCurve_inj
#print axioms Jacobian.ofCurve_contMDiff
#print axioms Jacobian.pushforward_contMDiff
#print axioms Jacobian.pullback_contMDiff
#print axioms Jacobian.pushforward_pullback

/- ## (2) The injectivity headline under T-GEN: standard-3 ONLY -/
#print axioms Jacobian.ofCurve_inj_of_tgen
#print axioms ofCurveImpl_inj_of_tgen

/- ## (3) Basis-free Abel-⊆ engine under T-GEN: standard-3 ONLY -/
#print axioms abel_subset_basis_free
#print axioms zeroPeriodChainSolvabilityLattice_of_engine

/- ## (4) The global period-lattice instances (THE axiom carrier) -/
#print axioms instPeriodLatticeDiscrete
#print axioms AX_PeriodLattice

/- ## (5) Their T-GEN-conditional, axiom-free, signature-matching replacements
   (Path2Prototype). The PL lane swaps these into (4) once T-GEN is a theorem. -/
#print axioms periodLatticeInBasis_discreteTopology_of_tgen
#print axioms periodLatticeInBasis_isZLattice_of_tgen

/- ## (6) The manifold/ContMDiff residual: the Jacobian X manifold instance
   itself carries AX_PeriodCycleBasis (via (4)), so ContMDiff-on-Jacobian-X
   statements inherit it through instance synthesis at STATEMENT-elaboration
   time — not routable via a consumer-side hgen. -/
noncomputable def jacIsManifold_term (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    IsManifold (𝓘(ℂ, Fin (Jacobians.RiemannSurface.genus X) → ℂ)) ω
      (Jacobians.Jacobian X) := inferInstance

#print axioms jacIsManifold_term
