import Jacobians.RiemannSurface.PeriodDiscretenessKirovRoute
import Jacobians.Layer3.PeriodLatticeDiscrete
import Jacobians.RiemannSurface.H1Composite
import Jacobians.RiemannSurface.AnalyticApproxGeneration

open Jacobians.RiemannSurface

-- (1) ANALYTIC-LOOP lattice: should be standard-3, NO AX_PeriodCycleBasis
#print axioms discreteTopology_loopPeriodLattice
#print axioms isZLattice_loopPeriodLattice_unconditional
#print axioms loopPeriodLattice_isolated_zero

-- (2) HEADLINE lattice bridge: forward direction free, full equality uses axiom
#print axioms Jacobians.Layer3.loopPeriodLattice_eq_periodLatticeInBasis
#print axioms Jacobians.Layer3.periodLatticeInBasis_discreteTopology_of_loopSpan

-- (3) The T-GEN-conditional bridge (should be standard-3: T-GEN is a hypothesis)
#print axioms range_devValPeriodVec_eq_loopPeriodLattice
#print axioms analyticLoopsGenerateH1_of_analyticRep
