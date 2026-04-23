/-
Named axioms for deep facts the project uses but does not (yet) discharge.

Each axiom lives in its own submodule, with a docstring stating:
* The mathematical content.
* A classical reference (Mumford, Milne, Forster, …).
* Why it's axiomatized rather than proved at this stage.

See `docs/formalization-plan.md` §7 for the full axiom-discharge priority
order. Discharge priority (revised 2026-04-22 after Gemini review —
infrastructure axioms first, since downstream constructions collapse
silently when `genus X` is 0):

1. `AX_FiniteDimOneForms` (compactness + normal families; foundation)
2. `AX_H1FreeRank2g` (CW topology of compact oriented surfaces —
   subsumed by #4 but kept for direct use while callers migrate)
3. `AX_IntersectionForm` (non-degenerate alternating ℤ-bilinear pairing
   on `H_1`; prerequisite for "symplectic basis")
4. `AX_AnalyticCycleBasis` (piecewise-real-analytic ℤ-basis of `H_1`;
   enables a tractable `PathIntegral` restricted to analytic arcs, and
   subsumes `AX_H1FreeRank2g` once `periodMap` uses the basis)
5. `AX_PeriodLattice` (period image is a ℤ-lattice in `Fin g → ℂ`;
   needed for Jacobian as a complex torus)
6. `AX_RiemannBilinear` (Hodge / symplectic positivity; discharges
   `AX_PeriodLattice`)
7. `AX_BranchLocus` (local `meromorphicOrderAt` + properness)
8. `AX_SerreDuality` (classical pairing)
9. `AX_RiemannRoch` (deepest algebraic axiom)
10. `AX_PluckerFormula` (adjunction; Track 2 `SmoothPlaneCurve` only)
11. `AX_AbelTheorem` (via Riemann theta divisor or Forster-style residue)
-/
import Jacobians.Axioms.FiniteDimOneForms
import Jacobians.Axioms.PeriodLattice
import Jacobians.Axioms.RiemannBilinear
import Jacobians.Axioms.H1FreeRank2g
import Jacobians.Axioms.IntersectionForm
import Jacobians.Axioms.AnalyticCycleBasis
import Jacobians.Axioms.RiemannRoch
import Jacobians.Axioms.SerreDuality
import Jacobians.Axioms.AbelTheorem
import Jacobians.Axioms.BranchLocus
import Jacobians.Axioms.PluckerFormula
