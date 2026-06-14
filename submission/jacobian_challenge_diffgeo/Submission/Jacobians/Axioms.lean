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
2. `AX_IntersectionForm` (non-degenerate alternating ℤ-bilinear pairing
   on `H_1`; prerequisite for "symplectic basis")
3. `AX_PeriodCycleBasis` (piecewise-real-analytic ℤ-basis of `H_1`
   carrying the arc-level Riemann bilinear relations R1/R2 — the D1
   merge of the former `AX_AnalyticCycleBasis` + `AX_RBR1` + `AX_RBR2`;
   **subsumes** the former `AX_H1FreeRank2g`, now a theorem)
4. `AX_PeriodLattice` (period image is a ℤ-lattice in `Fin g → ℂ`;
   needed for Jacobian as a complex torus)
5. `AX_RiemannBilinear` (Hodge / symplectic positivity; discharges
   `AX_PeriodLattice`)
6. `AX_BranchLocus` (local `meromorphicOrderAt` + properness)
7. `AX_SerreDuality` (classical pairing)
8. `AX_RiemannRoch` (deepest algebraic axiom)
9. `AX_PluckerFormula` (adjunction; Track 2 `SmoothPlaneCurve` only)
10. `AX_AbelSupset (the split remainder of the discharged AX_AbelTheorem)` (via Riemann theta divisor or Forster-style residue)
-/
import Submission.Jacobians.Axioms.FiniteDimOneForms
import Submission.Jacobians.Axioms.PeriodLattice
import Submission.Jacobians.Axioms.RiemannBilinear
import Submission.Jacobians.Axioms.H1FreeRank2g
import Submission.Jacobians.Axioms.IntersectionForm
import Submission.Jacobians.Axioms.PeriodCycleBasis
import Submission.Jacobians.Axioms.AbelJacobiMap
import Submission.Jacobians.Axioms.AbelJacobiDivDef
import Submission.Jacobians.Axioms.Uniformization0
import Submission.Jacobians.Axioms.RiemannRoch
import Submission.Jacobians.Axioms.SerreDuality
import Submission.Jacobians.Axioms.AbelTheorem
import Submission.Jacobians.Axioms.OfCurveInjective
import Submission.Jacobians.Axioms.BranchLocus
import Submission.Jacobians.Axioms.PluckerFormula
import Submission.Jacobians.Axioms.UniversalProperty
