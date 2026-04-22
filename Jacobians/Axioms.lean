/-
Named axioms for deep facts the project uses but does not (yet) discharge.

Each axiom lives in its own submodule, with a docstring stating:
* The mathematical content.
* A classical reference (Mumford, Milne, Forster, …).
* Why it's axiomatized rather than proved at this stage.

See `docs/formalization-plan.md` §7 for the full axiom-discharge priority
order. Discharge priority (rough):

1. `AX_PeriodInjective` (follows from `AX_RiemannBilinear`)
2. `AX_BranchLocus` (local `meromorphicOrderAt` + properness)
3. `AX_H1FreeRank2g` (CW topology of compact oriented surfaces)
4. `AX_RiemannBilinear` (Hodge / symplectic positivity)
5. `AX_FiniteDimOneForms` (compactness + normal families, or Serre duality)
6. `AX_PluckerFormula` (adjunction; Track 2 `SmoothPlaneCurve` only)
7. `AX_SerreDuality` (classical pairing)
8. `AX_RiemannRoch` (deepest algebraic axiom)
9. `AX_AbelTheorem` (via Riemann theta divisor or Forster-style residue)
-/
import Jacobians.Axioms.FiniteDimOneForms
import Jacobians.Axioms.RiemannBilinear
import Jacobians.Axioms.H1FreeRank2g
import Jacobians.Axioms.RiemannRoch
import Jacobians.Axioms.SerreDuality
import Jacobians.Axioms.AbelTheorem
import Jacobians.Axioms.BranchLocus
import Jacobians.Axioms.PluckerFormula
