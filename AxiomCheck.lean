/-
Verify the discharge port: every key declaration depends only on
[propext, Classical.choice, Quot.sound] — no sorryAx. Run:
  lake env lean AxiomCheck.lean
-/
import Jacobians
import Jacobians.Discharge.Manifold.RegularValueExistsRegUnconditional

#print axioms ContMDiff.degree
#print axioms Jacobians.degreeFiber
#print axioms Jacobians.RegularValueWitnessReg
#print axioms Jacobians.regularValueWitnessReg_nonempty_of_nonConstantMap
#print axioms Jacobians.Discharge.ContMDiff.degreeFiber
#print axioms Jacobians.Discharge.ContMDiff.Degree.regular_value_exists_reg_unconditional
#print axioms Jacobians.Discharge.ContMDiff.Degree.regular_value_exists_statement_unconditional

-- Degree well-definedness (ported from brsanch; discharges #8′): every regular
-- fibre has the same cardinality `= degreeFiber f`. Axiom-clean.
#print axioms Jacobians.Discharge.degreeFiber_eq_card_of_regular_witness
#print axioms Jacobians.degreeFiber_eq_card_of_regularWitness
#print axioms Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq

-- Newly-closed local theorems (3 sorries → 0):
#print axioms Jacobians.isClosed_criticalSet
#print axioms Jacobians.criticalSet_ne_univ_of_nonconstant
#print axioms Jacobians.finite_criticalSet_of_nonconstant
#print axioms Jacobians.finite_branchLocus_of_nonconstant
#print axioms Jacobians.degDiv_eq_zero
#print axioms Jacobians.exists_properMapDegree
-- The declarations above are the genuinely axiom-CLEAN core (the guard:
-- CI fails if any acquires `sorryAx`). The headline theorems about maps
-- into `Jacobian X` (`ofCurve_contMDiff`, `pushforward_pullback`, `ofCurve_inj`,
-- …) deliberately are NOT listed here: they carry `sorryAx` via the open
-- classical theorems (esp. the period-lattice instances #7/#8, which make
-- `Jacobian X` a manifold). See `docs/STATUS.md` for the per-theorem status.

