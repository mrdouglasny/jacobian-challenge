/-
Axiom-trace report for the tracked headline declarations.

Run:  lake env lean scripts/axiom_report.lean > docs/axiom-report.txt

`#print axioms D` prints the COMPLETE transitive axiom dependency of `D`
and surfaces any `sorryAx`. Committing the output as a golden file and
diffing it in CI guarantees, permanently, that:
  * no tracked headline secretly depends on a `sorry` (`sorryAx`), and
  * any change to a headline's axiom set is a reviewed diff.

This file is NOT part of the build root (`scripts/` is outside it); it is
a standalone checker. Keep the list in sync with the headline theorems in
README "Current state". See docs/validation-plan.md Part 1.1.
-/
import Jacobians.Challenge
import Jacobians.Extensions.HyperellipticEven
import Jacobians.ProjectiveCurve.Elliptic.OneForm
import Jacobians.ProjectiveCurve.Line.Genus
import Jacobians.ProjectiveCurve.Line.OneForm
import Jacobians.ProjectiveCurve.Hyperelliptic
import Jacobians.ProjectiveCurve.PlaneCurve
import Jacobians.RiemannSurface.RiemannRochAPI

open Jacobians Jacobian

-- Buzzard API: the 6 data defs + instances and the 11 property theorems.
#print axioms genus
#print axioms Jacobian
#print axioms Jacobian.ofCurve
#print axioms Jacobian.pushforward
#print axioms Jacobian.pullback
#print axioms ContMDiff.degree
#print axioms genus_eq_zero_iff_homeo
#print axioms Jacobian.ofCurve_self
#print axioms Jacobian.ofCurve_inj
#print axioms Jacobian.ofCurve_contMDiff
#print axioms Jacobian.pushforward_contMDiff
#print axioms Jacobian.pushforward_id_apply
#print axioms Jacobian.pushforward_comp_apply
#print axioms Jacobian.pullback_contMDiff
#print axioms Jacobian.pullback_id_apply
#print axioms Jacobian.pullback_comp_apply
#print axioms Jacobian.pushforward_pullback

-- Concrete genus headlines (the definition-validating results).
-- `genus ℙ¹ = 0` and `genus Elliptic = 1` are PROVEN_CORE_AXIOMS (no project axioms).
#print axioms Jacobians.ProjectiveCurve.genus_projectiveLine_eq_zero
#print axioms Jacobians.ProjectiveCurve.HolomorphicOneForm_projectiveLine_eq_zero
#print axioms Jacobians.ProjectiveCurve.genus_Elliptic_eq_one
#print axioms Jacobians.Extensions.HyperellipticEven.genus_HyperellipticEven_eq
-- `h⁰(0) = 1` over the corrected (germ-quotient) L(D): axiom-free faithfulness check.
#print axioms Jacobians.RiemannSurface.h0_zero

-- Phase-3 prerequisite-type discharges: kernel evidence for the AXIOM_AUDIT
-- "Recently discharged" claims. The carriers are standard-3 (no atlas axioms);
-- the chart/manifold instances correctly transport the (sound) atlas axioms.
#print axioms Jacobians.ProjectiveCurve.Hyperelliptic
#print axioms Jacobians.ProjectiveCurve.Hyperelliptic.instTopologicalSpace
#print axioms Jacobians.ProjectiveCurve.Hyperelliptic.instChartedSpace
#print axioms Jacobians.ProjectiveCurve.Hyperelliptic.instIsManifold
#print axioms Jacobians.ProjectiveCurve.AX_Hyperelliptic_oddEquiv
#print axioms Jacobians.ProjectiveCurve.AX_Hyperelliptic_evenEquiv
#print axioms Jacobians.ProjectiveCurve.PlaneCurve
#print axioms Jacobians.ProjectiveCurve.PlaneCurve.instTopologicalSpace
#print axioms Jacobians.ProjectiveCurve.PlaneCurve.instNonempty
