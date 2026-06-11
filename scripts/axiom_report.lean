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
import Jacobians.ProjectiveCurve.PlaneCurve.CrossCompat
import Jacobians.RiemannSurface.Cohomology.RiemannRochAPI

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

-- Jacobian typeclass instances: the 7 Buzzard-required obligations
-- (TopologicalSpace, T2Space, CompactSpace, ChartedSpace, IsManifold, LieAddGroup,
-- AddCommGroup) plus ConnectedSpace which Challenge.lean explicitly marks as extra
-- (not one of Buzzard's 7 — see line 105 comment).
-- Anonymous instances in Challenge.lean; wrap in named decls to use #print axioms.
-- @[implicit_reducible] suppresses class-type-def warnings for the two data instances.
section JacobianInstances
open scoped Manifold ContDiff
variable {X' : Type*} [TopologicalSpace X'] [T2Space X'] [CompactSpace X']
    [ConnectedSpace X'] [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) ⊤ X']

-- Use _root_.Jacobian to disambiguate from open Jacobian namespace
@[implicit_reducible] private noncomputable def jacInst_AddCommGroup :
    AddCommGroup (_root_.Jacobian X') := inferInstance
@[implicit_reducible] private noncomputable def jacInst_TopologicalSpace :
    TopologicalSpace (_root_.Jacobian X') := inferInstance
private theorem jacInst_T2Space : T2Space (_root_.Jacobian X') := inferInstance
private theorem jacInst_CompactSpace : CompactSpace (_root_.Jacobian X') := inferInstance
-- ConnectedSpace: NOT one of Buzzard's 7 (Challenge.lean line 105); included for completeness
private theorem jacInst_ConnectedSpace : ConnectedSpace (_root_.Jacobian X') := inferInstance
@[implicit_reducible] private noncomputable def jacInst_ChartedSpace :
    ChartedSpace (Fin (genus X') → ℂ) (_root_.Jacobian X') := inferInstance
private theorem jacInst_IsManifold :
    IsManifold 𝓘(ℂ, Fin (genus X') → ℂ) ⊤ (_root_.Jacobian X') := inferInstance
private theorem jacInst_LieAddGroup :
    LieAddGroup 𝓘(ℂ, Fin (genus X') → ℂ) ⊤ (_root_.Jacobian X') := inferInstance

#print axioms jacInst_AddCommGroup
#print axioms jacInst_TopologicalSpace
#print axioms jacInst_T2Space
#print axioms jacInst_CompactSpace
#print axioms jacInst_ConnectedSpace
#print axioms jacInst_ChartedSpace
#print axioms jacInst_IsManifold
#print axioms jacInst_LieAddGroup
end JacobianInstances

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
#print axioms Jacobians.ProjectiveCurve.PlaneCurve.instChartedSpace
#print axioms Jacobians.ProjectiveCurve.PlaneCurve.instIsManifold
#print axioms Jacobians.ProjectiveCurve.PlaneCurve.instConnectedSpace

