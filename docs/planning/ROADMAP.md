# Axiom Discharge Roadmap

Routing decisions for all **90 real axioms** across 27 files of the `Jacobians` lean_lib. One markdown plan-file per axiom in this directory (`docs/planning/`); this page is the index. **Every plan has been vetted by Gemini 3.1 Pro** (`gemini-3.1-pro-preview`, extended thinking; 2026-06-03) and the route + effort columns below reflect Gemini's corrections.

> **Starting fresh?** Read [`PHASE_1_HANDOFF.md`](PHASE_1_HANDOFF.md) — a self-contained brief that scopes the first 4 discharges (Divisor cluster + AX_BranchLocus), names the toolchain, lists the cross-plan invariants, and gives a worker prompt template. ~4 focused days of work, axiom count 90 → 86.

> ⚠️ **This page is a point-in-time routing plan (baseline 90 axioms, authored 2026-06-03), not a live status tracker.** The canonical, kernel-checked live count and per-axiom status are in [`AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) + [`axiom-report.txt`](../axiom-report.txt). **Discharged since authoring** (the route/verdict rows below are kept for historical record):
> - **Phase 1** (2026-06-04): `Divisor` / `Divisor-instAddCommGroup` / `Divisor-deg`, `AX_BranchLocus` → 90 → 86.
> - **bridgePath structural cluster** (2026-06-04, branch `phase2-bridgepath`): `bridgePath` (now a `def`), `bridgePath_continuous`, `bridgePath_chart_differentiable`, `bridgePath_at_zero`, `bridgePath_at_one` → 86 → 81, via the new `Bridge/BridgePath.lean` smooth-path-connectedness infrastructure. Only `bridgePath_lineIntegrable` remains of this cluster.
> - **Hyperelliptic leaf instances** (branch `phase2-leaves`, PR #3): `Hyperelliptic.instCompactSpace` / `instConnectedSpace` / `instT2Space` / `instNonempty` discharged there (86 → 82); still listed as open *on this branch* since that PR is not yet merged. Counts compose at merge.

## Vetting summary

| Gemini verdict | Count |
|---|---|
| `accept` | 13 |
| `revise` | 36 |
| `reject` | 41 |
| **Total** | 90 |

Of the 77 plans flagged `revise` or `reject`, **all 77 have been rewritten in place** to address every specific issue Gemini raised; each carries a `**Vetting trail.**` footer pointing to its critique in `_vetting/<slug>.md`. Per-axiom critiques are full referee-grade analyses (~3.5K chars each).

## Summary by route (post-vetting)

| Route | Count |
|---|---|
| `mathlib-now` | 21 |
| `provable-from-other-axioms` | 31 |
| `needs-infra` | 33 |
| `genuine-textbook` | 5 |
| `split` | 0 |
| **Total** | **90** |

## mathlib-now — direct Mathlib discharge

| Effort | Plan | File | Verdict |
|---|---|---|---|
| 1 | [`Divisor`](Divisor.md) | `Jacobians/RiemannSurface/LineBundle.lean` | revise |
| 1 | [`Divisor-deg`](Divisor-deg.md) | `Jacobians/RiemannSurface/LineBundle.lean` | accept |
| 1 | [`Divisor-instAddCommGroup`](Divisor-instAddCommGroup.md) | `Jacobians/RiemannSurface/LineBundle.lean` | revise |
| 1 | [`H0-instModule`](H0-instModule.md) | `Jacobians/RiemannSurface/LineBundle.lean` | revise |
| 1 | [`H1-instModule`](H1-instModule.md) | `Jacobians/RiemannSurface/LineBundle.lean` | accept |
| 1 | [`LineBundle`](LineBundle.md) | `Jacobians/RiemannSurface/LineBundle.lean` | reject |
| 1 | [`LineBundle-ofDivisor`](LineBundle-ofDivisor.md) | `Jacobians/RiemannSurface/LineBundle.lean` | revise |
| 1 | [`PlaneCurve`](PlaneCurve.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | revise |
| 1 | [`ambientPhi_ambientPsi_eq`](ambientPhi_ambientPsi_eq.md) | `Jacobians/Vendor/Kirov/HolomorphicForms.lean` | reject |
| 1 | [`polynomialLocalHomeomorph_no_critical_in_source`](polynomialLocalHomeomorph_no_critical_in_source.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean` | reject |
| 2 | [`H1`](H1.md) | `Jacobians/RiemannSurface/LineBundle.lean` | reject |
| 2 | [`squareLocalHomeomorph_zero_notMem_source`](squareLocalHomeomorph_zero_notMem_source.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean` | revise |
| 3 | [`AX_Elliptic_aLoop_analytic`](AX_Elliptic_aLoop_analytic.md) | `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean` | revise |
| 3 | [`AX_Elliptic_bLoop_analytic`](AX_Elliptic_bLoop_analytic.md) | `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean` | revise |
| 4 | [`AX_BranchLocus`](AX_BranchLocus.md) | `Jacobians/Axioms/BranchLocus.lean` | revise |
| 5 | [`AX_PlaneCurveAffine_nonempty`](AX_PlaneCurveAffine_nonempty.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | reject |
| 6 | [`contDiffOn_symm_toOpenPartialHomeomorph`](contDiffOn_symm_toOpenPartialHomeomorph.md) | `Jacobians/GeneralResults/InverseFunctionTheorem.lean` | reject |
| 6 | [`infinityLiftChart_compat_affineLiftChart`](infinityLiftChart_compat_affineLiftChart.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` | reject |
| 7 | [`affineLiftChart_compat_infinityLiftChart`](affineLiftChart_compat_infinityLiftChart.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` | reject |
| 9 | [`AX_RiemannBilinear`](AX_RiemannBilinear.md) | `Jacobians/Axioms/RiemannBilinear.lean` | revise |
| 10 | [`AX_SerreDuality`](AX_SerreDuality.md) | `Jacobians/Axioms/SerreDuality.lean` | reject |

## provable-from-other-axioms — discharge after named prereqs land

| Effort | Plan | File | Verdict |
|---|---|---|---|
| 1 | [`AX_pullback_contMDiff`](AX_pullback_contMDiff.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | revise |
| 1 | [`Hyperelliptic-instCompactSpace`](Hyperelliptic-instCompactSpace.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | accept |
| 1 | [`Hyperelliptic-instConnectedSpace`](Hyperelliptic-instConnectedSpace.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | accept |
| 1 | [`Hyperelliptic-instNonempty`](Hyperelliptic-instNonempty.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | revise |
| 1 | [`Hyperelliptic-instT2Space`](Hyperelliptic-instT2Space.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | revise |
| 1 | [`bridgePath_at_one`](bridgePath_at_one.md) | `Jacobians/Bridge/KirovLineIntegral.lean` | accept |
| 1 | [`bridgePath_at_zero`](bridgePath_at_zero.md) | `Jacobians/Bridge/KirovLineIntegral.lean` | accept |
| 1 | [`genus_eq_zero_iff_homeo`](genus_eq_zero_iff_homeo.md) | `Jacobians/Vendor/Kirov/Genus.lean` | revise |
| 1 | [`infinityChart_mem_source`](infinityChart_mem_source.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` | accept |
| 2 | [`AX_Hyperelliptic_evenEquiv`](AX_Hyperelliptic_evenEquiv.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | accept |
| 2 | [`AX_Hyperelliptic_genus`](AX_Hyperelliptic_genus.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | reject |
| 2 | [`bridgePath_continuous`](bridgePath_continuous.md) | `Jacobians/Bridge/KirovLineIntegral.lean` | accept |
| 3 | [`AX_curve_generates_jacobian`](AX_curve_generates_jacobian.md) | `Jacobians/Axioms/UniversalProperty.lean` | reject |
| 3 | [`affineLiftProjX_compat_infinityChart`](affineLiftProjX_compat_infinityChart.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` | accept |
| 3 | [`affineLiftProjY_compat_infinityChart`](affineLiftProjY_compat_infinityChart.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` | revise |
| 3 | [`infinityChart_compat_affineLiftProjX`](infinityChart_compat_affineLiftProjX.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` | accept |
| 3 | [`infinityChart_compat_affineLiftProjY`](infinityChart_compat_affineLiftProjY.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` | accept |
| 4 | [`AX_HyperellipticOneForm_eq_form`](AX_HyperellipticOneForm_eq_form.md) | `Jacobians/Axioms/HyperellipticLiouville.lean` | revise |
| 4 | [`AX_Hyperelliptic_oddEquiv`](AX_Hyperelliptic_oddEquiv.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | revise |
| 4 | [`AX_PeriodLattice`](AX_PeriodLattice.md) | `Jacobians/Axioms/PeriodLattice.lean` | accept |
| 4 | [`PlaneCurve-instConnectedSpace`](PlaneCurve-instConnectedSpace.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | revise |
| 4 | [`infinityInverseMap`](infinityInverseMap.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` | reject |
| 4 | [`instPeriodLatticeDiscrete`](instPeriodLatticeDiscrete.md) | `Jacobians/Axioms/PeriodLattice.lean` | revise |
| 4 | [`loopIntegralToH1`](loopIntegralToH1.md) | `Jacobians/RiemannSurface/PathIntegral.lean` | reject |
| 6 | [`AX_genus_eq_zero_iff_homeo`](AX_genus_eq_zero_iff_homeo.md) | `Jacobians/Axioms/Uniformization0.lean` | reject |
| 6 | [`PlaneCurve-instCompactSpace`](PlaneCurve-instCompactSpace.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | revise |
| 6 | [`bridgePath_lineIntegrable`](bridgePath_lineIntegrable.md) | `Jacobians/Bridge/KirovLineIntegral.lean` | reject |
| 7 | [`AX_Elliptic_H1_symplectic`](AX_Elliptic_H1_symplectic.md) | `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean` | reject |
| 7 | [`AX_ofCurve_contMDiff`](AX_ofCurve_contMDiff.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | revise |
| 7 | [`infinityChart`](infinityChart.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` | revise |
| 10 | [`AX_RiemannRoch`](AX_RiemannRoch.md) | `Jacobians/Axioms/RiemannRoch.lean` | reject |

## needs-infra — build bounded missing infrastructure first

| Effort | Plan | File | Verdict |
|---|---|---|---|
| 1 | [`H0`](H0.md) | `Jacobians/RiemannSurface/LineBundle.lean` | reject |
| 1 | [`H0-instAddCommGroup`](H0-instAddCommGroup.md) | `Jacobians/RiemannSurface/LineBundle.lean` | revise |
| 1 | [`H1-instAddCommGroup`](H1-instAddCommGroup.md) | `Jacobians/RiemannSurface/LineBundle.lean` | revise |
| 1 | [`PlaneCurve-instNonempty`](PlaneCurve-instNonempty.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | revise |
| 1 | [`PlaneCurve-instTopologicalSpace`](PlaneCurve-instTopologicalSpace.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | revise |
| 1 | [`abelJacobiDiv`](abelJacobiDiv.md) | `Jacobians/Axioms/AbelTheorem.lean` | revise |
| 2 | [`Hyperelliptic-instTopologicalSpace`](Hyperelliptic-instTopologicalSpace.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | reject |
| 2 | [`PrincipalDivisors`](PrincipalDivisors.md) | `Jacobians/RiemannSurface/LineBundle.lean` | reject |
| 3 | [`AX_pushforwardOneForm_id`](AX_pushforwardOneForm_id.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | revise |
| 3 | [`Hyperelliptic-instChartedSpace`](Hyperelliptic-instChartedSpace.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | revise |
| 3 | [`intersectionForm`](intersectionForm.md) | `Jacobians/Axioms/IntersectionForm.lean` | reject |
| 5 | [`AX_pushforward_contMDiff`](AX_pushforward_contMDiff.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | revise |
| 5 | [`Hyperelliptic`](Hyperelliptic.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | revise |
| 5 | [`PlaneCurve-instT2Space`](PlaneCurve-instT2Space.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | revise |
| 8 | [`AX_AbelTheorem`](AX_AbelTheorem.md) | `Jacobians/Axioms/AbelTheorem.lean` | revise |
| 8 | [`AX_H1_ProjectiveLine_trivial`](AX_H1_ProjectiveLine_trivial.md) | `Jacobians/ProjectiveCurve/Line/Witnesses.lean` | revise |
| 8 | [`AX_HyperellipticAffine_connected`](AX_HyperellipticAffine_connected.md) | `Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean` | reject |
| 8 | [`AX_PlaneCurveAffine_noncompact`](AX_PlaneCurveAffine_noncompact.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | reject |
| 8 | [`AX_pushforwardAmbient_preserves_lattice`](AX_pushforwardAmbient_preserves_lattice.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | reject |
| 8 | [`Hyperelliptic-instIsManifold`](Hyperelliptic-instIsManifold.md) | `Jacobians/ProjectiveCurve/Hyperelliptic.lean` | revise |
| 8 | [`PlaneCurve-instChartedSpace`](PlaneCurve-instChartedSpace.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | revise |
| 8 | [`bridgePath`](bridgePath.md) | `Jacobians/Bridge/KirovLineIntegral.lean` | reject |
| 8 | [`bridgePath_chart_differentiable`](bridgePath_chart_differentiable.md) | `Jacobians/Bridge/KirovLineIntegral.lean` | reject |
| 8 | [`pathIntegralBasepointFunctional`](pathIntegralBasepointFunctional.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | reject |
| 9 | [`AX_ofCurve_inj`](AX_ofCurve_inj.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | reject |
| 9 | [`AX_pathIntegral_local_antiderivative`](AX_pathIntegral_local_antiderivative.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | reject |
| 9 | [`AX_pullbackAmbient_preserves_lattice`](AX_pullbackAmbient_preserves_lattice.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | reject |
| 9 | [`AX_pushforwardOneForm_comp`](AX_pushforwardOneForm_comp.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | reject |
| 10 | [`AX_AnalyticCycleBasis`](AX_AnalyticCycleBasis.md) | `Jacobians/Axioms/AnalyticCycleBasis.lean` | reject |
| 10 | [`AX_IntersectionForm_alternating`](AX_IntersectionForm_alternating.md) | `Jacobians/Axioms/IntersectionForm.lean` | reject |
| 10 | [`AX_IntersectionForm_perfect`](AX_IntersectionForm_perfect.md) | `Jacobians/Axioms/IntersectionForm.lean` | reject |
| 10 | [`canonicalDivisor`](canonicalDivisor.md) | `Jacobians/RiemannSurface/LineBundle.lean` | reject |
| 10 | [`pushforwardOneForm`](pushforwardOneForm.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | reject |

## genuine-textbook — multi-month classical theorems

| Effort | Plan | File | Verdict |
|---|---|---|---|
| 5 | [`AX_HyperellipticForm_polynomial_decomposition`](AX_HyperellipticForm_polynomial_decomposition.md) | `Jacobians/Axioms/HyperellipticLiouville.lean` | reject |
| 8 | [`AX_PluckerFormula`](AX_PluckerFormula.md) | `Jacobians/Axioms/PluckerFormula.lean` | reject |
| 8 | [`AX_pushforward_pullback`](AX_pushforward_pullback.md) | `Jacobians/Axioms/AbelJacobiMap.lean` | reject |
| 9 | [`PlaneCurve-instIsManifold`](PlaneCurve-instIsManifold.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | reject |
| 10 | [`AX_PlaneCurveAffine_connected`](AX_PlaneCurveAffine_connected.md) | `Jacobians/ProjectiveCurve/PlaneCurve.lean` | reject |

## Full per-axiom table (by source location)

| Source | Plan | Route | Effort | Vetting verdict |
|---|---|---|---|---|
| `Jacobians/Axioms/AbelJacobiMap.lean:98` | [`pathIntegralBasepointFunctional`](pathIntegralBasepointFunctional.md) | needs-infra | 8 | reject |
| `Jacobians/Axioms/AbelJacobiMap.lean:116` | [`AX_pathIntegral_local_antiderivative`](AX_pathIntegral_local_antiderivative.md) | needs-infra | 9 | reject |
| `Jacobians/Axioms/AbelJacobiMap.lean:146` | [`pushforwardOneForm`](pushforwardOneForm.md) | needs-infra | 10 | reject |
| `Jacobians/Axioms/AbelJacobiMap.lean:190` | [`AX_pushforwardOneForm_id`](AX_pushforwardOneForm_id.md) | needs-infra | 3 | revise |
| `Jacobians/Axioms/AbelJacobiMap.lean:197` | [`AX_pushforwardOneForm_comp`](AX_pushforwardOneForm_comp.md) | needs-infra | 9 | reject |
| `Jacobians/Axioms/AbelJacobiMap.lean:238` | [`AX_ofCurve_contMDiff`](AX_ofCurve_contMDiff.md) | provable-from-other-axioms | 7 | revise |
| `Jacobians/Axioms/AbelJacobiMap.lean:257` | [`AX_ofCurve_inj`](AX_ofCurve_inj.md) | needs-infra | 9 | reject |
| `Jacobians/Axioms/AbelJacobiMap.lean:310` | [`AX_pushforwardAmbient_preserves_lattice`](AX_pushforwardAmbient_preserves_lattice.md) | needs-infra | 8 | reject |
| `Jacobians/Axioms/AbelJacobiMap.lean:324` | [`AX_pullbackAmbient_preserves_lattice`](AX_pullbackAmbient_preserves_lattice.md) | needs-infra | 9 | reject |
| `Jacobians/Axioms/AbelJacobiMap.lean:582` | [`AX_pushforward_contMDiff`](AX_pushforward_contMDiff.md) | needs-infra | 5 | revise |
| `Jacobians/Axioms/AbelJacobiMap.lean:631` | [`AX_pullback_contMDiff`](AX_pullback_contMDiff.md) | provable-from-other-axioms | 1 | revise |
| `Jacobians/Axioms/AbelJacobiMap.lean:679` | [`AX_pushforward_pullback`](AX_pushforward_pullback.md) | genuine-textbook | 8 | reject |
| `Jacobians/Axioms/AbelTheorem.lean:60` | [`abelJacobiDiv`](abelJacobiDiv.md) | needs-infra | 1 | revise |
| `Jacobians/Axioms/AbelTheorem.lean:66` | [`AX_AbelTheorem`](AX_AbelTheorem.md) | needs-infra | 8 | revise |
| `Jacobians/Axioms/AnalyticCycleBasis.lean:257` | [`AX_AnalyticCycleBasis`](AX_AnalyticCycleBasis.md) | needs-infra | 10 | reject |
| `Jacobians/Axioms/BranchLocus.lean:100` | [`AX_BranchLocus`](AX_BranchLocus.md) | mathlib-now | 4 | revise |
| `Jacobians/Axioms/HyperellipticLiouville.lean:215` | [`AX_HyperellipticForm_polynomial_decomposition`](AX_HyperellipticForm_polynomial_decomposition.md) | genuine-textbook | 5 | reject |
| `Jacobians/Axioms/HyperellipticLiouville.lean:260` | [`AX_HyperellipticOneForm_eq_form`](AX_HyperellipticOneForm_eq_form.md) | provable-from-other-axioms | 4 | revise |
| `Jacobians/Axioms/IntersectionForm.lean:59` | [`intersectionForm`](intersectionForm.md) | needs-infra | 3 | reject |
| `Jacobians/Axioms/IntersectionForm.lean:66` | [`AX_IntersectionForm_alternating`](AX_IntersectionForm_alternating.md) | needs-infra | 10 | reject |
| `Jacobians/Axioms/IntersectionForm.lean:91` | [`AX_IntersectionForm_perfect`](AX_IntersectionForm_perfect.md) | needs-infra | 10 | reject |
| `Jacobians/Axioms/PeriodLattice.lean:77` | [`instPeriodLatticeDiscrete`](instPeriodLatticeDiscrete.md) | provable-from-other-axioms | 4 | revise |
| `Jacobians/Axioms/PeriodLattice.lean:92` | [`AX_PeriodLattice`](AX_PeriodLattice.md) | provable-from-other-axioms | 4 | accept |
| `Jacobians/Axioms/PluckerFormula.lean:55` | [`AX_PluckerFormula`](AX_PluckerFormula.md) | genuine-textbook | 8 | reject |
| `Jacobians/Axioms/RiemannBilinear.lean:69` | [`AX_RiemannBilinear`](AX_RiemannBilinear.md) | mathlib-now | 9 | revise |
| `Jacobians/Axioms/RiemannRoch.lean:59` | [`AX_RiemannRoch`](AX_RiemannRoch.md) | provable-from-other-axioms | 10 | reject |
| `Jacobians/Axioms/SerreDuality.lean:54` | [`AX_SerreDuality`](AX_SerreDuality.md) | mathlib-now | 10 | reject |
| `Jacobians/Axioms/Uniformization0.lean:55` | [`AX_genus_eq_zero_iff_homeo`](AX_genus_eq_zero_iff_homeo.md) | provable-from-other-axioms | 6 | reject |
| `Jacobians/Axioms/UniversalProperty.lean:44` | [`AX_curve_generates_jacobian`](AX_curve_generates_jacobian.md) | provable-from-other-axioms | 3 | reject |
| `Jacobians/Bridge/KirovLineIntegral.lean:164` | [`bridgePath`](bridgePath.md) | needs-infra | 8 | reject |
| `Jacobians/Bridge/KirovLineIntegral.lean:167` | [`bridgePath_continuous`](bridgePath_continuous.md) | provable-from-other-axioms | 2 | accept |
| `Jacobians/Bridge/KirovLineIntegral.lean:182` | [`bridgePath_chart_differentiable`](bridgePath_chart_differentiable.md) | needs-infra | 8 | reject |
| `Jacobians/Bridge/KirovLineIntegral.lean:188` | [`bridgePath_at_zero`](bridgePath_at_zero.md) | provable-from-other-axioms | 1 | accept |
| `Jacobians/Bridge/KirovLineIntegral.lean:191` | [`bridgePath_at_one`](bridgePath_at_one.md) | provable-from-other-axioms | 1 | accept |
| `Jacobians/Bridge/KirovLineIntegral.lean:212` | [`bridgePath_lineIntegrable`](bridgePath_lineIntegrable.md) | provable-from-other-axioms | 6 | reject |
| `Jacobians/GeneralResults/InverseFunctionTheorem.lean:9` | [`contDiffOn_symm_toOpenPartialHomeomorph`](contDiffOn_symm_toOpenPartialHomeomorph.md) | mathlib-now | 6 | reject |
| `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:86` | [`AX_Elliptic_aLoop_analytic`](AX_Elliptic_aLoop_analytic.md) | mathlib-now | 3 | revise |
| `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:90` | [`AX_Elliptic_bLoop_analytic`](AX_Elliptic_bLoop_analytic.md) | mathlib-now | 3 | revise |
| `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean:166` | [`AX_Elliptic_H1_symplectic`](AX_Elliptic_H1_symplectic.md) | provable-from-other-axioms | 7 | reject |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:59` | [`Hyperelliptic`](Hyperelliptic.md) | needs-infra | 5 | revise |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:61` | [`Hyperelliptic-instTopologicalSpace`](Hyperelliptic-instTopologicalSpace.md) | needs-infra | 2 | reject |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:65` | [`Hyperelliptic-instT2Space`](Hyperelliptic-instT2Space.md) | provable-from-other-axioms | 1 | revise |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:68` | [`Hyperelliptic-instCompactSpace`](Hyperelliptic-instCompactSpace.md) | provable-from-other-axioms | 1 | accept |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:72` | [`Hyperelliptic-instConnectedSpace`](Hyperelliptic-instConnectedSpace.md) | provable-from-other-axioms | 1 | accept |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:76` | [`Hyperelliptic-instNonempty`](Hyperelliptic-instNonempty.md) | provable-from-other-axioms | 1 | revise |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:81` | [`Hyperelliptic-instChartedSpace`](Hyperelliptic-instChartedSpace.md) | needs-infra | 3 | revise |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:87` | [`Hyperelliptic-instIsManifold`](Hyperelliptic-instIsManifold.md) | needs-infra | 8 | revise |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:93` | [`AX_Hyperelliptic_oddEquiv`](AX_Hyperelliptic_oddEquiv.md) | provable-from-other-axioms | 4 | revise |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:99` | [`AX_Hyperelliptic_evenEquiv`](AX_Hyperelliptic_evenEquiv.md) | provable-from-other-axioms | 2 | accept |
| `Jacobians/ProjectiveCurve/Hyperelliptic.lean:104` | [`AX_Hyperelliptic_genus`](AX_Hyperelliptic_genus.md) | provable-from-other-axioms | 2 | reject |
| `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean:66` | [`squareLocalHomeomorph_zero_notMem_source`](squareLocalHomeomorph_zero_notMem_source.md) | mathlib-now | 2 | revise |
| `Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean:247` | [`polynomialLocalHomeomorph_no_critical_in_source`](polynomialLocalHomeomorph_no_critical_in_source.md) | mathlib-now | 1 | reject |
| `Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean:101` | [`AX_HyperellipticAffine_connected`](AX_HyperellipticAffine_connected.md) | needs-infra | 8 | reject |
| `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean:243` | [`affineLiftChart_compat_infinityLiftChart`](affineLiftChart_compat_infinityLiftChart.md) | mathlib-now | 7 | reject |
| `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean:252` | [`infinityLiftChart_compat_affineLiftChart`](infinityLiftChart_compat_affineLiftChart.md) | mathlib-now | 6 | reject |
| `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:48` | [`infinityInverseMap`](infinityInverseMap.md) | provable-from-other-axioms | 4 | reject |
| `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:58` | [`infinityChart`](infinityChart.md) | provable-from-other-axioms | 7 | revise |
| `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:62` | [`infinityChart_mem_source`](infinityChart_mem_source.md) | provable-from-other-axioms | 1 | accept |
| `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:66` | [`infinityChart_compat_affineLiftProjX`](infinityChart_compat_affineLiftProjX.md) | provable-from-other-axioms | 3 | accept |
| `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:78` | [`affineLiftProjX_compat_infinityChart`](affineLiftProjX_compat_infinityChart.md) | provable-from-other-axioms | 3 | accept |
| `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:90` | [`infinityChart_compat_affineLiftProjY`](infinityChart_compat_affineLiftProjY.md) | provable-from-other-axioms | 3 | accept |
| `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:102` | [`affineLiftProjY_compat_infinityChart`](affineLiftProjY_compat_infinityChart.md) | provable-from-other-axioms | 3 | revise |
| `Jacobians/ProjectiveCurve/Line/Witnesses.lean:43` | [`AX_H1_ProjectiveLine_trivial`](AX_H1_ProjectiveLine_trivial.md) | needs-infra | 8 | revise |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:103` | [`AX_PlaneCurveAffine_nonempty`](AX_PlaneCurveAffine_nonempty.md) | mathlib-now | 5 | reject |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:113` | [`AX_PlaneCurveAffine_connected`](AX_PlaneCurveAffine_connected.md) | genuine-textbook | 10 | reject |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:121` | [`AX_PlaneCurveAffine_noncompact`](AX_PlaneCurveAffine_noncompact.md) | needs-infra | 8 | reject |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:161` | [`PlaneCurve`](PlaneCurve.md) | mathlib-now | 1 | revise |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:163` | [`PlaneCurve-instTopologicalSpace`](PlaneCurve-instTopologicalSpace.md) | needs-infra | 1 | revise |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:167` | [`PlaneCurve-instT2Space`](PlaneCurve-instT2Space.md) | needs-infra | 5 | revise |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:170` | [`PlaneCurve-instCompactSpace`](PlaneCurve-instCompactSpace.md) | provable-from-other-axioms | 6 | revise |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:174` | [`PlaneCurve-instConnectedSpace`](PlaneCurve-instConnectedSpace.md) | provable-from-other-axioms | 4 | revise |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:178` | [`PlaneCurve-instNonempty`](PlaneCurve-instNonempty.md) | needs-infra | 1 | revise |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:181` | [`PlaneCurve-instChartedSpace`](PlaneCurve-instChartedSpace.md) | needs-infra | 8 | revise |
| `Jacobians/ProjectiveCurve/PlaneCurve.lean:185` | [`PlaneCurve-instIsManifold`](PlaneCurve-instIsManifold.md) | genuine-textbook | 9 | reject |
| `Jacobians/RiemannSurface/LineBundle.lean:51` | [`Divisor`](Divisor.md) | mathlib-now | 1 | revise |
| `Jacobians/RiemannSurface/LineBundle.lean:56` | [`Divisor-instAddCommGroup`](Divisor-instAddCommGroup.md) | mathlib-now | 1 | revise |
| `Jacobians/RiemannSurface/LineBundle.lean:63` | [`Divisor-deg`](Divisor-deg.md) | mathlib-now | 1 | accept |
| `Jacobians/RiemannSurface/LineBundle.lean:70` | [`PrincipalDivisors`](PrincipalDivisors.md) | needs-infra | 2 | reject |
| `Jacobians/RiemannSurface/LineBundle.lean:77` | [`LineBundle`](LineBundle.md) | mathlib-now | 1 | reject |
| `Jacobians/RiemannSurface/LineBundle.lean:85` | [`H0`](H0.md) | needs-infra | 1 | reject |
| `Jacobians/RiemannSurface/LineBundle.lean:90` | [`H0-instAddCommGroup`](H0-instAddCommGroup.md) | needs-infra | 1 | revise |
| `Jacobians/RiemannSurface/LineBundle.lean:96` | [`H0-instModule`](H0-instModule.md) | mathlib-now | 1 | revise |
| `Jacobians/RiemannSurface/LineBundle.lean:104` | [`H1`](H1.md) | mathlib-now | 2 | reject |
| `Jacobians/RiemannSurface/LineBundle.lean:108` | [`H1-instAddCommGroup`](H1-instAddCommGroup.md) | needs-infra | 1 | revise |
| `Jacobians/RiemannSurface/LineBundle.lean:114` | [`H1-instModule`](H1-instModule.md) | mathlib-now | 1 | accept |
| `Jacobians/RiemannSurface/LineBundle.lean:123` | [`canonicalDivisor`](canonicalDivisor.md) | needs-infra | 10 | reject |
| `Jacobians/RiemannSurface/LineBundle.lean:128` | [`LineBundle-ofDivisor`](LineBundle-ofDivisor.md) | mathlib-now | 1 | revise |
| `Jacobians/RiemannSurface/PathIntegral.lean:101` | [`loopIntegralToH1`](loopIntegralToH1.md) | provable-from-other-axioms | 4 | reject |
| `Jacobians/Vendor/Kirov/Genus.lean:94` | [`genus_eq_zero_iff_homeo`](genus_eq_zero_iff_homeo.md) | provable-from-other-axioms | 1 | revise |
| `Jacobians/Vendor/Kirov/HolomorphicForms.lean:340` | [`ambientPhi_ambientPsi_eq`](ambientPhi_ambientPsi_eq.md) | mathlib-now | 1 | reject |

---

**How to use.** Each per-axiom file follows the recipe template (statement → why-axiomatized → numbered proof recipe with `file:line` citations → files touched → acceptance criteria → escalation triggers), with a Gemini-critique-addressed subsection and vetting-trail footer. When a recipe is discharged, replace the axiom with the theorem and check the box in the section table; the lean-fleet gate (`python3 gate.py --repo jacobian-challenge --build Jacobians`) verifies axiom-count drops and no new sorries.

**Vetting artefacts.** `_vetting/<slug>.md` per-axiom critiques · `_vetting/_RESULTS*.json` raw tallies · `_vetting/VETTING_SUMMARY.md` strategic-subset analysis · `_vetting/_FIXES_results.json` rewrite log.
