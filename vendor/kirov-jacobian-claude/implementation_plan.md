# Implementation Plan: Repository Alignment and Integration

This plan outlines the status of the alignment between our repository (`daouid/jacobian-claude`) and their repository (`mrdouglasny/jacobian-challenge`), bridging our real proofs to replace their custom axioms, resolving definition mismatches, and fixing version compatibility bugs.

## Current Status Summary

All alignment, compatibility, and integration phases have been **successfully completed and verified**. The codebase builds with **0 errors** via `lake build`, conforms 100% to Kevin Buzzard's v0.4 spec, and preserves our strictly **axiom-free** policy for our own proofs (only carrying standard `sorry` on our 4 open mathematical targets).

---

## Completed Phases

### [COMPLETED] Phase 0: Mathlib Compatibility and Build Repair
All compilation errors caused by the Mathlib version gap between the two codebases have been repaired:
- **Convex Combination Renaming**: Renamed all instances of `convexComb` to `convexCombo` (plus lemma variants `le_convexCombo` / `convexCombo_le`) in [HomotopyInvarianceDevelop.lean](file:///d:/MATHS/jacobian-claude/Jacobians/RiemannSurface/HomotopyInvarianceDevelop.lean).
- **Connectedness Transport**: Resolved universe level mismatch of `connectedSpace_iff` in [Construction.lean](file:///d:/MATHS/jacobian-claude/Jacobians/Jacobian/Construction.lean) by defining `Homeomorph.connectedSpace_iff_local` as a `_root_` lemma with a universe-safe direct proof.
- **Scalar Tower and SMul Synthesis**: Resolved typeclass synthesis errors for `IsScalarTower ℝ ℂ ℂ` and `ContinuousSMul ℝ ℂ` in [BridgePathArc.lean](file:///d:/MATHS/jacobian-claude/Jacobians/Bridge/BridgePathArc.lean) and [DevelopingBridge.lean](file:///d:/MATHS/jacobian-claude/Jacobians/RiemannSurface/DevelopingBridge.lean) by importing `Mathlib.Analysis.Normed.Module.Basic` and disabling respectTransparency.
- **Universe Variable Declarations**: Added explicit universe declarations `universe u v w` to [AbelJacobiMap.lean](file:///d:/MATHS/jacobian-claude/Jacobians/Axioms/AbelJacobiMap.lean), [AbelTheorem.lean](file:///d:/MATHS/jacobian-claude/Jacobians/Axioms/AbelTheorem.lean), [OfCurveInjective.lean](file:///d:/MATHS/jacobian-claude/Jacobians/Axioms/OfCurveInjective.lean), and [TorusAlbanese.lean](file:///d:/MATHS/jacobian-claude/Jacobians/Axioms/TorusAlbanese.lean).

### [COMPLETED] Phase 1: Holomorphic Forms Equivalence Bridge
Established a formal equivalence (`Equiv` / `LinearEquiv`) between our cotangent-bundle section representation and their coordinate-vector representation:
- **Forms Equivalence Isomorphism**: Verified [KirovHolomorphicEquiv.lean](file:///d:/MATHS/jacobian-claude/Jacobians/Bridge/KirovHolomorphicEquiv.lean), defining `bridgeFormEquiv` as a `LinearEquiv` between `HolomorphicOneForm` and Kirov's section representation.
- **Ambient Degree Trace Identity**: Proved `ambientPhi_ambientPullback_eq` and `pushforward_pullback` in [Jacobians.lean](file:///d:/MATHS/jacobian-claude/Jacobians.lean).

### [COMPLETED] Phase 2: Path Connectedness and Line Integrals Bridge
Replaced stubs and path integration expectations with our fully proven smooth path and line integral theorems:
- **Canonical Integral Agreement**: Proved `kirovBackedFunctional_eq_canonicalArcIntegral` in [KirovCanonicalEq.lean](file:///d:/MATHS/jacobian-claude/Jacobians/Bridge/KirovCanonicalEq.lean), connecting smooth paths and line integrals to Kirov's line integrals.
- **Homotopy Invariance**: Verified that homotopy-invariance theorems (`discCoverPathPrimitive` and `discCoverIntegral_homotopic`) cleanly discharge path integration expectations.

### [COMPLETED] Phase 3: Terminology and Naming Convention Alignment
Aligned all core declarations to the v0.4 challenge signature layout:
- **Spec Conformance**: Verified via [ChallengeConformance.lean](file:///d:/MATHS/jacobian-claude/ChallengeConformance.lean) that all signatures (`genus`, `Jacobian`, `ofCurve`, `pushforward`, `pullback`) match the v0.4 specification exactly.

### [COMPLETED] Phase 4: Track 2 Curve Integration
Integrated the algebraic curves definitions into our codebase:
- **Curves Support**: Imported `Line` (sphere), `Elliptic`, `Hyperelliptic`, and `PlaneCurve` definitions in [ProjectiveCurve.lean](file:///d:/MATHS/jacobian-claude/Jacobians/ProjectiveCurve.lean) and verified that all curves build successfully.

---

## Proposed Changes: Phase 5 (Mathlib & Toolchain Alignment to v4.30.0)

We propose aligning our Lean toolchain and Mathlib pin to match `mrdouglasny/jacobian-challenge` exactly. This will allow us to discard our local compatibility workarounds, clean up the codebase, and prevent future integration drift.

### Proposed Changes

#### [MODIFY] [lean-toolchain](file:///d:/MATHS/jacobian-claude/lean-toolchain)
* Update toolchain pin from `v4.30.0-rc1` to `v4.30.0`.

#### [MODIFY] [lakefile.lean](file:///d:/MATHS/jacobian-claude/lakefile.lean)
* Update mathlib package dependency requirement to commit `c5ea00351c28e24afc9f0f84379aa41082b1188f` (v4.30.0 release version).

#### [MODIFY] Revert Local Compatibility Workarounds (19 files)
Since we are aligning our toolchain and Mathlib to their version, we will discard our local changes to the 19 modified files (e.g. reverting `convexCombo` to `convexComb`, removing custom scalar tower instances and connectedness transport helper definitions).
Specifically, we will run `git checkout` on the following files:
* `Jacobians/Axioms/AbelJacobiMap.lean`
* `Jacobians/Axioms/AbelTheorem.lean`
* `Jacobians/Axioms/OfCurveInjective.lean`
* `Jacobians/Axioms/TorusAlbanese.lean`
* `Jacobians/Bridge/BridgePath.lean`
* `Jacobians/Bridge/BridgePathArc.lean`
* `Jacobians/Bridge/KirovLineIntegral.lean`
* `Jacobians/HolomorphicForms.lean`
* `Jacobians/Jacobian/Construction.lean`
* `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
* `Jacobians/RiemannSurface/AnalyticArc.lean`
* `Jacobians/RiemannSurface/ArcAlgebra.lean`
* `Jacobians/RiemannSurface/ArcChartDifferentiable.lean`
* `Jacobians/RiemannSurface/DevelopingBridge.lean`
* `Jacobians/RiemannSurface/DevelopingMap.lean`
* `Jacobians/RiemannSurface/DevelopingValueAlgebra.lean`
* `Jacobians/RiemannSurface/HomotopyInvarianceDevelop.lean`
* `Jacobians/RiemannSurface/IntegrandIndependence.lean`
* `Jacobians/RiemannSurface/LineBundle.lean`

---

## Verification Plan

### Automated Tests
1. **Retrieve Package and Cache**:
   ```bash
   lake update
   lake exe cache get
   ```
2. **Build Workspace**:
   ```bash
   lake build
   ```
3. **Spec Conformance**:
   ```bash
   lake env lean ChallengeConformance.lean
   ```
4. **Axiom Hygiene**:
   ```bash
   lake env lean AxiomCheck.lean
   ```
