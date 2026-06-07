# Handover: Discharging PlaneCurve Manifold Axioms

This file outlines the current progress, design details, task list, implementation plan, and next steps for the task of eliminating the `PlaneCurve.instChartedSpace` and `PlaneCurve.instIsManifold` axioms.

---

## 1. Current Status & Completed Work
We are working on the branch `discharge-plane-curve-manifold`. The following files have been successfully implemented, verified with `lake build`, committed, and pushed:
* **`Jacobians/ProjectiveCurve/PlaneCurve.lean`**: Updated with definitions and basic topological instances (`T2Space`, `LocallyCompactSpace`) for `PlaneCurveAffineY` and `PlaneCurveAffineX`.
* **`Jacobians/ProjectiveCurve/PlaneCurve/Euler.lean`**: Proves Euler's homogeneous theorem and the relation between projective smoothness and affine smoothness.
* **`Jacobians/ProjectiveCurve/PlaneCurve/AffineChart.lean`**: Constructs the 6 coordinate charts (2 per patch) using the Implicit Function Theorem (`GeneralResults.InverseFunctionTheorem`).

---

## 2. Implementation Plan

The goal is to prove that the smooth projective plane curve `PlaneCurve H` is a smooth complex 1-manifold, replacing the two `axiom` stubs (`PlaneCurve.instChartedSpace` and `PlaneCurve.instIsManifold`) with fully verified, sorry-free instances.

### Proposed Changes

We organize the proof into three helper modules:

#### A. Affine Charts (`PlaneCurve/AffineChart.lean`)
* **Definitions:**
  * Define `PlaneCurveAffineY` (the $y = 1$ patch): `{ p : ℂ × ℂ // H.F.val.eval ![p.1, 1, p.2] = 0 }`
  * Define `PlaneCurveAffineX` (the $x = 1$ patch): `{ p : ℂ × ℂ // H.F.val.eval ![1, p.1, p.2] = 0 }`
  * Define `PlaneCurveAffine` (the existing $z = 1$ patch in `PlaneCurve.lean`).
* **Smoothness at Roots:**
  * Prove that the projective smoothness condition `H.h_smooth` (non-vanishing gradient on the curve) implies that for any point on each affine patch, at least one of the two affine partial derivatives is non-zero.
* **IFT Local Inverses:**
  * Invoke `Jacobians.GeneralResults.InverseFunctionTheorem` to construct local charts:
    * `affineChartProjX`, `affineChartProjY` (for Z patch)
    * `affineChartProjZ_Y`, `affineChartProjX_Y` (for Y patch)
    * `affineChartProjY_X`, `affineChartProjZ_X` (for X patch)

#### B. Projective Atlas (`PlaneCurve/Atlas.lean`)
* **Open Embeddings:**
  * Define the inclusion maps `toPlaneCurveZ : PlaneCurveAffine H → PlaneCurve H`, `toPlaneCurveY : PlaneCurveAffineY H → PlaneCurve H`, and `toPlaneCurveX : PlaneCurveAffineX H → PlaneCurve H`.
  * Prove that each inclusion is an `IsOpenEmbedding`.
* **Chart Pushforward:**
  * Use `OpenPartialHomeomorph.lift_openEmbedding` to lift the charts of the three affine patches to `PlaneCurve H`.
* **Unified Chart:**
  * Define `chartAt` on `PlaneCurve H` by selecting the chart corresponding to the first non-vanishing coordinate ($z \neq 0$, then $y \neq 0$, then $x \neq 0$).
  * Prove the `ChartedSpace` instance for `PlaneCurve H`.

#### C. Transition Compatibility (`PlaneCurve/CrossCompat.lean`)
* **Transition Analyticity:**
  * Prove that the transition maps between any two charts are analytic (`ContDiffOn ℂ ω`).
  * Diagonal transitions (same summand) reduce to the affine patch compatibility.
  * Cross-summand transitions (different summands) reduce to rational maps of the form $(x/z, y/z) \mapsto (1/x, y/x)$ composed with the IFT local inverses, which are analytic on their domains since the denominators do not vanish on the overlaps.

#### D. Main PlaneCurve Module (`PlaneCurve.lean`)
* Import `Jacobians.ProjectiveCurve.PlaneCurve.Atlas` and `Jacobians.ProjectiveCurve.PlaneCurve.CrossCompat`.
* Remove the `axiom PlaneCurve.instChartedSpace` and `axiom PlaneCurve.instIsManifold` declarations.
* Replace them with:
  * `noncomputable instance PlaneCurve.instChartedSpace (H : PlaneCurveData) : ChartedSpace ℂ (PlaneCurve H)`
  * `noncomputable instance PlaneCurve.instIsManifold (H : PlaneCurveData) : IsManifold 𝓘(ℂ, ℂ) ω (PlaneCurve H)`

---

## 3. Task List
Track progress with this checklist:

- [x] Set up the git branch (`discharge-plane-curve-manifold`)
- [x] Implement `Jacobians/ProjectiveCurve/PlaneCurve/AffineChart.lean`
  - [x] Define `PlaneCurveAffineY` and `PlaneCurveAffineX` patches
  - [x] Prove smoothness at roots using Euler's formula
  - [x] Construct IFT local inverse charts
- [ ] Implement `Jacobians/ProjectiveCurve/PlaneCurve/Atlas.lean`
  - [ ] Define open embeddings into `PlaneCurve H`
  - [ ] Lift charts via `OpenPartialHomeomorph.lift_openEmbedding`
  - [ ] Define `chartAt` on `PlaneCurve H` and prove `ChartedSpace`
- [ ] Implement `Jacobians/ProjectiveCurve/PlaneCurve/CrossCompat.lean`
  - [ ] Prove diagonal compatibility cases
  - [ ] Prove cross-summand compatibility cases (rational transitions)
- [ ] Integrate into `Jacobians/ProjectiveCurve/PlaneCurve.lean`
  - [ ] Import modules and replace stubs with concrete instances
- [ ] Verify the build and axioms
  - [ ] Compile the project with `lake build`
  - [ ] Run `#print axioms` to ensure sorry-free / standard-3 clean proofs

---

## 4. Verified Proof Snippets for Phase 2
During this session, we verified the following crucial topological proofs in Lean 4 to simplify the coordinate patch openness in the projective space. These can be dropped directly into the upcoming `Jacobians/ProjectiveCurve/PlaneCurve/Atlas.lean`:

### Coordinate Patch Openness
Using `isQuotientMap_quotient_mk'.isOpen_preimage` with a local noncomputable setoid instance:
```lean
import Mathlib
import Jacobians.ProjectiveCurve.PlaneCurve
import Jacobians.ProjectiveCurve.PlaneCurve.AffineChart

open MvPolynomial
open scoped Manifold Topology ContDiff

namespace Jacobians.ProjectiveCurve

noncomputable local instance instSetoid : Setoid { v : Fin 3 → ℂ // v ≠ 0 } :=
  projectivizationSetoid ℂ (Fin 3 → ℂ)

instance instTopologicalSpaceProjectivization :
    TopologicalSpace (Projectivization ℂ (Fin 3 → ℂ)) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (Fin 3 → ℂ))))

attribute [local instance] instTopologicalSpaceProjectivization

def Projectivization.U (i : Fin 3) : Set (Projectivization ℂ (Fin 3 → ℂ)) :=
  { p | ∃ v : Fin 3 → ℂ, ∃ hv : v ≠ 0,
    Projectivization.mk ℂ v hv = p ∧ v i ≠ 0 }

theorem isOpen_U (i : Fin 3) : IsOpen (Projectivization.U i) := by
  change IsOpen { p : Quotient instSetoid |
    ∃ v : Fin 3 → ℂ, ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv = p ∧ v i ≠ 0 }
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  have h_eq : Quotient.mk' ⁻¹'
      { p : Quotient instSetoid |
        ∃ v : Fin 3 → ℂ, ∃ hv : v ≠ 0, Projectivization.mk ℂ v hv = p ∧ v i ≠ 0 } =
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val i ≠ 0 } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, h_mk, h_vi⟩
      have h_mk' : Projectivization.mk ℂ v hv = Projectivization.mk ℂ x.val x.property := h_mk
      rw [Projectivization.mk_eq_mk_iff ℂ v x.val hv x.property] at h_mk'
      rcases h_mk' with ⟨c, hc⟩
      intro h_zero
      apply h_vi
      have h_eval := congr_fun hc i
      change (c : ℂ) • x.val i = v i at h_eval
      rw [smul_eq_mul] at h_eval
      rw [h_zero, mul_zero] at h_eval
      exact h_eval.symm
    · intro h_xi
      refine ⟨x.val, x.property, ?_, h_xi⟩
      rfl
  rw [h_eq]
  have h_pre : { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val i ≠ 0 } =
      (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val i) ⁻¹' { z : ℂ | z ≠ 0 } := rfl
  rw [h_pre]
  refine IsOpen.preimage ?_ isOpen_compl_singleton
  exact (continuous_apply i).comp continuous_subtype_val
```
