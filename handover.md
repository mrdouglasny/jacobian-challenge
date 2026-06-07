# Handover: Discharging PlaneCurve Manifold Axioms

This file outlines the current progress, design details, and next steps for the task of eliminating the `PlaneCurve.instChartedSpace` and `PlaneCurve.instIsManifold` axioms.

---

## 1. Current Status & Completed Work
We are working on the branch `discharge-plane-curve-manifold`. The following files have been successfully implemented, verified with `lake build`, committed, and pushed:
* **`Jacobians/ProjectiveCurve/PlaneCurve.lean`**: Updated with definitions and basic topological instances (`T2Space`, `LocallyCompactSpace`) for `PlaneCurveAffineY` and `PlaneCurveAffineX`.
* **`Jacobians/ProjectiveCurve/PlaneCurve/Euler.lean`**: Proves Euler's homogeneous theorem and the relation between projective smoothness and affine smoothness.
* **`Jacobians/ProjectiveCurve/PlaneCurve/AffineChart.lean`**: Constructs the 6 coordinate charts (2 per patch) using the Implicit Function Theorem (`GeneralResults.InverseFunctionTheorem`).

---

## 2. Verified Proof Snippets for Phase 2
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

---

## 3. Next Steps

### Step 1: Implement `Jacobians/ProjectiveCurve/PlaneCurve/Atlas.lean`
* Define coordinate patches `PlaneCurve.U H i : Set (PlaneCurve H)` as the subtype preimage of `Projectivization.U i`. Prove they are open using `isOpen_U`.
* Define inclusion maps:
  * `PlaneCurveAffine.toPlaneCurve` (already exists in `PlaneCurve.lean`).
  * `PlaneCurveAffineY.toPlaneCurve` using `![p.1, 1, p.2]`.
  * `PlaneCurveAffineX.toPlaneCurve` using `![1, p.1, p.2]`.
* Prove that these inclusion maps are continuous and injective.
* Identify their ranges as `PlaneCurve.U H 2`, `PlaneCurve.U H 1`, and `PlaneCurve.U H 0` respectively.
* Show that they are open embeddings (`Topology.IsOpenEmbedding`) using `isOpenEmbedding_of_continuous_inverse` and the coordinate projection left inverses.
* Lift the 6 affine charts to `PlaneCurve H` via `OpenPartialHomeomorph.lift_openEmbedding`.
* Define `chartAt` on `PlaneCurve H` by matching on non-vanishing coordinates and prove the `ChartedSpace` instance.

### Step 2: Implement `Jacobians/ProjectiveCurve/PlaneCurve/CrossCompat.lean`
* Prove that all transitions between the lifted charts are `ContDiffOn ℂ ω` on their overlaps.
* Transitions reduce to rational coordinate changes (e.g. $(x/z, y/z) \mapsto (1/x, y/x)$), which are analytic since the coordinate denominators do not vanish on overlaps.

### Step 3: Main Module Integration
* Import `Jacobians.ProjectiveCurve.PlaneCurve.Atlas` and `Jacobians.ProjectiveCurve.PlaneCurve.CrossCompat` in `Jacobians/ProjectiveCurve/PlaneCurve.lean`.
* Replace the `axiom PlaneCurve.instChartedSpace` and `axiom PlaneCurve.instIsManifold` declarations with concrete `noncomputable instance` definitions.
* Run `lake build` to verify everything compiles cleanly and axiom counts drop by 2.
