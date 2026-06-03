# Gemini 3.1 Pro critique — `PlaneCurve-instTopologicalSpace`

**Model:** gemini-3.1-pro-preview
**Duration:** 33.9s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **revise**

---

Here is a rigorous review of the proposed discharge plan for `PlaneCurve.instTopologicalSpace`:

1. **Route classification**: **needs-infra** is absolutely correct. The topology of the curve is a trivial, immediate consequence of how the type `PlaneCurve` is constructed. This axiom cannot be discharged until the parent type is de-axiomatized. 
2. **Effort**: **1** is perfectly calibrated. It will take less than 5 minutes once `PlaneCurve` is a real definition.
3. **Proof recipe**:
   - The topological reasoning (Subtype inherits from `Projectivization`, Pushouts inherit from `Sum`/`Quotient`) is mathematically and structurally correct. 
   - *However*, the Lean 4 execution is unidiomatic. You should not write a manual `instance` block using `inferInstanceAs` if you don't have to. For Options A (Quotient) and C (Subtype), Lean 4's `deriving` handler is robust. The parent PR that defines `PlaneCurve` should simply append `deriving TopologicalSpace` to the `def`.
   - The Mathlib file for the topology on projective space in v4.30 is typically `Mathlib.Topology.Instances.ProjectiveSpace` (or integrated into `Geometry.Projective.Projectivization`), not `Mathlib.Topology.Algebra.Projectivization`.
4. **Textbook citations**: N/A. This is purely type-theoretic boilerplate, no math references are needed.
5. **What's missing or wrong**:
   - The plan states you should replace the axiom with a "one-line instance". You should plan to **delete lines 163–165 entirely**. If the parent `PlaneCurve` definition is implemented properly with `deriving TopologicalSpace` (or as an `abbrev`), no replacement text is needed in this file at all.
   - The plan mentions it "drops to a one-liner once `PlaneCurve` is a real `def`", but it needs to state explicitly: **This discharge must be bundled in the exact same PR as the `PlaneCurve` definition**. You cannot provide an instance for an `axiom` type without using another `axiom` (which defeats the purpose). 
6. **Recommendation**: **Revise**. Coordinate with the `PlaneCurve` parent recipe to ensure they use `deriving TopologicalSpace`, and change this recipe's action from "write an `inferInstanceAs` instance" to "delete the axiom block completely."

VERDICT: revise — Coordinate with the parent definition to use `deriving TopologicalSpace`, allowing you to completely delete this axiom rather than writing a manual instance.
