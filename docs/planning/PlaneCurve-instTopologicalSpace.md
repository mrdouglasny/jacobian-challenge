# `PlaneCurve.instTopologicalSpace` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:163`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 1 &nbsp;&nbsp; **Est:** ~30 minutes, 0 LOC — completely eliminated since parent `def` will use `deriving TopologicalSpace`
**Blocked by:** `PlaneCurve`

**Statement (verbatim):**
```lean
axiom PlaneCurve.instTopologicalSpace (H : PlaneCurveData) :
    TopologicalSpace (PlaneCurve H)
attribute [instance] PlaneCurve.instTopologicalSpace
```

**Why it's an axiom right now:** Stub forced by the axiomatic `PlaneCurve` type at `PlaneCurve.lean:161`. There is nothing topologically non-trivial here: as soon as `PlaneCurve H` becomes a real `def` (its own recipe — `docs/planning/PlaneCurve.md`), the topology is determined by the construction. The axiom exists only so that the downstream `PlaneCurve.instT2Space` / `instCompactSpace` / `instConnectedSpace` / `instNonempty` / `instChartedSpace` / `instIsManifold` can be stated at all.

**Proof recipe**

**Crucial prerequisite:** This discharge MUST be bundled in the exact same PR as the `PlaneCurve` definition. You cannot provide a topological instance for an `axiom` type without using another `axiom`. 

1. Ensure the parent `PlaneCurve` definition (`docs/planning/PlaneCurve.md`) successfully generates its own `TopologicalSpace` instance automatically. Lean 4's `deriving` handler is robust for this:
   - **For Subtype (Option C):** Mathlib provides the topology on projective space via `Mathlib.Topology.Instances.ProjectiveSpace` (or integrated into `Geometry.Projective.Projectivization`). The parent PR defining `PlaneCurve` as a subtype of `Projectivization ℂ (Fin 3 → ℂ)` should simply append `deriving TopologicalSpace` to the `def`.
   - **For Quotient pushout (Option A):** Pushouts inherit from `Sum` and `Quotient` topologies. The `deriving TopologicalSpace` handler on the definition (or making it an `abbrev`) will also succeed here.
2. Because the parent definition now automatically provides the `TopologicalSpace` instance, no replacement manual `instance` block (e.g., using `inferInstanceAs`) is needed in this file.
3. Completely **delete the `axiom` and the `attribute [instance]` line** at `PlaneCurve.lean:163–165`.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — delete lines 163–165 entirely. (Also ensure the parent `def PlaneCurve` at line 161 uses `deriving TopologicalSpace` as part of the bundled PR).

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurve.instT2Space` (`PlaneCurve.lean:167`) and any other downstream consumer no longer lists `PlaneCurve.instTopologicalSpace`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1 (bundled with parent `PlaneCurve`).

**Risk / escalation triggers**
- If the parent `PlaneCurve` definition fails to support `deriving TopologicalSpace` (e.g., due to an unexpected Type class resolution failure with `Projectivization`), escalate to determine if a manual instance block using `inferInstanceAs` must be written after all.

### Gemini critique addressed:
- Shifted the plan from writing a manual `inferInstanceAs` block to simply deleting the axiom entirely, relying on `deriving TopologicalSpace` in the parent `PlaneCurve` definition.
- Updated the Mathlib citation for projective space topology to `Mathlib.Topology.Instances.ProjectiveSpace` (or `Geometry.Projective.Projectivization`), correcting the previous incorrect reference.
- Added explicit instruction that this discharge must be bundled in the exact same PR as the `PlaneCurve` definition.

---
**Vetting trail.** Critique: `_vetting/PlaneCurve-instTopologicalSpace.md`. Verdict: revise. Revised: 2026-06-03.