# `PlaneCurve.instT2Space` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:167`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 5 &nbsp;&nbsp; **Est:** ~1-2 focused weeks, ~150-200 LOC
**Blocked by:** `PlaneCurve`

**Statement (verbatim):**
```lean
axiom PlaneCurve.instT2Space (H : PlaneCurveData) : T2Space (PlaneCurve H)
attribute [instance] PlaneCurve.instT2Space
```

**Why it's an axiom right now:** Stub forced by the axiomatic `PlaneCurve` type at `PlaneCurve.lean:161`. Once `PlaneCurve H` is properly defined as a topological quotient of three affine charts, we must manually establish that this glued space is Hausdorff (T2). 

**Proof recipe**

Classical reference: **Lee, *Introduction to Topological Manifolds*, Lemma 3.23** (or similar point-set topology textbook result detailing how gluing T2 spaces along open subsets via homeomorphisms with closed graphs yields a T2 space).

1. **Rely on the Option A quotient structure.** This recipe assumes `PlaneCurve H` has been redefined as a quotient of the disjoint union of three affine charts (`PlaneCurveAffineZ`, `PlaneCurveAffineX`, `PlaneCurveAffineY`).
2. **Chart-level T2.** Each affine chart is naturally T2 because it is a closed subspace of `ℂ²` (e.g., `PlaneCurveAffineZ.instT2` at `PlaneCurve.lean:76` and analogs in `PlaneCurve/AffineCharts.lean`).
3. **Open gluing domains.** Prove that the overlap regions (e.g., the locus where $x \neq 0$ in the $Z$-chart) are open subsets of their respective affine charts. 
4. **Transition continuity.** Prove that the transition maps between these open subsets (e.g., $(x,y) \mapsto (1/x, y/x^d)$) are continuous and act as homeomorphisms on the overlap regions.
5. **Concrete chart separation.** Prove that the quotient map is open, and that the equivalence relation $R$ has a closed graph. For any distinct points $p \neq q \in \text{PlaneCurve } H$:
   - If they lift to the *same* chart, they are separated by that chart's existing T2 instances. Push these disjoint open neighborhoods forward through the open quotient map.
   - If they lift to *different* charts and do not share a common chart, construct disjoint neighborhoods in the affine charts by pulling back non-overlapping neighborhoods through the continuous transition polynomials. 
6. **Instance replacement.** Drop the `axiom` and the `attribute [instance]` line at `PlaneCurve.lean:167–168`, replacing them with:
   ```lean
   instance PlaneCurve.instT2Space (H : PlaneCurveData) : T2Space (PlaneCurve H) := ...
   ```

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — replace lines 167–168 (`axiom PlaneCurve.instT2Space` + the `attribute [instance]`) with an `instance` establishing the quotient is T2 via explicit separation of the affine charts.
- `Jacobians/ProjectiveCurve/Transitions.lean` (or similar) — may need helper lemmas proving continuity of the rational transition functions on the non-vanishing open sets.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms` on any downstream consumer (e.g. `AX_PluckerFormula` at `Axioms/PluckerFormula.lean:55`) no longer lists `PlaneCurve.instT2Space`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the transition polynomials between the affine charts lack basic continuity and openness API in Mathlib, this effort will balloon further. Escalate to split out a sub-task for complex polynomial continuity.
- If the point-set topology of quotienting spaces with closed equivalence relations requires building general Mathlib API that doesn't exist, escalate to avoid a generic topology rabbit hole.

### Gemini critique addressed:
- **Dropped Options B and C entirely:** Acknowledged that Mathlib v4.30 lacks `Mathlib.Topology.Algebra.Projectivization` and that `OpenCover` does not build glued spaces.
- **Committed to 3-chart pushout (Option A):** Forced the recipe to explicitly handle the topological gluing of the affine charts.
- **Upgraded Effort and Estimate:** Changed Effort from 2 to 5, as manual chart separation is highly non-trivial.
- **Replaced circular `ℙ²` logic:** Outlined a concrete topological separation argument that pulls disjoint neighborhoods back through the transition polynomials rather than relying on a non-existent topological `ℙ²_ℂ`.
- **Added appropriate references:** Included a point-set topology reference for gluing (Lee, *Topological Manifolds*) instead of relying purely on algebraic geometry textbooks that suppress the topological details.

---
**Vetting trail.** Critique: `_vetting/PlaneCurve-instT2Space.md`. Verdict: revise. Revised: 2026-06-03.