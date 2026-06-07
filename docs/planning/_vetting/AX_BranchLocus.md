> **✅ DISCHARGED — 2026-06-04 (Phase 1).** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# Gemini 3.1 Pro critique — `AX_BranchLocus`

**Model:** gemini-3.1-pro-preview
**Duration:** 70.1s
**Source axiom:** `Jacobians/Axioms/BranchLocus.lean`
**Note:** flag: mathlib-now but manifold OMT absent
**Verdict:** **revise**

---

Here is a rigorous referee critique of the proposed discharge plan.

### 1. Route Classification
**Incorrect.** The plan reclassifies the route to `needs-infra` but immediately contradicts this by stating: *"Blocked by: none (the supposed blocker... is already discharged inside `Vendor...`)"* and *"no Mathlib PR needed."* 
If the heavy-lifting (the manifold-level Open Mapping Theorem) is already fully available as `weightedFiberConservation_of_contMDiff` in the project's vendor files, you do not need new infrastructure. You merely need to glue existing project code to Mathlib's `IsLocallyConstant`. The correct classification is **`mathlib-now`**.

### 2. Effort
**Calibrated, but slightly pessimistic.** An effort of 5 (~1 week) is reasonable given the friction of juggling `tsum`, `Finset.sum`, and converting local constancy to global constancy via connectedness, but it leans slightly high considering the "hard part" (the OMT) is already completely handed to you by the vendor file. A 4 is probably more accurate for 150 LOC of pure glue.

### 3. Proof Recipe & Logical Gaps
The overall strategy (local-constancy $\to$ global constancy $\to$ fiber sums $\to$ branch locus) is exactly right. However, **Step 6 contains a fatal point-set topology fallacy.**

You state: *"give every ramified point `p` an open neighborhood on which **no other** ramified point lies... the open cover thus produced, restricted to compact `X`, has a finite subcover."*
You cannot extract a finite subcover from an open cover of a *subset* $S \subset X$ simply because the superset $X$ is compact, unless you have already proven $S$ is closed. To invoke the compactness of $X$ directly, you must construct an open cover of **all of $X$**. 

To fix this gap: You must explicitly provide open neighborhoods for the *unramified* points (where $k=1$). At these points, the map is a local homeomorphism, so there exists a neighborhood where the derivative is non-zero (or you can just reuse `local_kfold_ramified_of_contMDiff` with $k=1$), meaning the neighborhood contains **zero** ramified points. Combine these with the neighborhoods of the ramified points to form a valid open cover of $X$. *Then* extract the finite subcover of $X$, and conclude that since each open set contains at most 1 ramified point, the total number of ramified points in $X$ is finite.

### 4. Textbook Citations
**Excellent.** Forster's Theorem 4.24 and Miranda's Ch. II §2 / §4.1 are the gold standard for this specific sequence of deductions. 

### 5. What's Missing or Wrong
*   **The topological gap in Step 6:** As detailed above, an open cover of the ramification locus does not magically inherit a finite subcover from $X$. You must cover the unramified points.
*   **Contradictory classification:** Labeling this `needs-infra` obfuscates the state of the project. It is a straight line of standard Mathlib tactics connecting two existing lemmas.
*   **Smoothness index coercion (`ω ≥ ⊤`):** Your escalation trigger correctly identifies the risk here. In Mathlib, generic topological or charted space variables `ω` do not automatically coerce to `⊤` (smooth) unless `ω` is constrained. If the axiom leaves `ω` completely unconstrained, `hf.of_le le_top` will fail to typecheck. If that happens, the axiom signature itself is too weak and needs `[Preorder ...] (hω : ⊤ ≤ ω)`.

### 6. Recommendation
**Revise.** The plan is 90% of the way there and correctly identifies the vendor tools, but you must fix the route classification back to `mathlib-now` and rewrite Step 6 to include the unramified points in the open cover argument.

VERDICT: revise — The route classification contradicts the text (should be mathlib-now) and Step 6 contains a fatal point-set topology error by failing to cover the unramified points of X before invoking compactness.
