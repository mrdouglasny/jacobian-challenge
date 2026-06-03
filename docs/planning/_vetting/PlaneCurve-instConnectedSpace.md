# Gemini 3.1 Pro critique — `PlaneCurve-instConnectedSpace`

**Model:** gemini-3.1-pro-preview
**Duration:** 89.9s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **revise**

---

Here is a rigorous review of your axiom-discharge plan.

### 1. Route classification
**Correct.** `provable-from-other-axioms` is the right category. This is standard topology boilerplate deducing the connectedness of a projective variety from its affine chart.

### 2. Effort
**Calibrated (4).** The estimate of 2–3 days and ~50 LOC is accurate for the pushout topology boilerplate, provided the manifold/chart API for `PlaneCurve` is well-behaved.

### 3. Proof recipe & API accuracy
The high-level logic (image of connected is connected $\to$ dense implies closure is the whole space $\to$ closure of connected is connected) is mathematically valid. However, your tactic sketch hallucinates Mathlib API:
* `IsConnected` is a `Prop` (specifically, `Nonempty s ∧ IsPreconnected s`), not a set. You cannot call `hRange.closure.subset hUniv` or `.preconnectedSpace` on it. That is a pure type error.
* You do not need to manually apply `(isConnected_univ ...).image`. Mathlib has the exact lemma `isConnected_range`, which takes a `Continuous f` (and infers the `ConnectedSpace` domain).

The correct, fully working Mathlib 4 idiom is:
```lean
instance PlaneCurve.instConnectedSpace (H : PlaneCurveData) : ConnectedSpace (PlaneCurve H) := by
  have _hAff : ConnectedSpace (PlaneCurveAffine H) := AX_PlaneCurveAffine_connected H
  have hRange : IsConnected (Set.range (centralChart H)) := isConnected_range (centralChart_continuous H)
  have hDense : Dense (Set.range (centralChart H)) := centralChart_dense H
  have hUniv : IsConnected Set.univ := hDense.closure_eq ▸ hRange.closure
  exact isConnected_univ_iff.mp hUniv
```

### 4. Textbook citations
N/A. This is standard point-set topology.

### 5. What's missing or wrong (The "Not Polite" Section)
* **Bogus topological reasoning:** You claim: *"Density needs compactness of `PlaneCurve H` ... to get the closure right when the affine patch is noncompact"*. This is **geometrically and topologically false**. Compactness has absolutely zero logical relationship to the density of the affine patch. The affine patch is dense simply because it is the complement of a finite set of points in a complex manifold of dimension 1 (which has no isolated points). A cofinite set in $\mathbb{R}^2$ is dense regardless of whether the ambient space is compact.
* **Kicking the can / Better alternatives:** Pushing the work to `centralChart_dense` is an acceptable local helper, but formalizing that "cofinite sets in this specific charted space are dense" might be surprisingly tedious if the local manifold topology isn't deeply transparent to Lean. Your "Risk/escalation" fallback—covering the space with the three affine charts and showing they have nonempty pairwise intersections—is actually **much better and more standard**. If $U_x, U_y, U_z$ are connected (which they are) and pairwise intersect, their union is connected. Finding a single point in an overlap (e.g., $X \neq 0 \wedge Z \neq 0$) is an elementary algebraic evaluation, entirely bypassing the need to prove density or deal with closures.

### 6. Recommendation
**Revise.** Fix the hallucinated Lean 4 API in the tactic sketch, remove the mathematically false claim about compactness, and strongly consider promoting your "Risk" fallback (nonempty overlaps of open charts) to the primary strategy to avoid formalizing `centralChart_dense`. 

VERDICT: revise — The topological strategy is fundamentally sound, but the tactic sketch hallucinates Lean API for `IsConnected` and the mathematical justification for density incorrectly relies on compactness.
