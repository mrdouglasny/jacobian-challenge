# Gemini 3.1 Pro critique — `PlaneCurve-instT2Space`

**Model:** gemini-3.1-pro-preview
**Duration:** 35.4s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **revise**

---

Here is a referee-level critique of the proposed axiom-discharge plan.

**1. Route classification**
The `needs-infra` classification is correct, as this fundamentally depends on how the `PlaneCurve H` type is defined. However, the scope of the required infrastructure is severely underestimated.

**2. Effort estimate**
The estimate of **Effort 2 (half a day, ~10 LOC)** is wildly optimistic. It relies heavily on Option C working out of the box. Because Option C is completely non-viable in Mathlib v4.30 (see below), you will be forced into manual topological gluing. Proving that a quotient of three affine charts is Hausdorff is at least an **Effort 5** task. 

**3. Proof recipe: logical gaps and hallucinations**
- **Option C is a phantom path.** The plan cites `Mathlib.Topology.Algebra.Projectivization` and hopes for a `t2Space` instance. This module **does not exist** in Mathlib v4.30. Mathlib has `LinearAlgebra.Projectivization.Basic` for the algebraic projective space, but it lacks the standard quotient topology over `ℂ` (let alone the proofs of compactness and Hausdorffness). Building the topological `ℙⁿ_ℂ` from scratch to enable Option C would be an Effort 7+ detour. 
- **Option B is conceptually flawed.** Mathlib's `TopologicalSpace.OpenCover` does *not* construct glued spaces; it is an API for evaluating an open cover of an *already existing* topological space. To build a space from charts, you have to use a quotient type or `TopologicalSpace.Glue`. 
- **Option A is the only viable path**, but the recipe waves its hands over the hardest part. You cannot simply invoke a generalized `T2Space.quotient_of_isClosedMap` without doing the hard analytical work. The gluing relation's graph being closed implies you need to prove that the transition functions (e.g., $(x,y) \mapsto (1/x, y/x^d)$) are continuous and separate points that do not map to each other. 

**4. Textbook citations**
Hartshorne I.2 and Beauville are mathematically correct, but they sweep the exact point-set topology under the rug. You need a reference for the topological fact that gluing T2 spaces along open subsets via homeomorphisms with closed graphs yields a T2 space.

**5. What's missing or wrong**
- **No topological `ℙ²_ℂ`:** The plan acts as though `ℙ²_ℂ` is available as a topological space in Mathlib v4.30. It isn't. The fallback ("open-cover-of-`ℙ²` argument separates them") is therefore circular: you cannot use disjoint neighborhoods in `ℙ²` if you haven't built `ℙ²`!
- **Concrete chart separation:** If you glue the curve directly from 3 affine charts (Option A), you must explicitly prove separation using the charts themselves. For two points in different charts, you have to construct disjoint neighborhoods pulling back through the transition polynomials. The plan lacks this explicit fallback.

**6. Recommendation**
**Revise.** You must discard Option C entirely unless the project intends to build the entire topological API for complex projectivization. Commit to Option A (the 3-chart pushout), upgrade the effort to at least 5, and sketch the actual explicit separation argument using the transition functions between the affine charts.

VERDICT: revise — Option C relies on a non-existent Mathlib topology for `Projectivization` in v4.30, forcing you to use the chart-gluing route which is significantly harder than Effort 2.
