# Gemini 3.1 Pro critique — `AX_HyperellipticAffine_connected`

**Model:** gemini-3.1-pro-preview
**Duration:** 133.1s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic/Basic.lean`
**Verdict:** **reject**

---

Here is a referee-level critique of the proposed discharge plan for `AX_HyperellipticAffine_connected`.

### 1. Route Classification
**Correct as `needs-infra`**. While conceptually a "genuine-textbook" result (Riemann surfaces), your approach correctly identifies that building the algebraic geometry bridge ("irreducible variety over $\mathbb{C}$ implies connected in classical topology") requires missing Mathlib infrastructure. Proceeding via point-set topology and covering spaces is the right call for Lean 4 right now.

### 2. Effort Estimate
**Underestimated (closer to 8 than 6)**. Even with the simplifications below, formalizing path lifting on half-open intervals, gluing paths at limits, and managing the topology of $\mathbb{C} \times \mathbb{C}$ is highly non-trivial. It will take more than ~30 lines of discharge and an 80 LOC helper file.

### 3. Proof Recipe (Logical Gaps & Flaws)
The proposed recipe contains a **fatal mathematical flaw** in Sub-step 3a and a **massive overcomplication** in Sub-step 3b.
*   **Gap in Sub-step 3a:** You cannot just compose an arbitrary path with `Complex.sqrt`. Mathlib's `Complex.sqrt` has a fixed branch cut along the negative real axis. As your path $f(\alpha(t))$ winds through $\mathbb{C} \setminus \{0\}$ to avoid roots, it will inevitably cross this cut, making your proposed lift strictly discontinuous. You cannot "holomorphically continue" by hand without building analytic continuation infrastructure. 
*   **Overcomplication in Sub-step 3b:** You absolutely do not need the Implicit Function Theorem, local charts, or smooth manifolds to "switch sheets" at a branch point. The topological fiber $\pi^{-1}(a)$ over a root $a$ is the single point $(a,0)$. Because the curve is defined by $y^2 = f(x)$, if a path in the base $x(t) \to a$, then $y(t)^2 \to 0$, which forces $y(t) \to 0$. Any continuous lift over the punctured path *automatically* converges to $(a,0)$. The "sheet switch" is a trivial topological consequence of subspace convergence in $\mathbb{C}^2$, not a differential property.

### 4. Textbook Citations
**Appropriate.** Forster §1 is standard for the topological construction of Riemann surfaces. However, your execution of the topological recipe diverges from standard texts by trying to force a static branch cut (`Complex.sqrt`) to do the job of a universal cover.

### 5. What's Missing or Wrong
*   **Broken continuity claim:** `Continuous (Complex.sqrt ∘ f ∘ α)` is mathematically false for arbitrary paths avoiding $R$.
*   **False dependency:** By using IFT to construct a chart at the branch point, you needlessly entangle this purely topological connectedness proof with the differential topology roadmap (the `ContDiffAt` and `squareLocalHomeomorph` blockers).
*   **Missing covering space machinery:** The plan completely ignores Mathlib's existing `IsCoveringMap` API, which is designed exactly to solve the monodromy/path-lifting problem you are trying to hand-roll.

### 6. Recommendation
**Reject and revise.** The `Complex.sqrt` approach will fail to typecheck/prove, and the IFT approach is a boondoggle. 

**Alternative Recipe (to include in revision):**
1.  **For Sub-step 3a:** Pick a path $x(t)$ in $\mathbb{C}$ from your starting point to a root $a$, such that $f(x(t)) \neq 0$ for $t < 1$. To lift the unbranched portion $t \in [0, 1)$, map it through $f$ to get a path in $\mathbb{C}^\times$. Lift this path to the universal cover (the log plane) using Mathlib's `Complex.isCoveringMap_exp` and `IsCoveringMap.exists_path_lift` (taking exhaustion limits for the half-open interval). Define your continuous square root as $\exp(\text{lift}(t) / 2)$.
2.  **For Sub-step 3b:** Delete the IFT argument entirely. Define the path value at $t=1$ to be $(a,0)$. Prove continuity at $t=1$ purely from the ambient topology: since $x(t) \to a$, $y(t)^2 = f(x(t)) \to 0$, hence $y(t) \to 0$. 
3.  This completely decouples the axiom from the `OddAtlas` escalation risks.

VERDICT: reject — The plan relies on a mathematically false continuity claim for `Complex.sqrt` along arbitrary paths and needlessly entangles a purely topological limit with Implicit Function Theorem chart machinery.
