# Gemini 3.1 Pro critique — `bridgePath_chart_differentiable`

**Model:** gemini-3.1-pro-preview
**Duration:** 58.6s
**Source axiom:** `Jacobians/Bridge/KirovLineIntegral.lean`
**Verdict:** **reject**

---

An expert review of your axiom-discharge plan for `bridgePath_chart_differentiable`.

### 1. Route classification
**Incorrect.** This is **`needs-infra`**, not `provable-from-other-axioms`. Mathlib does not have a differentiable path concatenation API. You will have to build the infrastructure to glue path segments with matching derivatives from scratch. 

### 2. Effort
**Wildly underestimated.** 5 (~1 day, 30–80 LOC) is fantasy. Defining a piecewise path, reparametrizing it to have zero derivatives at the joints, and manually pushing the limits through Lean's `HasFDerivAt.piecewise` or `DifferentiableAt` boundary logic will easily cost you **300–500 LOC** and several days. Effort is an **8**.

### 3. Proof recipe
There are massive logical gaps and outright hallucinations in the recipe:

* **Fake Mathlib Citation:** `Topology.MetricSpace.LipschitzAddSubgroup` does not exist in Mathlib. Neither does any general "path smoothing theorem." You cannot invoke magic topology infra that isn't there.
* **Mathematical Failure in Step 4 (Chart-overlap matching):** The recipe claims that if two adjacent affine segments share a chart source, "step 3 already covers it." **False.** A piecewise affine path has a corner at the joint. The left tangent vector and right tangent vector are different. It is strictly *not differentiable* at `t = tᵢ`. You cannot skip derivative-matching.
* **Wrong Tool in Step 4 (Smooth-bump):** The recipe proposes using `Mathlib`'s `ContDiffBump` to reparametrize the affine segments. `ContDiffBump` creates a bell-curve function (1 at the center, 0 outside). You do not want a bump; you want an **easing function**—an increasing bijection `[0, 1] → [0, 1]` with zero derivatives at the endpoints. A simple polynomial like `s(t) = 3t^2 - 2t^3` is `C¹` and perfectly sufficient, but you must build it yourself.
* **Field mismatch in Step 3:** The chart transition maps are complex-differentiable (since `X` is a complex manifold), but the axiom requires `DifferentiableAt ℝ`. You must explicitly apply `DifferentiableAt.restrict_scalars` (from ℂ to ℝ) when using the chain rule on the chart transitions.

### 4. Textbook citations
N/A, but the geometric topology folklore cited in the docstring is missing from Mathlib.

### 5. What's missing or wrong
* **Missing Easing Infra:** You need to explicitly define a polynomial easing function `ℝ → ℝ`, prove it maps `0 ↦ 0` and `1 ↦ 1`, and prove its derivative is `0` at both endpoints.
* **Missing Gluing Infra:** You must prove a lemma that if two differentiable paths meet at a point, and both have derivative `0` at that parameter time, their piecewise concatenation is differentiable there. This requires careful limit manipulation.
* **Delusional LOC estimate:** The recipe ignores the heavy Lean boilerplate required to prove differentiability of piecewise functions at boundary points. 

### 6. Recommendation
**Reject and revise.** 

**Alternative plan required:**
1. Change route to `needs-infra` and effort to 8.
2. Ditch the hallucinated Mathlib citations.
3. Explicitly state the need to build a polynomial easing function (e.g., `t ↦ 3t^2 - 2t^3`) to flatten the derivatives at the joints of the chart-lines.
4. Add a prerequisite step to build a "differentiable concatenation" lemma for paths with zero-derivative joints. 
5. Mention `DifferentiableAt.restrict_scalars` for the `ℂ → ℝ` transition in Step 3.

VERDICT: reject — The plan hallucinates non-existent Mathlib smoothing infrastructure and mathematically fails to recognize that concatenated affine pieces have non-differentiable corners.
