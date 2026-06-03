# Gemini 3.1 Pro critique — `infinityChart`

**Model:** gemini-3.1-pro-preview
**Duration:** 88.2s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean`
**Verdict:** **revise**

---

Here is a rigorous referee critique of the proposed axiom-discharge plan for `infinityChart`.

### 1. Route classification
The route **provable-from-other-axioms** is acceptable here since the heavy analytic machinery (the local uniformizer and its series) is sequestered inside the `infinityInverseMap` axiom, and this task is purely about assembling that data into Mathlib's topological chart structure. However, given the heavy topological filter work required (see below), this touches closely on **genuine-textbook**.

### 2. Effort
**The effort is drastically underestimated.** An effort of 3 and ~3–5 days is completely uncalibrated for what Step 5b actually requires. You are mapping analytic asymptotics at infinity through Lean’s filter system (`Filter.cocompact`). Proving that limits as $p \to \infty$ in the one-point compactification correspond to limits where $x \to \infty$ algebraically, and then proving the polynomial limit $|y| / |x|^{g+1} \to 0$, will take significant filter and polynomial-bound manipulation. Bump this to **Effort: 6 or 7** (~300–500 LOC). 

### 3. Proof recipe
There are **two fatal logical flaws** and one missing piece in the recipe:

* **FATAL FLAW (Junk Values in Step 3):** Your "more cleanly" formulation of `source` is critically broken. Lean handles division by zero by returning `0`. If $f(0) \neq 0$, the affine point $p = (0, \sqrt{f(0)})$ on the curve evaluates to $y / 0 = 0$ under `infinityForward`. Because $0$ is in your target `Metric.ball 0 r`, this point $p$ is accidentally included in your `source`. But $y/x^{g+1} \to \infty$ as $x \to 0$, meaning the function is strictly discontinuous there, and your `continuousOn_toFun` proof in Step 7 will irrevocably fail. 
  **Fix:** You must explicitly exclude the $x = 0$ locus from the domain. Define `source := (infinityForward H h) ⁻¹' target ∩ {p | p = ∞ ∨ p.val.1 ≠ 0}`. This works perfectly: its complement is the finite (hence closed) set of affine points where $x=0$, meaning `{p | p = ∞ ∨ p.val.1 ≠ 0}` is open, and `infinityForward` is genuinely continuous there.
* **FATAL FLAW (Circular reasoning in Step 5b):** You state you can prove continuity of `infinityForward` at $\infty$ by citing that it "agrees with the inverse of `infinityInverseMap` on the punctured disk". This is circular. You do not yet know that the image of the disk under the inverse map actually covers a punctured neighborhood of $\infty$ in the topology of the curve—that is exactly what proving continuity at $\infty$ establishes!
  **Fix:** You must prove the limit `Tendsto (fun p => p.y / p.x^(g+1)) (cocompact X) (𝓝 0)` algebraically. You must formalize that if $p = (x,y)$ leaves compact sets in the curve $y^2 = f(x)$, then $x \to \infty$ in $\mathbb{C}$, and thus $|y / x^{g+1}|^2 \sim |f(x)| / |x|^{2g+2} \to 0$ because $\deg f = 2g+1 < 2g+2$.
* **Missing element:** Step 7 references `continuousOn_invFun`, but the recipe never explicitly defines the Lean function for the inverse. You need an explicit `noncomputable def infinityBackward` using `if t = 0 then ∞ else ...`.

### 4. Textbook citations
The references to Miranda §III.1 and Forster §1.1–1.2 are exactly correct for this construction.

### 5. What's missing or wrong
* **The `source` definition is wrong:** It will accidentally swallow affine points where $x=0$ due to Lean's `x / 0 = 0` convention, destroying continuity.
* **The continuity proof at $\infty$ is circular:** You cannot rely on the inverse map to prove the topological limit; it must be done via `Filter.cocompact X` and polynomial degree bounds. 
* **The inverse function definition is missing** from the recipe blocks.
* **The effort is uncalibrated** for the sheer amount of boilerplate required for limits at infinity.

### 6. Recommendation
**Revise**. Rewrite Step 3 to explicitly exclude $x=0$ from the source intersection, update Step 5b to mandate an algebraic `cocompact` filter proof without citing the inverse map, add the explicit definition of the inverse function, and double the effort estimate.

VERDICT: revise — The source definition accidentally swallows singularities due to Lean's division-by-zero junk values, and the continuity proof at infinity relies on circular reasoning.
