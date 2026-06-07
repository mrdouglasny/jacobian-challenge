# Gemini 3.1 Pro critique — `affineLiftProjY_compat_infinityChart`

**Model:** gemini-3.1-pro-preview
**Duration:** 105.9s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean`
**Verdict:** **revise**

---

Here is a referee-level critique of the proposed axiom-discharge plan. 

### 1. Route Classification
**Correct.** The route `provable-from-other-axioms` is accurate because the target of this transition map (`infinityChart H h`) is itself an axiom/pending deliverable in the project. The proof is a structurally standard, albeit topologically delicate, chain rule application that is blocked only by the infinity API.

### 2. Effort Estimation
**Calibrated.** An effort of 3 (~3–5 days, ~150 LOC) is realistic. The pure calculus (chain rule for polynomials and division) is mechanically straightforward in Mathlib, but wrestling with chart source restrictions and `ContDiffOn.congr` to satisfy the manifold library will take up the bulk of the time.

### 3. Proof Recipe & Logical Gaps
The calculus core of your recipe (Steps 2 & 4) is mathematically correct and leverages standard Mathlib `ContDiffOn` composition patterns flawlessly. However, **Step 3 (Source analysis) contains a critical logical gap regarding injectivity.**

You claim that condition (c) — the transition value $y / x(y)^{g+1}$ landing in the target `Metric.ball 0 R` — automatically excludes the branch point $y = 0$. 
*   **The flaw:** This is only true if $a = 0$ (where the formula hits a pole or $0/0$). What if $a \neq 0$? At a branch point $p = (a, 0)$ with $a \neq 0$, we have $x(0) = a$. Your transition formula evaluates to $0 / a^{g+1} = 0$. Since $0$ is the exact center of the target metric ball, condition (c) is perfectly **satisfied**!
*   If your transition source were defined merely as the preimage of the target ball, your map would incorrectly swallow the finite branch point $(a,0)$ and fail to be injective (mapping both $\infty$ and $(a,0)$ to $0$).
*   **The fix:** You cannot rely on the complex target ball to exclude $y=0$. Your proof *must* use the actual manifold-level `.source` restriction of `infinityChart` (which will geometrically restrict the affine patch to something like $|x| > R > |a|$ for all roots $a$). This manifold source condition is what strictly bounds $x(y)$ away from zero and formally excludes all finite branch points. 

### 4. Textbook Citations
The citations are completely appropriate. The standard affine-to-infinity change of coordinates for hyperelliptic curves of odd degree is indeed $y' = y / x^{g+1}$, and your Mathlib pointers (`ContDiffOn.comp`, `ContDiffOn.inv`) are spot on.

### 5. What's Missing or Wrong
*   **Source vs. Target Conflation in Step 3:** You state `(infinityChart H h).source ⊂ Metric.ball 0...`. You mean `.target`. In Mathlib's `PartialHomeomorph` / manifold library, `.source` is a subset of the domain (the manifold) and `.target` is a subset of the codomain ($\mathbb{C}$).
*   **The $a \neq 0$ Blindspot:** As detailed above, the target ball condition does *not* exclude $y=0$ when $a \neq 0$. You must extract $x(y) \neq 0$ from the geometric `infinityChart.source` property on the curve, not from the complex explicit formula. 
*   **Lean's Division by Zero:** In your Risk section, you claim "the division is undefined". In Lean, $z / 0 = 0$. It is mathematically undefined, but Lean evaluates it to $0$, which is exactly why the $a \neq 0$ blindspot is so dangerous (it evaluates to $0$ and lands in the ball!). You avoid this trap via `ContDiffOn`, which rightly fails at poles. 
*   **Hallucinated Mathlib Namespace:** You cite `OpenPartialHomeomorph.lift_openEmbedding_apply` as a Mathlib theorem. There is no `OpenPartialHomeomorph` in Mathlib (the type is exactly `PartialHomeomorph`, or `LocalHomeomorph` in older versions). However, because `.lift_openEmbedding` is used via dot-notation in the verbatim axiom statement, the lemma you need clearly exists in the project namespace.

### 6. Recommendation
**Revise.** The calculus assembly is well-planned, but the topological source analysis in Step 3 must be rewritten. Do not rely on the non-injective complex target formula to rule out branch points; explicitly state that the proof will leverage the geometric manifold `.source` of `infinityChart` to guarantee $x(y)$ is bounded away from zero. 

VERDICT: revise — The calculus chain rule strategy is solid, but the source analysis in Step 3 contains a critical logical gap because the explicit formula evaluates to 0 at branch points where a ≠ 0, meaning you must rely on the manifold-level source of the infinity chart rather than the target ball to exclude these points.
