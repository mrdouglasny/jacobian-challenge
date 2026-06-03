# Gemini 3.1 Pro critique — `affineLiftChart_compat_infinityLiftChart`

**Model:** gemini-3.1-pro-preview
**Duration:** 197.0s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean`
**Verdict:** **reject**

---

An evaluation of the proposed axiom-discharge plan for `affineLiftChart_compat_infinityLiftChart`:

### 1. Route Classification
**Incorrect.** The plan claims `provable-from-other-axioms` but justifies this by saying it is a "mechanical bundling of existing infrastructure." This is the exact definition of **`mathlib-now`** (or "project-now"). `provable-from-other-axioms` applies when a result is a direct logical corollary of another specific unproven axiom (e.g. deriving the symmetric statement from this one via `transition_fderiv_mul`), not when you're just chaining existing lemmas.

### 2. Effort Estimate
The estimate of **6** (~250–400 LOC) is reasonably calibrated for writing a 4-way sub-case transition. However, because the mathematical plan contains severe gaps (detailed below), you will likely discover that some required smoothness lemmas are missing from the project, which could bump the effort up to a 7. 

### 3. Proof Recipe
The proof recipe is mathematically incoherent. The author has completely swapped the roles of forward charts and inverse charts, rendering steps 3 and 4 mathematically fictional.

The transition `(affineLiftChart H a).symm.trans (infinityLiftChart H b)` as a function `ℂ → ℂ` evaluates precisely as $b \circ F \circ a^{-1}$ (where $F$ is `affineToInfinity`). Note the domains:
* $a^{-1}$ (`a.symm`) maps $\mathbb{C} \to \text{Curve}$. 
* $b$ (forward chart) maps $\text{Curve} \to \mathbb{C}$.

Let's look at the catastrophic errors in the recipe's treatment of these components:
* **The affine side ($a^{-1}$):** The recipe claims in Step 4 that `affineChartProjX.symm` is "just `Subtype.val.fst`... smoothness is `contDiff_fst.contDiffOn`". This is backward and fundamentally wrong. The *forward* chart `a` is `fst`. The *inverse* chart `a.symm` maps $x \mapsto (x, y(x))$. Its second component is the non-trivial algebraic branch function $y(x) = \sqrt{f(x)}$. You cannot dismiss `a.symm` as `fst`.
* **The infinity side ($b$):** The recipe claims that for (projX, projY), the infinity-side chart uses `polynomialLocalHomeomorph`. This is also backward. The infinity chart `b` is evaluated in the *forward* direction. The forward Y-chart is literally just `snd` ($(X,Y) \mapsto Y$). It does not use any local homeomorph/inverse machinery. The local homeomorph is only relevant for the *inverse* Y-chart, which is not evaluated here.

Because of these direction swaps, the case-by-case analysis misses the actual hard parts:
* **(projX, projY):** The transition is $x \mapsto y(x) / x^{d/2}$. The recipe falsely claims the infinity side uses `polynomialLocalHomeomorph_contDiffOn_symm`, while completely failing to address how to prove the smoothness of $x \mapsto y(x)$ on the affine side.
* **(projY, projY):** The transition is $y \mapsto y / x(y)^{d/2}$. The recipe claims *both* halves use `polynomialLocalHomeomorph_contDiffOn_symm`. In reality, only the affine side $a^{-1}$ uses it (to compute $y \mapsto x(y)$). The infinity side $b$ is just a simple evaluation of `snd`.

### 4. Textbook Citations
N/A. This is internal project infrastructure/API bundling. 

### 5. What's Missing or Wrong
Be specific:
1. **Fatal direction confusion:** You cannot use `contDiff_fst` to prove `affineChartProjX.symm` is smooth. You must deal with the explicit algebraic square root $y(x)$.
2. **Fabricated infinity-side complexity:** The forward infinity charts are simple `fst`/`snd` projections. Stop trying to shove `polynomialLocalHomeomorph_contDiffOn_symm` onto the target side. 
3. **Missing $x \mapsto y(x)$ lemma:** The recipe completely lacks a strategy to prove the $x \mapsto y(x)$ transition is `ContDiffOn ℂ ω`. You will either need to extract this from an existing intra-affine X-to-Y compatibility lemma or write a new one utilizing `contDiffOn_inverse` (or the implicit function theorem) on the local homeomorph. 

### 6. Recommendation
**Reject.** The proof plan requires a complete rewrite. The author must write down the explicit $\mathbb{C} \to \mathbb{C}$ transition formulas in the correct sequence ($x \mapsto 1/x$, $x \mapsto y(x)/x^{d/2}$, $y \mapsto 1/x(y)$, and $y \mapsto y/x(y)^{d/2}$) and accurately identify the existing project lemmas that prove the smoothness of $x \mapsto y(x)$ and $y \mapsto x(y)$. 

VERDICT: reject — The proof recipe fundamentally confuses forward and inverse charts, falsely claiming that non-trivial branch roots are trivial projections and that simple projections require local homeomorphism machinery.
