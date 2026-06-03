# Gemini 3.1 Pro critique — `AX_PlaneCurveAffine_noncompact`

**Model:** gemini-3.1-pro-preview
**Duration:** 100.3s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed discharge plan.

### 1. Route Classification
The classification "provable-from-other-axioms" is nominally true because you lean heavily on `AX_PlaneCurveAffine_nonempty`, but in reality, this is **needs-infra**. You are assuming drop-in API exists for treating an arbitrary 2-variable `MvPolynomial` as a 1-variable polynomial over a polynomial ring, extracting its leading coefficient, and showing it evaluates sensibly. Mathlib's `MvPolynomial` API is famously clunky for this; it is not a turnkey operation. 

### 2. Effort 1..10
Your estimate of **2** (~half a day, ~40 LOC) is a pipe dream. The actual effort is an **8**. 
The hyperelliptic case was a 2 because the polynomial is strictly of the form $Y^2 - f(X)$; the degree in $Y$ is manifestly 2, and the leading coefficient is manifestly 1. For a general plane curve, you will have to wrestle with `MvPolynomial.optionEquivRight` (or similar) to extract leading coefficients and bounds, which will easily consume 200+ LOC of tedious algebra.

### 3. Proof Recipe
- **Fatal Logical Flaw in Sub-step 2:** Your claim that the $X$-projection $\pi$ always has a cofinite image (unless $F$ is a pure power of $Y$) is **mathematically false**. Consider the smooth plane curve $F = X$ (a vertical line in the affine patch). Here, $F(X,Y,1) = X$, meaning the univariate polynomial $F_x(Y) = x$. For any $x \neq 0$, this is a non-zero constant, which has **zero** roots. The image of the $X$-projection is exactly $\{0\}$. This is bounded and finite, *not* cofinite.
- **The required fix:** You cannot rely solely on the $X$-projection. Because $F(X,Y,1)$ is not a constant (guaranteed by the nonempty axiom), it must have positive degree in *at least one* of $X$ or $Y$. If it has positive degree in $Y$, the leading coefficient in $X$ has finitely many roots, and the $X$-projection has a cofinite (hence unbounded) image. If it has positive degree in $X$, the *Y*-projection has a cofinite image. You must prove that at least one projection is unbounded.
- **The "Shortcut Alternative" is nonsense:** Scaling coordinates by $t$ does not magically bypass degree-counting. $F(tx_0, y, 1) = 0$ is just another polynomial; to know it actually has a root $y$ as $t \to \infty$, you are right back to needing the leading coefficient of $Y$ to not vanish, which is exactly the degree argument you are trying to avoid.

### 4. Textbook Citations
The references to Hartshorne and Beauville are correct for the high-level algebraic geometry fact, but they provide zero help for the elementary complex polynomial bashing proposed in the recipe. 

### 5. What's Missing or Wrong
- **The $F=Z$ edgecase makes the axiom FALSE as stated:** A major omission in your domain knowledge. If $F = Z$ (which is a perfectly valid smooth plane curve of degree 1), its affine patch is the set of points where $1 = 0$. This is the empty set. The empty space **is compact**. Therefore, `NoncompactSpace` is mathematically false for $F=Z$. The only thing saving this formalization from inconsistency is that `AX_PlaneCurveAffine_nonempty` handwaves away the $F=Z$ case by asserting the patch is nonempty. You must acknowledge that the nonempty axiom is structurally load-bearing here to rule out the line at infinity.
- **Missing API bridging:** You completely handwave the jump from `MvPolynomial (Fin 3) ℂ` to `Polynomial ℂ`. Evaluating a 3-variable homogeneous polynomial at $Z=1$, then factoring it as a univariate polynomial in $Y$ whose coefficients are polynomials in $X$, requires significant boilerplate that does not yet exist in this project.

### 6. Recommendation
**Reject.** The proof recipe is mathematically broken for vertical lines (where the $X$-projection is just a point), the "shortcut" is invalid, and the effort estimate is detached from the reality of Mathlib's `MvPolynomial` API. 

Revise the plan to:
1. Symmetrize the argument to show that *either* the $X$-projection *or* the $Y$-projection has a cofinite image.
2. Upgrade the effort to an 8 and explicitly plan for building the `MvPolynomial` -> `Polynomial (Polynomial ℂ)` bridge infrastructure.

VERDICT: reject — The proof recipe's projection argument fails mathematically for vertical curves (where the X-projection image is a single point, not cofinite), and the effort is drastically underestimated due to the heavy `MvPolynomial` infrastructure needed.
