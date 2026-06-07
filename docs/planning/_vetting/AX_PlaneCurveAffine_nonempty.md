> **✅ DISCHARGED — 2026-06-07 (PR #92).** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# Gemini 3.1 Pro critique — `AX_PlaneCurveAffine_nonempty`

**Model:** gemini-3.1-pro-preview
**Duration:** 102.1s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed discharge plan for `AX_PlaneCurveAffine_nonempty`.

1. **Route classification**: Incorrect. The route cannot be `mathlib-now` because **the axiom as stated is mathematically false** (see below). Once the axiom statement is corrected, `mathlib-now` will be the right classification.

2. **Effort 1..10**: 4 is reasonable for a corrected theorem, but currently 0, since you cannot prove a false statement.

3. **Proof recipe**: The plan is filled with fatal logical gaps and hides a glaring counterexample.
   * **Fatal Gap 1 (Covers up the counterexample)**: In Sub-step 1 Case B, you assert that if $F = zF'$, then $F'(x,y,0) = 0$ has a root "directly by FTA when $d = 1$". If $d=1$, $F'$ has degree 0. **A non-zero constant polynomial has no roots.** You cannot invoke the Fundamental Theorem of Algebra on a degree 0 polynomial.
   * **Fatal Gap 2 (Degree 0 failure)**: In Sub-step 1 Case A, you assume `Complex.exists_root` applies as long as $G \neq 0$. You completely forgot that if $G$ is a non-zero constant (e.g., $G = c$), it has degree 0 and no roots. This corresponds to the curve $F = c z^d$. You must explicitly prove that $F=cz^d$ is singular for $d \ge 2$ to rule out $G$ being a constant.
   * **Fatal Gap 3 (Variable selection)**: In Sub-step 1 Case A, you lazily assume there exists $y_0$ such that $G(x, y_0)$ has positive degree in $x$. If $G$ only depends on $y$ (e.g., $G(x,y) = y - 1$), evaluating at *any* $y_0$ yields a constant polynomial in $x$. To fix this, you must explicitly pick a variable that has a positive degree in $G$, say $y$, write $G(x,y) = \sum_{i=0}^k P_i(x) y^i$, pick an $x_0$ such that the leading coefficient $P_k(x_0) \neq 0$, and *then* apply FTA to $G(x_0, y)$. 

4. **Textbook citations**: Hartshorne I.2 and Beauville are conceptually correct, but standard textbooks implicitly assume you are working with an affine patch that actually intersects the curve (i.e., the curve is not the hyperplane at infinity). Lean will not make this assumption for you.

5. **What's missing or wrong**:
   * **THE AXIOM IS DEAD WRONG.** The polynomial $F(x,y,z) = z$ gives a valid smooth plane curve of degree $d = 1$ (the gradient is $(0,0,1)$ everywhere, which is never zero). Its affine patch on $z=1$ is exactly the locus $\{ (x,y) \mid 1 = 0 \}$, which is **completely empty**. Thus, `Nonempty (PlaneCurveAffine H)` is false. You are trying to prove that the line at infinity has points in the finite plane. Leaving this axiom as an `instance` introduces a logical inconsistency into the codebase. 

6. **Recommendation**: Reject. The axiom is mathematically false. You must weaken the axiom to require `2 ≤ d` (or $F \notin (Z)$), propagate this change to downstream consumers like `PlaneCurve.instNonempty`, and rewrite the proof recipe to handle the constant $G$ case and correct variable selection.

VERDICT: reject — The axiom is mathematically false for $d=1$ (the smooth curve $F=z$ has an empty affine patch), so you must change the axiom to require $d \ge 2$ and fix the proof's false claims about polynomial degrees.
