# Gemini 3.1 Pro critique — `AX_Elliptic_aLoop_analytic`

**Model:** gemini-3.1-pro-preview
**Duration:** 80.5s
**Source axiom:** `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean`
**Verdict:** **revise**

---

An excellent, thorough plan that correctly identifies the geometric triviality of the A-cycle and properly anticipates the exact Mathlib / API bottlenecks. However, a few structural and tactical details need correction before execution.

Here is the critique:

1. **Route classification**: **Wrong.** You classified this as `provable-from-other-axioms`, but in the "Blocked by" section you explicitly note that all cited helpers are already *real theorems*. If it does not depend on any remaining `axiom` declarations in the project, the route is `mathlib-now`.

2. **Effort**: **3** is well calibrated. The underlying math is trivial, but wrangling manifold charts, limits, and quotient topologies in Lean easily takes 60–100 LOC of boilerplate. 

3. **Proof recipe & Logical gaps**:
   - **Step 1 (Partition unpacking)**: You restrict to `u ∈ Set.Ioo (0:ℝ) 1`. Depending on the exact project definition of `IsAnalyticArc`, analyticity is usually required on an open neighborhood of the *closed* interval `[0, 1]` (or right/left analyticity at the endpoints). Because `aLoopExtend` is analytic on **all** of `ℝ`, do not artificially restrict to the open interval. Just prove `AnalyticAt ℝ f u` for an arbitrary `u : ℝ`; it will trivially satisfy whatever boundary conditions `IsAnalyticArc` demands.
   - **Step 5 (Analyticity lemmas)**: `Complex.analyticAt_ofReal` is a hallucination. The map `r ↦ (r : ℂ) * ω₁` is the application of a continuous `ℝ`-linear map `r ↦ r • ω₁`. As you correctly identified in your risk section, `ContinuousLinearMap.analyticAt` is the actual Mathlib way to prove this. Promote your fallback to the primary path. 
   - **Step 4 & Risk (Private helpers)**: You noted that `chartTarget`, `liftPoint`, etc., are `private` in `ComplexTorus.lean`. Do not try to hack around this or leave it as an "optional" fallback. **Mandate** the addition of a `public` (or `protected`) wrapper lemma in `ComplexTorus.lean` (e.g., `extChartAt_eq_sub_lift_lattice_offset`) that packages the local affine behavior. Refactoring privacy modifiers of internal construction details usually breaks encapsulation; providing a clean public API for the chart formula is the correct architectural choice.

4. **Textbook citations**: N/A, this is a standard manifold chart verification.

5. **What's missing or wrong**:
   - Route must be `mathlib-now`.
   - Hallucinated `Complex.analyticAt_ofReal` in Step 5 (use `ContinuousLinearMap.analyticAt`).
   - Unnecessary restriction to `Ioo (0:ℝ) 1` in Step 1.
   - The "optional" mitigation for `private` declarations must be a hard requirement.

6. **Recommendation**: Revise. Update the route, clean up the Step 5 analyticity proof to use continuous linear maps natively, generalize Step 1 to all `u : ℝ`, and explicitly require the addition of a public chart lemma in `ComplexTorus.lean`.

VERDICT: revise — Change route to `mathlib-now`, promote the `ContinuousLinearMap` analyticity fallback to the primary path, and mandate the public wrapper lemma for chart privacy.
