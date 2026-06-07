# Gemini 3.1 Pro critique — `AX_ofCurve_contMDiff`

**Model:** gemini-3.1-pro-preview
**Duration:** 55.8s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **revise**

---

An evaluation of your axiom-discharge plan for `AX_ofCurve_contMDiff`:

1. **Route classification**: **Correct.** `provable-from-other-axioms` is exactly right. The smoothness of the Abel-Jacobi map is a direct consequence of the Fundamental Theorem of Calculus applied to the path integrals of holomorphic forms, which is encapsulated in `AX_pathIntegral_local_antiderivative`.

2. **Effort estimate**: **Optimistic (5 → 6 or 7).** The 150–250 LOC estimate is likely too low unless the project already contains extremely robust bridge lemmas for `ContMDiff ... ω` (analytic smoothness). Moving from `HasDerivAt` everywhere to `AnalyticOn` to `ContMDiff` with index `ω` across a manifold chart will require painful chart-domain bookkeeping. 

3. **Proof recipe & Logical gaps**:
   There are two major, embarrassing mathematical errors in your recipe:
   * **The Quotient Map is NOT linear:** In Step 2, you claim `QuotientAddGroup.mk'` is "continuous + linear, automatically smooth". **This is categorically false.** The codomain is the Jacobian, which is a complex torus (`ℂ^g / Λ`), *not* a vector space. A map to a torus cannot be "linear". The quotient map is smooth because it is a local diffeomorphism / covering map of Lie groups, not because of topological vector space linearity. You cannot rely on automatic linearity tactics here; you must use the specific Lie group quotient manifold lemma (likely `contMDiff_quotient_mk` from Mathlib or the project's Jacobian construction).
   * **Misunderstanding the FTC Basepoint:** In Step 5a, you state: *"the axiom is universal in the chart centre P, so by translating P to nearby points we get HasDerivAt everywhere"*. **Absolutely not.** In the Abel-Jacobi map `ofCurveImpl X P₀ Q`, the basepoint `P₀` is **globally fixed**. You do not, and cannot, "translate" it to get derivatives. The FTC axiom `AX_pathIntegral_local_antiderivative` states that the derivative with respect to the *upper limit* `Q` is `ω(Q)`. To get differentiability on the chart, you simply leave `P₀` fixed and evaluate the FTC axiom at varying upper endpoints `Q'` inside the chart neighborhood. 

4. **Textbook citations**: Mumford and Griffiths-Harris are the correct gold-standard references here.

5. **What's missing or wrong**:
   * **Subtraction order in Tactic Sketch:** Your tactic sketch says `apply ContMDiff.sub _ contMDiff_const`. The subtraction `ofCurveAmbient X P Q - ofCurveAmbient X P P` happens in the vector space `Fin (genus X) → ℂ` *before* the quotient map. Your tactic order correctly reflects this (`Quotient.mk.comp (sub)`), but be careful that you apply the vector space subtraction lemma, not a Lie group subtraction lemma.
   * **Analytic Smoothness (`ω`):** The index `ω` in `ContMDiff` means *real/complex analytic*. Your identification of `Complex.analyticOn_of_differentiableOn` is spot-on for bridging 1D complex differentiability to analyticity. However, be prepared to write a custom bridging lemma if Mathlib lacks the exact `contMDiffAt_iff_analyticAt_extChart` theorem for index `ω` on 1D complex manifolds.

6. **Recommendation**: **Revise.** Fix the justification for the quotient map's smoothness (it is a Lie group covering, not linear) and correct the fundamental misunderstanding of the FTC application (vary the upper limit `Q`, do not "translate" the fixed basepoint `P₀`).

VERDICT: revise — The plan correctly routes the proof through the FTC axiom, but must be revised to fix severe mathematical misconceptions about the linearity of the torus quotient map and the role of the fixed basepoint in the FTC step.
