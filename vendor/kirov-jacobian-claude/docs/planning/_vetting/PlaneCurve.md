# Gemini 3.1 Pro critique — `PlaneCurve`

**Model:** gemini-3.1-pro-preview
**Duration:** 54.0s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **revise**

---

Here is a rigorous critique of the proposed discharge plan:

1. **Route classification**: **Incorrect**. If you use Option C (which you absolutely must), this axiom is just a type definition via a subtype. The route is **mathlib-now**, not `needs-infra`. The heavy infrastructure (the 600 LOC atlas construction) is required for the *manifold structure* (`instChartedSpace` and `instIsManifold`), not for the `Type` axiom.
2. **Effort 1..10**: **Vastly overestimated**. Defining a subtype takes 5 minutes. The effort for *this specific axiom* is **1**, not 8.
3. **Proof recipe**:
   - **Mandatory Option C**: Options A and B (defining a projective curve via an abstract gluing of affine charts) are formalization suicide. This completely severs the curve from the ambient space `ℙ²`, which will make classical intersection theory and Bézout's Theorem (which the project explicitly references) artificially difficult or impossible. Option C (a subvariety of `ℙ²`) is the *only* mathematically sane choice for plane curves. 
   - **Syntax Error**: Your proposed Lean 4 definition for Option C is syntactically invalid. You wrote `Projectivization.mk ℂ v (by simp [v])` following an unnamed `v ≠ 0` implication. A tactic block cannot magically extract the antecedent of an implication. You must explicitly bind the hypothesis: `∀ (v : Fin 3 → ℂ) (hv : v ≠ 0), Projectivization.mk ℂ v hv = p → ...`.
   - **Clunky API**: Do not use the `∀ v, ...` encoding to define the zero locus on projective space. Mathlib's `Projectivization` API provides a representative function (`Projectivization.rep p`). The condition should simply be `MvPolynomial.eval p.rep H.F.val = 0`. The homogeneity of `F` ensures this is well-defined independent of the representative.
   - **Misplaced scope**: Steps 1 and 2 (affine charts and transitions) are completely irrelevant to discharging the `PlaneCurve : Type` axiom. They should be excised from this recipe and moved to the plan for `PlaneCurve.instChartedSpace`.
4. **Textbook citations**: Hartshorne and Beauville are conceptually fine for the atlas, but overkill here. You are just defining a set in `ℙ²`. 
5. **What's missing or wrong**: The plan conflates the definition of the underlying space (`Type`) with the definition of its manifold structure (`ChartedSpace`). By failing to separate these concerns, the recipe attempts to front-load 4–6 weeks of work onto a 3-line definition.

VERDICT: revise — Adopt Option C exclusively, fix the invalid Lean 4 syntax by using `Projectivization.rep`, and remove the 600-LOC atlas construction (Steps 1-2) which belongs in the downstream manifold axioms, dropping the effort to 1.
