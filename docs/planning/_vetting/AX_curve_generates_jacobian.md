# Gemini 3.1 Pro critique — `AX_curve_generates_jacobian`

**Model:** gemini-3.1-pro-preview
**Duration:** 30.6s
**Source axiom:** `Jacobians/Axioms/UniversalProperty.lean`
**Verdict:** **reject**

---

Here is a rigorous referee critique of the proposed axiom-discharge plan:

1. **Route classification**
   **Wrong.** The plan classifies this as `genuine-textbook`, but steps 2 and 3 explicitly invoke `AX_RiemannRoch`, `AX_SerreDuality`, and `AX_AbelTheorem`. If your proof strategy is to reduce the target axiom to *other* standalone axioms in the project, the route is by definition `provable-from-other-axioms`. 

2. **Effort estimate**
   **Wildly overestimated.** You estimated an Effort 8 (6–8 weeks, 600–900 LOC). But since you are assuming the heavy lifting is done by `AX_RiemannRoch` and `AX_AbelTheorem`, the actual proof is just trivial arithmetic ($h^0(E) - h^1(E) = g + 1 - g = 1 \implies h^0(E) \ge 1$) followed by divisor manipulation. This is an Effort 3 task (~1–2 weeks, ~150 LOC). You are budgeting for a from-scratch textbook proof while simultaneously wielding a Riemann-Roch sledgehammer.

3. **Proof recipe**
   - **Step 3 (Serre Duality) is useless fluff.** You admit it is "not strictly needed for the surjectivity claim", so why is it here? To prove that `range ofCurve` *generates* the Jacobian, you only need to show that every element can be written as a sum of points. The uniqueness/genericity of the effective divisor is entirely irrelevant to `AddSubgroup.closure = ⊤`. Drop Step 3 completely.
   - **Step 2 has a major logical gap.** You write: "`h⁰(O(E)) ≥ 1`. Hence `|E|` is non-empty: there exists an effective divisor `E' ≥ 0` linearly equivalent to `E`." Mathematically standard, but formally, this is the hardest missing piece of the proof. You need the explicit bijection between non-zero global sections of $O(E)$ and effective divisors $E' \sim E$. Your "Next discrete deliverable" and "Files touched" completely ignore the infrastructure needed to define the divisor of a section and prove this correspondence.
   - **Minor observation on Genus 0:** The axiom requires `0 < genus X`. If `genus X = 0`, the Jacobian is the trivial group, `ofCurve x₀` maps to zero, and the subgroup generated is `⊤` trivially. The hypothesis `0 < genus X` is actually unnecessary for the statement to be true (though it avoids a triviality). 

4. **Textbook citations**
   The references (Mumford, ACGH) are standard and correct for Jacobi Inversion, though deriving Inversion as a corollary of Riemann-Roch is standard fare in almost any algebraic curves text (e.g., Miranda's *Algebraic Curves and Riemann Surfaces*).

5. **What's missing or wrong**
   - The route must be changed to `provable-from-other-axioms`.
   - The effort estimate must be revised down to ~3, as the plan delegates the deep math to other axioms.
   - Step 3 must be deleted.
   - The plan lacks the required API design to transition from $H^0(X, O(E)) \neq 0$ to the existence of an effective $E' \sim E$. You must explicitly plan for the `Section -> Divisor` machinery.

6. **Recommendation**
   Reject. The plan misunderstands its own architecture (it is a corollary of other axioms, not a standalone textbook proof), overestimates the effort as a result, includes irrelevant steps, and handwaves the only formally difficult part that remains. 

VERDICT: reject — The route must be `provable-from-other-axioms` since it relies heavily on `AX_RiemannRoch`, the effort is drastically overestimated for a simple corollary, Step 3 is logically irrelevant, and the plan handwaves the crucial API linking non-zero global sections to effective divisors.
