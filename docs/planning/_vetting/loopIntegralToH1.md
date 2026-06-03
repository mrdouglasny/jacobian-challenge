# Gemini 3.1 Pro critique — `loopIntegralToH1`

**Model:** gemini-3.1-pro-preview
**Duration:** 90.9s
**Source axiom:** `Jacobians/RiemannSurface/PathIntegral.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan:

1. **Route classification**: **Incorrect.** The plan claims `provable-from-other-axioms` while explicitly stating it will create `Homotopy.lean` to host Cauchy-on-disks tiling and approximate smooth homotopies. The topological prerequisites for this (smooth/analytic approximation of continuous homotopies on manifolds) are completely absent from Mathlib. Thus, the homotopy portion is unequivocally **`needs-infra`**. If the plan genuinely intended to assume `homotopyInvariance` as an axiom, the route would be correct, but the plan contradicts itself by detailing and scoping its proof. 

2. **Effort**: **Wildly uncalibrated due to scope confusion.** If you intend to prove homotopy invariance and build smooth approximation on manifolds, this is an Effort 10 (requiring months of infrastructure work). If you strip out the topology and strictly perform the algebraic descent assuming `homotopyInvariance` and `pathIntegralAnalyticArc` as axioms, it is an Effort 4.

3. **Proof recipe**:
   - **Fatal analytical gap (Step 3):** You casually state, "Approximate smooth homotopies by piecewise-real-analytic ones." You cannot evaluate `pathIntegralAnalyticLoop` on the boundaries of a grid tiling of a purely *continuous* homotopy, because those boundaries are non-rectifiable continuous paths. Proving that any continuous homotopy is homotopic to an analytic one is a profound missing theorem (Whitney approximation), not a one-liner.
   - **Logical contradiction (Step 5):** You claim you will "Use `Path.Homotopic.Quotient.lift`... to obtain a well-defined map," but your code sketch immediately bypasses the quotient entirely: `intro g; exact ... pathIntegralAnalyticLoop (chosenRep g)`. These approaches are mutually exclusive. 
     - If you use `Quotient.lift`, you must define a function on the raw type `Path X x₀ x₀` (meaning you must define a systematic analytic approximation for *every* continuous path, not just classes). 
     - If you use `chosenRep g` directly on the quotient element `g`, well-definedness is trivial, but you must manually prove `map_mul` by invoking `homotopyInvariance` to show that the analytic loop `chosenRep (a * b)` is continuously homotopic to the concatenation `chosenRep a * chosenRep b`. 
   - **Change of variables (Step 4):** Applying `intervalIntegral.integral_add_adjacent_intervals` to concatenated paths in local charts requires non-trivial affine change-of-variables (`intervalIntegral_comp_mul_add`) mapped through chart coordinate derivatives. It is significantly more painful than the plan implies.

4. **Textbook citations**: Correct. Mumford (Tata I) and Forster are the standard, precise references for this sequence. 

5. **What's missing or wrong**: 
   - You are attempting to "kick the can" on the analytical topology while simultaneously taking credit for proving it.
   - Complete ignorance of the difficulty of analytic approximation of continuous maps on manifolds in Lean.
   - The mutually exclusive constructions in Step 5 demonstrate a failure to understand Lean's quotient API versus the Axiom of Choice.

6. **Recommendation**: **Reject.** Separate the concerns. Rewrite this plan to focus *strictly* on the algebraic descent (`provable-from-other-axioms`), assuming `homotopyInvariance` as a standalone axiom. Fix the Step 5 logic to use `chosenRep` correctly without `Quotient.lift`. Move all Cauchy tiling and analytic approximation logic to a dedicated `needs-infra` plan.

VERDICT: reject — The plan conflates achievable algebraic descent with topological homotopy invariance, ignores the lack of smooth approximation infrastructure in Mathlib required for Cauchy tiling, and proposes a logically contradictory Quotient/Choice construction in Step 5.
