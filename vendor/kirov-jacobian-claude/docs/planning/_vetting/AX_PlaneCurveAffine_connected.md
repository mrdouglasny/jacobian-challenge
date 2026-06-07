# Gemini 3.1 Pro critique — `AX_PlaneCurveAffine_connected`

**Model:** gemini-3.1-pro-preview
**Duration:** 34.9s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **reject**

---

Here is a referee critique of the proposed discharge plan:

**1. Route classification**
**Incorrect.** The classification `provable-from-other-axioms` implies that this is a straightforward deduction from existing Mathlib tools or already-axiomatized project lemmas. It is actually `needs-infra` or `genuine-textbook`. Connecting algebraic irreducibility to topological connectedness over $\mathbb{C}$ requires a massive amount of missing topology and complex geometry infrastructure (covering spaces, path-lifting, fundamental groups, and the analytic continuation / symmetric polynomials argument). 

**2. Effort estimate**
**Wildly uncalibrated.** An effort of 5 (2 weeks, ~300 LOC) is pure fiction. Formalizing the irreducibility-to-monodromy-transitivity dictionary from scratch in Lean is an Effort 10 project that would take months and thousands of lines of code.

**3. Proof recipe**
* **Steps 1 & 2** (local chart via the Implicit Function Theorem) are reasonable and use existing Mathlib calculus (`ContDiffAt.toOpenPartialHomeomorph`).
* **Step 3a** (generic fibre is a finite set of points off a bad set $B$) is plausible using Bézout, but proving that the projection is an unramified cover off $B$ requires formalizing local homeomorphism lifting, which is non-trivial.
* **Step 3b** (monodromy connects the sheets) contains a **massive logical gap** and is effectively a brick wall. The plan blithely states "Going around a critical value braids the sheets... monodromy acts transitively". Mathlib does not have the fundamental group of punctured planes, general path-lifting for covering spaces, or the analytic continuation machinery required to define the monodromy action. Furthermore, proving that this monodromy is *transitive* precisely because the polynomial is *algebraically irreducible* requires constructing symmetric polynomials from the roots of invariant subsets and showing they are globally analytic and thus polynomials, contradicting irreducibility. The recipe does exactly what you feared: it kicks the can to a missing, massive "transitive monodromy" helper theorem. 
* **Axiom signature mismatch:** The plan notes that the axiom lacks the `hd : 3 ≤ H.d` assumption. As the plan itself hints, over $\mathbb{C}$, the affine patch of a smooth curve is *always* connected for $d \ge 1$ (it is a compact Riemann surface minus a finite number of points, and removing points from a real 2-manifold does not disconnect it). Modifying the axiom to restrict to $d \ge 3$ is mathematically unnecessary and will needlessly break downstream API.

**4. Textbook citations**
The citations (Hartshorne, Beauville, Forster) are mathematically appropriate for a human, but they highlight the problem: they rely on deep bridge theorems (like GAGA or the Riemann Existence Theorem) connecting algebraic geometry to complex analytic topology. You cannot simply "cite" these in Lean; you have to build the bridge.

**5. What's missing or wrong**
* **The "Risk" is a certainty:** The plan's escalation trigger says "if the discharge requires axiomatizing a transitive monodromy intermediate lemma, escalate." Consider this escalated. You *cannot* do Step 3b without that lemma, and proving that lemma is a thesis-level project on its own.
* **Complex vs. Real topology confusion:** The docstring's note about "1 or 2 connected components" for conics is true for $\mathbb{R}$, but false for $\mathbb{C}$. A smooth conic over $\mathbb{C}$ is $\mathbb{P}^1$ (a sphere), and its affine patch is a sphere minus 1 or 2 points (a plane or a cylinder), which are both manifestly connected. The docstring needs to be rewritten, and the proof should not hinge on $d \ge 3$. 
* **Real 2-manifold approach ignored:** The simplest path to connectedness for the affine patch avoids monodromy entirely: prove the projective curve is a connected real 2-manifold, and show that the affine patch is the complement of a finite set of points (the points at infinity). Removing a finite set of points from a connected manifold of real dimension $\ge 2$ leaves it connected. (Note: proving the projective curve is connected is still hard, but avoids the algebraic/monodromy dictionary).

**6. Recommendation**
**Reject.** Do not attempt this as a 2-week discharge. Reclassify this axiom as `genuine-textbook` or `needs-infra`. If the goal is strictly to close the Jacobian challenge without a multi-month detour into Riemann surface covering theory, you should leave it as an axiom, fix the erroneous docstring (smooth affine plane curves over $\mathbb{C}$ are connected for *all* $d \ge 1$), and move on to the actual Jacobian API.

VERDICT: reject — The plan drastically underestimates the effort required to formalize the correspondence between algebraic irreducibility and topological monodromy, which is missing from Mathlib, making this a `needs-infra` or `genuine-textbook` endeavor rather than a 2-week `provable-from-other-axioms` task.
