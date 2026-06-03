# Gemini 3.1 Pro critique — `AX_HyperellipticOneForm_eq_form`

**Model:** gemini-3.1-pro-preview
**Duration:** 92.9s
**Source axiom:** `Jacobians/Axioms/HyperellipticLiouville.lean`
**Note:** L3 demo recipe; provable-from-L2
**Verdict:** **revise**

---

**1. Route Classification**  
Correct. `provable-from-other-axioms` is exactly right. This is a pure sheaf-gluing / chart-coverage consequence of Level 2.

**2. Effort Estimate**  
Calibrated at a 4, but it will likely lean towards a 5 because you have completely overlooked the topological patching required at the chart origins, which will add Mathlib friction. 

**3. Proof Recipe & Logical Gaps**  
The proposed recipe has a **fatal logical gap** regarding chart overlaps, and includes a completely redundant step.
*   **The Fatal Flaw (Chart Origins):** Your tactic sketch relies on pointwise evaluation (`funext q z`), assuming that for any `z` in a `projY` (branch point) or `inr` (infinity) chart target, a "cocycle hop" will connect it back to a `projX` chart. This is **false at `z = 0`**. The transition map from a branch point `projY` chart to an affine `projX` chart is undefined at the branch point itself. Therefore, `z = 0` is *not in the chart overlap* (the source of the transition map). The cocycle identity `EvenForm.lean:2119` will strictly require `z ∈ source`, which reduces to `z ≠ 0`. Algebraic cocycle hopping will literally fail to prove `form.coeff q 0 = form'.coeff q 0`.
*   **The Redundancy (Step 4):** Step 4 (`inl_inl` propagation) is entirely useless. Look at your own Step 1: the L2 axiom guarantees the formula for *every* `a ∈ smoothLocusY`. Step 3 also holds for *every* `a ∈ smoothLocusY`. Therefore, you already have strict pointwise equality on all `projX` charts directly from L2. You do not need the `inl_inl` cocycle to propagate anything.

**4. Textbook Citations**  
N/A (Standard Riemann surface chart arithmetic/identity principle).

**5. What's Missing or Wrong**  
*   **Missing continuity argument:** You cannot bypass the hole at `z = 0`. You must introduce a topological step to show that since `form.coeff` and `form'.coeff` are continuous (by virtue of being HolomorphicOneForms) and agree on the punctured neighborhood `target \ {0}`, they must agree at `0`. You will need Mathlib lemmas like `ContinuousOn.ext` or `ContinuousAt` combined with the density of the punctured disk. 
*   **Tactic Sketch is broken:** The `… -- one cocycle hop using EvenForm.lean:2119` block will leave an unprovable goal for the `z = 0` case. You need to pull the `funext` out, prove equality on the punctured sets via cocycles, and then apply a closure/density lemma to get function-level equality on the whole chart target. 
*   **Wrong Step 4:** Delete it. 

**6. Recommendation**  
Revise. Restructure the proof plan so it proves equality of functions on charts (handling the `z = 0` boundary cases via continuity/density) rather than naïve pointwise cocycle application, and remove the redundant Step 4.

VERDICT: revise — The pointwise cocycle argument fails at branch/infinity chart origins (`z = 0`) because they lie outside the chart overlap; you must add a continuity step to extend equality to these points and remove the redundant Step 4.
