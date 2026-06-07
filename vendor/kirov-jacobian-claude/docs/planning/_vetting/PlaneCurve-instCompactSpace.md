# Gemini 3.1 Pro critique — `PlaneCurve-instCompactSpace`

**Model:** gemini-3.1-pro-preview
**Duration:** 69.8s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Note:** flag: mathlib-now but PlaneCurve atlas still axiomatic
**Verdict:** **revise**

---

Here is a rigorous referee critique of the proposed discharge plan.

### 1. Route classification
**Incorrect.** The route is labeled `mathlib-now`, but the text itself admits it is "effectively `provable-from-other-axioms` once `PlaneCurve` lands." Because this instance is entirely dependent on how the `PlaneCurve` type is constructed (which is currently an axiom stub), the correct classification is **`provable-from-other-axioms`**.

### 2. Effort estimate
**Wildly uncalibrated.** The estimate of "Effort: 3 (2 days, ~40 LOC)" is dangerously optimistic. To prove this via a 3-chart quotient, you will need to:
1. Define the three closed unit polydiscs in `ℂ²`.
2. Prove they are compact (using Heine-Borel/closed-in-compact).
3. Push them forward through the sum-to-quotient map and prove continuity.
4. Prove the images cover the projective curve.

Managing absolute value inequalities, maximums over `Fin 3`, and quotient-topology continuity in Lean will easily take 200–300 LOC. This is an **Effort 6** task. 

### 3. Proof recipe & Logical gaps
The overarching topological strategy (a closed polydisc cover) is mathematically beautiful and precisely the right way to avoid building full projective space topology from scratch. However, there is a **critical logical gap in Step 2B**.

The plan states:
> *Step B — the union of those three closed-ball-truncated patches covers `PlaneCurve H` (every projective point has at least one nonzero homogeneous coordinate...)*

**This is mathematically insufficient.** Dividing by an arbitrary *nonzero* coordinate does not guarantee that the resulting affine coordinates fall inside the closed unit ball (they could easily have modulus $> 1$). To ensure the affine coordinates are $\le 1$ and thus actually land in your truncated patches, you must pick the coordinate with the **maximum absolute value** (which is strictly positive since `[0:0:0]` is ruled out). The recipe needs to explicitly mandate a maximum-modulus selection argument to prove the cover is surjective.

### 4. Textbook citations
The Plücker/compactness references in the docstring are fine, but for the formalization itself, cite standard complex manifold theory (e.g., Griffiths & Harris, *Principles of Algebraic Geometry*) which uses exactly this maximum-modulus polydisc cover to prove that $\mathbb{P}^n$ is compact.

### 5. What's missing or wrong
- **Wrong Route:** Must be `provable-from-other-axioms`.
- **Missing Math:** The maximum-modulus trick in Step 2B to guarantee the affine charts actually hit the closed unit balls.
- **Underestimated Overhead:** The plan assumes stitching the quotient topology will be trivial. Mathlib's `Quotient.mk` topology requires proving the quotient map is continuous and using `IsCompact.image`. The recipe should explicitly state the use of `isCompact_image` over the finite union of the three charts.

### 6. Recommendation
**Revise.** Correct the route, bump the effort to 6, and fix the topological covering argument by incorporating the maximum-modulus coordinate logic. 

VERDICT: revise — Change route to provable-from-other-axioms, increase effort to 6 to reflect the heavy quotient-topology lifting, and fix the logical gap in Step 2B by requiring the maximum-modulus coordinate to guarantee the cover.
