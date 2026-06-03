# Gemini 3.1 Pro critique — `bridgePath`

**Model:** gemini-3.1-pro-preview
**Duration:** 41.8s
**Source axiom:** `Jacobians/Bridge/KirovLineIntegral.lean`
**Verdict:** **reject**

---

Here is a rigorous referee critique of the proposed axiom-discharge plan:

1. **Route classification**: Incorrect. The classification should be **`needs-infra`**, not `provable-from-other-axioms`. Proving that a connected topological manifold is smoothly path-connected is a standard theorem, but doing it in Lean requires establishing reusable manifold infrastructure (covers by convex chart balls, flat-at-endpoint reparameterizations) that is currently missing from Mathlib. 

2. **Effort 1..10**: The estimate of 6 is **too low**. Given the missing infrastructure and the mathematical gaps outlined below, properly formalizing this from scratch is an **8** (at least 3–4 weeks and ~800+ LOC).

3. **Proof recipe**: Route A contains **two fatal logical gaps**:
   * **The Convexity Gap**: The plan dictates replacing the path inside a chart with a straight line (`chartLine`). However, the image of `extChartAt` is an arbitrary open subset of $\mathbb{C}$, which is generally **not convex**. A straight line between two points in this image can easily exit the chart domain, rendering the pullback to $X$ undefined and destroying smoothness. You *must* refine your cover to use charts whose images are open balls (which are convex).
   * **The Junction Corner Gap**: The plan claims that concatenating the chart-lines end-to-end via `Path.trans` yields a path that is "chart-locally `DifferentiableAt`" everywhere. This is mathematically false. `Path.trans` scales intervals linearly; the left and right derivatives at the junction points will not match. The resulting path will have corners and will strictly fail the `∀ t, DifferentiableAt` requirement at finitely many points. You must apply a flat reparameterization to each segment (e.g., pre-composing with a $C^1$ function like $t \mapsto 3t^2 - 2t^3$) so that the derivatives vanish at the endpoints, making the concatenation everywhere differentiable.

4. **Textbook citations**: Missing entirely. The plan should cite the standard result that connected manifolds are smoothly path-connected. An appropriate reference is **John M. Lee, *Introduction to Smooth Manifolds*, Proposition 2.15**.

5. **What's missing or wrong**:
   * **`Path.trans` smoothness**: Falsely assumes generic path concatenation preserves differentiability.
   * **Chart topology**: Falsely assumes chart target domains are convex. 
   * **Mathlib instances**: `ChartedSpace.locPathConnected` does not exist as a free instance in Mathlib. Because `ChartedSpace` only requires local homeomorphisms, you will have to manually construct the `LocPathConnectedSpace X` instance by transferring the local path-connectedness of $\mathbb{C}$ through the chart basis.

6. **Recommendation**: **Reject**. The mathematical blueprint for Route A is fundamentally flawed. Revise the recipe to explicitly include (1) a topological refinement step using convex chart balls, and (2) a flat-at-endpoints polynomial reparameterization step to guarantee everywhere-differentiability at the concatenation joints.

VERDICT: reject — The proof recipe contains fatal mathematical flaws regarding chart convexity and non-differentiable corners at concatenation joints.
