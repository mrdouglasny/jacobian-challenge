# Gemini 3.1 Pro critique — `infinityLiftChart_compat_affineLiftChart`

**Model:** gemini-3.1-pro-preview
**Duration:** 41.2s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan.

1. **Route classification**
   The classification `provable-from-other-axioms` relies on Route (B), which attempts to deduce this axiom from the forward direction (`affineLiftChart_compat_infinityLiftChart`). However, because Route (B) is mathematically circular (see below), this axiom must be proven independently via explicit formulas. The correct route is **`mathlib-now`**, mirroring the forward direction. 

2. **Effort 1..10**
   The estimate of **5** is based on the flawed assumption that Route (B) provides a quick one-liner. Because you must use Route (A), the effort is exactly the same as the forward direction. If the forward direction is a **6**, this is also a **6**. 

3. **Proof recipe**
   **Route (B) contains a fatal, two-fold circularity and is mathematically invalid:**
   * **Mathematical Circularity:** Step 3 proposes using the Inverse Function Theorem (IFT) to prove that the backward map (`bwd`) is `ContDiffOn ω`. The IFT requires proving that the derivative of the forward map (`fwd`) is non-vanishing. The plan proposes proving `D(fwd) ≠ 0` by using `transition_fderiv_mul`, which states `D(fwd) * D(bwd) = 1`. **You cannot use the chain rule `D(fwd) * D(bwd) = 1` unless you *already know* `bwd` is differentiable!** If you already knew `bwd` was differentiable, you wouldn't need the IFT. 
   * **Lean / Architectural Circularity:** `Jacobians.GeneralResults.transition_fderiv_mul` assumes `[SmoothManifoldWithCorners ...]`. The manifold instance (`EvenAtlas.lean:275`) is built using `chartAt_compat` (`EvenAtlas.lean:271`), which explicitly requires the axiom you are currently trying to prove. This is a complete bootstrap failure. You correctly identified this as a "risk" in the plan, but your proposed mitigation ("make `transition_fderiv_mul` work directly on `OpenPartialHomeomorph` pairs") fails due to the mathematical circularity described above.

   **Route (A) is the only valid path:** 
   The transition from infinity to affine is governed by exact, explicit inverse formulas (e.g., $x \mapsto 1/x$ and polynomial root corrections). Just like the forward direction, you must case-split on the four sub-cases and prove them directly using `polynomialLocalHomeomorph_contDiffOn_symm` and `contDiffOn_inv`.

4. **Textbook citations**
   N/A. This is a standard coordinate transition computation for algebraic curves.

5. **What's missing or wrong**
   * Route (B) must be entirely scrapped. It is a trap that fundamentally misunderstands the prerequisites of the Inverse Function Theorem and the chain rule. 
   * The plan treats Route (A) as a secondary "fallback" when it is, in fact, the only logically sound way to proceed. Route (A) needs to be promoted to the primary plan and fully detailed.

6. **Recommendation**
   **Reject.** The plan must be rewritten to exclusively mandate Route (A). Discard all mentions of Route (B), `transition_fderiv_mul`, and `contDiffOn_symm_toOpenPartialHomeomorph`. The backward transition must be computed directly from the explicit rational/polynomial formulas, identically to the forward transition.

VERDICT: reject — Route B contains a fatal mathematical circularity by using the chain rule to satisfy the Inverse Function Theorem, meaning Route A must be the sole approach.
