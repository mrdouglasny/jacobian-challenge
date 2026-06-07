# Gemini 3.1 Pro critique — `ambientPhi_ambientPsi_eq`

**Model:** gemini-3.1-pro-preview
**Duration:** 51.9s
**Source axiom:** `Jacobians/Vendor/Kirov/HolomorphicForms.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan:

1. **Route classification**: Completely wrong. This isn't `genuine-textbook`, it is `trivially-false` and `needs-deletion`. The axiom signature provides `(d : ℕ) (y : Fin gY → ℂ)` as free parameters, which Lean treats as universally quantified. This asserts that for a fixed `y`, `ambientPhi (...) = d • y` for *all* `d : ℕ`. Setting `d = 0` and `d = 1` immediately forces `y = 0`, making the axiom logically contradictory unless the genus `gY` is 0.

2. **Effort 1..10**: 1 (to just delete the axiom). The estimate of 8 (~3–6 weeks, 500–1000 LOC) is absurd. The plan explicitly notes in Step 5 that the axiom has *zero usage* in the project. You do not spend over a month building complex manifold degree theory and geometric trace maps just to fix a broken, unused axiom in a vendor namespace. 

3. **Proof recipe**: Riddled with fatal logical and mathematical errors.
   - **Logical catastrophe (Step 5)**: The plan acknowledges the axiom states the equality for all `d`, but bizarrely concludes that the free-`d` version is "trivially derivable as a corollary" because it is "vacuous" when `d ≠ degree`. This fundamentally misunderstands formal logic. A universally quantified statement that fails for some `d` is unconditionally FALSE, not vacuous. You cannot prove a false statement.
   - **Mathematical falsehood (Step 2)**: The plan claims that the matrix transpose of the pullback (`ambientPhi`) in an *arbitrary* coordinate basis (`ambientIso`) coincides with the geometric trace (`pushforwardForm`). This is mathematically false. Pullback and pushforward are adjoints only with respect to the canonical Serre/Hodge inner product. If `ambientIso` is just an arbitrary linear isomorphism (as defined in the vendor code), the algebraic transpose has no geometric meaning and will not equal the trace. 
   - **Hallucinated Mathlib**: `Complex.analyticAt_of_differentiable_on_punctured` does not exist in Mathlib v4.30. (Removable singularities are handled via `Complex.continuous_extend_of_differentiableOn_punctured` or Laurent series).

4. **Textbook citations**: Forster §17 and Miranda §III.4 do properly cover the geometric trace identity $f_* f^* \omega = d \cdot \omega$. However, they do not claim that the trace is equivalent to the matrix transpose of the pullback in an unpolarized, arbitrary coordinate basis.

5. **What's missing or wrong**:
   - The axiom is trivially false (forces $y = 0$ for all $y$).
   - The author fails to realize that an axiom with a free variable in the signature is universally quantified.
   - The geometry in Step 2 is broken (transpose $\neq$ trace for arbitrary bases).
   - The plan ignores its own discovery that the axiom is uncalled dead code, instead proposing a massive 6-week engineering effort to preserve it.

6. **Recommendation**: Reject. Delete the `ambientPhi_ambientPsi_eq` axiom entirely. It is logically false, mathematically unsalvageable as stated, and has zero usage in the codebase.

VERDICT: reject — The axiom is logically false (universally quantifying `d` forces `y = 0`), mathematically unsound in arbitrary bases, and entirely unused, so it should be deleted rather than fixed.
