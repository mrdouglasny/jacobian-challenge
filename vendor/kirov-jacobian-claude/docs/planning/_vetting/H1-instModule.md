# Gemini 3.1 Pro critique — `H1-instModule`

**Model:** gemini-3.1-pro-preview
**Duration:** 15.5s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **accept**

---

1. **Route classification**: `mathlib-now` is acceptable here (though arguably `needs-infra` since it must wait for `H1` to be defined). The dependency is clearly stated, so the classification works in context.
2. **Effort 1..10**: 1. Perfectly calibrated. Once `H1` is defined as an object in `ModuleCat ℂ` (or similar), this is literally just `inferInstance`.
3. **Proof recipe**: Correct and realistic. It correctly links the definition of this instance to the eventual definitional unfolding of `H1`. The awareness in the risk section regarding Mathlib's `Sheaf.H` potentially returning an `Ab` rather than a `ModuleCat ℂ` (if one is not careful) is exactly the kind of Mathlib-specific foresight required for this challenge. 
4. **Textbook citations**: Forster Ch. II §13–15 is the standard and correct reference for the Čech cohomology of line bundles on Riemann surfaces and its $\mathbb{C}$-vector space structure.
5. **What's missing or wrong**: Nothing structurally wrong. The plan accurately identifies that this axiom is merely an artifact of `H1` currently being opaque. 
6. **Recommendation**: Accept as-is.

VERDICT: accept — The plan correctly identifies that the module instance will be trivially resolved by typeclass inference once the underlying `H1` type is properly defined, and accurately anticipates the potential category theory typeclass pitfalls.
