# Gemini 3.1 Pro critique — `Hyperelliptic-instT2Space`

**Model:** gemini-3.1-pro-preview
**Duration:** 67.6s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **revise**

---

1. **Route classification**: **Correct**. `provable-from-other-axioms` is exactly right since the logic propagates the `T2Space` property across the posited `AX_Hyperelliptic_oddEquiv` and `AX_Hyperelliptic_evenEquiv` homeomorphism axioms.
2. **Effort 1..10**: **1**. Perfectly calibrated. This is a standard topological transfer and takes minutes. 
3. **Proof recipe**: The structural logic is bulletproof—Hausdorff is invariant under homeomorphism, and Mathlib's `Homeomorph.t2Space` translates this directly. However, the recipe contains a syntax error and a misunderstanding of how Lean's typeclass resolution works regarding `Fact`.
4. **Textbook citations**: N/A. This is standard topological boilerplate.
5. **What's missing or wrong**:
   - **`theorem` vs `instance`**: The code block in step 1 declares `theorem Hyperelliptic.instT2Space ...`, but step 3 instructs the user to replace the axiom with an `instance` definition and drop the attribute. If you use `theorem`, Lean will not register it as a typeclass instance (unless you retain the explicit attribute, which is unidiomatic). The code block should simply read: `instance instT2Space (H : HyperellipticData) : T2Space (Hyperelliptic H) := by`.
   - **Redundant `haveI` shim**: The `haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩` line in the even branch is dead code. When you call `(AX_Hyperelliptic_evenEquiv H h).symm.t2Space`, Lean invokes typeclass resolution to find `[T2Space (HyperellipticEven H h)]`. If this instance already exists at lines 31–34 (as you noted, analogous to the verbatim `CompactSpace` instance), it takes `h` as a regular argument, not as a `Fact`. Typeclass resolution will succeed purely on the basis of the type. The `Fact` wrapper is only needed internally when *defining* instances that delegate to `HyperellipticEvenProj`, not when *using* the exported `HyperellipticEven` instances.
6. **Recommendation**: **Revise**. Change `theorem` to `instance` in the code snippet, and delete the redundant `haveI` line from the even branch.

VERDICT: revise — Fix the code block to use the `instance` keyword rather than `theorem`, and delete the unnecessary `haveI` typeclass shim.
