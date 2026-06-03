# Gemini 3.1 Pro critique — `Divisor`

**Model:** gemini-3.1-pro-preview
**Duration:** 55.5s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **revise**

---

Here is a rigorous critique of the proposed axiom-discharge plan:

1. **Route classification**: **Wrong.** This is strictly `mathlib-now`. You are not proving a theorem from other project axioms (`provable-from-other-axioms`); you are directly replacing an opaque type axiom with a concrete instantiation using Mathlib's existing `FreeAbelianGroup`.

2. **Effort**: **Wildly uncalibrated.** An effort of 4 (2–3 focused days) for a single-line alias is absurd. This is an **Effort 1** task. It will take less than 15 minutes to write the definition and fix the companion declarations. 

3. **Proof recipe**:
   - **`def` vs `abbrev` (Step 2)**: Your reasoning here is exactly backwards for Lean 4. You state: *"Use `def` (not `abbrev`): we want the typeclass instances to fire through the named alias"*. In Lean 4, `def` acts as an opacity boundary that often *blocks* typeclass inference! If you want the `AddCommGroup` instance on `FreeAbelianGroup` to implicitly fire for `Divisor X` without boilerplate, you **must use `abbrev`**. If you insist on `def` to deliberately hide the API, you are forced to write companion instances explicitly (e.g., `instance : AddCommGroup (Divisor X) := by delta Divisor; infer_instance`), which contradicts your stated goal. Just use `abbrev`.
   - **Universe sanity (Step 3)**: Spot on. `FreeAbelianGroup X` lives in the same universe as `X`, so migrating from `: Type` to `: Type _` or `: Type u` is necessary and correct.
   - **Unused variables warning**: You are passing `[TopologicalSpace X]`, `[IsManifold ... ]`, etc., into a definition that solely evaluates to `FreeAbelianGroup X`. Lean 4's linter will throw errors for unused variables. You must either rename them with underscores (e.g., `[_ : TopologicalSpace X]`) or locally suppress the linter (`set_option linter.unusedVariables false`). 

4. **Textbook citations**: **Correct.** Forster Ch. I §8 perfectly matches this definition (Weil divisors as the free abelian group on the points of the curve).

5. **What's missing or wrong**: 
   - The effort estimate is detached from reality.
   - The route is misclassified.
   - The advice to avoid `abbrev` demonstrates a misunderstanding of Lean 4's typeclass resolution transparency. 
   - The recipe ignores the linter errors that will inevitably trigger when passing geometric typeclasses to a purely algebraic right-hand side.

6. **Recommendation**: **Revise.** Fix the route to `mathlib-now`, drop the effort estimate to 1, change the recommendation from `def` to `abbrev`, and add instructions to handle the unused variable linter warnings.

VERDICT: revise — Change route to mathlib-now, drop the absurd 2-3 day effort estimate to Effort 1, and use `abbrev` instead of `def` to avoid typeclass resolution boilerplate.
