# Gemini 3.1 Pro critique — `Divisor-instAddCommGroup`

**Model:** gemini-3.1-pro-preview
**Duration:** 31.1s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **revise**

---

Here is a referee-level critique of the proposed discharge plan:

1. **Route classification**: **Correct (`mathlib-now`).** This contains zero mathematical content and is purely a matter of Lean 4 instance synthesis. 
2. **Effort 1..10**: **Correct (1).** It is completely trivial once the underlying type is exposed.
3. **Proof recipe**: The core logic (`inferInstanceAs (AddCommGroup (FreeAbelianGroup X))`) is mathematically and structurally correct. However, the recipe blindly copies a massive list of typeclasses (`[TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`) from the axiom. The group structure of formal sums of points depends **only** on `X : Type*`. Keeping these binders in the instance is bad practice, clutters the typeclass inference caching, and is mathematically nonsensical. 
4. **Textbook citations**: N/A for what is purely an infrastructural typeclass alias.
5. **What's missing or wrong**: 
   * **Junk Binders**: As noted above, drop all the manifold and topology assumptions from the instance signature. It should literally just be `instance {X : Type*} : AddCommGroup (Divisor X) := ...`.
   * **Lean 4 Idioms / Syntax**: The recipe mentions using `unseal Divisor locally` as a fallback. Lean 4 does not have a native `unseal` command out-of-the-box in the way this assumes. The idiomatic Lean 4 way to handle this (if you want an opaque API) is to define it as `def Divisor (X : Type*) := FreeAbelianGroup X deriving AddCommGroup`, which auto-generates the instance by looking through the definition *before* any `@[irreducible]` attribute is applied. If you absolutely must preserve the exact name `Divisor.instAddCommGroup` for downstream proofs, your manual `inferInstanceAs` is fine, but drop the `unseal` pseudocode.
6. **Recommendation**: **Revise.** Drop the mathematically irrelevant topological/manifold typeclasses from the instance binders, and strongly consider using Lean 4's `deriving AddCommGroup` on the `Divisor` definition instead of a manual instance declaration.

VERDICT: revise — Drop the mathematically irrelevant manifold/topology binders from the instance and rely on `deriving AddCommGroup` or a clean `inferInstanceAs` without fake `unseal` syntax.
