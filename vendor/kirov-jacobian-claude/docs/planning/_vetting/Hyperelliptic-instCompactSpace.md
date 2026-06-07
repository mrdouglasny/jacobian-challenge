# Gemini 3.1 Pro critique — `Hyperelliptic-instCompactSpace`

**Model:** gemini-3.1-pro-preview
**Duration:** 44.8s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **accept**

---

This is a rigorous and well-architected discharge plan that properly understands the project's dependency graph. You are successfully delegating the unified type's topological properties to the parity-specific types via the established homeomorphism axioms.

### 1. Route classification
**Correct.** `provable-from-other-axioms` is exactly right. You are kicking the can to `AX_Hyperelliptic_oddEquiv` and `AX_Hyperelliptic_evenEquiv`, which is the intended design for unifying the parity branches.

### 2. Effort
**Calibrated.** Effort 1 (~30 minutes) is spot on. This is purely a formal transport of a typeclass across an equivalence. 

### 3. Proof recipe
The recipe is logically sound. By casing on `Odd H.f.natDegree`, you gain access to the respective homeomorphism axioms. 
* **Logical Gaps:** None. `CompactSpace` is a `Prop`-valued class in Mathlib (`class CompactSpace (α : Type u) [TopologicalSpace α] : Prop`), which means `by_cases` inside an `instance` or `theorem` declaration is perfectly legal and will not trip up Lean 4's typeclass synthesis or result in code-extraction errors.
* **Mathlib API:** The plan astutely anticipates the exact Mathlib naming for transporting `CompactSpace`. In Mathlib v4, `Homeomorph` has `Homeomorph.compactSpace`, which takes `e : α ≃ₜ β` and `[CompactSpace α]` to yield `CompactSpace β`. Thus, applying `exact Homeomorph.compactSpace (AX_Hyperelliptic_oddEquiv H h).symm` will work directly. The fallback involving `IsCompact.image` of `Set.univ` is mathematically flawless if typeclass inference balks.

### 4. Textbook citations
N/A. This is structural Lean plumbing, not a mathematical theorem.

### 5. What's missing or wrong
* **Syntax Nitpick:** In your code block, you used the `theorem` keyword:
  ```lean
  theorem Hyperelliptic.instCompactSpace (H : HyperellipticData) : ...
  ```
  While the prose correctly says "Replace with an `instance` definition; drop the redundant `attribute [instance]`", make sure you actually write:
  ```lean
  instance instCompactSpace (H : HyperellipticData) : CompactSpace (Hyperelliptic H) := by
  ```
  If you name it `Hyperelliptic.instCompactSpace` explicitly while outside the namespace, Lean 4's `instance` command accepts `instance Hyperelliptic.instCompactSpace ...`.
* **Redundant `Fact`:** Your even branch includes `haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩`. As shown in the verbatim text, the target instance `CompactSpace (HyperellipticEven H h)` takes `H` and `h` as arguments directly, so typeclass synthesis for the homeomorphism's domain will likely succeed without you needing to manually inject `Fact` into the local context. Leaving it in won't hurt, but it is technically unnecessary.

### 6. Recommendation
**Accept as-is.** The plan is fully baked, accurately recognizes the axiom dependencies, and anticipates the correct Mathlib topological transport mechanisms. 

VERDICT: accept — The plan correctly identifies the route as a simple structural transport of a Prop-class along homeomorphism axioms and is ready for immediate implementation.
