# Gemini 3.1 Pro critique — `abelJacobiDiv`

**Model:** gemini-3.1-pro-preview
**Duration:** 46.4s
**Source axiom:** `Jacobians/Axioms/AbelTheorem.lean`
**Verdict:** **revise**

---

Here is a rigorous critique of the proposed axiom-discharge plan:

### 1. Route classification
**Correct.** `needs-infra` is exactly right. This isn't a theorem; it's a data-stub that is completely blocked by waiting for the `Divisor X` opaque type to be actualized as `FreeAbelianGroup X`.

### 2. Effort 1..10
**Wildly uncalibrated.** The estimate of "3" ("~2–3 focused days, ~80 LOC") makes zero sense given your own parenthetical "once `Divisor` is a real `def`." Once `Divisor X = FreeAbelianGroup X`, this is a single 5-line `noncomputable def` that essentially says `FreeAbelianGroup.lift ofCurveImpl`. It is an **Effort 1** task that should take 15 minutes. 

### 3. Proof recipe
The core mechanism is spot on: `FreeAbelianGroup.lift` applied to `ofCurveImpl` produces exactly the `Divisor X →+ Jacobian X` homomorphism you want, and your realization that the $-(∑ n_P) \cdot \text{ofCurveImpl } P_0 P_0$ term mathematically vanishes (because $\text{ofCurveImpl } P_0 P_0 = 0$) means you don't need any messy sum manipulations. The equivalence `FreeAbelianGroup.lift : (X → A) ≃ (FreeAbelianGroup X →+ A)` from Mathlib is real and used correctly.

**However, there is a strict typeclass error:**
You specify using `Classical.arbitrary X`. In Lean 4, `Classical.arbitrary α` demands an `[Inhabited α]` instance. Your axiom's binder only provides `[Nonempty X]`. If you literally type `Classical.arbitrary X`, it will fail to synthesize `Inhabited X`. Furthermore, `Classical.arbitrary` is not found in `Mathlib.Logic.Nonempty` (it is in Lean core / `Init.Classical`). 

To extract a value from `[Nonempty X]`, you must either:
1. Use `Classical.choice ‹Nonempty X›` directly.
2. Supply a local instance: `have : Inhabited X := Classical.inhabited_of_nonempty ‹Nonempty X›` and *then* use `Classical.arbitrary X`.

### 4. Textbook citations
Not strictly applicable here. You aren't proving Abel's theorem or anything analytic; you are just establishing the Lean algebraic data structure for extending a map to a formal sum. The references in the module docstring are sufficient.

### 5. What's missing or wrong
* **Typeclass mismatch:** `Classical.arbitrary` requires `Inhabited`, but you only have `Nonempty`. 
* **Bloated scope:** 80 LOC / 3 days is absurd for what is literally just:
  ```lean
  noncomputable def abelJacobiDiv (X : Type u) [...] : Divisor X →+ Jacobian X :=
    FreeAbelianGroup.lift (fun P => ofCurveImpl X (Classical.choice ‹Nonempty X›) P)
  ```
* Note: the recipe is appropriately scoped to discharging `abelJacobiDiv` (the data stub) while leaving `AX_AbelTheorem` alone. This separation of concerns is good.

### 6. Recommendation
**Revise.** Correct the implementation to use `Classical.choice ‹Nonempty X›` instead of `Classical.arbitrary X`, and drastically lower the effort estimate to properly reflect the triviality of this map once `FreeAbelianGroup X` is in place.

VERDICT: revise — The route and logic are completely sound, but the effort estimate is wildly inflated for a 1-line definition, and `Classical.arbitrary X` will fail to compile without an `Inhabited X` instance (use `Classical.choice ‹Nonempty X›` instead).
