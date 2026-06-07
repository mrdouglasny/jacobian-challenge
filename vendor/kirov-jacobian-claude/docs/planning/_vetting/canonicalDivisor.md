# Gemini 3.1 Pro critique — `canonicalDivisor`

**Model:** gemini-3.1-pro-preview
**Duration:** 51.8s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed discharge plan.

### 1. Route classification
**Incorrect.** The correct classification is **`needs-infra`**. 
The plan claims `provable-from-other-axioms` but admits in Stage 4 that it will likely introduce a *new* axiom (`nonzero_meromorphic_one_form_exists`) to replace the current one. Replacing a `Type`-valued data axiom with a `Prop`-valued existence axiom is good Lean practice, but it is an axiom refactor, not a mathematical discharge. Furthermore, the massive amount of missing infrastructure (global meromorphic functions, meromorphic differentials, finiteness of poles/zeros) means this is heavily blocked by missing Mathlib features.

### 2. Effort
**Wildly underestimated (6).** This is a **9 or 10**. 
The plan assumes you can throw together meromorphic 1-forms, their orders, and prove the finiteness of their zeros/poles in ~120 LOC. Building a rigorous theory of meromorphic sections of a line bundle, proving the order is well-defined across charts, and using compactness plus the Identity Theorem to prove the divisor has finite support is a multi-month undertaking in Mathlib. 

### 3. Proof recipe
There are severe mathematical and structural flaws in the proposed recipe:
*   **Fundamental confusion about orders and transitions (Stage 3):** The plan states the order in a chart is *"multiplied by the chart transition's contribution which is `≥ 0`"*. This is mathematically false on two fronts. First, orders of vanishing **add**, they do not multiply ($ord(f \cdot g) = ord(f) + ord(g)$). Second, the transition function for a 1-form is the Jacobian derivative of the coordinate change ($dz_j / dz_i$). Because the transition is a local biholomorphism, this derivative is nowhere-zero. Its order of vanishing is **exactly 0**, which is precisely why the order of a 1-form is chart-independent. 
*   **Naive Cocycle Condition (Stage 2):** The plan claims you can keep the cocycle condition "unchanged" by just swapping holomorphic functions for meromorphic ones. In Lean, functions to `ℂ` return junk values (often `0`) outside their domain or at poles. A pointwise equality $f_i(x) = f_j(x) \cdot (dz_j/dz_i)(x)$ will be vacuously true or demonstrably false at the poles depending on how the junk values interact. The cocycle condition for meromorphic forms must be enforced on a dense open set (the punctured neighborhood) or at the level of germs/fraction fields. 
*   **Handwaving Finiteness (Stage 3):** The invocation of `(orderAt_form_finite ω).toFinset` hides an immense amount of work. Proving that a non-zero meromorphic form on a compact surface has finitely many zeros and poles requires the Identity Theorem for meromorphic functions.
*   **Kicking the can (Stage 4):** By introducing `AX_nonzero_meromorphic_one_form_exists`, the recipe fails to discharge the axiom and instead routes it to a helper axiom. While replacing a data axiom with a Prop axiom using `Classical.choice` (Stage 5) is structurally superior for Lean, it is not a proof.

### 4. Textbook citations
The textbook citations are correct. Forster Ch. II §17 and Miranda Ch. IV §1 are the standard references for canonical divisors via meromorphic differentials.

### 5. What's missing or wrong
*   **Wrong math:** The explanation of why the divisor of a 1-form is well-defined is mathematically incorrect (orders add, transition derivatives have order exactly 0).
*   **Wrong types:** You cannot define `MeromorphicOneForm` using global functions `X → ℂ → ℂ` with point-wise cocycle conditions without deeply addressing the behavior at the poles.
*   **Missing Identity Theorem:** Finiteness of the divisor sum is completely glossed over but represents the bulk of the actual formalization work.
*   **No actual discharge:** The plan essentially admits it cannot prove the existence of a meromorphic 1-form (Riemann Existence Theorem / Riemann-Roch) without adding another axiom.

### 6. Recommendation
**Reject.** The plan must be completely overhauled. If the goal is purely to fix the fact that `canonicalDivisor` is a data axiom (which breaks definitional equality and typeclass inference), the plan should just explicitly state that it is refactoring a `Type`-level axiom into a `Prop`-level `AX_exists_canonical_divisor_class` or `AX_nonzero_meromorphic_one_form_exists` axiom, without pretending to build the meromorphic 1-form infrastructure trivially. If the goal is a genuine textbook discharge, you must first build a robust API for meromorphic sections of line bundles, which is currently far out of scope.

VERDICT: reject — The plan contains fundamental mathematical errors regarding chart transitions for 1-forms, drastically underestimates the required infrastructure for meromorphic functions, and ultimately just kicks the can to a new axiom.
