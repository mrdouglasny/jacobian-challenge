# Gemini 3.1 Pro critique — `Hyperelliptic-instNonempty`

**Model:** gemini-3.1-pro-preview
**Duration:** 26.3s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **revise**

---

An expert review of your axiom-discharge plan for `Hyperelliptic.instNonempty`.

### 1. Route classification
**Correct.** `provable-from-other-axioms` is the exact right classification here. This is pure architectural glue that delegates to the concrete parity branches via the homeomorphism axioms.

### 2. Effort
**Calibrated.** Effort 1 (~20 mins, 5 LOC) is spot on.

### 3. Proof recipe
The conceptual logic is flawless: case split on parity, grab the nonempty instance from the corresponding concrete type, and push it through the equivalence. 

However, the proposed Lean 4 code snippet contains three specific errors/antipatterns:
1. **`theorem` vs `instance`:** You declared `theorem Hyperelliptic.instNonempty`. Since the goal is `Nonempty` (a typeclass), it must be declared as an `instance`. Otherwise typeclass inference will fail to pick it up without manual `haveI` incantations downstream.
2. **Hallucinated `Equiv.nonempty`:** As you correctly suspected in your risk triggers, `Equiv.nonempty` is not a Mathlib lemma (the closest is `Equiv.nonempty_congr`, which is an `iff`). But you don't even need to drop down to `Equiv`! `Nonempty.map` takes any function. Since `Homeomorph` coerces to a function, `Nonempty.map (AX_Hyperelliptic_oddEquiv H h).symm inferInstance` is the idiomatic one-liner. 
3. **Bogus `Fact` wrapper:** In the even branch, you wrote `haveI : Fact (¬ Odd H.f.natDegree) := ⟨h⟩`. This is completely unnecessary. The prompt explicitly shows that the even nonemptiness instance takes `h` as a regular explicit argument (`(h : ¬ Odd H.f.natDegree)`), not as a `Fact` typeclass. 

### 4. Textbook citations
**N/A.** This is a pure Lean architecture/glue result, so no mathematical reference is needed or expected.

### 5. What's missing or wrong
Your fallback witness-extraction strategy in the "Risk" section is bulletproof, but we can write the clean `Nonempty.map` version natively. The snippet should be revised to:

```lean
instance Hyperelliptic.instNonempty (H : HyperellipticData) :
    Nonempty (Hyperelliptic H) := by
  by_cases h : Odd H.f.natDegree
  · exact Nonempty.map (AX_Hyperelliptic_oddEquiv H h).symm inferInstance
  · exact Nonempty.map (AX_Hyperelliptic_evenEquiv H h).symm inferInstance
```
*(Note: If Lean complains about synthesizing `inferInstance`, you can use `(by infer_instance)` or your `obtain ⟨x⟩ := inferInstance...` fallback, but the `instance` keyword is mandatory either way).*

### 6. Recommendation
**Revise.** The plan is structurally correct and safe, but the code snippet must be updated to use `instance`, remove the `Fact` wrapper, and use `Nonempty.map`.

VERDICT: revise — The strategy is perfectly sound, but the Lean 4 snippet contains three syntactical/API errors (`theorem` instead of `instance`, hallucinated `Equiv.nonempty`, and an unnecessary `Fact` wrapper) that must be fixed.
