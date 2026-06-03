# Gemini 3.1 Pro critique — `PlaneCurve-instNonempty`

**Model:** gemini-3.1-pro-preview
**Duration:** 38.7s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **revise**

---

Here is a rigorous critique of the proposed axiom-discharge plan:

1. **Route classification**: Incorrect. This should be **needs-infra**. You explicitly state that the proof is "Blocked by: `PlaneCurve`" and waiting for it to be "a real `def`." You literally cannot write this proof until the pushout infrastructure and the `centralCoe` inclusion map are constructed. It ceases to be `provable-from-other-axioms` because it strictly requires the type definition to land first.

2. **Effort**: 1 is perfectly calibrated. This is a trivial typeclass transport once the inclusion map exists.

3. **Proof recipe**: The geometric logic is perfectly sound—the central affine chart trivially injects into the glued projective curve, so nonemptiness transports directly. However, your Lean 4 syntax is botched. 
   In Mathlib, `Nonempty.map` has the signature `(f : α → β) (h : Nonempty α) : Nonempty β`. Lean 4's dot notation `(AX_PlaneCurveAffine_nonempty H).map (centralCoe H)` will pass the `Nonempty` instance as the *first* explicit argument (where it expects the function `α → β`), resulting in an immediate type error. 
   You must write it using standard application:
   ```lean
   Nonempty.map (centralCoe H) (AX_PlaneCurveAffine_nonempty H)
   ```
   Or simply bypass `map` entirely with a direct construction:
   ```lean
   let ⟨x⟩ := AX_PlaneCurveAffine_nonempty H; ⟨centralCoe H x⟩
   ```

4. **Textbook citations**: None needed for what is essentially a trivial gluing topological property. 

5. **What's missing or wrong**: 
   - The dot-notation syntax for `Nonempty.map` is completely backward. 
   - The route is misclassified. 
   - On the positive side: your escalation trigger/risk assessment is highly accurate. If the project abandons the three-chart pushout for a pure `Proj`-style homogeneous variety definition, `centralCoe` won't exist and you will have to lift through `PlaneCurveProjective H → PlaneCurve H` as noted.

6. **Recommendation**: Revise. Fix the `Nonempty.map` syntax error, change the route to `needs-infra`, and rewrite the code snippet to be functionally correct Lean 4 code.

VERDICT: revise — Fix the backward `Nonempty.map` dot-notation syntax and change the route to needs-infra since the required inclusion map does not yet exist.
