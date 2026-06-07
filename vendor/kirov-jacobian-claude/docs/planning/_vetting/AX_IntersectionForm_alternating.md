# Gemini 3.1 Pro critique — `AX_IntersectionForm_alternating`

**Model:** gemini-3.1-pro-preview
**Duration:** 30.1s
**Source axiom:** `Jacobians/Axioms/IntersectionForm.lean`
**Verdict:** **reject**

---

Here is a rigorous referee critique of the proposed discharge plan:

1. **Route classification**: **Wrong.** The correct classification is `needs-infra`. The plan falsely claims `provable-from-other-axioms` by relying on a future, nonexistent definition of `intersectionForm` that itself requires massive missing algebraic topology machinery (singular cohomology, cup products, Poincaré Duality). You cannot classify a theorem as "provable from other axioms" when the proof directly invokes infrastructure that doesn't exist.

2. **Effort**: **Wildly uncalibrated.** An effort of "3" and "~1 focused day" assumes all of Hatcher Chapter 3 magically appeared in Mathlib overnight. The real effort to build cup products, graded commutativity, and top-cohomology fundamental classes from scratch in Mathlib is a 10 (a multi-month, multi-contributor project). 

3. **Proof recipe**: Mathematically sound, but practically a hallucination. 
   - The lemmas `cup_graded_comm`, `PD`, and the fundamental class evaluation do not exist in Mathlib. The provided "Lean script" is pure fictional pseudo-code.
   - There is a major hidden gap in the bridge step: converting `2x = 0` in `H²(X; ℤ)` to `intersectionForm x₀ a a = 0`. This requires formally proving `H²(X; ℤ) ≅ ℤ` (via Poincaré Duality or the Universal Coefficient Theorem) and proving that the evaluation on the fundamental class is an isomorphism. This is not a simple `linarith` or `omega` step as the script implies; it requires serious categorical and topological tracking.
   - The "optional shortcut" is a formalization anti-pattern. Swapping this axiom for a new `AX_IntersectionForm_cup_compatible` axiom does not discharge anything; it is simply axiom-juggling. 

4. **Textbook citations**: **Correct.** Hatcher Thm 3.14 and Thm 3.26 are the standard, precise references for graded commutativity of the cup product and the top cohomology of a compact orientable surface.

5. **What's missing or wrong**:
   - The plan acknowledges it is blocked by `intersectionForm.md`, but fails to inherit its `needs-infra` reality.
   - It treats `Cohomology.lean` as if it is a module already waiting in a PR queue. Mathlib does not currently have singular cohomology or cup products.
   - The script fakes the API. If you write pseudo-code in a discharge plan, it must be explicitly labeled as such, rather than presented as a ready-to-paste `theorem`.

6. **Recommendation**: Reject. Reclassify as `needs-infra`. Strip out the fake Lean script and replace it with a high-level mathematical dependency tree clearly showing that this simple result is deeply blocked by singular cohomology, cup products, and Poincaré Duality. Remove the "optional shortcut" entirely.

VERDICT: reject — The route must be `needs-infra` because the proof entirely depends on non-existent singular cohomology, cup products, and Poincaré duality infrastructure, making the provided Lean script pure fantasy.
