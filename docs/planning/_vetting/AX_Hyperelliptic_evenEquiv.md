> **✅ DISCHARGED — Phase 3.** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# Gemini 3.1 Pro critique — `AX_Hyperelliptic_evenEquiv`

**Model:** gemini-3.1-pro-preview
**Duration:** 31.6s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **accept**

---

Here is a referee-level critique of the proposed axiom-discharge plan:

1. **Route classification**: Correct. This is essentially `provable-from-other-axioms` (or `needs-infra`), as it is entirely dependent on resolving the `Hyperelliptic` axiom into a concrete definition first.

2. **Effort**: 2 is well-calibrated. This is boilerplate glue once the blocker is resolved.

3. **Proof recipe**: The naive `rw [dif_neg h]` inside the goal `Hyperelliptic H ≃ₜ HyperellipticEven H h` will almost certainly fail. `Homeomorph` takes implicit `[TopologicalSpace α] [TopologicalSpace β]` arguments. Rewriting the type `Hyperelliptic H` into `HyperellipticEven H h` will leave behind the `Hyperelliptic.instTopologicalSpace` instance on the left side, which will not unify definitionally with `HyperellipticEvenProj.instTopologicalSpace` on the right side. `Homeomorph.refl _` will then complain about mismatched topologies. 
You correctly anticipated elaboration trouble in step 3. The robust way to do this is to use `Equiv.cast (dif_neg h)` to construct the naked equivalence, then upgrade it via `Homeomorph.mk` by proving continuity. The continuity proof will simply require unfolding `Hyperelliptic.instTopologicalSpace` (which itself must be defined via a corresponding `dite`) and applying `dif_neg h` to the instance as well.

4. **Textbook citations**: N/A. This is purely an architectural Lean lemma to route parity-dispatched structures.

5. **What's missing or wrong**: The plan is missing the explicit realization that the topological space instance for `Hyperelliptic H` must *also* be defined via a parity `dite`, and that this instance will need to be explicitly rewritten or unfolded to prove the continuity of the cast. The "Sum-encoded fallback" mentioned in the risks is also topologically tricky (a disjoint union is disconnected, which violates the curve's connected property), so the `dite` approach (or an inductive type) is strictly required.

6. **Recommendation**: Accept as-is. The structural strategy is correct, and the fallback notes show sufficient awareness of the dependent-type hurdles to successfully navigate the implementation.

VERDICT: accept — The plan correctly reduces this axiom to a definitional cast once the unified type lands, properly anticipating the need for a manual fallback when rewriting types breaks topology typeclasses.
