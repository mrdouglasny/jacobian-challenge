# Gemini 3.1 Pro critique — `genus_eq_zero_iff_homeo`

**Model:** gemini-3.1-pro-preview
**Duration:** 41.7s
**Source axiom:** `Jacobians/Vendor/Kirov/Genus.lean`
**Verdict:** **revise**

---

Here is a referee critique of the proposed axiom-discharge plan:

1. **Route classification**: **Correct**. `provable-from-other-axioms` is the exactly right classification here. This is a vendor-side bridging task to eliminate Kirov's duplicate axiom by delegating it to the main-tree `AX_genus_eq_zero_iff_homeo` axiom. 

2. **Effort 1..10**: **Wildly miscalibrated**. The plan estimates "Effort: 7, ~1 focused week, ~150–250 LOC" for Route (a). But Route (a) is literally a single `LinearEquiv.finrank_eq` bridge lemma and a 3-line substitution proof. The code provided in the recipe is ~20 LOC total. The effort should be **1**, taking at most an hour. 

3. **Proof recipe**: The underlying logic for Route (a) is sound, but there are Lean 4 unification/syntax bugs in the proposed code:
   - In Step 2: `exact (LinearEquiv.finrank_eq bridgeFormEquiv).symm` will likely fail because `X` is implicit in `bridgeFormEquiv`. You should write `exact (LinearEquiv.finrank_eq (bridgeFormEquiv (X := X))).symm` or `exact (bridgeFormEquiv (X := X)).finrank_eq.symm`.
   - In Step 3: `have hg ... := (Jacobians.Bridge.genus_eq_kirovGenus).symm` will fail with an "unable to infer implicit argument" error because you invoke `.symm` before Lean knows what `X` is. You must supply the explicit universe/type variable: `(Jacobians.Bridge.genus_eq_kirovGenus (X := X)).symm`. (Better yet, just do `rw [← Jacobians.Bridge.genus_eq_kirovGenus (X := X)]`).

4. **Textbook citations**: Forster and Miranda are standard and correct for the *underlying math*, but since Route (a) is just a type-translation exercise delegating to the main tree, the math references aren't strictly relevant here (they belong on the main-tree axiom's documentation). 

5. **What's missing or wrong**:
   - **Contradictory Effort**: The LOC and time estimates contradict the extremely short proof scripts provided.
   - **Scope Creep (Route b)**: Including Route (b) in this vendor handoff plan is confusing and out of scope. Route (b) is the genuine-textbook proof plan for discharging the *main-tree* axiom (`AX_genus_eq_zero_iff_homeo`), not for bridging the Kirov vendor duplicate. You should delete Route (b) entirely and just link to `docs/planning/AX_genus_eq_zero_iff_homeo.md` if the reader is curious about how the main-tree axiom will eventually be proved.
   - **Implicit Argument Application**: Missing `(X := X)` in the bridging lemmas.

6. **Recommendation**: **Revise**. Fix the effort estimate to 1 / <30 LOC, add the required `(X := X)` implicit applications to the Lean 4 proof scripts to prevent unification errors, and delete the distracting Route (b) (it belongs in the main tree's planning documents).

VERDICT: revise — The plan correctly identifies the trivial bridge strategy but provides a wildly inflated effort estimate (Effort 7 for what is essentially a 20-line substitution) and contains basic Lean 4 implicit-argument unification bugs.
