# Gemini 3.1 Pro critique — `AX_Hyperelliptic_genus`

**Model:** gemini-3.1-pro-preview
**Duration:** 33.5s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed discharge plan for `AX_Hyperelliptic_genus`.

1. **Route classification**: **Incorrect.** The route should be **`provable-from-other-axioms`**. Your own Step 1 delegates the proof to the parity-specific genus theorems and the `AX_Hyperelliptic_oddEquiv` / `AX_Hyperelliptic_evenEquiv` axioms. Steps 2, 3, and 4 detail the proofs of *other* axioms (like L2, L3, and the odd parity genus). This specific axiom is just the top-level dispatch gluing them together.
2. **Effort**: **Not calibrated.** Because you incorrectly subsumed L2, L3, and the odd-parity construction into this plan, you estimated it at 9 (2-3 months). Scoped correctly (just the parity dispatch assuming the other axioms), this is an **Effort 2** (a few days). The L2 and L3 work belongs in their respective axiom-discharge plans.
3. **Proof recipe**: **Contains a fatal mathematical and Lean type-theoretic error.** 
   In Step 1, you propose a lemma: `genus_eq_of_homeomorph : X ≃ₜ Y → genus X = genus Y`, claiming it follows from `Module.finrank_eq_of_equiv` applied to the `LinearEquiv` of `HolomorphicOneForm`s. 
   **This is mathematically false.** The definition of genus here is the *analytic* genus ($h^{1,0}$), which is the complex dimension of `H⁰(X, Ω¹)`. A mere topological homeomorphism (`X ≃ₜ Y`) does **not** induce a pullback on holomorphic 1-forms. Even if the underlying map happens to be analytic on paper, Lean's typeclass system only knows it is a `Homeomorph`. You cannot construct a `LinearEquiv` of holomorphic forms from a `Homeomorph`. Without deep Hodge theory (which Mathlib lacks), you cannot equate the analytic genus using only topological equivalence.
4. **Textbook citations**: Miranda and Forster are the correct references for the hyperelliptic genus, but they are technically overkill for this specific axiom since this axiom's sole job is to dispatch to the parity-specific theorems (which is where the textbook math actually happens). 
5. **What's missing or wrong**:
   * **The `≃ₜ` axioms must be upgraded:** `AX_Hyperelliptic_oddEquiv` and `AX_Hyperelliptic_evenEquiv` are typed as `Homeomorph`s (`≃ₜ`). To transport the analytic genus, these axioms must be redefined to provide biholomorphisms (e.g., an equivalence that is `ContMDiff` / holomorphic in both directions).
   * **Massive scope creep:** Your proof recipe solves the entire hyperelliptic genus problem inside this one plan. `AX_Hyperelliptic_genus` should *only* be the glue. The Liouville L2/L3 proofs belong in `AX_HyperellipticForm_polynomial_decomposition` and `AX_HyperellipticOneForm_eq_form`.
6. **Recommendation**: **Reject**. Revise the plan by (1) changing the route to `provable-from-other-axioms`, (2) dropping the effort to ~2, (3) stripping out the L2/L3 proofs, and (4) crucially, requiring an upgrade of the `AX_Hyperelliptic_*Equiv` axioms to biholomorphisms so that the analytic genus can actually be transported. 

VERDICT: reject — The plan relies on a mathematically false lemma (a topological homeomorphism `≃ₜ` does not induce a linear equivalence of holomorphic 1-forms) and misclassifies the route by subsuming the L2/L3 axioms.
