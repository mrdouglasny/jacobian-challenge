# Gemini 3.1 Pro critique — `AX_pullbackAmbient_preserves_lattice`

**Model:** gemini-3.1-pro-preview
**Duration:** 124.3s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan:

1. **Route classification**
   **Incorrect.** This is firmly **`needs-infra`** (or at best `kicks-the-can` to a new axiom). The recipe claims `provable-from-other-axioms`, but you cannot bypass the need for the homological transfer map infra. If you try to prove it via axioms, you will find you are missing the integral trace axiom linking homology pullback and 1-form pushforward. 

2. **Effort 1..10**
   **Badly uncalibrated (Score: 9+).** A 7 assumes the pieces easily snap together. If you take the textbook geometric route, formalizing the transfer/trace map on singular homology for finite branched covers and proving its integration duality with 1-forms is a massive, highly technical undertaking in Mathlib. 

3. **Proof recipe**
   The recipe contains severe logical gaps and a fatal circularity:
   * **Fatal Circularity in Step 2:** The "pragmatic alternative" tries to define `pullbackH1` by composing `(periodMap X)⁻¹` with `pullbackAmbientLinear`. However, the period map is an isomorphism from $H_1(X, \mathbb{Z})$ strictly to the *period lattice* $\Lambda_X \subset \mathbb{C}^g$. Its inverse is only well-defined (or only lands in integral homology) if the output of `pullbackAmbientLinear` is *already known* to land in $\Lambda_X$. That is literally the axiom you are trying to prove! You cannot assume the axiom to define the helper map you need to discharge the axiom.
   * **Trace Identity Hallucination in Step 3:** For the geometric branched-cover route, you claim the trace identity $\int_{f^* \gamma} \omega = \int_\gamma f_* \omega$ "follows from the definition of pullbackH1". This is impossible. As you noted, `pushforwardOneForm` is an opaque axiom. You cannot prove a theorem about how an axiomatic function behaves under integration without an axiom explicitly giving you that integration behavior. 
   * **Missing Constant Map Case:** The axiom signature applies to *any* continuous manifold map $f$. The geometric route assumes $f$ is a finite branched cover (which requires a non-constant holomorphic map). The recipe completely forgets that $f$ can be constant. (If $f$ is constant, $f_* = 0$, so `pullbackAmbientLinear` is the zero map, which trivially preserves the lattice, but this requires an explicit case split).

4. **Textbook citations**
   Mumford and Griffiths-Harris are the correct mathematical references for homological transfer and the trace of 1-forms, but they don't solve the formalization circularity or the missing axioms in your Lean environment.

5. **What's missing or wrong**
   * The "pragmatic alternative" is a textbook circular dependency and must be scrapped entirely.
   * The proof blindly assumes that finite branched covers apply to all maps, missing the constant map case split.
   * The recipe hallucinates the ability to prove a trace integral identity for an axiomatic definition (`pushforwardOneForm`) that lacks any integral axioms. 

6. **Recommendation**
   **Reject.** 
   *Alternative Proposal:* You must split the proof into constant vs. non-constant maps. For the non-constant case, you cannot discharge this without either (A) genuinely formalizing the homology transfer map and the definition of `pushforwardOneForm` (`needs-infra`), OR (B) introducing a new, explicit helper axiom `AX_pushforwardOneForm_integral_trace` that directly postulates $\int_{f^* \gamma} \omega = \int_\gamma f_* \omega$, replacing this lattice axiom with the trace identity axiom.

VERDICT: reject — The recipe contains a logically circular "pragmatic" definition, ignores constant maps, and falsely assumes it can prove the integral trace identity for an unaxiomatized axiomatic pushforward form.
