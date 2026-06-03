# Gemini 3.1 Pro critique — `AX_pushforwardOneForm_id`

**Model:** gemini-3.1-pro-preview
**Duration:** 41.0s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **revise**

---

Here is a rigorous critique of the proposed discharge plan:

1. **Route classification**: **Incorrect.** This should be `needs-infra`. The proof is entirely blocked by the non-existent definition of `pushforwardOneForm` (the trace map for differentials). Constructing the trace map over a Riemann surface—handling the sum over preimages, local branches, and analytic continuation over the branch locus—is a massive piece of missing infrastructure, not merely a trivial dependency.

2. **Effort**: **3** is calibrated *only* for the task of proving this identity once the trace infrastructure is completely built and provides a computable fiber-sum API. 

3. **Proof recipe**:
   - **Steps 1–3 (The Trace Route)**: Mathematically sound and standard. If `pushforwardOneForm` is properly defined via the trace formula, computing it for $f = \text{id}$ degenerates to a single-term sum at the unramified point $q$, yielding $f_* \omega = \omega$. Applying `Finset.sum_singleton` along with `mfderiv_id` is the correct Lean strategy here.
   - **Step 4 (The Dual Route)**: **Mathematical nonsense.** The linear dual of the pullback of 1-forms $f^* : H^0(Y, \Omega^1) \to H^0(X, \Omega^1)$ is a map acting on the dual spaces: $(f^*)^* : H^0(X, \Omega^1)^* \to H^0(Y, \Omega^1)^*$. The pushforward (trace) of 1-forms acts on the spaces of forms themselves: $f_* : H^0(X, \Omega^1) \to H^0(Y, \Omega^1)$. These domains and codomains do not match. Without choosing a specific canonical pairing (like the Serre duality pairing $H^0 \times H^1 \to \mathbb{C}$ or an intersection product), there is no functorial isomorphism between the vector space of 1-forms and its dual. (Note: The dual of the pullback is what induces the *Albanese pushforward* on Jacobians, whereas the trace of 1-forms induces the *Picard pullback* on Jacobians).

4. **Textbook citations**: Missing. You should cite standard literature for the definition of the trace of a differential on a Riemann surface (e.g., Forster's *Lectures on Riemann Surfaces*, Section 17, or Miranda's *Algebraic Curves and Riemann Surfaces*, Chapter VI).

5. **What's missing or wrong**:
   - The route must reflect that this theorem is heavily blocked by a major infrastructure project (the actual `def` of the trace map).
   - Step 4 fundamentally confuses the trace map of differentials with the linear dual of the pullback. It must be completely removed.

6. **Recommendation**: Revise. Update the route to `needs-infra`, ensure the dependency on the highly non-trivial `pushforwardOneForm` definition is heavily emphasized, and purge the invalid dualization alternative.

VERDICT: revise — Change route to needs-infra and completely delete the mathematically invalid Step 4, which confuses the trace of 1-forms with the linear dual of the pullback.
