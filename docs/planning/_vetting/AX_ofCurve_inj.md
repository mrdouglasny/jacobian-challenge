> **✅ DISCHARGED — 2026-06-05.** This axiom is now a proved theorem; this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# Gemini 3.1 Pro critique — `AX_ofCurve_inj`

**Model:** gemini-3.1-pro-preview
**Duration:** 116.1s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan.

### 1. Route classification
**Incorrect as proposed.** The roadmap rightly classifies this as `genuine-textbook`, but your recipe treats it as `provable-from-other-axioms` by attempting to bypass the actual mathematical content of Abel's theorem. To execute a genuine textbook proof, the route must be classified as **`needs-infra`**, because the project currently lacks the required analytic machinery (meromorphic differentials of the third kind) or cohomological machinery (the exponential sheaf sequence) needed to bridge the gap between analytic periods and principal divisors.

### 2. Effort 1..10
**Uncalibrated for the sub-steps.** While an overall Effort 9 is accurate for a complete proof of Abel's theorem from scratch, the estimate of "2–3 weeks" for sub-step 6 is pure fantasy. The proposed "abstract Abel injectivity" lemma is mathematically unprovable from `AX_RiemannBilinear` alone. 

### 3. Proof recipe
The logic is completely broken and hallucinates a trivial proof of a deep theorem. 
*   **Gap 1 (Topology):** In Step 2, you define $c = [Q \longrightarrow P] - \gamma$ and repeatedly call it a "closed cycle." It is not. If $P \neq Q$, $c$ is an open 1-chain with boundary $\partial c = P - Q$.
*   **Gap 2 (Bilinear Relations):** In Step 3, you claim `AX_RiemannBilinear` will "kill the closed cycle." Riemann's bilinear relations (specifically, the non-degeneracy of the period matrix) apply *only* to closed cycles (elements of $H_1(X, \mathbb{Z})$). You cannot apply them to an open chain. 
*   **Gap 3 (The Grand Canyon):** In Step 3, you casually assert: *"From step 3 the divisor $D = P - Q$ is principal (linearly equivalent to zero) via a meromorphic function $g$."* **This is exactly Abel's Theorem, and you are assuming it without proof.** `AX_RiemannBilinear` (which only talks about holomorphic forms) does not magically conjure a meromorphic function out of thin air. 
*   **Gap 4 (Logical contradiction):** If $c$ actually *were* a closed cycle that is null-homologous, it would imply $P = Q$ immediately without ever needing Riemann–Roch (Step 4). The fact that you invoke Riemann–Roch to finish the proof shows a fundamental confusion about what proving $P=Q$ entails.

### 4. Textbook citations
You cited the correct textbooks (Forster §21, Griffiths–Harris 2.7) but **completely misread their proofs**. For example, Griffiths & Harris (pp. 235–236) do *not* apply Riemann's bilinear relations to holomorphic forms to deduce Abel's theorem. They apply the generalized bilinear relations (reciprocity) to a meromorphic differential of the **third kind** (a differential $\omega_{P,Q}$ with simple poles at $P$ and $Q$). Your recipe entirely omits third-kind differentials.

### 5. What's missing or wrong
*   **The construction of the meromorphic function is missing.** To prove that $\int_Q^P \omega \equiv 0$ implies $P-Q$ is principal, you cannot just do linear algebra on the period matrix of holomorphic 1-forms. You must construct $g$ explicitly.
*   **Missing infrastructure:** You either need the analytic route (construct a third-kind differential $\omega_{P,Q}$ and apply reciprocity laws) or the cohomological route (use the exponential exact sequence $0 \to \underline{\mathbb{Z}} \to \mathcal{O}_X \to \mathcal{O}_X^* \to 0$ to relate the analytic Jacobian $H^1(\mathcal{O}) / H^1(\mathbb{Z})$ to $\text{Pic}^0(X)$).
*   **The core deliverable is a dead end.** The lemma `ofCurveImpl_injective_of_no_principal_diff` (Step 6) cannot be proven using `AX_RiemannBilinear`. The proof will fail.

### 6. Recommendation
**Reject.** Throw out Steps 1–3 of the recipe. Re-read Griffiths-Harris or Forster and write a new plan that explicitly accounts for the construction of the meromorphic function, likely by adding infrastructure for differentials of the third kind or the exponential sheaf sequence.

VERDICT: reject — The proof recipe hallucinates a trivial proof of Abel's theorem by confusing open 1-chains with closed 1-cycles and falsely claiming that Riemann's bilinear relations for holomorphic forms imply the existence of a meromorphic function.
