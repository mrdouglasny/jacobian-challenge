# Gemini 3.1 Pro critique — `AX_pushforward_pullback`

**Model:** gemini-3.1-pro-preview
**Duration:** 42.6s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Note:** degree identity
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed discharge plan:

1. **Route classification:** **Incorrect.** You classified this as `provable-from-other-axioms`, but in Step 2 you propose to "introduce a small helper axiom" because `pushforwardOneForm` is currently opaque. Replacing one axiom with another is not a discharge—it is a refactor. The correct route is `blocked-by` (waiting for a `genuine-textbook` definition of the 1-form trace map and its API to be built) or `needs-infra`. 

2. **Effort:** **Uncalibrated.** If this plan requires actually defining the trace map and proving the 1-form projection formula from scratch, it is an Effort 9+ project involving complex local coordinate analysis and integration. If you are *only* doing the abstract nonsense in Steps 3 and 4 (pushing a 1-form identity through the `dualMap` and Jacobian quotient), it is an Effort 2 or 3. Your Effort 6 reflects a confused middle-ground that neither builds the theory nor properly delegates it.

3. **Proof recipe:** **Fatally flawed at Step 2.** You explicitly instruct the user to "Unfold `pushforwardOneForm` ... using its docstring's local description." This is a fundamental misunderstanding of formalization. Lean cannot "unfold" an `axiom`, and the kernel does not read docstrings. Because the underlying definition doesn't exist, the proposed 1-form identity (`pushforwardOneForm_apply_pullback`) cannot be proved. 
That said, the linear algebra in Step 3 and Step 4 is correct: because pullback/pushforward on the Jacobian are defined via the `dualMap` of the pushforward/pullback on 1-forms, the contravariance of `dualMap` perfectly aligns the composition order (`pushforwardAmbient ∘ pullbackAmbient` comes from `pullbackOneForm^* ∘ pushforwardOneForm^* = (pushforwardOneForm ∘ pullbackOneForm)^*`), and lifting the natural scalar multiplication via `jacobianHomOfAmbient_natSmul` is a standard, correct tactic. It just rests on a phantom foundation.

4. **Textbook citations:** Forster §17, Miranda VII §1, and Griffiths–Harris 2.1 are mathematically correct for the trace/projection formula, but they are irrelevant here until `pushforwardOneForm` is given a non-axiomatic definition in Lean.

5. **What's missing or wrong:**
   - **No docstring proofs:** You cannot execute a formal proof by citing a docstring description of an undefined map.
   - **No new axioms:** Proposing a "small helper axiom" violates the entire premise of discharging an axiom. If the project's gate script sees you delete one axiom and add another, the net progress is zero. 
   - **Dependency confusion:** The plan mentions the Kirov-side axiom `ambientPhi_ambientPsi_eq`. If that Kirov axiom logically implies your Step 2 without needing *new* axioms, the plan must explicitly state the exact `exact` or `rw` chain from the Kirov axiom. If it doesn't, this axiom is strictly blocked.

6. **Recommendation:** **Reject.** Rewrite the plan to either strictly reduce the Jacobian-level statement to the *already existing* Kirov roadmap axiom (with no new helpers), or mark it as explicitly blocked by the genuine formalization of the 1-form pushforward API.

VERDICT: reject — You cannot formally "unfold" an axiom's docstring, and replacing the target axiom with a new helper axiom is a can-kicking refactor, not a discharge.
