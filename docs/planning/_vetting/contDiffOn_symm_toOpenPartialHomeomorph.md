# Gemini 3.1 Pro critique — `contDiffOn_symm_toOpenPartialHomeomorph`

**Model:** gemini-3.1-pro-preview
**Duration:** 118.8s
**Source axiom:** `Jacobians/GeneralResults/InverseFunctionTheorem.lean`
**Verdict:** **reject**

---

Here is a rigorous evaluation of the proposed discharge plan. 

### 1. Route classification
**Incorrect.** The route is classified as `mathlib-now`, but it should be **`revise`** (requiring a signature change). The axiom as stated is mathematically false, so no proof strategy will succeed without modifying the axiom or upstream definitions. 

### 2. Effort 1..10
**Uncalibrated.** The effort estimate of "1 focused day" is meaningless for a false statement. Fixing this requires modifying downstream consumers, changing the estimated scope.

### 3. Proof recipe
**Fatally flawed.** The proposed proof recipe attempts an impossible step. The statement binds `e := hf.toOpenPartialHomeomorph f hf' hn`. This exact local homeomorphism `e` is structurally fixed. You cannot "shrink the IFT radius into power-series radius" inside a tactic proof (as suggested in the comments of your first `sorry`). The `sorry` for `AnalyticAt ℂ f (e.symm y)` is fundamentally unprovable because `e.source` will generally contain points where $f$ is not analytic. 

### 4. Textbook citations
N/A

### 5. What's missing or wrong
- **The statement is mathematically false:** The function `ContDiffAt.toOpenPartialHomeomorph` delegates to `HasStrictFDerivAt.toOpenPartialHomeomorph`. The radius of `e.source` is determined entirely by the Lipschitz constant of $f - f'$ on a neighborhood of $a$. It is completely oblivious to the analyticity radius of $f$. A function can approximate a linear map on a large ball while being analytic only on a much smaller sub-ball (e.g., if $f$ continues as a non-differentiable Lipschitz function outside the analytic neighborhood). Thus, $f$ is not guaranteed to be analytic on `e.source`, meaning `e.symm` is not guaranteed to be analytic on the entirety of `e.target`.
- **Option (a) is logically broken:** You cannot propagate local analyticity at $a$ to all of `e.source` using `AnalyticAt.eventually_analyticAt`. That lemma only guarantees analyticity on *some* neighborhood of $a$, not on the exact radius selected by the IFT construction.
- **Option (b) is useless here:** Adding `OpenPartialHomeomorph.contDiffOn_symm` to Mathlib is mathematically sound and a good idea in a vacuum. However, you would not be able to apply it to discharge your axiom because satisfying its hypothesis requires exactly the false claim: `∀ y ∈ e.target, ContDiffAt ℂ ω f (e.symm y)`.
- **Ignoring your own risk triggers:** You explicitly identified the correct failure mode in your "Risk / escalation triggers" ("The IFT ball ... cannot be shrunk ... If true, the statement must be weakened"), but then wrote a tactic script acting as if the risk didn't exist. The risk is not just possible; it is guaranteed.

### 6. Recommendation
**Reject and Revise.** Do not attempt to prove this statement. You must revise the axiom signature. You have two valid mathematical choices:
1. **Weaken the conclusion:** Change the axiom conclusion to assert the existence of a smaller open subset of the target: `∃ V ⊆ e.target, IsOpen V ∧ f a ∈ V ∧ ContDiffOn ℂ ω e.symm V`. You will then need to update downstream consumers to extract and work with $V$.
2. **Needs-infra:** Define a custom `analyticToOpenPartialHomeomorph` function that explicitly takes the intersection of the IFT ball and the analyticity neighborhood, producing a genuinely analytic `OpenPartialHomeomorph`. Then restate the axiom to use this new definition instead of `hf.toOpenPartialHomeomorph`.

VERDICT: reject — The axiom is mathematically false because the radius of the local inverse constructed by `toOpenPartialHomeomorph` is not guaranteed to be contained within the analyticity neighborhood of $f$, requiring a signature change.
