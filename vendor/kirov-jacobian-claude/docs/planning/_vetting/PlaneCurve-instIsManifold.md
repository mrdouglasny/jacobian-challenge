# Gemini 3.1 Pro critique — `PlaneCurve-instIsManifold`

**Model:** gemini-3.1-pro-preview
**Duration:** 48.6s
**Source axiom:** `Jacobians/ProjectiveCurve/PlaneCurve.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed discharge plan for `PlaneCurve.instIsManifold`.

### 1. Route Classification
**Incorrect in spirit.** While `needs-infra` is technically true, the plan treats the cross-summand transition maps as a triviality that can be deferred. In reality, proving the analyticity of these transition maps *is* the entire mathematical content of this axiom. The route should be deeply tied to Mathlib's Implicit Function Theorem (IFT) infrastructure. 

### 2. Effort
**Poorly calibrated (Underestimated).** The estimate of 7 assumes that the 6 cross-summand transitions can just be left as new axioms. If you actually prove them—which you must—the effort is at least an **8** or **9**. Connecting abstract IFT inverses across projective coordinate charts for arbitrary degree $d$ in Lean is highly non-trivial. 

### 3. Proof Recipe
**Unacceptable. This is a textbook example of kicking the can down the road.**
* **Axiom proliferation:** The recipe explicitly states it will "admit each cross-summand as a bounded sub-axiom if necessary" and then bafflingly claims "the 1 axiom dropped equals the ≤ 6 new bounded... net axiom-count change... ≤ 0". Replacing 1 axiom with up to 6 new axioms is an *increase* of 5 axioms. This is not a discharge plan; it is an axiom-renaming plan.
* **Mathematical impossibility:** The plan states under Stage 2 that it will use "explicit chart formula + `Inv.contDiffOn`". Under "Risks", it mentions that the implicit function inverse might not be written in elementary form. This is not a *risk*; it is a **mathematical certainty**. By the Abel-Ruffini theorem, you cannot write closed-form chart inverses for a general plane curve of degree $d \geq 5$. The "fallback" plan (routing through `ContDiffAt.toOpenPartialHomeomorph` and abstract analyticity) is the **only** mathematically valid approach and must be the primary, detailed strategy.

### 4. Textbook Citations
**Missing.** You need a standard reference for the Riemann surface structure of a plane curve to justify the abstract coordinate transitions. Miranda's *Algebraic Curves and Riemann Surfaces* (Chapter II.1) or Forster's *Lectures on Riemann Surfaces* (Section 3) should be cited to guide the formalization of the transition maps via the holomorphic Implicit Function Theorem.

### 5. What's Missing or Wrong
* **Stage 1 / Stage 2 split is invalid:** A discharge plan must completely close the axiom loop. You cannot stage-gate the hard part (the 6 cross-summand lemmas) into future sub-axioms. 
* **Analyticity vs Smoothness:** The axiom claims `IsManifold 𝓘(ℂ, ℂ) ω` (analytic manifold). Mathlib's IFT API is heavily skewed towards `ContDiff ∞` (smooth). You must verify and explicitly state how you will bridge the gap to `ω` (e.g., using complex differentiability to imply analyticity), as Mathlib's support for `ContDiffOn ℂ ω` is much sparser than for the real smooth case.
* **Ambient space transitions:** The plan needs to explicitly state how the projective transition maps (e.g., $(x, y) \mapsto (1/x, y/x)$) are composed with the abstract IFT partial homeomorphisms, including verifying that the denominators do not vanish on the overlaps of the specific domains.

### 6. Recommendation
**Reject.** The plan evades the actual mathematical difficulty by spawning new axioms, relies on a primary proof strategy (closed-form inverses) that is impossible for general degree $d$, and fails to detail how Mathlib's abstract IFT will be used for the transition maps. 

VERDICT: reject — The plan kicks the can down the road by replacing one axiom with up to six new ones, and its primary strategy assumes closed-form inverses that are mathematically impossible for general curves of degree $d \geq 5$.
