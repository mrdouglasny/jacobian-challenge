# Gemini 3.1 Pro critique — `AX_RiemannRoch`

**Model:** gemini-3.1-pro-preview
**Duration:** 40.0s
**Source axiom:** `Jacobians/Axioms/RiemannRoch.lean`
**Note:** keystone
**Verdict:** **reject**

---

An evaluation of the proposed axiom-discharge plan for `AX_RiemannRoch`:

**1. Route classification**
Incorrect. You classified this as `genuine-textbook`, but in Step 5 you explicitly rely on `AX_SerreDuality`. If a proof simply reduces one axiom to another axiom, the route is mathematically `provable-from-other-axioms`. Furthermore, because Mathlib completely lacks the required sheaf cohomology, exact sequences, and finiteness theorems, the foundational prerequisites are aggressively `needs-infra`.

**2. Effort 1..10 & Calibration**
The effort score of 10 is correct, but your estimate of "2000–4000 LOC including the sheaf-cohomology layer" is laughably naive. Proving Serre's finiteness theorem analytically (Forster Ch. 14, as you suggested) requires a massive functional analysis library: Fréchet spaces, Montel spaces, the open mapping theorem for Fréchet spaces, and Schwartz's theorem on compact perturbations of the identity. Building that, plus the Čech cohomology API and Leray's theorem, is easily a 15,000+ LOC multi-year undertaking, not a ~6 month job.

**3. Proof recipe**
- **Logical gaps & Čech LES:** In Step 3, you casually assert the existence of a long exact cohomology sequence. If you are using Čech cohomology (as you propose in Step 1), it is a standard textbook warning that a short exact sequence of sheaves does *not* yield a long exact sequence of Čech cohomology in general. You must either take the direct limit over all covers (and prove exactness of the limit for paracompact spaces) or formalized Leray's theorem to show Čech agrees with derived functor cohomology. You glossed over a historically infamous topological trap.
- **Kicking the can:** Step 5 explicitly uses `AX_SerreDuality` to compute the base case `χ(0) = 1 - g`. You are not fully discharging the keystone axiom; you are shifting the heaviest part of the burden to another axiom.
- **Typeclass issues:** You propose dropping `[_h0fd]` and `[_h1fd]` once Serre Finiteness is proven. Because Serre Finiteness is so distant, you will be stuck with these typeclass assumptions for a very long time. Your plan doesn't account for how the intermediate API will handle these floating assumptions before Step 2 lands.

**4. Textbook citations**
Forster and Miranda are the correct standard references. However, Forster's analytic route is extremely heavy on functional analysis, and Miranda's algebraic route requires a deep scheme-theoretic or algebraic curves library. Both require foundations Mathlib does not currently possess for complex manifolds. 

**5. What's missing or wrong**
Bundling Serre Finiteness, general Sheaf Cohomology, and Riemann-Roch into a single discharge plan completely obscures the critical path. The Euler-characteristic induction (Step 4) is relatively trivial *if* you have the cohomology machinery. The plan fails to separate the easy algebraic bookkeeping of the Euler characteristic from the brutally difficult analytic geometry required to make the symbols `H⁰` and `H¹` behave as required.

**6. Recommendation**
Reject. You must split this monolithic plan. Reclassify `AX_RiemannRoch` as `provable-from-other-axioms`. The plan should *only* cover the Euler characteristic induction (Steps 3, 4, and 6), explicitly taking Serre Finiteness, the Long Exact Sequence, and `AX_SerreDuality` as assumed axiomatic prerequisites. Then, write separate, dedicated `needs-infra` plans for Sheaf Cohomology/LES and Serre Finiteness. 

VERDICT: reject — The plan falsely claims a genuine-textbook discharge while explicitly relying on another axiom (`AX_SerreDuality`) and severely underestimates the immense functional analysis and sheaf theory infrastructure required.
