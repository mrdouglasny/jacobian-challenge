# Gemini 3.1 Pro critique — `AX_Elliptic_H1_symplectic`

**Model:** gemini-3.1-pro-preview
**Duration:** 63.8s
**Source axiom:** `Jacobians/ProjectiveCurve/Elliptic/Witnesses.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan.

### 1. Route classification
**Incorrect.** The plan classifies this as `needs-infra`, but proposes "computing" a value for `intersectionForm`—which the plan itself acknowledges is an axiom. You cannot computationally evaluate an uninterpreted axiom. 
To actually discharge this axiom today, the route must be a hybrid: `needs-infra` for the `H_1` basis property (which can be built), and `provable-from-other-axioms` for the symplectic condition (which requires introducing a tightly scoped helper axiom).

### 2. Effort 1..10
**Uncalibrated due to ambiguity.** The estimate of Effort 7 (~3–6 weeks) is accurate *only* for the covering space and fundamental group component (Phase 1, Steps 1 & 2). 
If the author implicitly intends to fully define `intersectionForm` for arbitrary Riemann surfaces so that it becomes computable (Phase 1, Step 3), the estimate is a fantasy. That is an Effort 10 (>1 year) undertaking requiring singular homology, cup products, Poincaré duality, and orientability of manifolds, none of which exist in Mathlib yet. 

### 3. Proof recipe
- **Fatal logical gap in Step 7:** The recipe claims that `intersectionForm 0 (A-class) (B-class) = 1` will be derived via an "explicit sign computation from step 3." Because the global `intersectionForm` is an opaque axiom, it has no definitional equations. No computation is possible. In Lean, you cannot `#eval`, `rw`, or `simp` an axiomatic function into the number `1`. This step is impossible as written.
- **Vague Homology Layer (Steps 1 & 2):** The plan relies on a nonexistent `H1` without specifying how it will be defined. If `H1` is also an axiom, you won't be able to prove the `isBasis` field either. You must explicitly define `H1 X x₀ := Abelianization (FundamentalGroup X x₀)`. Mathlib already has `FundamentalGroup` and covering space theory (`Mathlib.Topology.Covering`); this makes Phase 1 genuinely feasible without waiting for singular homology. 
- **Correct use of Alternating Axiom (Step 7):** Using `AX_IntersectionForm_alternating` to prove `⟨A, A⟩ = 0` and `⟨B, B⟩ = 0` is formally correct and good practice.

### 4. Textbook citations
Griffiths–Harris (Ch 0.4) and Mumford are canonically correct mathematical references for the period matrix and intersection signs. However, they are completely irrelevant for solving the formalization problem of how to bypass an uninterpreted function in Lean 4. 

### 5. What's missing or wrong
- **Conflating math with formalization:** The author confuses a mathematical calculation (drawing two curves on a torus and counting intersections) with a formal reduction in Lean (evaluating a function). 
- **All-or-nothing trap:** The plan fails to isolate the algebraic topology we *can* formalize today (the fact that the A and B loops form a basis of $\pi_1$, via covering spaces) from the algebraic topology we *cannot* (the intersection product on a surface). 
- **No definition of H1:** Kicking the can to an undefined "homology layer" without specifying the `Abelianization (FundamentalGroup _)` workaround guarantees this ticket will rot in the backlog.

### 6. Recommendation
**Reject.** The proposed computation on the intersection form is formally impossible. 

**Alternative plan to enforce:**
1. Define `H1 X x₀` directly as `Abelianization (FundamentalGroup X x₀)`. 
2. Use Mathlib's covering space API to genuinely prove the `isBasis` field for `aLoop` and `bLoop`. 
3. Explicitly introduce a narrowly scoped helper axiom `axiom AX_Elliptic_intersection_A_B : intersectionForm _ _ (A-class) (B-class) = 1`. 
4. Use this helper axiom alongside `AX_IntersectionForm_alternating` to populate the `symplectic` field of `AnalyticCycleBasis`.

This alternative destroys the monolithic structure axiom, replaces the basis requirement with real Lean code, and neatly corners the missing topology into a single, highly specific integer equality.

VERDICT: reject — The plan proposes an impossible "computation" on the opaque `intersectionForm` axiom; it must be revised to genuinely construct the basis via fundamental groups while explicitly introducing a helper axiom for the A/B intersection number.
