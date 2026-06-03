# Gemini 3.1 Pro critique — `pushforwardOneForm`

**Model:** gemini-3.1-pro-preview
**Duration:** 34.6s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed discharge plan.

### 1. Route Classification
**Correct, but incomplete.** This is indeed a `genuine-textbook` theorem, but it heavily leans into `needs-infra`. A formalization of the trace of differentials requires significant infrastructure that Mathlib currently lacks: finite unramified covering spaces, symmetric products of local analytic functions, and a robust Riemann removable singularity theorem on manifolds. 

### 2. Effort Estimate
**Wildly uncalibrated.** The estimate of "3–4 weeks, 500–800 LOC" is a hallucination. Formalizing the trace map, proving it is holomorphic across the branch locus, and dealing with the local Puiseux-series/roots-of-unity cancellations required to prove the singularity is removable is a massive undertaking. This is an **Effort 10** project that will likely require 3,000+ LOC and months of dedicated work. 

### 3. Proof Recipe & Logical Gaps
The proposed mathematical recipe contains catastrophic flaws:

* **Discontinuous unramified definition:** The definition of `pushforwardOneForm.coeff_unramified` filters the sum by `localOrder f p q = 1` globally across $Y$. As $q$ approaches a branch value, preimages coalesce and their `localOrder` jumps to $k > 1$. By filtering them out, the terms simply vanish from the sum, resulting in a function that is **discontinuous** at the branch locus! You cannot apply Riemann's removable singularity theorem to a function that drops terms and jumps at the singularity. You must define the trace strictly on the open set $Y \setminus B$ (where $f$ is a local homeomorphism and the fiber size is locally constant), and then define the extension to $B$ via limits or topological closure.
* **The core algebraic argument is missing:** The recipe says "the trace is bounded because the singularity contributions from the colliding sheets cancel" but completely ignores *how* to prove this. Locally, $f$ looks like $z \mapsto z^k = w$. The inverse branches are $w^{1/k} \zeta^j$. Pulling back a form $g(z)dz$ involves taking the derivative of the inverse, yielding terms with fractional powers of $w$. To prove the singularity is removable, you must prove that summing over the roots of unity $\zeta$ causes all negative fractional powers of $w$ to algebraically cancel out (Newton sums / symmetric polynomials). The plan provides zero infrastructure for this Galois-theoretic local argument, which is the entire mathematical substance of the textbook proof.
* **The "Alternative route" is mathematically nonsensical:** The plan suggests defining pushforward by dualizing the pullback map $f^* : \Omega^1(Y) \to \Omega^1(X)$. The dual of the pullback is a map $(f^*)^* : \Omega^1(X)^* \to \Omega^1(Y)^*$. The plan claims that reflexivity ($V \simeq V^{**}$) allows you to turn this into a map $\Omega^1(X) \to \Omega^1(Y)$. This is a severe misunderstanding of linear algebra. Reflexivity gives an isomorphism to the *second* dual, not the first dual. To identify $\Omega^1(X)$ with $\Omega^1(X)^*$ you would need a non-degenerate bilinear pairing (e.g., Serre Duality or a Hodge inner product), which does not exist in the purely holomorphic algebraic category without conjugation.

### 4. Textbook Citations
The citations (Forster §17, Griffiths-Harris p. 137, Mumford) are precisely the correct references for the trace of meromorphic/holomorphic differentials.

### 5. What's Missing or Wrong (Specifics)
* **`Finset.sum` vs `tsum`:** Using `∑'` (`tsum`) for a sum over a finite fiber is analytically painful because you must prove summability everywhere. You should obtain the finite fiber $f^{-1}(q)$ as a `Finset` from `AX_BranchLocus` and use `Finset.sum`.
* **Analytic Continuation API:** The plan states "The Lean realisation uses `AnalyticOn.continuous_extension`". Mathlib does not currently have an out-of-the-box theorem that takes a holomorphic function on a punctured disk, proves it is bounded, and returns the extended holomorphic function. This removable singularity API must be built from scratch.
* **Derivatives of local inverses:** Writing `deriv (locInv f p) w` assumes `locInv` is a well-defined function. On a Riemann surface, local inverses on overlapping charts require tracking branch cuts. It is much safer to define the trace locally via symmetric functions of the coordinates of the preimages rather than picking explicit inverse functions.

### 6. Recommendation
**Reject.** The piecewise definition is mathematically flawed, the LOC/effort estimate is completely divorced from reality, the central algebraic cancellation argument for the removable singularity is ignored, and the alternative duality route relies on a fundamental linear algebra error. 

VERDICT: reject — The piecewise definition is discontinuous at branch values, the plan ignores the required roots-of-unity cancellation (Newton sums) for the removable singularity, and the alternative duality route is mathematically nonsensical since vector spaces are not canonically isomorphic to their first duals.
