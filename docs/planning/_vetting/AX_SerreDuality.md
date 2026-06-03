# Gemini 3.1 Pro critique — `AX_SerreDuality`

**Model:** gemini-3.1-pro-preview
**Duration:** 32.3s
**Source axiom:** `Jacobians/Axioms/SerreDuality.lean`
**Note:** flag: mathlib-now but sheaf cohomology is missing infra
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan.

### 1. Route classification
**Wrong.** The plan classifies this as `genuine-textbook`, but the prompt heavily hints and the reality of Mathlib dictates that this is `needs-infra`. The plan itself admits that the "entire sheaf-cohomology / line-bundle layer" is missing, but it vastly understates the gravity of the missing pieces. This is not a matter of just applying a textbook proof to existing objects; you have to build the universe first.

### 2. Effort estimate
**Wildly uncalibrated.** The plan estimates an 8 (multi-month) and claims the recipe post-infra is "~150 LOC". This is a **10/10**. Even assuming you have a basic definition of Čech cohomology, proving Serre Duality on a Riemann surface requires immense functional analysis (Fréchet spaces, Montel spaces, Serre's lemma on compact operators) or heavy PDE theory (elliptic regularity, Hodge theory). The actual proof of non-degeneracy will be thousands of lines of Lean. 

### 3. Proof recipe
The recipe is a dangerous chimera of algebraic and analytic methods that hallucinates Mathlib capabilities:
* **Step 3 (The pairing):** You propose taking a Čech cocycle, multiplying by a partition of unity, taking the $\bar{\partial}$ derivative, and integrating the resulting 2-form over the manifold (`∫_X ∂̄η`). **Mathlib does not currently have integration of differential forms on manifolds, nor Stokes' theorem for them.** You cannot just write this down. Furthermore, by doing this, you are manually proving the Čech-Dolbeault isomorphism in the middle of your Serre duality proof.
* **Step 4 (Non-degeneracy):** You casually drop "surjective by Hahn–Banach" and "L² density". Forster's proof relies on equipping the space of Čech cochains with a Fréchet topology (arising from compact convergence of holomorphic functions), showing the coboundary map has closed range (using the finiteness of cohomology / Schwartz's theorem on compact perturbations), and then applying Hahn-Banach for locally convex spaces. The topological vector space structure on sheaf cohomology is a colossal prerequisite completely ignored here.
* **Step 1 (Derived Functors vs Čech):** You suggest we can just use derived functors. Mathlib's derived category API is highly abstract and currently completely disconnected from complex analytic sheaves or analytic topology.

### 4. Textbook citations
The citations (Forster Ch. II §17; Griffiths-Harris Ch. 1) are mathematically standard but dangerous for formalization context. They heavily rely on intuition for topological vector spaces and PDEs that must be rigorously and painfully spelled out in Lean. 

### 5. What's missing or wrong
* **Integration of Forms:** The plan relies on `∫_X` for differential forms, which doesn't exist in Mathlib.
* **Topology on Cohomology:** Serre Duality isn't just pure algebra. The duality pairs a Fréchet space with its topological dual. Because $H^1$ is finite-dimensional (Cartan-Serre), the topological dual coincides with the algebraic dual, but the *proof* goes through the topological dual and functional analysis. The plan treats this as a pure algebraic equivalence.
* **Finiteness:** You mention "finite-dimensionality of H¹... (Cartan-Serre)", treating it as a prerequisite you can just grab. Proving Cartan-Serre (or Theorem B for coordinate disks) is just as hard as Serre Duality and intertwined with the exact same functional analytic machinery.

### 6. Recommendation
**Reject.** The plan treats one of the deepest theorems in complex geometry as a routine 150-line algebraic exercise. It needs to be reclassified as `needs-infra`, upgraded to Effort 10, and rewritten to acknowledge the monumental blockers: integration of differential forms on manifolds, Fréchet space topologies on spaces of sections, and the topological proofs of finite-dimensionality.

VERDICT: reject — Reclassify as needs-infra, upgrade effort to 10, and rewrite to acknowledge the massive missing functional analysis and differential form integration prerequisites.
