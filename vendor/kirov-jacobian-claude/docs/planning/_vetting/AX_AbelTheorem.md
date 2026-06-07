# Gemini 3.1 Pro critique — `AX_AbelTheorem`

**Model:** gemini-3.1-pro-preview
**Duration:** 78.0s
**Source axiom:** `Jacobians/Axioms/AbelTheorem.lean`
**Note:** keystone
**Verdict:** **revise**

---

Here is a rigorous referee critique of the proposed axiom-discharge plan:

1. **Route classification**: The plan claims `genuine-textbook`, which is true for the final assembly. However, given that it requires building out meromorphic 1-forms and the residue theorem from scratch, this heavily `needs-infra`. The proof also operates by reducing to four other major axioms (`AX_RiemannRoch`, `AX_SerreDuality`, `AX_RiemannBilinear`, `AX_AnalyticCycleBasis`), meaning structurally it acts as `provable-from-other-axioms`. 

2. **Effort 1..10**: The effort level 8 is accurate, but the **LOC estimate (2000–3000) is a massive underestimation**. The claim that the residue theorem on a compact Riemann surface is a "50-LOC corollary" of Stokes' theorem is a formalization fantasy. Mathlib currently lacks integration over manifolds with boundaries, limit theorems for shrinking tubular neighborhoods (cutting out disks around poles), and consistent orientation tracking. Building `Residues.lean` alone will likely consume 3000+ LOC.

3. **Proof recipe**: There are several glaring mathematical and logical errors that must be fixed:
   * **Basepoint suicide (Step 5)**: `P₀` is defined via `Classical.arbitrary X`. If `P₀ ∈ supp(D)`, it is a pole of the 3rd-kind differential `ω̃_D`. The integral $\int_{P_0}^P \tilde{\omega}_D$ will diverge, failing to yield a valid meromorphic function. You must explicitly choose a basepoint $P_0 \notin \text{supp}(D)$.
   * **Period algebra failures (Steps 2 & 4)**: The plan claims you need "purely imaginary periods (so that exp is single-valued)". This is strictly false: $e^{i\pi} = -1 \neq 1$. You need periods to be integer multiples of $2\pi i$ (i.e., strictly in $2\pi i \mathbb{Z}$). Furthermore, Step 4 refers to "real periods"—a nonsense term in this context. The author means **A-periods** (integrals over the $a_j$ homology cycles).
   * **Missing Reciprocity (Step 1)**: Step 1(c) claims that evaluating `u(div f)` is easy because "pairing [holomorphic forms] against `dlog f` modulo the period lattice yields zero." You cannot just trivially "pair" them. Equating the integral of a holomorphic form over a divisor boundary to the periods of `dlog f` requires the **Reciprocity Law** for differentials of the 1st and 3rd kind. This means Step 1 fundamentally depends on `AX_RiemannBilinear`, which is missing from the Step 1 recipe.

4. **Textbook citations**: Forster §21 is the correct gold-standard reference for this approach. However, the author clearly skimmed §21.6–21.8, leading to the confusion between normalizing A-periods to zero and "real periods".

5. **What's missing or wrong**: 
   * The dependency of Step 1 (`⊇`) on `AX_RiemannBilinear` is missing.
   * Basepoint selection logic for `f(P)` integration is mathematically broken.
   * Definitions of periods required for $f(P)$ to be well-defined are algebraically wrong.
   * The "discrete deliverable" difficulty for the residue theorem is completely uncalibrated for Lean 4's current manifold capabilities.

6. **Recommendation**: Revise. The Forster route is viable, but the author must correct the period algebra (using A-periods and $2\pi i \mathbb{Z}$), fix the basepoint logic to avoid poles, add the Bilinear dependency for the $\supseteq$ direction, and completely rework the LOC expectations for the required manifold-integration infrastructure.

VERDICT: revise — Fix the mathematical errors regarding periods ("purely imaginary" vs $2\pi i \mathbb{Z}$, "real periods" vs A-periods), properly cite Bilinear Relations for Step 1, handle the basepoint avoiding poles, and radically correct the 50-LOC estimate for the residue theorem.
