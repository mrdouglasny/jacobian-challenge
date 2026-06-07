> **✅ DISCHARGED — de-opaqued to a real `def`.** This opaque axiom is now a concrete `noncomputable def` (`Jacobians/Axioms/AbelJacobiMap.lean`); this plan is retained as a historical record of the route, not active work. Canonical status: `AXIOM_AUDIT.md` → "Recently discharged".

# Gemini 3.1 Pro critique — `pathIntegralBasepointFunctional`

**Model:** gemini-3.1-pro-preview
**Duration:** 35.8s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **reject**

---

Here is a rigorous referee critique of the proposed discharge plan.

### 1. Route classification
The classification **needs-infra** is correct in spirit, but the plan presents a schizophrenic approach. "Route A" is not a discharge at all—it is an axiom-shuffling refactor. "Route B" is the genuine **needs-infra** route, as it requires building the actual partition and integration machinery for 1-forms on manifolds.

### 2. Effort estimate
The effort estimate (8) and timeline (3–4 weeks) are **wildly optimistic for Route B as stated**. Smoothing an arbitrary continuous path on a manifold into a piecewise analytic one (Step 3d) is a monumental formalization task that involves heavy partition-of-unity or polygonal approximation machinery. If you attempt Route B using the plan's exact steps, you will be stuck for months. However, if you fix the mathematical approach in Step 3d (see below), the effort drops back to a realistic 8.

### 3. Proof recipe
- **Kicking the can:** Route A is completely unacceptable as a "discharge" plan. The prompt explicitly warns against kicking the can, and Route A literally boasts that it will *raise* the axiom count from 1 to 6. Swapping one axiom for six deferred `bridgePath*` axioms is a shell game, not a proof.
- **The Formalization Trap (Step 3d):** Route B proposes taking Mathlib's `PathConnectedSpace.somePath` (which yields a purely continuous path) and performing a "chart-local smoothing argument." This is a classic beginner's trap in formalizing differential geometry. You do not want to mollify or smooth arbitrary continuous paths in Lean.
- **The Correct Approach for 3d:** You bypass continuous paths entirely. You define the set of points $E = \{ x \in X \mid \exists \text{ piecewise analytic path from } P_0 \text{ to } x \}$. 
  1. $E$ is non-empty ($P_0 \in E$).
  2. $E$ is open: For any $x \in E$, taking a chart around $x$ gives a neighborhood homeomorphic to an open ball in $\mathbb{C}$. Open balls are convex, so any $y$ in the chart can be connected to $x$ by a straight, analytic line segment. Concatenating paths shows the whole neighborhood is in $E$.
  3. $E$ is closed: If $x \in \overline{E}$, the chart around $x$ intersects $E$ at some point $y$. Connect $y$ to $x$ via a straight line in the chart.
  Since $X$ is connected, $E = X$. This elegant, standard topological proof gives you your piecewise analytic path *directly*, with zero smoothing required.

### 4. Textbook citations
**Completely missing.** A plan of this magnitude needs a rock-solid mathematical reference. You should be citing standard Riemann surface texts that explicitly construct path integration via chart-refinement and cocycle conditions, such as:
- **Forster, *Lectures on Riemann Surfaces*** (Chapter 1, §9 on integration of 1-forms).
- **Donaldson, *Riemann Surfaces***. 

### 5. What's missing or wrong
- **No commitment to a real proof:** Offering Route A as "preferred" undermines the entire point of the project. Axiom discharge means the logic grounds out in Mathlib, not in a Kirov vendor prototype guarded by 6 more axioms.
- **Naïve path connectivity:** As detailed above, Step 3d will fail practically in Lean 4. The open/closed set argument is mandatory here to keep the sorry-budget bounded.
- **Cocycle independence details:** Step 3b waves away cover-independence with "chain rule + cocycle identity." You must explicitly account for the fact that chart overlaps might not be connected, meaning the integrals could technically differ by constants on different connected components of the overlap unless you refine your partition to be subordinate to a suitably fine cover (e.g., Lebesgue number lemma on the parameter interval).
- **Typeclass anomalies:** `[IsManifold 𝓘(ℂ) ω X]` is not standard Mathlib v4.30 syntax. You should be using `[ChartedSpace ℂ X] [HasGroupoid X (contDiffGroupoid ℂ ⊤)]` (or the holomorphic equivalent) to ensure compatibility with standard Mathlib manifold infra.

### 6. Recommendation
**Reject.** The plan must be revised to completely scrap Route A. Route B must become the sole plan, and Step 3d must be rewritten to use the open/closed connectedness argument rather than attempting to smooth `PathConnectedSpace.somePath`. Additionally, add proper textbook citations for the integration construction.

VERDICT: reject — The preferred Route A is an unacceptable can-kicking exercise that increases the axiom count, while Route B relies on a mathematically naive and formally nightmarish continuous-path smoothing argument instead of the standard open/closed set connectivity proof.
