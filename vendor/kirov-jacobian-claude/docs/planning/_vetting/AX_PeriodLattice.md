# Gemini 3.1 Pro critique — `AX_PeriodLattice`

**Model:** gemini-3.1-pro-preview
**Duration:** 73.8s
**Source axiom:** `Jacobians/Axioms/PeriodLattice.lean`
**Verdict:** **accept**

---

This is a remarkably well-thought-out and mature formalization plan. It correctly identifies the mathematical pathway (evaluating the period map on a symplectic basis to yield the standard $I$ and $\tau$ blocks) and perfectly translates it into the Lean/Mathlib API. 

Here is a detailed breakdown of the critique:

1. **Route classification**: Correct (`provable-from-other-axioms`). The classical period lattice theorem is fundamentally the assertion that the Riemann bilinear relations guarantee the linear independence of the period vectors over $\mathbb{R}$, allowing one to construct a full $\mathbb{Z}$-lattice.

2. **Effort**: 4 is well-calibrated (maybe slightly conservative, but safe). Working with `restrictScalars`, `Complex.re`/`im`, dual bases, and `ContinuousLinearEquiv` transports in Mathlib can often lead to "motive is not type correct" or defeq-leaking headaches, so setting aside 3–5 days to fight the typechecker on the matrix/basis manipulations is a very realistic estimate.

3. **Proof recipe**: 
   - **Steps 1–3** are structurally perfect. Evaluating the normalized basis to get $e_i$ and the rows of $\tau$ is the standard textbook approach.
   - **Step 4** correctly zeroes in on how positive-definiteness of $\Im \tau$ over $\mathbb{R}$ forces $\mathbb{R}$-linear independence. In Mathlib, `PosDef M` means $x^T M x > 0$ for $x \neq 0$. Your derivation $c \cdot \Im \tau = 0 \implies c^T (\Im \tau) c = 0 \implies c = 0$ translates flawlessly. (Just be mindful of row vs. column multiplication conventions in `Matrix.mulVec` vs `Matrix.vecMul`, but mathematically it is trivial).
   - **Step 6 & 7** brilliantly utilize the recent `IsZLattice` API (`Zspan.isZLattice` / `instIsZLatticeRealSpan`). 
   - **Step 8** correctly diagnoses the need for a transport instance along a `ContinuousLinearEquiv`. Note: if Mathlib's `instIsZLatticeComap` gives you trouble going *forward* (via `Submodule.map`), you can trivially cast your `map` as a `comap` of the inverse (`M.symm`), or manually transport `span = ⊤` (via `LinearEquiv.map_span`) and `DiscreteTopology` (via `Homeomorph.discreteTopology`).

4. **Textbook citations**: Excellent. Mumford's *Tata Lectures on Theta I* and Griffiths–Harris Chapter 2 are the gold standards for exactly this construction (specifically extracting the $2g$ independent real vectors from the $\tau$ matrix).

5. **What's missing or wrong**: 
   There are no logical gaps. The only minor technicality is ensuring that the action of the change-of-basis matrix $M$ is applied correctly depending on whether Lean expects the matrix to act on the left or the right of the period vectors (covariant vs contravariant functoriality of $\Omega^1 \to \mathbb{C}^g$). However, because $M$ is simply an invertible linear map, any algebraic transposition won't affect the topological or lattice properties of the image. The fallback mentioned in your escalation triggers explicitly anticipates this.

6. **Recommendation**: Accept as-is. The shared-helper strategy with `instPeriodLatticeDiscrete` is exactly how this should be engineered to minimize duplicated matrix pain.

VERDICT: accept — The plan is mathematically flawless, deeply integrated with the latest Mathlib `IsZLattice` API, and anticipates the correct typeclass and module-restriction friction points.
