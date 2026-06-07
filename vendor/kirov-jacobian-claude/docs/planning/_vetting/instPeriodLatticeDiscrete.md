# Gemini 3.1 Pro critique — `instPeriodLatticeDiscrete`

**Model:** gemini-3.1-pro-preview
**Duration:** 91.0s
**Source axiom:** `Jacobians/Axioms/PeriodLattice.lean`
**Verdict:** **revise**

---

Here is a rigorous review of your proposed axiom-discharge plan.

### 1. Route classification
**Correct.** The route is `provable-from-other-axioms`. `AX_RiemannBilinear` gives the period matrix whose positive-definite imaginary part guarantees it forms an $\mathbb{R}$-basis, which implies discreteness of its $\mathbb{Z}$-span.

### 2. Effort
**Underestimated.** You rated this a 3, but handwaved the hardest Lean-specific part (the matrix algebra for linear independence). Splitting complex matrix-vector products into real and imaginary parts in Mathlib and bridging it with `imPosDef` will be painful. This is an **Effort 4** task (~3–5 days).

### 3. Proof recipe
The overarching logic is mathematically sound, but the execution details contain severe hallucinations and syntax errors:
* **The discreteness transfer is topologically false (Steps 3 & 7):** You cited a fabricated lemma `DiscreteTopology.of_continuous_injective`. In general topology, continuous injective maps **do not** preserve discreteness (e.g., embedding $\mathbb{Z}$ into the circle $\mathbb{R}/\mathbb{Z}$ via an irrational rotation gives a dense image!). You cannot use continuous injections. 
* **The matrix algebra is entirely glossed over (Step 4):** You say "By Mumford II.2 Lemma... this $v$ is $\mathbb{R}$-linearly independent." Lean does not read Mumford. You must prove this explicitly.
* **Gibberish syntax (Step 3):** `M.toLin'.range.map` makes no sense. The correct operation is pushing the submodule forward via `Submodule.map (M.toLin'.restrictScalars ℤ)`.
* **Typeclass transfer pain (Steps 5 & 6):** You plan to identify the lattices via equality and then just drop the Mathlib instance on it. You cannot trivially `rw` an equality of `Submodule`s inside a `DiscreteTopology` typeclass inference without running into motive type errors. 

### 4. Textbook citations
**Accurate.** Mumford's *Tata Lectures on Theta I*, Ch. II §2, and Griffiths-Harris, Ch. 2 §2, are exactly the right mathematical references for the positivity of $\text{Im}(\tau)$ implying lattice discreteness.

### 5. What's missing or wrong
Be precise and fix the following in your plan:
1. **Fix the topology lemma:** Since $M$ is an invertible matrix, use `Matrix.toContinuousLinearEquiv` to get a `ContinuousLinearEquiv`. This is a `Homeomorph`, which is an `Embedding`. You must use `Embedding.discreteTopology` to transport discreteness, not a fake continuous-injective lemma.
2. **Flesh out the linear independence proof:** Add explicit steps for Step 4. You must take $\sum c_i e_i + \sum d_j \tau_j = 0$, apply `Complex.im` to the vector, prove the $c_i e_i$ terms vanish in the imaginary part, and invoke the injectivity of the linear map associated to `imPosDef` to deduce $d_j = 0$, forcing $c_i = 0$. Factor in the LOC for this matrix-vector manipulation.
3. **Fix the Submodule pushforward syntax:** Change Step 3 to use `Submodule.map`.
4. **Plan for the typeclass transfer:** In Step 5, instead of relying on definitional or propositional equality of submodules to trick the typeclass system, plan to construct a `LinearEquiv` (or `Homeomorph`) between the Mathlib `span ℤ (Set.range v)` and `periodLatticeInBasis X x₀ cω` to safely transport the `DiscreteTopology` instance.

### 6. Recommendation
Revise the plan to correct the topologically false claim about continuous injections, fix the submodule syntax, and explicitly outline the matrix real/imaginary splitting required to prove $\mathbb{R}$-linear independence. 

VERDICT: revise — The mathematical strategy is correct, but the plan fabricates a topologically false lemma for discreteness transfer and completely handwaves the heavily Lean-dependent matrix algebra required for linear independence.
