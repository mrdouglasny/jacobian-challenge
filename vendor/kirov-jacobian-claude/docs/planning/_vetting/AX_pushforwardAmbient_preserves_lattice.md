# Gemini 3.1 Pro critique — `AX_pushforwardAmbient_preserves_lattice`

**Model:** gemini-3.1-pro-preview
**Duration:** 74.2s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed discharge plan.

### 1. Route classification
**Incorrect.** The route should be **`needs-infra`**, not `provable-from-other-axioms`. The docstring literally tells you what infrastructure is missing: `"Retires to a theorem once pushforwardH1 + path-integral naturality land."` The plan attempts to bypass building this infrastructure by using a circular trick (see Section 3), which fails completely.

### 2. Effort 1..10
**Underestimated (8, not 7).** Building the genuine topological pushforward on $H_1$ is easy (Mathlib has fundamental groupoids), but establishing the change-of-variables formula for line integrals ($\int_{f \circ \gamma} \omega = \int_\gamma f^* \omega$) on a manifold is analytically non-trivial and will require serious work if it doesn't already exist in the project.

### 3. Proof recipe
There is a **fatal logical circularity** in Step 2. 

The plan proposes a "pragmatic alternative" to avoid defining a topological `pushforwardH1`. It suggests defining it as:
`pushforwardH1 := (periodMap Y)^{-1} ∘ (pushforwardAmbientLinear) ∘ periodMap X`
restricted to the integral lattice. 

You **cannot** do this. The period lattice is the image of the period map. To restrict `pushforwardAmbientLinear` to the integral lattice of $X$ and apply `(periodMap Y)^{-1}`, you must first know that `pushforwardAmbientLinear` maps the lattice of $X$ into the lattice of $Y$. But **that is literally the axiom you are trying to prove**. You are assuming the conclusion to build the map that you intend to use to prove the conclusion.

Furthermore, in Step 3, you claim that the naturality formula $\int_{f_* \gamma} \omega = \int_\gamma f^* \omega$ is "free of any `pushforwardH1` baggage"—yet the left-hand side of that very equation integrates over $f_* \gamma$ (which *is* `pushforwardH1`). You cannot state this change-of-variables lemma without a genuine topological definition of `pushforwardH1`.

### 4. Textbook citations
The citations (Forster §20, Mumford) are correct for the underlying mathematics, but the Lean execution misses the point of why these theorems hold: periods are preserved over $\mathbb{Z}$ precisely because the continuous map $f$ pushes integer 1-cycles to integer 1-cycles topologically.

### 5. What's missing or wrong
* **The `pushforwardH1` definition:** Step 2's suggestion to build it via "basis transport" (sending basis vectors to basis vectors using intersection numbers) is grotesque. In Mathlib, the fundamental group is just `x ⟶ x` in the `FundamentalGroupoid`, which is functorial via `FundamentalGroupoid.map f`. $H_1$ is just its `Abelianization`. You get `pushforwardH1` trivially by applying `Abelianization.map` to the induced map on the fundamental group. Do not overcomplicate this.
* **The change-of-variables lemma:** Step 3 assumes `integral (f ∘ γ) ω = integral γ (f^* ω)` is a "clean consequence" of existing code. Unless this exact contour-integral naturality lemma already exists in the project's API, it is a significant missing piece of infrastructure that must be proved from scratch using charts and real calculus.
* **Basepoint independence:** Step 6 correctly identifies the basepoint mismatch for `Classical.arbitrary`. However, because you are dealing with fundamental groups, you will need to insert a change-of-basepoint isomorphism (a path between $f(x_0)$ and $y_0$) and prove that integrating over a cycle conjugated by this path doesn't change the closed-form integral (which it doesn't, because the cycle is abelianized).

### 6. Recommendation
**Reject.** The "pragmatic alternative" is logically circular and invalidates the entire proof. You must build genuine topological functoriality for $H_1$ (using Mathlib's `FundamentalGroupoid` and `Abelianization`) and formally prove the path-integral change of variables. 

VERDICT: reject — The plan relies on a fatal circularity by defining the $H_1$ pushforward using the very lattice-preservation property the axiom is trying to prove.
