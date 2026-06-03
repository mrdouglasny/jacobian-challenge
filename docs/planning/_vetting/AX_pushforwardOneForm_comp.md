# Gemini 3.1 Pro critique — `AX_pushforwardOneForm_comp`

**Model:** gemini-3.1-pro-preview
**Duration:** 102.5s
**Source axiom:** `Jacobians/Axioms/AbelJacobiMap.lean`
**Verdict:** **reject**

---

Here is a rigorous review of the proposed axiom-discharge plan.

### 1. Route classification
**Incorrect.** It is classified as `provable-from-other-axioms`, but because the proof fundamentally depends on the internal construction of a nonexistent `def` (which the plan acknowledges), this is actually **`needs-infra`**. You cannot plan a theorem's internal structural rewrites (`tsum_sigma`, `mfderiv_comp`) before deciding how the `def` handles local inverses and ramification points.

### 2. Effort estimate
**Miscalibrated.** The effort of `4` (2 days) drastically underestimates the difficulty of building a fiberwise trace map in Lean and proving its functoriality. To do this, you have to formalize local inverse branches of a branched cover, chain rule for local inverses, and removable singularities at ramification points. If the infrastructure doesn't exist yet, this is an `8` or `9` (weeks).

### 3. Proof recipe
The recipe contains severe mathematical and type-theoretic errors:
* **Conflation of pullback and pushforward differentials:** In Step 3 and Step 5, the plan claims that the trace `(f_* ω)(q)` decomposes via `mfderiv_comp` applied directly to `f` and `g`. This is backwards. Pushforward (trace) of a 1-form is defined by summing the pullbacks along the **local inverses** of the map, i.e., `(f_* ω)_q = \sum_{p \in f^{-1}(q)} (f_p^{-1})^* \omega_p`. Applying the chain rule to the forward derivatives of `f` and `g` computes the pullback `(g ∘ f)^*`, not the pushforward. The proof must invoke the Inverse Function Theorem and apply the chain rule to `(g ∘ f)^{-1} = f^{-1} \circ g^{-1}`.
* **The "Dualized" shortcut is a category error (Step 6):** The recipe claims that `pushforwardOneForm` could just be `pullbackOneForm.dualMap`. `pullbackOneForm f` has type `Ω¹(Y) → Ω¹(X)`. Its dual map has type `Ω¹(X)* → Ω¹(Y)*` (this is the covariant functoriality of the Albanese/Jacobian tangent space). But the docstring clearly defines `pushforwardOneForm` as the trace of 1-forms, acting on the forms themselves: `Ω¹(X) → Ω¹(Y)`. There is no canonical holomorphic isomorphism `Ω¹ ≅ Ω¹*` to "transport" this dual map back to `Ω¹`. Step 6 will fail to typecheck.
* **Summation over fibers:** In Step 4/5, proposing `tsum_sigma` implies summing over infinite types. A non-constant map of compact Riemann surfaces is a finite branched cover. The unbranched fibers are strictly finite (`Finset`), and using `tsum` is a massive red flag because it glosses over the analytic continuation needed to handle fiber collisions at ramification points. 

### 4. Textbook citations
The Mumford and Griffiths-Harris references are conceptually correct for the trace map, but the plan completely ignores the analytic details of local inverses and ramification loci that those very sections emphasize.

### 5. What's missing or wrong
* **Handling of ramification points:** The trace formula `Σ_{p ∈ f⁻¹(r)}` is only valid on the dense open set of regular values. The plan fails to mention how it will extend this to ramification points (e.g., Riemann Removable Singularity theorem). You cannot just `funext r` everywhere.
* **Wrong derivatives:** The Lean template is unusable because `mfderiv` goes the wrong direction. You need `mfderiv` of the inverse branches.
* **Dualization fallacy:** Step 6 must be entirely scrapped.

### 6. Recommendation
**Reject.** The proposed proof recipe is mathematically unsound because it confuses the forward derivative with the derivative of local inverses, and proposes an impossible type-theoretic shortcut using `dualMap`. The plan must be rewritten to address the analytic trace strictly via local inverse branches on the unramified locus, and explicitly list the removable singularity infrastructure required to bridge the gaps.

VERDICT: reject — The plan fundamentally confuses forward derivatives with local inverse derivatives for the trace map and proposes a mathematically impossible dualization shortcut.
