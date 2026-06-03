# Gemini 3.1 Pro critique — `Divisor-deg`

**Model:** gemini-3.1-pro-preview
**Duration:** 28.8s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Note:** effort-1 instance; should be trivial
**Verdict:** **accept**

---

**1. Route classification**
The `mathlib-now` classification is completely correct. `FreeAbelianGroup.lift` precisely encapsulates the universal property needed to lift a map on generators to a bundled `AddMonoidHom` on the free abelian group.

**2. Effort**
The estimate of 1 (trivial/15 mins) is perfectly calibrated. This is a one-line substitution.

**3. Proof recipe**
The recipe is rock solid. Assuming `Divisor X` is resolved to `FreeAbelianGroup X` (as explicitly noted in your dependencies), `FreeAbelianGroup.lift (fun _ : X => (1 : ℤ))` directly synthesizes a term of type `FreeAbelianGroup X →+ ℤ`. 

A minor note on `noncomputable`: `FreeAbelianGroup` is computationally a quotient of a list-based free group in Mathlib, so without `DecidableEq X` it is indeed noncomputable. Preemptively marking the definition `noncomputable` is the right, safe choice.

Your suggested `Divisor.deg_of` lemma is highly recommended. It will be immediately necessary for Riemann-Roch and evaluating degrees of principal divisors. You can prove it trivially with `simp [Divisor.deg]`, as `FreeAbelianGroup.lift_of` is already a `@[simp]` lemma in Mathlib.

**4. Textbook citations**
Forster and Mumford both use exactly this definition (the constant 1 summed over the divisor). Citations are perfectly on point.

**5. What's missing or wrong**
Nothing of consequence. You correctly reproduced the rather verbose manifold class brackets from the axiom signature (including `ω`, which must be a `variable` in the environment). Since Lean 4 doesn't complain about unused instance implicits in a `def`, keeping the signature identical to the axiom ensures a seamless drop-in replacement. 

**6. Recommendation**
Accept as-is. This is a model discharge plan.

VERDICT: accept — The plan correctly and efficiently leverages `FreeAbelianGroup.lift` from Mathlib to instantiate the degree map as a one-line bundled `AddMonoidHom`.
