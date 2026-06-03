# Gemini 3.1 Pro critique — `LineBundle`

**Model:** gemini-3.1-pro-preview
**Duration:** 50.1s
**Source axiom:** `Jacobians/RiemannSurface/LineBundle.lean`
**Verdict:** **reject**

---

Here is a rigorous critique of the proposed axiom-discharge plan:

**1. Route classification**
The proposed route of `needs-infra` is **wrong** because the plan fundamentally misunderstands what infrastructure is being built. The correct classification for discharging *this specific axiom* (`LineBundle`) in the context of the provided API is **mathlib-now** (or trivial). The infrastructure for meromorphic functions is needed for `H0`, not for `LineBundle`. 

**2. Effort 1..10**
The effort estimate of "7 (~3 focused weeks)" is completely miscalibrated. You are assigning weeks of effort to define what must logically be a dummy index type in this API, while misattributing the heavy lifting (defining the space of sections) to the bundle itself. 

**3. Proof recipe**
Your Track L2 proof recipe contains a **fatal mathematical and type-theoretic category error.** 
You propose defining `LineBundle D` as the space of global sections:
```lean
structure LineBundle (D : Divisor X) where
  section_ : MeromorphicFunction X
  divisor_le : 0 ≤ section_.div + D
```
Look at the next axiom in the file: `axiom H0 (L : LineBundle D) : Type`. 
If you implement Track L2, an element `L : LineBundle D` is a *single meromorphic function*. The type `H0 L` then becomes "the space of global sections of a specific meromorphic function." This is mathematical nonsense. You have entirely conflated the line bundle $\mathcal{O}(D)$ with its space of global sections $H^0(X, \mathcal{O}(D))$.

Because the API is designed such that `H0` takes `L : LineBundle D` as an argument, `LineBundle D` must merely be a token representing the bundle itself. Therefore, your Track L1 (`def LineBundle D := Unit`) is not a "hack" or a "cheap discharge"—it is the **mathematically mandated** lightweight encoding for this specific API design. The actual structure you proposed in Track L2 belongs in the discharge plan for `H0`, not `LineBundle`.

Furthermore, your claim about Track L3 that `Mathlib.CategoryTheory.Sheaves` is "absent from the project / no grep hits" is false. Mathlib v4.30 has an extensive sheaf library (`Mathlib.CategoryTheory.Sites.Sheaf`, `Mathlib.AlgebraicGeometry.SheafedSpace`, etc.). What is missing is its specific instantiation for complex manifolds, not the category-theoretic sheaf infrastructure itself.

**4. Textbook citations**
Forster Ch. II §16 is the correct reference for the correspondence between divisors, line bundles, and sections. However, you have misread Forster. Forster defines $\mathcal{O}(D)$ as a sheaf (which you correctly note in Track L3), and its sections $\Gamma(U, \mathcal{O}(D))$ as the meromorphic functions bounded by $D$. Forster does *not* define the bundle as the space of global sections.

**5. What's missing or wrong**
*   **Fundamental conflation:** You confused a bundle with its sections. 
*   **Misplaced infrastructure:** You put the plan for `H0` inside the plan for `LineBundle`.
*   **Track L2 breaks the API:** Implementing Track L2 makes it impossible to define `H0` sensibly.
*   **Track L1 misunderstanding:** You view `PUnit` as a temporary hack. In a non-sheaf-theoretic API where sections are decoupled into a separate `H0` type class/family, `LineBundle D := Unit` is the exact correct permanent formulation. The dependency `{D : Divisor X}` in `H0` already carries all the geometric data needed to define the sections.

**6. Recommendation**
Reject. You must rewrite this plan. The plan for `LineBundle` should be a 1-line `mathlib-now` discharge defining it as `Unit` (or a 1-field wrapper struct for type safety). Move the entire Track L2 meromorphic function structure to the discharge plan for `H0`. 

VERDICT: reject — The plan mathematically conflates a line bundle with its space of global sections, leading to a type-theoretically nonsensical Track L2 that breaks the downstream `H0` axiom.
