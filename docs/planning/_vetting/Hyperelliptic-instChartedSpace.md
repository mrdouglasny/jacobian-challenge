# Gemini 3.1 Pro critique — `Hyperelliptic-instChartedSpace`

**Model:** gemini-3.1-pro-preview
**Duration:** 56.4s
**Source axiom:** `Jacobians/ProjectiveCurve/Hyperelliptic.lean`
**Verdict:** **revise**

---

Here is a referee-style critique of the proposed discharge plan.

**1. Route classification**
The `needs-infra` classification is correct. However, your effort scope is slightly conflated: if the 7 sub-axioms (like `infinityChart` and its compatibilities) are truly handled by their own discharge recipes, the effort for *this specific axiom* is just the parity-dispatch assembly and the `HyperellipticOdd` base charts, which is closer to an Effort 3. If you intend for this PR to also build the entire odd atlas from scratch, then Effort 7 is accurate.

**2. Effort estimate**
As noted above, calibrated for the whole odd atlas, but over-estimated if just doing the assembly. The LOC estimate (~400) is reasonable for defining the full odd atlas and the pullback instance.

**3. Proof recipe & 5. What's missing or wrong**
This recipe suffers from severe API hallucinations regarding Mathlib's manifold library and bad practices for Lean 4 typeclasses:

*   **Fake API (`OpenPartialHomeomorph`):** There is no `OpenPartialHomeomorph` in Mathlib 4. The correct type is `PartialHomeomorph`.
*   **Fake API (`OpenPartialHomeomorph.lift_openEmbedding`):** Mathlib does not have this. To push a chart forward along an open embedding $i : X \hookrightarrow Y$, you must convert the open embedding to a partial homeomorphism and compose (`trans`) its inverse with your chart: `(OpenEmbedding.toPartialHomeomorph i).symm.trans chart`.
*   **Fake API (`ChartedSpace.comp` / `Homeomorph.toChartedSpace`):** Mathlib does not provide automatic pullback instances for `ChartedSpace` along homeomorphisms because it would cause typeclass loops. You cannot just call `ChartedSpace.comp`. You must build the instance manually by pushing the `dite` into the fields and using `PartialHomeomorph.trans` with `e.toPartialHomeomorph`.
*   **Data-carrying `dite` antipattern:** The plan proposes defining the `ChartedSpace` instance using a top-level `by_cases` (Block C). Because `ChartedSpace` is a data-carrying class, a top-level `dite` wraps the *entire record*. This means `(inst H).chartAt x` will not definitionally reduce to the expected chart; it will be stuck on a `dite` of records. You must push the case split *into* the fields:
    ```lean
    noncomputable instance Hyperelliptic.instChartedSpace (H : HyperellipticData) : ChartedSpace ℂ (Hyperelliptic H) where
      atlas := if h : Odd H.f.natDegree then ... else ...
      chartAt x := if h : Odd H.f.natDegree then ... else ...
      -- etc...
    ```

**4. Textbook citations**
N/A (this is pure Lean/Mathlib infrastructure transport).

**6. Recommendation**
Revise to correct the hallucinated manifold API and fix the data-carrying `dite` architecture.

VERDICT: revise — Remove hallucinated `OpenPartialHomeomorph` and `ChartedSpace.comp` API, manually use `PartialHomeomorph.trans` for the homeomorphism pullback, and push the `by_cases` split into the structure fields to avoid defeq nightmares.
