# `PlaneCurve.instChartedSpace` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/PlaneCurve.lean:181`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~1-2 focused weeks, ~400 LOC (once `PlaneCurve` is a real `def`)
**Blocked by:** `PlaneCurve`

**Statement (verbatim):**
```lean
axiom PlaneCurve.instChartedSpace (H : PlaneCurveData) :
    ChartedSpace ℂ (PlaneCurve H)
attribute [instance] PlaneCurve.instChartedSpace
```

**Why it's an axiom right now:** Stub forced by the axiomatic `PlaneCurve` type at `PlaneCurve.lean:161`. The docstring at lines 128–151 spells out the obstruction: the projective compactification of a smooth plane curve `{F = 0} ⊂ ℙ²` requires gluing **three** affine charts (dehomogenize at `z ≠ 0`, `y ≠ 0`, `x ≠ 0`), and there is currently no project infrastructure for that pushout. The hyperelliptic atlas pattern (two-chart `Quotient (Sum ...)` at `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean`) is the direct model, with three summands instead of two.

**Proof recipe**

1. Build the three-summand quotient `PlaneCurve` definition first (`docs/planning/PlaneCurve.md`, effort 8). To support pushing forward charts later, prove that the canonical inclusion maps from each affine summand (`Sum.inl (Sum.inl a)` etc.) into the quotient are open embeddings. This establishes that the quotient map is an open map.
2. Define `dehomogenize : PlaneCurveData → Fin 3 → MvPolynomial (Fin 2) ℂ` (setting the $i$-th homogeneous variable to 1). The closedness of each carrier follows from `PlaneCurveAffine.isClosed_carrier` at `PlaneCurve.lean:82–93` applied to the resulting non-homogeneous 2-variable polynomial.
3. **Euler's Formula Step (Projective to Affine Smoothness):** Prove that `H.h_smooth` (`PlaneCurve.lean:52–53`, which asserts $\exists i, \partial_i F \ne 0$) implies that at any point on the affine curve $\{F_{dehom} = 0\}$, at least one of the two affine partial derivatives is non-zero. If both affine derivatives vanished, Euler's homogeneous function theorem ($\sum_{i=0}^2 x_i \partial_i F = d \cdot F$) evaluated at $(x, y, 1)$ with $F=0$ would force $1 \cdot \partial_z F = 0$, meaning all three projective derivatives vanish, which contradicts `H.h_smooth`.
4. **Subtype Restriction from Ambient IFT:** For each affine patch, build the 1D subtype chart. Mathlib's IFT constructs an ambient map $\mathbb{C}^2 \to \mathbb{C}^2$. Define the coordinate projection $\mathbb{C}^2 \to \mathbb{C}$ along the coordinate with the non-vanishing partial derivative. Use the ambient IFT on $F_{dehom}$ to prove the ambient inverse is smooth. Rigorously build the restricted `PartialHomeomorph` from the subtype $\{F_{dehom} = 0\}$ to $\mathbb{C}$ by taking the intersection of the ambient IFT open domain with the curve subtype, and showing the image is open in $\mathbb{C}$.
5. **Chart Pushforward:** Push each 1D affine chart forward along the open embeddings $e_i : \text{Affine}_i \hookrightarrow \text{PlaneCurve}$ defined in Step 1. For each open embedding $e_i$, construct a `PartialHomeomorph` $E_i$ with `source = Set.univ` and `target = Set.range e_i`. Assemble the final pushed-forward chart on `PlaneCurve` via `E_i.symm.trans affineChart`.
6. **Definition of `chartAt`**: Mirror `Hyperelliptic/EvenAtlas.lean:133–138` with three branches, matching on `Quotient.out q` to extract a representative in one of the three summands, and return the corresponding pushed-forward chart:
   ```lean
   noncomputable def chartAt (H : PlaneCurveData) :
       PlaneCurve H → PartialHomeomorph (PlaneCurve H) ℂ :=
     fun q =>
       match Quotient.out q with
       | Sum.inl (Sum.inl a) => affineLiftChartZ H a   -- z ≠ 0 summand
       | Sum.inl (Sum.inr b) => affineLiftChartY H b   -- y ≠ 0 summand
       | Sum.inr c           => affineLiftChartX H c   -- x ≠ 0 summand
   ```
   Mirror precisely `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean:148–171` for `mem_chartAt_source`.
7. **ChartedSpace instance**: Assemble exactly as at `Hyperelliptic/EvenAtlas.lean:174–180` utilizing `PartialHomeomorph`.
8. Replace `axiom PlaneCurve.instChartedSpace` with `noncomputable instance PlaneCurve.instChartedSpace` in `PlaneCurve.lean`, drop the `attribute [instance]` at line 183.

**Files touched**
- `Jacobians/ProjectiveCurve/PlaneCurve.lean` — replace lines 181–183 with a real instance referring to the helper in the new `Atlas` module.
- `Jacobians/ProjectiveCurve/PlaneCurve/Atlas.lean` — new module hosting the `PartialHomeomorph` pushforwards via `.trans`, `chartAt`, `mem_chartAt_source`, and the `ChartedSpace` instance.
- `Jacobians/ProjectiveCurve/PlaneCurve/AffineChart.lean` — new module for `dehomogenize`, the Euler's formula proofs, the ambient $\mathbb{C}^2$ IFT invocation, and the rigorous restriction to the 1D Subtype `PartialHomeomorph`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.PlaneCurve` succeeds.
- `#print axioms PlaneCurveData.genus` no longer lists `PlaneCurve.instChartedSpace`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The construction of the 1D subtype chart from the ambient 2D IFT homeomorphism (Step 4) requires meticulous point-set topology bounds. If Mathlib's `PartialHomeomorph.subtypeRestr` equivalent behaves poorly with domain intersections, escalate.
- If proving that the canonical affine inclusions are open embeddings (Step 1) requires general quotient-topology lemmas missing from Mathlib, escalate for a bounded topology infrastructure task.
- Any change to `PlaneCurveData.h_smooth`'s statement (currently "∃ i, ∂ᵢF ≠ 0", at `PlaneCurve.lean:52–53`) affects the Euler's formula step and must be reconciled.

**`Gemini critique addressed:`**
- **Effort increased (6 $\to$ 8):** Adjusted to account for the heavy lifting required for subtype chart restrictions and quotient pushforwards.
- **Fixed `dehomogenize` type signature:** Corrected the impossible `PlaneCurveData` return type to `MvPolynomial (Fin 2) ℂ` since dehomogenization inherently drops the homogeneity required by the struct.
- **Removed hallucinated API:** Replaced `OpenPartialHomeomorph` with `PartialHomeomorph` and replaced `lift_openEmbedding` with explicit composition (`E_i.symm.trans affineChart`) using a `PartialHomeomorph` constructed from the open embedding.
- **Euler's Formula & Affine Smoothness:** Added an explicit step (Step 3) leveraging Euler's homogeneous function theorem to rigorously connect projective smoothness (`H.h_smooth`) to the non-vanishing of affine partial derivatives.
- **Rigorous Subtype Restriction:** Replaced the handwaved IFT application with concrete steps (Step 4) outlining how the ambient $\mathbb{C}^2 \to \mathbb{C}^2$ mapping must be explicitly restricted to the $\{F=0\}$ subtype intersecting the ambient open domain.

---
**Vetting trail.** Critique: `_vetting/PlaneCurve-instChartedSpace.md`. Verdict: revise. Revised: 2026-06-03.