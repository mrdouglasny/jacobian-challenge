# `affineLiftChart_compat_infinityLiftChart` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean:243`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 7 &nbsp;&nbsp; **Est:** ~1.5 focused weeks, ~300–450 LOC, mostly in `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` plus possible helper extractions in `OddAtlas/AffineChart.lean` for $x \mapsto y(x)$ smoothness
**Blocked by:** `infinityLiftChart_compat_affineLiftChart` (the symmetric direction; the two recipes share the same case-split skeleton and one supplies the chart-transition-derivative input to the other via `Jacobians.GeneralResults.transition_fderiv_mul`)

**Statement (verbatim):**
```lean
axiom affineLiftChart_compat_infinityLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (a : HyperellipticAffine H) (b : HyperellipticAffineInfinity H) :
    ContDiffOn ℂ ω
      (((affineLiftChart H h a).symm.trans (infinityLiftChart H h b)) : ℂ → ℂ)
      ((affineLiftChart H h a).symm.trans (infinityLiftChart H h b)).source
```

**Why it's an axiom right now:** Per the docstring on `EvenAtlas.lean:232-242`, this is the **cross-summand** chart transition: the source chart is lifted from the affine summand via `proj ∘ Sum.inl` (`EvenAtlas.lean:91-98`) and the target chart from the affine-infinity summand via `proj ∘ Sum.inr` (`EvenAtlas.lean:102-109`). The Mathlib helper `OpenPartialHomeomorph.lift_openEmbedding_trans` (`.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Constructions.lean:420`) requires both charts to be lifted along the same embedding, which fails here (`isOpenEmbedding_proj_inl` vs `isOpenEmbedding_proj_inr`, `EvenAtlas.lean:91, :102`). What is load-bearing is the Möbius identification `x ↦ 1/x` on the gluing region, already packaged as `affineInfinityOverlapHomeomorph` in `Even.lean:756`. This requires a 4-way case-split (projX/Y × projX/Y) to explicitly calculate the $\mathbb{C} \to \mathbb{C}$ chart transitions. It is a mechanical bundling of existing API and explicit transition formulas.

**Proof recipe**

The map is a transition from an inverse affine chart $a^{-1} : \mathbb{C} \to \text{Curve}$ to a forward infinity chart $b : \text{Curve} \to \mathbb{C}$, wrapping the gluing map $F : \text{Curve} \to \text{Curve}$. 

1. **Unfold both lifted charts.** From `OpenPartialHomeomorph.lift_openEmbedding_symm` (`Constructions.lean:403`) and `lift_openEmbedding_source` (`Constructions.lean:395`),
   ```
   (affineLiftChart H h a).symm = (proj H ∘ Sum.inl) ∘ (affineChartAt (H := H) a).symm
   (infinityLiftChart H h b)    = e_b ∘ (proj H ∘ Sum.inr)⁻¹ on its source
   ```
   where `e_b := HyperellipticAffine.affineChartAt (H := HyperellipticAffineInfinity.reverseData H hf.out) b` (compare `EvenAtlas.lean:115-128`).

2. **Reduce to an explicit chart-level transition.** On the source, the composition `(infinityLiftChart H h b) ∘ (affineLiftChart H h a).symm` evaluates precisely as $b \circ F \circ a^{-1}$, which in Lean is:
   ```
   e_b ∘ affineToInfinity H h ∘ ι ∘ (affineChartAt (H := H) a).symm
   ```
   where `affineToInfinity H h` is the Möbius identification $F(x, y) = (1/x, y/x^{d/2})$ (`Even.lean:820-822`, built from `Even.lean:744-748`), and `ι` is the subtype inclusion. This reduction uses `hyperellipticEvenSetoid_rel_iff` (`Even.lean:673`) because `affineInfinityOverlapHomeomorph` (`Even.lean:756`) is the explicit witness for the quotient equivalence.

3. **Case-split on projX / projY.** The affine chart `affineChartAt` dispatches over `smoothLocusY` (`OddAtlas/AffineChart.lean:594-612`). Inverse charts ($a^{-1}$) handle the non-trivial algebraic branch functions mapping $\mathbb{C} \to (X, Y)$, while forward charts ($b$) are simple projections mapping $(X, Y) \to \mathbb{C}$. This creates four explicit formulas for $b \circ F \circ a^{-1}$:
   - **(projX, projX):** `a` is projX, so $a^{-1}(x) = (x, y(x))$. `b` is projX, evaluating via `fst`. The transition is $x \mapsto 1/x$.
   - **(projX, projY):** `a` is projX, so $a^{-1}(x) = (x, y(x))$. `b` is projY, evaluating via `snd`. The transition is $x \mapsto y(x) / x^{d/2}$.
   - **(projY, projX):** `a` is projY, so $a^{-1}(y) = (x(y), y)$. `b` is projX, evaluating via `fst`. The transition is $y \mapsto 1/x(y)$.
   - **(projY, projY):** `a` is projY, so $a^{-1}(y) = (x(y), y)$. `b` is projY, evaluating via `snd`. The transition is $y \mapsto y / x(y)^{d/2}$.

4. **Per-sub-case `ContDiffOn ω` proof.** 
   * **(projX, projX):** Smooth by `contDiffOn_inv` (since $x \ne 0$ on the gluing overlap).
   * **(projX, projY):** Requires proving $x \mapsto y(x)$ is `ContDiffOn ℂ ω`. Extract this proof from the existing intra-affine compatibility lemma `affineChartProjX_compat_affineChartProjY` in `OddAtlas/AffineChart.lean` (which already handles implicit branch smoothness). Compose with $x \mapsto 1/x^{d/2}$ via `contDiffOn_inv` and `contDiff_pow.contDiffOn`.
   * **(projY, projX):** Requires proving $y \mapsto x(y)$ is smooth. Use `polynomialLocalHomeomorph_contDiffOn_symm` (`OddAtlas/AffineChart.lean:536`) exactly as in `affineChartProjY_compat_affineChartProjX` (`OddAtlas/AffineChart.lean:556-573`), then compose with `contDiffOn_inv`.
   * **(projY, projY):** Use `polynomialLocalHomeomorph_contDiffOn_symm` for $x(y)$, then compose with smooth algebraic operations $y \cdot x(y)^{-d/2}$.

5. **Pointwise congruence.** Steps 1–2 give pointwise agreement with the explicit formulas in Step 3. Step 4 proves those formulas are `ContDiffOn ω`. Close with `ContDiffOn.congr` exactly as `affineChartProjY_compat_affineChartProjX` does at `OddAtlas/AffineChart.lean:571-573`.

6. **Replace `axiom` with `theorem`.** Drop the body in place of lines `EvenAtlas.lean:243-248`; the downstream `chartAt_compat` at `EvenAtlas.lean:270` already calls it by name, so no caller update is needed.

Tactic sketch (final shape):
```lean
theorem affineLiftChart_compat_infinityLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (a : HyperellipticAffine H) (b : HyperellipticAffineInfinity H) :
    ContDiffOn ℂ ω
      (((affineLiftChart H h a).symm.trans (infinityLiftChart H h b)) : ℂ → ℂ)
      ((affineLiftChart H h a).symm.trans (infinityLiftChart H h b)).source := by
  -- Step 1: unfold the lifted charts.
  simp only [affineLiftChart, infinityLiftChart,
    OpenPartialHomeomorph.lift_openEmbedding_symm,
    OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.lift_openEmbedding_target]
  -- Step 3: case-split on smoothLocusY membership for a and (in reverseData) for b.
  by_cases hpY : a ∈ HyperellipticAffine.smoothLocusY H
  · by_cases hbY : b ∈ HyperellipticAffine.smoothLocusY
        (HyperellipticAffineInfinity.reverseData H h)
    · -- (projX, projX): F(x, y) = (1/x, y/x^(d/2)), target is fst. Transition is x ↦ 1/x.
      exact affineLiftChart_compat_infinityLiftChart_projX_projX hpY hbY
    · -- (projX, projY): Target is snd. Transition is x ↦ y(x) / x^(d/2).
      have hbX : b ∈ HyperellipticAffine.smoothLocusX
          (HyperellipticAffineInfinity.reverseData H h) :=
        mem_smoothLocusX_of_y_eq_zero _ (by by_contra h0; exact hbY h0)
      exact affineLiftChart_compat_infinityLiftChart_projX_projY hpY hbX hbY
  · -- a is a branch point: projY on the affine side. a.symm uses local homeo for x(y).
    have hpX : a ∈ HyperellipticAffine.smoothLocusX H :=
      mem_smoothLocusX_of_y_eq_zero _ (by by_contra h0; exact hpY h0)
    by_cases hbY : b ∈ HyperellipticAffine.smoothLocusY
        (HyperellipticAffineInfinity.reverseData H h)
    · -- (projY, projX): Target is fst. Transition is y ↦ 1/x(y).
      exact affineLiftChart_compat_infinityLiftChart_projY_projX hpX hpY hbY
    · -- (projY, projY): Target is snd. Transition is y ↦ y / x(y)^(d/2).
      have hbX : b ∈ HyperellipticAffine.smoothLocusX
          (HyperellipticAffineInfinity.reverseData H h) :=
        mem_smoothLocusX_of_y_eq_zero _ (by by_contra h0; exact hbY h0)
      exact affineLiftChart_compat_infinityLiftChart_projY_projY hpX hpY hbX hbY
```

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` — replace `axiom affineLiftChart_compat_infinityLiftChart` (lines 243-248) with the assembled `theorem`. 
- `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` — add the four sub-case chart-transition smoothness helpers (`_projX_projX`, `_projX_projY`, `_projY_projX`, `_projY_projY`) as `private lemma`s.
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/AffineChart.lean` — (If needed) factor out the core $x \mapsto y(x)$ smoothness step from `affineChartProjX_compat_affineChartProjY` into a reusable lemma for the `_projX_projY` case here.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas` succeeds.
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticEvenProj.instIsManifold` (defined at `EvenAtlas.lean:275`) no longer lists `affineLiftChart_compat_infinityLiftChart`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the `x ↦ y(x)` smoothness derivation in the `(projX, projY)` case cannot be cleanly extracted from `affineChartProjX_compat_affineChartProjY` and requires invoking the implicit function theorem from scratch, escalate (as this would significantly expand the scope).
- If the symmetric recipe `infinityLiftChart_compat_affineLiftChart` lands first and uses `transition_fderiv_mul` (`GeneralResults/ChartTransition.lean:35`) to derive *this* direction by symmetry, then this recipe collapses to a 5-line `exact`. Escalate to confirm the order of discharge.

### Gemini critique addressed:
- **Route & Effort corrected:** Reclassified from `provable-from-other-axioms` to `mathlib-now` as it relies on chaining existing Mathlib infrastructure and API bundling. Effort increased to 7 to reflect the careful extraction of branch smoothness lemmas.
- **Fixed forward/inverse chart confusion:** The recipe now correctly identifies that the *inverse* charts ($a^{-1}$) produce the algebraic coordinates $(x, y(x))$ or $(x(y), y)$, while the *forward* charts ($b$) are simple `fst`/`snd` projections on the curve.
- **Rewrote transition formulas:** Formulated explicit $\mathbb{C} \to \mathbb{C}$ transition maps ($x \mapsto 1/x$, $x \mapsto y(x)/x^{d/2}$, $y \mapsto 1/x(y)$, and $y \mapsto y/x(y)^{d/2}$), eliminating the previous plan's impossible attempt to push `polynomialLocalHomeomorph` onto the infinity side.
- **Targeted extraction of $x \mapsto y(x)$:** Explicitly planned the extraction of the $x \mapsto y(x)$ smoothness from existing intra-affine compatibility proofs (`OddAtlas/AffineChart.lean`) instead of incorrectly dismissing it as `fst`.

---
**Vetting trail.** Critique: `_vetting/affineLiftChart_compat_infinityLiftChart.md`. Verdict: reject. Revised: 2026-06-03.