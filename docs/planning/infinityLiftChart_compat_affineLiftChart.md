# `infinityLiftChart_compat_affineLiftChart` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean:252`
**Route:** mathlib-now &nbsp;&nbsp; **Effort:** 6 &nbsp;&nbsp; **Est:** ~1 focused week, ~200–300 LOC, entirely in `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean`
**Blocked by:** none

**Statement (verbatim):**
```lean
axiom infinityLiftChart_compat_affineLiftChart
    (H : HyperellipticData) (h : ¬ Odd H.f.natDegree)
    (b : HyperellipticAffineInfinity H) (a : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((infinityLiftChart H h b).symm.trans (affineLiftChart H h a)) : ℂ → ℂ)
      ((infinityLiftChart H h b).symm.trans (affineLiftChart H h a)).source
```

**Why it's an axiom right now:** Per the docstring on `EvenAtlas.lean:250-251`, this is the symmetric companion to `affineLiftChart_compat_infinityLiftChart` (`EvenAtlas.lean:243`). The same Möbius identification on the gluing region governs both directions: `affineInfinityOverlapHomeomorph` (`Even.lean:756`) is a `Homeomorph`, so its `.symm` is `infinityToAffineOverlap` (`Even.lean:750-754`), which has the same $x \mapsto 1/x$ formula. It was axiomatized to defer the tedious coordinate transition computations; it requires a direct algebraic proof via explicit rational and polynomial formulas mirroring the forward direction.

**Proof recipe**

This is the symmetric direction of the transition between the affine and infinity charts. It must be computed directly from explicit formulas; an attempt to deduce it from the forward direction using the Inverse Function Theorem would introduce mathematical circularity (since confirming a non-vanishing derivative via chart-transitions presumes differentiability).

1. **Unfold chart definitions.** Start by expanding `infinityLiftChart` and `affineLiftChart`. The transition map is governed by `infinityToAffineOverlap` (`Even.lean:750`) and `affineInfinityOverlapHomeomorph.symm` (`Even.lean:756`), corresponding to the geometric transition map $x \mapsto 1/x$ along with the appropriate hyperelliptic $y$-coordinate transformation.
2. **Four-case dispatch.** Case-split on the specific local chart components the points $a$ and $b$ fall into. Since each chart (affine and infinity) splits into two domains (where `projX` or `projY` is a local diffeomorphism), there are $2 \times 2 = 4$ sub-cases:
   - $a \in \text{projX}$, $b \in \text{projX}$
   - $a \in \text{projX}$, $b \in \text{projY}$
   - $a \in \text{projY}$, $b \in \text{projX}$
   - $a \in \text{projY}$, $b \in \text{projY}$
3. **Apply explicit transition formulas.** For each case, write down the composition of the coordinate charts. The base coordinate transition is invariably $x \mapsto 1/x$, which is smooth away from $0$. 
4. **Smoothness via Mathlib.** Prove that each explicitly written rational/polynomial map is `ContDiffOn ℂ ω`. Build the proofs by chaining:
   - `contDiffOn_inv` for the $x \mapsto 1/x$ transitions.
   - Standard polynomial/rational operation lemmas (`ContDiffOn.mul`, `ContDiffOn.add`, `ContDiffOn.pow`).
   - `polynomialLocalHomeomorph_contDiffOn_symm` (`OddAtlas/AffineChart.lean:536`) for inverting the branch coordinate where `projY` is used.
5. **Replace `axiom` with `theorem`.** Drop the proof in place of lines `EvenAtlas.lean:252-257`. The downstream `chartAt_compat` at `EvenAtlas.lean:271` already calls it by name (`exact infinityLiftChart_compat_affineLiftChart H h b a'`), so no caller update is needed.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/EvenAtlas.lean` — replace `axiom infinityLiftChart_compat_affineLiftChart` (lines 252-257) with the assembled `theorem`.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas` succeeds.
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticEvenProj.instIsManifold` (defined at `EvenAtlas.lean:275`) no longer lists `infinityLiftChart_compat_affineLiftChart`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the explicit rational map for the $y$-coordinate transition in one of the mixed `projX`/`projY` sub-cases involves an un-simplifiable branch cut that `polynomialLocalHomeomorph_contDiffOn_symm` (`OddAtlas/AffineChart.lean:536`) cannot handle without new IFT-based infrastructure, escalate to ensure the chart formulas are correct.
- If handling the four sub-cases explicitly requires duplicating more than 100 lines of identical logic from `affineLiftChart_compat_infinityLiftChart`, escalate to consider factoring out the rational algebraic transition lemmas into a shared helper file before proceeding.

### Gemini critique addressed:
- **Route and Effort updated:** Reclassified from `provable-from-other-axioms` to `mathlib-now` and raised effort from 5 to 6. This aligns the effort with the forward direction, as the backward transition must be proven independently.
- **Removed Route B (Mathematical Circularity):** Completely scrapped the previous Route (B) which erroneously proposed using the Inverse Function Theorem and `transition_fderiv_mul`. Using `transition_fderiv_mul` to establish a non-vanishing derivative mathematically requires already knowing the backward map is differentiable, creating a fatal circularity.
- **Promoted Route A:** The direct four-case coordinate transition proof, which relies on explicit algebraic formulas ($x \mapsto 1/x$) and `contDiffOn_inv`, is now the mandated primary and sole path.
- **Removed architectural circularities:** Scrubbed all references to utilizing downstream manifold properties to prove this axiom, preventing the Lean instance bootstrap failure identified in the critique.

---
**Vetting trail.** Critique: `_vetting/infinityLiftChart_compat_affineLiftChart.md`. Verdict: reject. Revised: 2026-06-03.