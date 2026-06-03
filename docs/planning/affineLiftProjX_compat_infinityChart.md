# `affineLiftProjX_compat_infinityChart` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:78`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~3–5 days, ~150 LOC (a single ContDiffOn proof in `InfinityChart.lean`, sharing helper algebra with `infinityChart_compat_affineLiftProjX`)
**Blocked by:** `infinityChart`, `infinityInverseMap` (transitively)

**Statement (verbatim):**
```lean
/-- Remaining OA2 local boundary: the lifted affine `x`-chart followed by the infinity chart. -/
axiom affineLiftProjX_compat_infinityChart
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) : ℂ → ℂ)
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source
```

**Why it's an axiom right now:** The transition is the *reverse* of `infinityChart_compat_affineLiftProjX`: now we start with `x ∈ ℂ` (the `affineChartProjX` chart value), produce the affine point `(x, y(x)) = (affineChartProjX p hpY).symm x`, lift along `OnePoint.isOpenEmbedding_coe`, then apply the forward `infinityChart` map `(x, y) ↦ y / x^{g+1}`. The map is `x ↦ y(x) / x^{g+1}` where `y(x) = (squareLocalHomeomorph H p hp).symm (H.f.eval x)` is the chosen branch of `√(f(x))` (per `OddAtlas/AffineChart.lean:184–186`). This is rational-times-analytic in `x` on the overlap region (where `x ≠ 0` and `‖y(x) / x^{g+1}‖ < someRadius H h`), hence in `ContDiffOn ℂ ω`. As with the X→∞ direction, the axiom exists because both `infinityChart` and the local-inverse branch live behind axioms.

**Proof recipe**

Follow `docs/hyperelliptic-odd-atlas-plan.md` §OA2 / OA3 (the same `affine × infinity` bullet, lines 105–115). Mathematical reference: chain rule for `ContDiffOn` (`Mathlib.Analysis.Calculus.ContDiff.Basic` `ContDiffOn.comp`); analyticity of the local square-root branch (`squareLocalHomeomorph_contDiffOn_symm` at `OddAtlas/AffineChart.lean:480`); rational-function analyticity (`Mathlib.Analysis.Calculus.ContDiff.Polynomial`).

1. **Prerequisites.** Both `infinityChart` and `infinityInverseMap` real (per `docs/planning/infinityChart.md`, `docs/planning/infinityInverseMap.md`). Available API: `infinityForward` (the OnePoint.rec wrapper from the `infinityChart` recipe Step 2), `squareLocalHomeomorph_contDiffOn_symm` (`OddAtlas/AffineChart.lean:480`, already a theorem), `affineChartProjX_symm_apply_fst`, `affineChartProjX_symm_apply_snd` (`OddAtlas/AffineChart.lean:255, 264`, already simp lemmas), `PartialHomeomorph.lift_openEmbedding_apply` (`.lake/packages/mathlib/Mathlib/Topology/PartialHomeomorph/Constructions.lean:388`).

2. **Compute the transition explicitly.** Using `PartialHomeomorph.trans_apply`, `lift_openEmbedding_apply`, and the simp lemmas above, the composite `((lift_openEmbedding (affineChartProjX p hpY) ...).symm.trans (infinityChart H h)) x` reduces on the source to
   ```lean
   = infinityForward H h ((↑) ((affineChartProjX p hpY).symm x))
   = (((affineChartProjX p hpY).symm x).val.2) / (((affineChartProjX p hpY).symm x).val.1) ^ (g H h + 1)
   = (squareLocalHomeomorph H p hpY).symm (H.f.eval x) / x ^ (g H h + 1)
   ```
   using `affineChartProjX_symm_apply_fst` (`= x`) and `affineChartProjX_symm_apply_snd` (`= (squareLocalHomeomorph H p hpY).symm (H.f.eval x)`). Prove this as a `@[simp]` helper `affineLiftProjX_trans_infinityChart_apply` parallel to `affineChartProjX_trans_affineChartProjY_apply` at `OddAtlas/AffineChart.lean:468`.

3. **Source analysis.** The source of the composite is the set of `x ∈ (affineChartProjX p hpY).target` such that (a) the produced point lies in `(affineChartProjX p hpY).target ⊂ ℂ`, i.e. `H.f.eval x ∈ (squareLocalHomeomorph H p hpY).target` (already part of the chart target); (b) the lifted-affine source contains the image of `(affineChartProjX p hpY).symm x` under `(↑)`; (c) the image lies in `(infinityChart H h).source`. Use the `infinityChart_source_eq` simp lemma from the `infinityChart` recipe Step 3: this restricts to `x` such that `0 < ‖(squareLocalHomeomorph H p hpY).symm (H.f.eval x) / x^{g+1}‖ < someRadius H h` — in particular `x ≠ 0` and the denominator is nonzero.

4. **Analyticity on the source.** Decompose:
   - `x ↦ (squareLocalHomeomorph H p hpY).symm (H.f.eval x)` is `ContDiffOn ℂ ω` on `{x | H.f.eval x ∈ (squareLocalHomeomorph H p hpY).target}` by composition: `Polynomial.contDiff_aeval H.f ω` for `x ↦ H.f.eval x` (Mathlib `Mathlib.Analysis.Calculus.ContDiff.Polynomial`, cited at `OddAtlas/AffineChart.lean:511`), composed with `squareLocalHomeomorph_contDiffOn_symm` (`OddAtlas/AffineChart.lean:480`) via `ContDiffOn.comp`. This is *the same composition* used in the proof of `affineChartProjX_compat_affineChartProjY` at `OddAtlas/AffineChart.lean:518`.
   - `x ↦ 1 / x^{g+1}` is `ContDiffOn ℂ ω` on `{x | x ≠ 0}` via `ContDiffOn.inv` + `(contDiff_id.pow (g+1)).contDiffOn`. (Pattern at `OddAtlas/AffineChart.lean:564–566`.)
   - Multiply via `ContDiffOn.mul` (`Mathlib.Analysis.Calculus.ContDiff.Basic`).

5. **Assemble with `ContDiffOn.congr`.** Same pattern as `affineChartProjX_compat_affineChartProjY` (`OddAtlas/AffineChart.lean:503–520`): combine Step 4's `ContDiffOn ℂ ω` on the explicit form with Step 2's "transition = explicit form" `@[simp]` helper.

6. **Discharge.** In `InfinityChart.lean:77–87`, replace
   ```lean
   axiom affineLiftProjX_compat_infinityChart ... :
       ContDiffOn ℂ ω ...
   ```
   with the `theorem` body from Step 5. Signature unchanged so the consumer `affineLift_compat_infinityChart` at `OddAtlas.lean:120` continues to compile.

**Next discrete deliverable.** **Steps 2 + 4 together as a single PR** — the helper `affineLiftProjX_trans_infinityChart_apply` and the proof of `ContDiffOn ℂ ω` of the explicit form on `{x | x ≠ 0 ∧ H.f.eval x ∈ (squareLocalHomeomorph ...).target}`. The source restriction in Step 3 can then be threaded via `ContDiffOn.mono` (Mathlib `Mathlib.Analysis.Calculus.ContDiff.Basic`) as a second, tiny PR.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` — replace `axiom affineLiftProjX_compat_infinityChart ...` (lines 77–87) with a `theorem` body. Add `affineLiftProjX_trans_infinityChart_apply` `@[simp]` helper from Step 2.
- (no other files; the existing `OddAtlas/AffineChart.lean` API covers `squareLocalHomeomorph_contDiffOn_symm`, `affineChartProjX_symm_apply_fst`, `affineChartProjX_symm_apply_snd`)
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean` — no signature change; consumer at line 120 continues to type-check.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas` succeeds with the axiom replaced by a `theorem` (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticOdd.instIsManifold` no longer lists `affineLiftProjX_compat_infinityChart` (consumer `affineLift_compat_infinityChart` at `OddAtlas.lean:120`, transitively `instIsManifold` at `:159`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the `infinityChart` recipe's `source` formulation does *not* include a tractable `‖y/x^{g+1}‖ < someRadius H h` form (Step 3 of this recipe relies on it), Step 3 here cannot complete cleanly — escalate to the `infinityChart` recipe rather than working around it locally.
- If the source ends up being *empty* (e.g. the punctured-disk radius `someRadius H h` is small enough and `p` is "far from `∞`"), then the `ContDiffOn ℂ ω _ ∅` is trivially true and the proof becomes `ContDiffOn.empty`-style — but this is a *fragile* discharge, since downstream the source needs to be nonempty for the `IsManifold` instance to have content at the overlap. If this happens, **escalate**: it indicates a radius mismatch upstream.
- If the statement needs to change shape (e.g. the `lift_openEmbedding` API moves in a Mathlib bump), do not silently rewrite — consumer at `OddAtlas.lean:120` and the precise `PartialHomeomorph.lift_openEmbedding` API at `.lake/packages/mathlib/Mathlib/Topology/PartialHomeomorph/Constructions.lean:347` are load-bearing.

**Cross-plan patch (2026-06-03):** Namespace standardised on Mathlib's `PartialHomeomorph` (the stale `OpenPartialHomeomorph` references were hallucinated).
