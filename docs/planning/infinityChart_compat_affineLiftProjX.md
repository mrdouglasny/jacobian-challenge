# `infinityChart_compat_affineLiftProjX` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:66`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~3–5 days, ~150 LOC (a single ContDiffOn proof in `InfinityChart.lean` plus ~30 LOC of helper algebra)
**Blocked by:** `infinityChart`, `infinityInverseMap` (transitively)

**Statement (verbatim):**
```lean
/-- Remaining OA2 local boundary: infinity chart followed by the lifted affine `x`-chart. -/
axiom infinityChart_compat_affineLiftProjX
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) : ℂ → ℂ)
      ((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source
```

**Why it's an axiom right now:** The transition map is `t ↦ x(t)`, where `(x(t), y(t)) = infinityInverseMap H h t` is the chart-at-infinity inverse and `x(t)` is then read off via `affineChartProjX` (which is the projection `(x, y) ↦ x` on `smoothLocusY`, see `OddAtlas/AffineChart.lean:146–148`). By the explicit formula `x(t) = 1/(lc(f)·t²)·(1 + O(t))` from `InfinityChart.lean:11` and the `infinityInverseMap` recipe, the map is `t ↦ 1/(c·t²) · x̂(t)`, which is *meromorphic* in `t` with a pole of order 2 at `t = 0` and is analytic on `0 < ‖t‖ < r`. The map is thus rational-times-analytic, hence in `ContDiffOn ℂ ω` on its domain — but proving this requires the analytic API for `infinityInverseMap` (from the `infinityInverseMap` recipe Step 5), the formula for `affineChartProjX ∘ infinityInverseMap` (Step 2 below), and an `r > 0` strict-punctured-disk argument to avoid the pole.

**Proof recipe**

Follow `docs/hyperelliptic-odd-atlas-plan.md` §OA2 "Phase OA3" (lines 105–115): "* `affine × infinity` — the chart at `∞` is `t ↦ (x(t), y(t))`; the transition `t ↦ x(t) = 1/t²` is analytic on `t ≠ 0`." Mathematical reference: chain rule for `ContDiffOn` (Mathlib `Mathlib.Analysis.Calculus.ContDiff.Basic` `ContDiffOn.comp`) plus rational-function analyticity (`Mathlib.Analysis.Calculus.ContDiff.Polynomial`).

1. **Prerequisites.** Both `infinityChart` and `infinityInverseMap` must be real `noncomputable def`s (per their recipes). Available API after those discharges: `infinityInverseMap_analyticOn`, `infinityInverseMap_x_eq`, `infinityInverseMap_y_eq`, `someRadius`, plus the simp lemmas from the `infinityChart` recipe (`infinityChart_source_eq`, `infinityChart_target_eq` if exposed). The pattern lemma `PartialHomeomorph.lift_openEmbedding_apply` is at `.lake/packages/mathlib/Mathlib/Topology/PartialHomeomorph/Constructions.lean:388`; `lift_openEmbedding_source` at `:394`.

2. **Compute the transition explicitly.** The forward composite map `t ↦ (...) ↦ x` works out (using `OnePoint.isOpenEmbedding_coe` and `lift_openEmbedding_apply`) to
   ```lean
   ((infinityChart H h).symm.trans (...)) t = (infinityInverseMap H h t).val.1
   ```
   on its source (everywhere a punctured disk + the `target` of `affineChartProjX p hpY`). Use `infinityInverseMap_x_eq` (recipe of `infinityInverseMap`, Step 5) to rewrite this as `c⁻¹ · t^{−2} · x̂(t)`, where `x̂` is analytic on `‖t‖ < someRadius H h` and `x̂(0) = 1`. Prove this via a sequence of `simp`s using `PartialHomeomorph.trans_apply`, `lift_openEmbedding_apply`, `affineChartProjX` unfolding (which is the projection `(x, y) ↦ x`, see `OddAtlas/AffineChart.lean:163`).

3. **Show the source is contained in a punctured disk.** `(infinityChart H h).symm.trans (...).source ⊆ {t | 0 < ‖t‖ ∧ ‖t‖ < someRadius H h}`. From the `infinityChart` recipe (Step 3), `(infinityChart H h).target = Metric.ball 0 (someRadius H h)`; the `.symm.trans (...)`source` is the intersection of `(infinityChart H h).target` with `(infinityChart H h) '' ((infinityChart H h).source ∩ (lift_openEmbedding ...).source)`. The lift_openEmbedding source excludes `∞` (since `affineChartProjX p hpY` is on the affine part), so `t ≠ 0`. Combine.

4. **Apply rational-times-analytic on the punctured disk.** With `c := H.f.leadingCoeff`, `c ≠ 0` (from `Polynomial.leadingCoeff_ne_zero_iff`), the function `t ↦ c⁻¹ · t^{−2} · x̂(t)` factors as `(t ↦ t^{−2}) · (t ↦ c⁻¹ · x̂(t))`. Citations:
   - `t ↦ c⁻¹ · x̂(t)` is `ContDiffOn ℂ ω` on `Metric.ball 0 (someRadius H h)`: `infinityInverseMap_analyticOn` (recipe of `infinityInverseMap` Step 5) gives `AnalyticOn ℂ x̂ (Metric.ball 0 r)`, hence `ContDiffOn ℂ ω x̂ (Metric.ball 0 r)` via `AnalyticOn.contDiffOn` (Mathlib `Mathlib.Analysis.Analytic.ContDiff`); then `(ContDiffOn.const_smul c⁻¹)` (Mathlib `Mathlib.Analysis.Calculus.ContDiff.Basic`).
   - `t ↦ t^{−2}` is `ContDiffOn ℂ ω` on `{t | t ≠ 0}`: use `ContDiffOn.zpow` (`Mathlib.Analysis.Calculus.ContDiff.Basic`) or `ContDiffOn.inv` (`.Mul`) composed with `(contDiff_id.pow 2).contDiffOn` (the pattern at `OddAtlas/AffineChart.lean:564–566`).
   - Multiply via `ContDiffOn.mul` (`Mathlib.Analysis.Calculus.ContDiff.Basic`).

5. **Assemble with `ContDiffOn.congr`.** Pattern from `OddAtlas/AffineChart.lean:518` (`affineChartProjX_compat_affineChartProjY`): rewrite the transition map to match the explicit `c⁻¹ · t^{−2} · x̂(t)` formula using `ContDiffOn.congr`, citing Step 2's explicit-form lemma and Step 4's analyticity.

6. **Discharge.** In `InfinityChart.lean:65–75`, replace
   ```lean
   axiom infinityChart_compat_affineLiftProjX
       (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
       (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
       ContDiffOn ℂ ω ...
   ```
   with the `theorem` whose body is the Step 5 assembly. Signature unchanged so the consumer `infinityChart_compat_affineLift` at `OddAtlas.lean:95` continues to compile.

**Next discrete deliverable.** **Step 2 alone** — prove the formula `((infinityChart H h).symm.trans (lift_openEmbedding (affineChartProjX p hpY) ...)) t = (infinityInverseMap H h t).val.1` as a separate `@[simp]` helper. This is a ~30 LOC chase through `PartialHomeomorph.trans_apply` + `lift_openEmbedding_apply` + `affineChartProjX` unfolding, and once proved, Steps 3–5 are mechanical applications of Mathlib's `ContDiffOn` calculus. This first deliverable is also shared verbatim with the recipe for `affineLiftProjX_compat_infinityChart` (which inverts the composition order), so it should land as a single PR feeding both.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` — replace `axiom infinityChart_compat_affineLiftProjX ...` (lines 65–75) with a `theorem` body. May also add `infinityChart_symm_trans_affineLiftProjX_apply` `@[simp]` helper from Step 2.
- (no other files; `InfinityInverse.lean` from the `infinityInverseMap` recipe already exports what we need)
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean` — no signature change; consumer at line 95 continues to type-check.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas` succeeds with the axiom replaced by a `theorem` (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticOdd.instIsManifold` no longer lists `infinityChart_compat_affineLiftProjX` (the consumer is `OddAtlas.lean:95`, transitively used by `instIsManifold` at `:159`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `infinityInverseMap_x_eq` from the `infinityInverseMap` recipe is *not* exposed as a usable `@[simp]` lemma (Step 5 of that recipe was a non-binding suggestion), Step 2 here cannot complete cleanly — escalate to that recipe rather than working around it locally.
- If the explicit formula `x(t) = c⁻¹ · t^{−2} · x̂(t)` turns out to require a non-trivial rebracketing (e.g. `x̂(t) = 1 + a₁t + …` with `a₁` depending on `H.f.coeff 1`/`H.f.coeff 0` in a non-uniform way that breaks `ContDiffOn ℂ ω`), **escalate** — the analyticity claim itself may be wrong as currently stated, and the recipe needs revision before continuing.
- If `ContDiffOn.zpow` for negative exponents is not directly available at the project's Mathlib pin, fall back to `ContDiffOn.inv` ∘ `ContDiffOn.pow` — but escalate if even those are missing, since the rational-function calculus is essential to the whole OA2 layer.

**Cross-plan patch (2026-06-03):** Namespace standardised on Mathlib's `PartialHomeomorph` (the stale `OpenPartialHomeomorph` references were hallucinated).
