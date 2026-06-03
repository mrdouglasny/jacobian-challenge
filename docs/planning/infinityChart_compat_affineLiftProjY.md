# `infinityChart_compat_affineLiftProjY` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:90`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~3–5 days, ~150 LOC (a single ContDiffOn proof in `InfinityChart.lean`; mirrors the X-direction but uses `affineChartProjY` which is `(x, y) ↦ y` on `smoothLocusX`)
**Blocked by:** `infinityChart`, `infinityInverseMap` (transitively)

**Statement (verbatim):**
```lean
/-- Remaining OA2 local boundary: infinity chart followed by the lifted affine `y`-chart. -/
axiom infinityChart_compat_affineLiftProjY
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpX : p ∈ HyperellipticAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) : ℂ → ℂ)
      ((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source
```

**Why it's an axiom right now:** The transition is `t ↦ y(t)` where `(x(t), y(t)) = infinityInverseMap H h t` and the chart reads off the `y`-coordinate via `affineChartProjY` (which is the projection `(x, y) ↦ y` on `smoothLocusX`, see `OddAtlas/AffineChart.lean:291–293`). By the formula `y(t) = (lc(f))^{−(2g+1)/2} · t^{−(2g+1)} · (1 + O(t))` from `InfinityChart.lean:12–13` and the `infinityInverseMap` recipe, the map is `t ↦ α^{−1} · t^{−(2g+1)} · ŷ(t)`, meromorphic in `t` with a pole of order `2g+1` at `t = 0`, analytic on `0 < ‖t‖ < r`. The chart `affineChartProjY` is valid where `f'(x) ≠ 0`, i.e. at branch points; the hypothesis `hpX : p ∈ smoothLocusX H` ensures we land on the branch-point branch of the chart family. This is the **branch-point case** flagged in ROADMAP.

**Proof recipe**

Follow `docs/hyperelliptic-odd-atlas-plan.md` §OA2 / OA3 (lines 105–115): "* `affineProjY × infinity` — composition of the above two." Mathematical reference: chain rule for `ContDiffOn` (`Mathlib.Analysis.Calculus.ContDiff.Basic` `ContDiffOn.comp`); rational-function analyticity (`Mathlib.Analysis.Calculus.ContDiff.Polynomial`).

1. **Prerequisites.** Both `infinityChart` and `infinityInverseMap` real (per `docs/planning/infinityChart.md`, `docs/planning/infinityInverseMap.md`). Available API: `infinityInverseMap_analyticOn`, `infinityInverseMap_y_eq`, `someRadius`, `OpenPartialHomeomorph.lift_openEmbedding_apply` (`.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Constructions.lean:388`), and `affineChartProjY` (`OddAtlas/AffineChart.lean:291`).

2. **Compute the transition explicitly.** Parallel to Step 2 of `infinityChart_compat_affineLiftProjX.md` but with `affineChartProjY` (which projects to `y`):
   ```lean
   ((infinityChart H h).symm.trans
       ((affineChartProjY p hpX).lift_openEmbedding ...)) t
   = (infinityInverseMap H h t).val.2     -- the y-coordinate of the inverse
   ```
   on its source (a punctured disk + the `target` of `affineChartProjY p hpX`). Use `infinityInverseMap_y_eq` (recipe of `infinityInverseMap`, Step 5) to rewrite this as `α⁻¹ · t^{−(2g+1)} · ŷ(t)`, where `ŷ` is analytic on `‖t‖ < someRadius H h` with `ŷ(0) = 1` and `α = c^{1/(2g+1)}` is a chosen `(2g+1)`-th root of `c := H.f.leadingCoeff`. Prove this as a `@[simp]` helper `infinityChart_symm_trans_affineLiftProjY_apply` parallel to the one in `infinityChart_compat_affineLiftProjX.md`.

3. **Show the source is contained in a punctured disk.** Same argument as Step 3 of `infinityChart_compat_affineLiftProjX.md`: the `lift_openEmbedding` source excludes `∞`, hence `t ≠ 0`, and `(infinityChart H h).target = Metric.ball 0 (someRadius H h)`. Combine.

4. **Apply rational-times-analytic on the punctured disk.** With `α := Complex.cpow c (1/(2g+1 : ℂ))`, `α ≠ 0` (since `c ≠ 0`, via `Complex.cpow_ne_zero`):
   - `t ↦ α⁻¹ · ŷ(t)` is `ContDiffOn ℂ ω` on `Metric.ball 0 (someRadius H h)`: `infinityInverseMap_analyticOn` gives `AnalyticOn ℂ ŷ (Metric.ball 0 r)`, hence `ContDiffOn ℂ ω`; then `ContDiffOn.const_smul α⁻¹`.
   - `t ↦ t^{−(2g+1)}` is `ContDiffOn ℂ ω` on `{t | t ≠ 0}`: use `ContDiffOn.zpow` or `ContDiffOn.inv ∘ (contDiff_id.pow (2g+1)).contDiffOn`, same pattern as `OddAtlas/AffineChart.lean:564–566`.
   - Multiply via `ContDiffOn.mul`.

5. **Assemble with `ContDiffOn.congr`.** Same pattern as `affineChartProjX_compat_affineChartProjY` at `OddAtlas/AffineChart.lean:518`.

6. **Discharge.** In `InfinityChart.lean:89–99`, replace the `axiom infinityChart_compat_affineLiftProjY ...` block with a `theorem` whose body is the Step 5 assembly. Signature unchanged so consumer `infinityChart_compat_affineLift` at `OddAtlas.lean:105` continues to compile.

**Next discrete deliverable.** **Step 2 + Step 4 together** — prove the explicit `α⁻¹ · t^{−(2g+1)} · ŷ(t)` form is `ContDiffOn ℂ ω` on the punctured disk. ~40 LOC, mechanical once `infinityInverseMap_analyticOn` is exported. Then Step 3 (source restriction via `ContDiffOn.mono`) is a ~10 LOC follow-up.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` — replace `axiom infinityChart_compat_affineLiftProjY ...` (lines 89–99) with a `theorem` body. May also add `infinityChart_symm_trans_affineLiftProjY_apply` `@[simp]` helper from Step 2.
- (no other files; `InfinityInverse.lean` from the `infinityInverseMap` recipe already exports what we need)
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean` — no signature change; consumer at line 105 continues to type-check.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas` succeeds with the axiom replaced by a `theorem` (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticOdd.instIsManifold` no longer lists `infinityChart_compat_affineLiftProjY` (consumer `infinityChart_compat_affineLift` at `OddAtlas.lean:105`, transitively `instIsManifold` at `:159`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `infinityInverseMap_y_eq` from the `infinityInverseMap` recipe (Step 5 of that recipe is non-binding) does *not* produce the explicit form `α⁻¹ · t^{−(2g+1)} · ŷ(t)` cleanly, escalate to that recipe — the local fix here would be to inline the formula, which duplicates work and risks divergence with the X-direction proof.
- The `Complex.cpow c (1/(2g+1 : ℂ))` choice in Step 4 picks a *specific* `(2g+1)`-th root of `c`; if that choice is incompatible with the choice made inside `infinityInverseMap` (Step 2 of that recipe), the formula in Step 2 here will be off by a `(2g+1)`-th root of unity, and Step 5's `ContDiffOn.congr` will fail. **Escalate** to coordinate the root choice between this recipe and the `infinityInverseMap` recipe before discharge.
- Branch-point regularity. `affineChartProjY` is valid only on `smoothLocusX` (where `f'(x) ≠ 0`); if the recipe of `infinityChart` builds a source that intersects `smoothLocusY \ smoothLocusX` in a way that ignores branch-point regularity, the composite source may be empty for *some* `p`. This is acceptable (the chart compat is trivially `ContDiffOn ℂ ω _ ∅`), but if it happens for *all* `p ∈ smoothLocusX`, the `IsManifold` instance has no content at branch points — escalate before silently shipping.
