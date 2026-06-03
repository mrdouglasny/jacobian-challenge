# `affineLiftProjY_compat_infinityChart` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:102`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 3 &nbsp;&nbsp; **Est:** ~3–5 days, ~150 LOC (a single ContDiffOn proof in `InfinityChart.lean`; the **branch-point symmetric** to `affineLiftProjX_compat_infinityChart`)
**Blocked by:** `infinityChart`, `infinityInverseMap` (transitively)

**Statement (verbatim):**
```lean
/-- Remaining OA2 local boundary: the lifted affine `y`-chart followed by the infinity chart. -/
axiom affineLiftProjY_compat_infinityChart
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpX : p ∈ HyperellipticAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) : ℂ → ℂ)
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source
```

**Why it's an axiom right now:** The transition is the *reverse* of `infinityChart_compat_affineLiftProjY`: now we start with `y ∈ ℂ` (the `affineChartProjY` chart value), produce the affine point `(x(y), y) = (affineChartProjY p hpX).symm y` (where `x(y) = (polynomialLocalHomeomorph H p hpX).symm (y^2)` is the chosen local inverse of `x ↦ f(x)` near a branch root, per `OddAtlas/AffineChart.lean:394–397`), lift along `OnePoint.isOpenEmbedding_coe`, then apply the forward `infinityChart` map `(x, y) ↦ y / x^{g+1}`. The map is `y ↦ y / (x(y))^{g+1}` where `x(y)` is analytic on the chart target. This is the **branch-point symmetric** case of `affineLiftProjX_compat_infinityChart`: the hypothesis `hpX : p ∈ smoothLocusX H` confines us to the chart family valid at branch points. As above, both `infinityChart` and the local-inverse branch live behind axioms, hence this is axiomatic too.

**Proof recipe**

Follow `docs/hyperelliptic-odd-atlas-plan.md` §OA2 / OA3 (the same `affineProjY × infinity` bullet, lines 105–115). Mathematical reference: chain rule for `ContDiffOn` (`Mathlib.Analysis.Calculus.ContDiff.Basic` `ContDiffOn.comp`); analyticity of the local polynomial-inverse branch (`polynomialLocalHomeomorph_contDiffOn_symm` at `OddAtlas/AffineChart.lean:536`).

1. **Prerequisites.** Both `infinityChart` and `infinityInverseMap` real (per their recipes). Available API: `infinityForward` (`infinityChart` recipe Step 2), `polynomialLocalHomeomorph_contDiffOn_symm` (`OddAtlas/AffineChart.lean:536`, already a theorem), `affineChartProjY_symm_apply_fst`, `affineChartProjY_symm_apply_snd` (`OddAtlas/AffineChart.lean:394, 404`, already simp lemmas), project-specific partial homeomorph lift/trans lemmas (often `.lift_openEmbedding_apply`).

2. **Compute the transition explicitly.** Using `PartialHomeomorph.trans_apply`, `lift_openEmbedding_apply`, and the simp lemmas above:
   ```lean
   ((lift_openEmbedding (affineChartProjY p hpX) ...).symm.trans (infinityChart H h)) y
   = infinityForward H h ((↑) ((affineChartProjY p hpX).symm y))
   = (((affineChartProjY p hpX).symm y).val.2) / (((affineChartProjY p hpX).symm y).val.1) ^ (g H h + 1)
   = y / ((polynomialLocalHomeomorph H p hpX).symm (y ^ 2)) ^ (g H h + 1)
   ```
   using `affineChartProjY_symm_apply_snd` (`= y`) and `affineChartProjY_symm_apply_fst` (`= (polynomialLocalHomeomorph H p hpX).symm (y^2)`). Prove this as a `@[simp]` helper `affineLiftProjY_trans_infinityChart_apply` parallel to the X-direction analog.

3. **Source analysis.** The source of the composite is the set of `y` in `(affineChartProjY p hpX).target` such that (a) `y^2 ∈ (polynomialLocalHomeomorph H p hpX).target` (already part of the chart target), and (b) the lifted affine point `(x(y), y)` lies in the manifold-level `(infinityChart H h).source`. Condition (b) enforces a geometric restriction on the curve (typically $|x(y)| > R$ for a large radius $R$ bounding all roots of $H.f$). Because this radius geometrically bounds $x(y)$ away from all roots $a$, this manifold-level source condition formally guarantees $x(y) \neq 0$ and strictly excludes all finite branch points (including $y=0$ for any branch root $a$). We specifically do *not* rely on the complex target ball `Metric.ball 0 R` to exclude branch points: at a branch point $p = (a, 0)$ with $a \neq 0$, the formula evaluates to $0/a^{g+1} = 0$, which incorrectly lands perfectly in the target ball. The manifold `.source` is what securely filters out the finite branch points.

4. **Apply rational-times-analytic on the source.** Decompose:
   - `y ↦ (polynomialLocalHomeomorph H p hpX).symm (y^2)` is `ContDiffOn ℂ ω` on `{y | y^2 ∈ (polynomialLocalHomeomorph H p hpX).target}` by composition: `(contDiff_id.pow 2).contDiffOn` for `y ↦ y^2` (Mathlib `Mathlib.Analysis.Calculus.ContDiff.Basic`, pattern at `OddAtlas/AffineChart.lean:564–566`), composed with `polynomialLocalHomeomorph_contDiffOn_symm` (`OddAtlas/AffineChart.lean:536`) via `ContDiffOn.comp`. This is *the same composition* used in the proof of `affineChartProjY_compat_affineChartProjX` at `OddAtlas/AffineChart.lean:556–573`.
   - `x ↦ 1 / x^{g+1}` is `ContDiffOn ℂ ω` on `{x | x ≠ 0}` (`ContDiffOn.inv ∘ (contDiff_id.pow (g+1))`).
   - `y` itself (numerator) is trivially `ContDiffOn ℂ ω` (`contDiffOn_id`).
   - Compose and multiply via `ContDiffOn.comp` + `ContDiffOn.mul`. Source restriction in Step 3 ensures $|x(y)| > R > 0$, feeding the `x ≠ 0` hypothesis.

5. **Assemble with `ContDiffOn.congr`.** Same pattern as `affineChartProjY_compat_affineChartProjX` (`OddAtlas/AffineChart.lean:556–573`).

6. **Discharge.** In `InfinityChart.lean:101–111`, replace the `axiom affineLiftProjY_compat_infinityChart ...` block with a `theorem` whose body is the Step 5 assembly. Signature unchanged so consumer `affineLift_compat_infinityChart` at `OddAtlas.lean:130` continues to compile.

**Next discrete deliverable.** **Steps 2 + 4 together** — prove the explicit `y / x(y)^{g+1}` form is `ContDiffOn ℂ ω` on `{y | y^2 ∈ ... .target ∧ x(y) ≠ 0}`. ~50 LOC, mechanical from the existing `polynomialLocalHomeomorph_contDiffOn_symm` theorem. Then Step 3's source-restriction analysis (using the manifold source to guarantee $x(y) \neq 0$) and Step 5's assembly form a second ~30 LOC PR.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` — replace `axiom affineLiftProjY_compat_infinityChart ...` (lines 101–111) with a `theorem` body. Add `affineLiftProjY_trans_infinityChart_apply` `@[simp]` helper from Step 2.
- (no other files; the existing `OddAtlas/AffineChart.lean` API covers `polynomialLocalHomeomorph_contDiffOn_symm`, `affineChartProjY_symm_apply_fst`, `affineChartProjY_symm_apply_snd`)
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean` — no signature change; consumer at line 130 continues to type-check.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas` succeeds with the axiom replaced by a `theorem` (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticOdd.instIsManifold` no longer lists `affineLiftProjY_compat_infinityChart` (consumer `affineLift_compat_infinityChart` at `OddAtlas.lean:130`, transitively `instIsManifold` at `:159`).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- The $x(y) \neq 0$ hypothesis in Step 4 is **load-bearing**: if the recipe of `infinityChart` does *not* restrict `(infinityChart H h).source` on the manifold to geometrically exclude points where $x = a$ for roots of $f$, the composite source would include finite branch points. **Escalate** if Step 3's source analysis cannot formally extract $|x(y)| > R$ (and therefore $x \neq 0$) from the manifold `infinityChart.source` property.
- Lean evaluates division by zero as $z / 0 = 0$. This means that the explicit complex formula mathematically "works" (lands exactly at 0 in the target ball) for a branch point where $a \neq 0$. If you mistakenly rely on the target ball to define injectivity and source compatibility, the proof will silently swallow these branch points until `ContDiffOn` (which requires bounded derivatives / avoids poles) correctly fails to typecheck. Pay strict attention to extracting the nonzero bound from the manifold `.source` before trying to discharge `ContDiffOn`.
- If the statement needs to change shape (e.g. via a Mathlib bump moving `PartialHomeomorph` structure), do not silently rewrite — both the precise `lift_openEmbedding` API and the consumer at `OddAtlas.lean:130` are load-bearing.

### Gemini critique addressed:
- **Fixed Source vs. Target conflation:** Updated Step 3 to rigorously pull the $x \neq 0$ condition from the manifold `.source` (the geometric property $|x| > R$) rather than the target ball in $\mathbb{C}$.
- **Addressed the $a \neq 0$ blindspot:** Explained that for branch points $(a, 0)$ with $a \neq 0$, the expression $0 / a^{g+1}$ evaluates to $0$, perfectly inside the target ball; thus, relying on the target ball is logically flawed and the manifold `.source` is required to guarantee branch point exclusion.
- **Corrected Lean Division by Zero nuance:** Updated the Risk section to reflect that $z / 0 = 0$ in Lean, meaning division by zero is not strictly "undefined" in the term language, making the $a \neq 0$ blindspot even more perilous. The failure is caught correctly by `ContDiffOn`.
- **Corrected Mathlib namespace:** Removed references to the hallucinated `OpenPartialHomeomorph` namespace, replacing them with standard `PartialHomeomorph` / local dot-notation.

---
**Vetting trail.** Critique: `_vetting/affineLiftProjY_compat_infinityChart.md`. Verdict: revise. Revised: 2026-06-03.