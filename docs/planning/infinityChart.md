# `infinityChart` — discharge recipe

**Location:** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean:58`
**Route:** provable-from-other-axioms &nbsp;&nbsp; **Effort:** 7 &nbsp;&nbsp; **Est:** ~1.5–2 weeks, ~400 LOC (a single `noncomputable def` body inside `InfinityChart.lean`, plus significant filter/cocompact limit lemmas)
**Blocked by:** `infinityInverseMap`

**Statement (verbatim):**
```lean
/-- The chart at infinity: `PartialHomeomorph (HyperellipticOdd H h) ℂ`
sending a neighborhood of `OnePoint.infty` to a neighborhood of
`0 ∈ ℂ`, with `OnePoint.infty ↦ 0`.

The forward map (going `HyperellipticOdd → ℂ`) is `(x, y) ↦ y / x^{g+1}`
on the affine part where `x ≠ 0`, extended by `infty ↦ 0`. The inverse
map is `infinityInverseMap` extended by `0 ↦ infty`. -/
axiom infinityChart (H : HyperellipticData) (h : Odd H.f.natDegree) :
    OpenPartialHomeomorph (HyperellipticOdd H h) ℂ
```

**Why it's an axiom right now:** The docstring (`InfinityChart.lean:51–57`) lays out both the forward map (`(x, y) ↦ y / x^{g+1}`, `infty ↦ 0`) and the inverse map (`infinityInverseMap` extended by `0 ↦ infty`) — but assembling them into a fully-bundled `OpenPartialHomeomorph` requires (i) the inverse map itself, which is currently axiomatized as `infinityInverseMap` at `InfinityChart.lean:48`, and (ii) the continuity of the forward `y / x^{g+1}` map at `∞` *as a function on `OnePoint (HyperellipticAffine H)`*, which is not packaged anywhere yet. Load-bearing pieces: (i) `infinityInverseMap` and its analytic data (`someRadius`, the `t = 0 ↦ ∞` extension); (ii) `OnePoint.continuous_iff_continuousAt_infty` (`.lake/packages/mathlib/Mathlib/Topology/Compactification/OnePoint/Basic.lean:479`) for verifying continuity of the forward map at the added point; (iii) `OnePoint.isOpenEmbedding_coe` (`.lake/packages/mathlib/Mathlib/Topology/Compactification/OnePoint/Basic.lean:272`) for pulling the affine-part formula through the embedding. This is the same OA2 "construct the `PartialHomeomorph` by hand" task flagged in the file header `InfinityChart.lean:24–26`.

**`Gemini critique addressed:`**
- **Effort recalibration**: Bumped effort to 7 and LOC to ~400, recognizing the heavy topological filter work required for limits at infinity.
- **Domain correction**: Altered the `source` definition to explicitly exclude the $x=0$ locus. This prevents Lean's `y / 0 = 0` fallback from accidentally placing points with $x=0$ into the source, which would irrecoverably break continuity.
- **Algebraic limits**: Replaced the circular proof of continuity at $\infty$ with a rigorous algebraic limit via `Filter.cocompact` and degree bounds ($|y / x^{g+1}|^2 \sim |f(x)| / |x|^{2g+2} \to 0$).
- **Inverse definition**: Added an explicit standalone step defining the inverse function `infinityBackward` required for the partial homeomorphism.

**Proof recipe**

Follow `docs/hyperelliptic-odd-atlas-plan.md` §OA2 (lines 60–98): "* **Files.** Land in `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean`: — `noncomputable def infinityChart (H : HyperellipticData) (h : Odd H.f.natDegree) : PartialHomeomorph (HyperellipticOdd H h) ℂ`". Mathematical reference: **Miranda, *Algebraic Curves and Riemann Surfaces*, §III.1** (hyperelliptic charts and the local uniformizer at branch points of degree-2 covers); **Forster, *Lectures on Riemann Surfaces*, §1.1–§1.2** (one-point compactification and chart construction at the added point).

1. **Prerequisite — `infinityInverseMap` is real.** Wait for `docs/planning/infinityInverseMap.md` to be discharged; from now on we may call `infinityInverseMap`, `infinityInverseMap_analyticOn`, `infinityInverseMap_x_eq`, `infinityInverseMap_y_eq` (the API exported from the new `InfinityInverse.lean` per that recipe).

2. **Define the forward map (`toFun`) on `HyperellipticOdd H h`.** Recall `HyperellipticOdd H h := OnePoint (HyperellipticAffine H)` (`Hyperelliptic/Basic.lean:136–137`). Define
   ```lean
   noncomputable def infinityForward (H : HyperellipticData) (h : Odd H.f.natDegree) :
       HyperellipticOdd H h → ℂ :=
     OnePoint.rec 0 (fun p => p.val.2 / p.val.1 ^ (g H h + 1))
   ```
   where `g H h := (H.f.natDegree − 1) / 2`. Here `OnePoint.rec` (Mathlib `Topology/Compactification/OnePoint/Basic.lean`) is the eliminator that takes one value at `∞` and a function on the affine part.

3. **Define the backward map (`invFun`) on `ℂ`.** Define the explicit Lean function for the inverse:
   ```lean
   noncomputable def infinityBackward (H : HyperellipticData) (h : Odd H.f.natDegree) (t : ℂ) :
       HyperellipticOdd H h :=
     if t = 0 then (∞ : HyperellipticOdd H h)
     else ((infinityInverseMap H h t : HyperellipticAffine H) : HyperellipticOdd H h)
   ```

4. **Define the source and target.** Choose a radius `r := someRadius H h` from `InfinityInverse.lean`. Set
   - `target := Metric.ball (0 : ℂ) r` (open disk of radius `r` around `0`).
   - `source := (infinityForward H h) ⁻¹' target ∩ {p : HyperellipticOdd H h | p = ∞ ∨ p.val.1 ≠ 0}`
   This explicitly excludes the $x = 0$ locus. Because Lean handles division by zero by returning `0`, affine points where $x=0$ evaluate to $0 \in \text{target}$. Without this intersection, they would accidentally be included in `source`, destroying continuity.

5. **Verify `target` is open.** `Metric.isOpen_ball` (Mathlib `Mathlib.Topology.MetricSpace.Basic`).

6. **Verify `source` is open.** First, `{p | p = ∞ ∨ p.val.1 ≠ 0}` is open because its complement is the finite (hence closed) set of affine points where $x=0$. Then use `OnePoint.continuous_iff_continuousAt_infty` (`.lake/packages/mathlib/Mathlib/Topology/Compactification/OnePoint/Basic.lean:479`) to show continuity of `infinityForward` on this subset:
   - **Affine part.** The restriction of `infinityForward` to `{p : HyperellipticAffine H | p.val.1 ≠ 0}` is continuous because the denominator $x^{g+1}$ is strictly nonzero. Citation: `continuous_subtype_val.fst`, `continuous_subtype_val.snd`, `Continuous.div` (Mathlib `Mathlib.Topology.Algebra.Field`), `Continuous.pow`. The preimage of an open ball is open.
   - **Point at `∞`.** Continuity of `infinityForward` at `∞` requires establishing `Tendsto (fun p => p.val.2 / p.val.1 ^ (g + 1)) (cocompact (HyperellipticAffine H)) (𝓝 0)` algebraically. Formalize that if $p = (x, y)$ leaves compact sets in the curve $y^2 = f(x)$, then $x \to \infty$ in $\mathbb{C}$, and thus $|y / x^{g+1}|^2 = |f(x)| / |x|^{2g+2} \to 0$ because $\deg f = 2g+1 < 2g+2$. (Do not rely on the inverse map to deduce this limit).

7. **Verify `Set.LeftInvOn` / `RightInvOn`.** Use `infinityInverseMap_x_eq`, `infinityInverseMap_y_eq` from `InfinityInverse.lean`: by construction `infinityForward (infinityBackward H h t) = t` for `0 < ‖t‖ < r`, and `infinityBackward H h (infinityForward p) = p` for $p$ in the affine sub-source (via formal series being mutually inverse, e.g. `FormalMultilinearSeries.leftInv_eq_rightInv` at `.lake/packages/mathlib/Mathlib/Analysis/Analytic/Inverse.lean:283`). Extend by $0 \leftrightarrow \infty$: trivial from the `if t = 0` branching in `infinityBackward`.

8. **Bundle into `OpenPartialHomeomorph (HyperellipticOdd H h) ℂ`.** Mathlib's `OpenPartialHomeomorph` (`.lake/packages/mathlib/Mathlib/Topology/OpenPartialHomeomorph/Basic.lean`) requires: `toPartialEquiv`, `open_source`, `open_target`, `continuousOn_toFun`, `continuousOn_invFun`. Fill these from Steps 2–7.

9. **Discharge.** In `InfinityChart.lean:58–59`, replace
   ```lean
   axiom infinityChart (H : HyperellipticData) (h : Odd H.f.natDegree) :
       OpenPartialHomeomorph (HyperellipticOdd H h) ℂ
   ```
   with the `noncomputable def infinityChart ... := { toPartialEquiv := ..., open_source := ..., open_target := ..., continuousOn_toFun := ..., continuousOn_invFun := ... }` body of Step 8. Same signature, no downstream type changes.

**Next discrete deliverable.** **Steps 2 + 4 + 6b alone** — define `infinityForward` and prove the algebraic `Filter.cocompact` limit bounds showing continuity at infinity. This is ~200 LOC of self-contained analytic bounding, and acts as the crux of the topological verification. Steps 6a + 7 + 8 + 9 form the second PR.

**Files touched**
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean` — replace `axiom infinityChart ...` (lines 51–59) with the `noncomputable def infinityChart` body. Add `infinityForward`, `infinityBackward`, `infinityChart_source_eq`, `infinityChart_target_eq` helpers.
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityInverse.lean` (created by the `infinityInverseMap` recipe) — may need a small API extension `infinityInverseMap_eq_infty_iff` or similar.
- `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean` — no signature change; the references to `infinityChart` at `OddAtlas.lean:53, 56, 85, 110, 139` continue to compile unchanged.

**Acceptance**
- `lake build Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas` succeeds with the axiom replaced by a `noncomputable def` (no `sorry`).
- `#print axioms Jacobians.ProjectiveCurve.HyperellipticOdd.instChartedSpace` no longer lists `infinityChart` (the four `*_compat_*` OA2 axioms and `infinityChart_mem_source` still appear until they too are discharged).
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If `infinityInverseMap`'s discharge produced a *non-uniform* radius (one depending on `‖H.f.leadingCoeff‖`), Step 4's `source` and `target` must thread that radius through cleanly; if it turns out the radius cannot be made `H`-uniform, **escalate** — the chart may need to take an extra `r` argument, changing the signature.
- If establishing the algebraic cocompact limit bounding for $|y / x^{g+1}|$ requires rewriting significant parts of Mathlib's `Filter.cocompact` API over subsets of $\mathbb{C}^2$, **escalate** before writing >300 lines of general topology boilerplate.
- If the proof requires changing the *target type* from `OpenPartialHomeomorph` to `PartialHomeomorph` (older Mathlib API), do **not** silently rewrite — the six dependent axioms (`infinityChart_mem_source`, `*_compat_*`) use `.source`, `.symm.trans`, and `.lift_openEmbedding` in ways that depend on the precise `OpenPartialHomeomorph` API. Escalate.
---
**Vetting trail.** Critique: `_vetting/infinityChart.md`. Verdict: revise. Revised: 2026-06-03.