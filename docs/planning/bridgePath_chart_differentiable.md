# `bridgePath_chart_differentiable` — discharge recipe

**Location:** `Jacobians/Bridge/KirovLineIntegral.lean:182`
**Route:** needs-infra &nbsp;&nbsp; **Effort:** 8 &nbsp;&nbsp; **Est:** ~3-5 focused days, ~300–500 LOC, in `Jacobians/Bridge/BridgePath.lean`
**Blocked by:** `bridgePath`

**Statement (verbatim):**
```lean
/-- The chosen path is `C¹` in chart pullbacks at every `t`.

This is the chart-local smoothness hypothesis used throughout
`Jacobians.Vendor.Kirov.LineIntegral` (cf.
`pathSpeed_comp_eq_mfderiv`, `lineIntegral_pullback`). It
sidesteps the real-vs-complex `ModelWithCorners` mismatch that a
naive `ContMDiff (𝓘(ℝ, ℝ)) 𝓘(ℂ, ℂ) ω` hypothesis would create.

Discharge plan: in a connected complex manifold, a path produced by
`PathConnectedSpace.somePath` can be smoothed (Mathlib has the
relevant smoothing infra in `Topology.MetricSpace.LipschitzAddSubgroup`
and friends; the exact statement we need is "every continuous path
between two points is homotopic to a chart-local-`C¹` path"). -/
axiom bridgePath_chart_differentiable (P₀ P : X) (t : ℝ) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (bridgePath (X := X) P₀ P t)).toFun ∘
        (bridgePath (X := X) P₀ P)) t
```

**Why it's an axiom right now:** The chart-local smoothness hypothesis underwrites every Kirov-side lemma that touches `pathSpeed`: `pathSpeed_comp_eq_mfderiv` (`Vendor/Kirov/LineIntegral.lean:506`) requires the chart-composite to be `DifferentiableAt`, and downstream consumers (`pathSpeed_reverse` `:194`, `lineIntegral_pullback` ~`:614`) propagate this. The axiom is scaffolding around `bridgePath`: per the docstring at `KirovLineIntegral.lean:108–114`, this is not load-bearing in `kirovBackedFunctional` itself, but it is mandatory for every downstream theorem that takes a `pathSpeed` derivative. Discharging this requires building missing infrastructure to correctly glue parameterized path segments with matching derivatives at chart boundaries, contrary to the overly optimistic docstring at `:177–181`.

**Proof recipe**

This recipe assumes `bridgePath` was discharged per [`bridgePath.md`](bridgePath.md) by the chart-line concatenation construction. We must build explicit piecewise gluing infrastructure and a polynomial easing function to ensure derivatives match (equal 0) at the joints, avoiding non-differentiable corners between affine pieces.

1. **Build polynomial easing infrastructure.** Define a polynomial easing function $s : \mathbb{R} \to \mathbb{R}$ specifically to flatten the derivatives at the boundaries of the interval $[0, 1]$. The standard choice is $s(t) = 3t^2 - 2t^3$. Prove:
   - $s(0) = 0$ and $s(1) = 1$.
   - $s'(0) = 0$ and $s'(1) = 0$.
   - $s$ is monotonic on $[0, 1]$, mapping it bijectively to $[0, 1]$.
   - $s$ is `Differentiable ℝ`.

2. **Build zero-derivative differentiable gluing infrastructure.** Since `Mathlib` lacks a pre-built differentiable concatenation API, formulate and prove a gluing lemma. Prove that if two differentiable paths $f_1, f_2 : \mathbb{R} \to E$ meet at time $t_i$ ($f_1(t_i) = f_2(t_i)$), and *both* have derivative $0$ at $t_i$, their piecewise concatenation at $t_i$ is `DifferentiableAt ℝ` at $t_i$. This will require manual limit manipulation using `HasFDerivAt` boundary logic.

3. **Identify the chart-line piece and apply easing.** The construction in [`bridgePath.md`](bridgePath.md) step 4 covers `[0, 1]` by finitely many sub-intervals `[t_i, t_{i+1}]`. We parameterize the path on each piece using the easing function $s$ composed with the affine map sending `[t_i, t_{i+1}]` to `[0,1]`. By the helper `extChartAt_chartLine` already in this file (`KirovLineIntegral.lean:263`), the path in local coordinates is:
   ```lean
   (extChartAt 𝓘(ℂ, ℂ) Pᵢ) (chartLine Pᵢ zᵢ t) = (1 - s(t)) • (extChartAt _) Pᵢ + s(t) • zᵢ
   ```
   By the chain rule (`Differentiable.add`, `Differentiable.smul_const`), this composite is `DifferentiableAt ℝ` everywhere on the sub-interval and strictly has derivative $0$ at the joints $t_i$ and $t_{i+1}$.

4. **Bridge from `extChartAt` to `chartAt`.** The axiom statement requires differentiability at `(chartAt (H := ℂ) (bridgePath P₀ P t)).toFun ∘ bridgePath P₀ P`, evaluated **at the point `bridgePath P₀ P t`**. When transitioning between charts, use chart compatibility (the transitions are $C^\infty$ on the overlap; `Mathlib/Geometry/Manifold/IsManifold.lean`). Because $X$ is a complex manifold, the chart transitions are natively complex-differentiable ($\mathbb{C}$-differentiable). Since the axiom requires `DifferentiableAt ℝ`, you **must explicitly apply `DifferentiableAt.restrict_scalars`** (from $\mathbb{C}$ to $\mathbb{R}$) after composing the transition map via the chain rule (`DifferentiableAt.comp` / `AnalyticAt.differentiableAt`).

5. **Final tactic body.**
   - Unfold the boundary definitions: `Path.extend` defines the path as constant outside `[0, 1]` (`Mathlib/Topology/Path.lean:189`, `:222`). Constant functions are trivially `DifferentiableAt`.
   - On the interior, use case-analysis to find the `[t_i, t_{i+1}]` interval.
   - For $t \in (t_i, t_{i+1})$, use Step 3 + Step 4.
   - For $t = t_i$, invoke the zero-derivative gluing lemma (Step 2) combined with the zero-derivative property of the easing function (Step 1).
   - Finally, move the finished proof to replace the `axiom` at `KirovLineIntegral.lean:182` with `theorem bridgePath_chart_differentiable`.

**Files touched**
- `Jacobians/Bridge/BridgePath.lean` — add easing function $3t^2 - 2t^3$ and its derivative properties, add the zero-derivative differentiable gluing lemma, and add `theorem bridgePath_chart_differentiable` (~300–500 LOC).
- `Jacobians/Bridge/KirovLineIntegral.lean` — delete `axiom bridgePath_chart_differentiable` at `:182` (lines 169–185 doc-block + axiom).

**Acceptance**
- `lake build Jacobians.Bridge.KirovLineIntegral` succeeds.
- `#print axioms Jacobians.Vendor.Kirov.pathSpeed_comp_eq_mfderiv`-using consumers (e.g. `chartLine_FTC` at `KirovLineIntegral.lean:276` once filled, or any downstream `lineIntegral_pullback` invocation) no longer list `bridgePath_chart_differentiable`.
- `python3 gate.py --repo jacobian-challenge --build Jacobians` returns PASS; axiom count drops by 1.

**Risk / escalation triggers**
- If the explicit limit manipulations required for the zero-derivative piecewise gluing lemma in Step 2 become excessively long or fail due to undocumented `HasFDerivAt.piecewise` gaps, escalate.
- If Lean's typeclass inference struggles with `DifferentiableAt.restrict_scalars` bridging the complex-manifold model bounds to real-differentiability bounds, escalate.

## Gemini critique addressed:
- Changed route to `needs-infra` and updated effort from 5 to 8 (300-500 LOC) reflecting the reality of building piecewise path concatenation API from scratch.
- Removed the hallucinated Mathlib reference `Topology.MetricSpace.LipschitzAddSubgroup` and replaced the invalid `ContDiffBump` approach with the correct mathematical construction: an explicit polynomial easing function ($3t^2 - 2t^3$).
- Added a prerequisite infrastructure step to prove a generic gluing lemma for zero-derivative differentiable paths meeting at a boundary, addressing the mathematical failure of concatenated affine pieces having non-differentiable corners.
- Detailed the explicit need for `DifferentiableAt.restrict_scalars` to transition from the complex-differentiable chart boundaries to the $\mathbb{R}$-differentiable axiom statement.
---
**Vetting trail.** Critique: `_vetting/bridgePath_chart_differentiable.md`. Verdict: reject. Revised: 2026-06-03.