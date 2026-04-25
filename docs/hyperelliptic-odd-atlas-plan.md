# HyperellipticOdd atlas plan (focused)

_Drafted 2026-04-25 (companion to `hyperelliptic-atlas-plan.md` from
2026-04-23, narrowed to the **odd-degree** parity that
`Jacobians/Extensions/Hyperelliptic.lean` immediately needs)._

## Why this plan exists

`Jacobians/Extensions/Hyperelliptic.lean` currently has two
**temporary `axiom`s** at the top:

```lean
axiom HyperellipticOdd.instChartedSpace : ChartedSpace ℂ (HyperellipticOdd H h)
axiom HyperellipticOdd.instIsManifold   : IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticOdd H h)
```

These were added by Codex when extending the challenge with hyperelliptic
test theorems, because `HolomorphicOneForm (HyperellipticOdd H h)` is
not even *well-typed* without `ChartedSpace + IsManifold`. We need to
discharge them with a real chart construction so the extension theorems
have an honest base.

This is **the prerequisite for**:
- `hyperellipticDxOverY` (warm-up: construct `dx/y` as a real
  `HolomorphicOneForm`);
- `hyperellipticBasisDifferential` and the canonical basis;
- `genus_HyperellipticOdd_eq` (the headline test).

## Current state

```
HyperellipticAffine H := { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 }
HyperellipticOdd H h  := OnePoint (HyperellipticAffine H)        -- requires Odd H.f.natDegree
```

`HyperellipticAffine` has: `TopologicalSpace`, `T2Space`,
`LocallyCompactSpace`, plus axioms for `connected` and `noncompact`.
**No `ChartedSpace` yet.**

`HyperellipticOdd` inherits the topology from `OnePoint`, plus instances
for `T2`, `Compact`, `Nonempty`, `ConnectedSpace`. **No `ChartedSpace`,
no `IsManifold`.**

## Phases (mirrors the master plan §H1–H4, scoped to odd parity)

### Phase OA1 — Affine smooth-locus chart (3–4 days, ~200–400 LOC)

Build a `ChartedSpace ℂ (HyperellipticAffine H)` instance using the
implicit function theorem.

* **Smooth-locus split.** Squarefreeness of `f` ⇒ at every point
  `(x₀, y₀)` of `HyperellipticAffine`, at least one of
  `∂_y(y² - f) = 2y₀` and `∂_x(y² - f) = -f'(x₀)` is nonzero. So:
  - **`y ≠ 0`**: chart `(x, y) ↦ x` works; inverse via the analytic
    branch of `√(f(x))` near `x₀`.
  - **`y = 0`** (necessarily a root of `f`): chart `(x, y) ↦ y`
    works; inverse via the analytic implicit function `x = x(y)` from
    `y² = f(x)`, since `f'(x₀) ≠ 0` by squarefreeness.

* **Mathlib API.** `ContDiffAt.toPartialHomeomorph` from
  `Mathlib.Analysis.Calculus.InverseFunctionTheorem`. Returns a
  `PartialHomeomorph` from a neighborhood of the source point to a
  neighborhood of the target. Use the `ω` smoothness level (analytic).

* **Files.** Land in
  `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/AffineChart.lean`:
  - `noncomputable def affineChartProjX : (x₀, y₀) ∈ smoothLocusY → PartialHomeomorph _ ℂ`
  - `noncomputable def affineChartProjY : (x₀, y₀) ∈ smoothLocusX → PartialHomeomorph _ ℂ`
  - The `ChartedSpace ℂ (HyperellipticAffine H)` instance.

### Phase OA2 — Chart at infinity (3–5 days, ~150–250 LOC)

Extend the affine atlas to a `ChartedSpace ℂ (HyperellipticOdd H h)` via
the `OnePoint` extension.

* **Odd-degree fact.** When `deg f = 2g + 1`, the Riemann surface has a
  *single* point at infinity which is a **branch point** of the
  hyperelliptic projection `(x, y) ↦ x`. So a chart at `∞` needs a
  uniformizer that captures this.

* **Standard chart.** Set `t := y / x^{g+1}`. Then near `∞`,
  `x = 1/t² · (1 + O(t))` and `y = 1/t^{2g+1} · (1 + O(t))`. The map
  `t ↦ (x(t), y(t))` is an analytic bijection from a punctured disk
  around `0` onto a punctured neighborhood of `∞`, extending continuously
  by `t = 0 ↦ ∞`.

* **Mathlib API.**
  `OnePoint.openEmbedding_coe : OpenEmbedding ((↑) : X → OnePoint X)` —
  affine charts pull back to charts on `OnePoint X` for points coming
  from `X`. The chart at `∞` itself needs a separate construction;
  there is no general "chart at the added point" lemma in Mathlib.

* **Files.** Land in
  `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas/InfinityChart.lean`:
  - `noncomputable def infinityChart (H : HyperellipticData) (h : Odd H.f.natDegree) : PartialHomeomorph (HyperellipticOdd H h) ℂ`
  - Compatibility lemma with affine charts on the punctured overlap.

### Phase OA3 — Assemble `ChartedSpace + IsManifold` (2–3 days, ~150–250 LOC)

* **`ChartedSpace ℂ (HyperellipticOdd H h)` instance.** Pack
  `{affineChartProjX, affineChartProjY, infinityChart}` into the
  instance. The `chartAt` function picks the right chart per point.

* **`IsManifold 𝓘(ℂ) ω` instance.** Verify all pairwise transitions
  are in `contDiffGroupoid ω 𝓘(ℂ)`. Three transitions:
  - `affineProjX × affineProjY` (overlap where both `y` and `f'(x)` are
    nonzero) — analytic by construction.
  - `affine × infinity` — the chart at `∞` is `t ↦ (x(t), y(t))`; the
    transition `t ↦ x(t) = 1/t²` is analytic on `t ≠ 0`.
  - `affineProjY × infinity` — composition of the above two.

* **Files.** `Jacobians/ProjectiveCurve/Hyperelliptic/OddAtlas.lean`
  (entry point) ties it all together.

### Phase OA4 — Retire the temp axioms (1 day)

Once `OddAtlas` builds, delete the two `axiom HyperellipticOdd.instX` /
`attribute [instance]` lines at the top of
`Jacobians/Extensions/Hyperelliptic.lean`. Lean's instance resolution
picks up the real instances from `OddAtlas`.

## Total estimate

**~10–13 days of focused Lean work, ~600–900 LOC.** Mirrors phases
H1–H4 of the master plan (`docs/hyperelliptic-atlas-plan.md`) but
specialized to the simpler odd-degree parity (single point at infinity
which is itself a branch point).

The even-degree parity (two points at infinity, `∞₊` and `∞₋`,
distinguished by sign of leading `y`) has its own atlas — different
file tree, different transition algebra. Out of scope for this plan;
addressed by an analogous `EvenAtlas/` later.

## Payoff

- The two temporary `axiom`s in `Extensions/Hyperelliptic.lean` retire.
- `HolomorphicOneForm (HyperellipticOdd H h)` is honestly typed.
- The warm-up theorems (`hyperellipticDxOverY`, basis differentials)
  become attackable.
- The headline genus theorem `genus_HyperellipticOdd_eq` becomes
  attackable (modulo the bridge sorries for the upper-bound side).

## Out of scope here

- Proving the genus formula itself — that's master plan phase H6.
- Even-degree parity — separate file tree.
- Discharging `AX_Hyperelliptic_oddEquiv` / `AX_Hyperelliptic_genus`
  on the unified `Hyperelliptic` type — those route through this work
  but live in `Jacobians/ProjectiveCurve/Hyperelliptic.lean`.
