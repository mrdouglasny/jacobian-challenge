# Plan: `genus (Hyperelliptic H) = H.genus` as a real theorem

_Drafted 2026-04-23. Target: retire `AX_Hyperelliptic_genus` to a
derived theorem via the explicit classical `x^k dx / y` basis._

## Axiom being retired

```lean
axiom AX_Hyperelliptic_genus (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus
```

Location: `Jacobians/ProjectiveCurve/Hyperelliptic.lean`.

`H.genus = (H.f.natDegree - 1) / 2`, equivalently `⌊(deg f - 1)/2⌋`.

## Classical content

The space of holomorphic 1-forms on a hyperelliptic curve
`C : y² = f(x)` (with `f` squarefree of degree `d = 2g+1` or `2g+2`)
has dimension exactly `g`. Explicit basis:

$$
\omega_k \;=\; \frac{x^k\, dx}{y}, \qquad k = 0, 1, \dots, g-1.
$$

These forms are holomorphic everywhere on the smooth projective
hyperelliptic curve — away from branch points, at branch points (where
`t = √(x-a)` is a local parameter and `y = t · g(t)` for some unit
`g`), and at infinity (where `1/x` or similar gives local coords).

## Target theorems

```lean
namespace Jacobians.ProjectiveCurve.Hyperelliptic

/-- The k-th classical holomorphic differential `x^k dx / y`
on the hyperelliptic curve, for `0 ≤ k < H.genus`. -/
noncomputable def hyperellipticDiff (H : HyperellipticData) (k : Fin H.genus) :
    HolomorphicOneForm (Hyperelliptic H)

theorem hyperellipticDiff_linearIndependent (H : HyperellipticData) :
    LinearIndependent ℂ (hyperellipticDiff H)

theorem hyperellipticDiff_span_top (H : HyperellipticData) :
    Submodule.span ℂ (Set.range (hyperellipticDiff H)) = ⊤

/-- **Theorem** (replaces `AX_Hyperelliptic_genus`). -/
theorem genus_Hyperelliptic_eq (H : HyperellipticData) :
    Jacobians.RiemannSurface.genus (Hyperelliptic H) = H.genus :=
  -- ... from `hyperellipticDiff_linearIndependent` + `_span_top` +
  -- finite-dim basis-of-size-g proof

end Jacobians.ProjectiveCurve.Hyperelliptic
```

## Phases

### Phase 1: Construct `hyperellipticDiff` in the three chart types

**Prerequisite**: the hyperelliptic atlas (`ChartedSpace` + `IsManifold`) 
must be a real def, not axiom-stubbed. Currently that's
`Hyperelliptic.instChartedSpace` axiom; see
`docs/hyperelliptic-atlas-plan.md` for the 6-phase discharge
(H0–H5). **This plan depends on H0–H5 finishing first** (~3 weeks).

Given the atlas, construct the chart-cocycle representation of
`x^k dx / y` on each chart:

- **Affine smooth chart** at a point `(x₀, y₀) ∈ HyperellipticAffine H`
  with `y₀ ≠ 0`: local parameter is `x`. Chart sends `(x, y)` near
  `(x₀, y₀)` to `x`. In chart coords, `x^k dx / y` has coefficient
  `z^k / √(f(z))` where the square root is chosen by the branch at
  `y₀`. The function `z ↦ z^k / √(f(z))` is analytic on a neighborhood
  of `x₀` (assuming `f(x₀) ≠ 0`, which holds away from branch points).

- **Branch-point chart** at `(a, 0)` where `a` is a root of `f`: local
  parameter is `t = √(x - a)`. So `x = a + t²`, `y = t · √(f(x)/(x-a))`
  (the remaining factor is analytic near `t = 0`). Then
  `dx = 2t · dt` and `dx/y = 2t · dt / (t · √(...)) = 2 · dt / √(...)`.
  The coefficient of `dt` is `2 · (a + t²)^k / √(f(a + t²)/(t²))`, which
  is analytic near `t = 0`. Holomorphic at the branch point.

- **Infinity chart**: depends on parity of `deg f`.
  - Odd `d = 2g+1`: single ∞ point. Local parameter `s = 1/√x` (so
    `x = 1/s²`, `dx = -2/s³ · ds`). Then `y ≈ x^{g+½} = s^{-(2g+1)}`,
    so `y = s^{-(2g+1)} · √(1 + ...)` where the tail is analytic in `s`.
    `x^k dx / y = s^{-2k} · (-2/s³) ds / s^{-(2g+1)} = -2 s^{2g-2k-2} ds`.
    For `k ≤ g-1`, `2g-2k-2 ≥ 0`, so this is analytic at `s = 0`.
  - Even `d = 2g+2`: two ∞ points. Each has `s = 1/x` as local parameter.
    Then `y = ±x^{g+1} √(1 + ...)` with sign = branch choice.
    `x^k dx / y = ∓ s^{-2k} ds / s^{-(g+1)} · (analytic) = ∓ s^{g-2k-1} ds`
    up to unit. For `k ≤ g-1`, `g - 2k - 1 ≥ g - 2(g-1) - 1 = 1 - g`,
    which could be negative for g ≥ 2. But wait — this should be
    holomorphic. The actual calculation is `dx/y = s^{g} ds / (analytic unit)`, so
    `x^k dx / y = s^{g - 2k} · ds / (unit)` — holomorphic iff `g - 2k ≥ 0`, i.e., `k ≤ g/2`.
    But we claimed `0 ≤ k ≤ g - 1`. For `g/2 < k ≤ g - 1` the basis
    element has a pole at ∞ — which contradicts classical content.
    **Rework**: the classical basis involves `x^k dx / y` only for
    `0 ≤ k < g`, and the verification at ∞ is more subtle. In the
    weighted projective model, the correct local coordinate at ∞
    makes these all holomorphic. Needs careful calculation, see
    Miranda, *Algebraic Curves*, Ch. VII §1.

Estimated effort: **2 weeks** (substantial chart-analytic work).

### Phase 2: Verify each `hyperellipticDiff H k` lies in `holomorphicOneFormSubmodule`

For each k:
- **`IsHolomorphicOneFormCoeff`**: analyticity on each chart target
  (verified by Phase 1 computation).
- **`SatisfiesCotangentCocycle`**: on overlaps of the three chart
  types, the coefficient transforms correctly under the chart-transition
  derivative. Reduces to the chain rule applied to `t ↦ a + t²`
  (affine ↔ branch) and `s ↦ 1/s²` (affine ↔ ∞, odd).

Estimated effort: **3–5 days** per chart overlap. Total: **1–2 weeks**.

### Phase 3: Linear independence of `{hyperellipticDiff H k}_{k=0}^{g-1}`

Evaluate at a specific point (e.g., in the affine chart at a
non-branch point `x₀` with `y₀ ≠ 0`). The Vandermonde-like evaluation
`ω_k(x₀) = x₀^k / y₀` gives a matrix with columns `(x₀)^k` — linearly
independent iff `x₀ ≠ 0` and the values are distinct.

Actually cleaner: linear independence follows because the chart-local
coefficient of `ω_k` is `z^k / √(f(z))`, and polynomial coefficients
`z^k` are linearly independent in `ℂ[[z]]`.

Estimated effort: **3 days**.

### Phase 4: Spanning (the hard direction)

Show every holomorphic 1-form on `Hyperelliptic H` is a ℂ-linear
combination of `{ω_0, …, ω_{g-1}}`. Classical proof via
Riemann-Roch / residue analysis:

1. For any holomorphic 1-form `ω` on `C`, consider its divisor
   `(ω)` — the "canonical divisor." Has degree `2g - 2`.
2. `deg (ω) = 2g - 2`. Also, `(x^k dx / y) = (positive stuff at
   branch points and ∞) - (poles at ∞)`. Compute explicit divisors.
3. By Riemann-Roch, `h⁰(K) = g` where `K` is the canonical class.
4. Our family `{ω_k}` has `g` elements, independent (Phase 3),
   so they span.

**This depends on Riemann-Roch** (`AX_RiemannRoch`). For a
non-circular argument, either:
- (a) Prove Riemann-Roch first (substantial, months).
- (b) Use a residue-based argument specific to hyperelliptic curves
  that doesn't need general Riemann-Roch. Classical: the pullback
  under the 2:1 map `C → ℙ¹` gives a decomposition
  `H⁰(C, Ω¹_C) = H⁰(ℙ¹, π_* Ω¹_C)` = 1-forms on ℙ¹ with prescribed
  behavior at branch points. Count: matches `g`.

Estimated effort (option b): **2 weeks** (residue analysis + careful
chart-level computation).

### Phase 5: Assemble `genus_Hyperelliptic_eq`

With independence + spanning established, `finrank = g`, hence
`genus = g`. Short proof (~20 LOC).

Estimated effort: **1 day**.

## Total

| Phase | Effort |
|---|---|
| 1. Construct ω_k on atlas | 2 weeks |
| 2. Verify cocycle | 1–2 weeks |
| 3. Linear independence | 3 days |
| 4. Spanning | 2 weeks |
| 5. Assemble | 1 day |
| **Total (given atlas)** | **~6 weeks** |
| Plus atlas prerequisite | +3 weeks |
| **Grand total** | **~9 weeks** |

Parallelization: Phase 1 & 3 can start once atlas lands; Phase 4 depends on Phase 1.

## Dependencies

- `docs/hyperelliptic-atlas-plan.md` — Phases H0–H5 must finish first.
- Mathlib: `HolomorphicOneForm` + `AnalyticOn` + chart cocycle (in place).
- Classical text: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. VII §1 (explicit
  hyperelliptic differentials); Farkas-Kra, Ch. III §7.

## Consequence

- `AX_Hyperelliptic_genus` retires to a derived theorem.
- Combined with `genus_Elliptic_eq_one` (plan above), the entire
  "genus of concrete curve" family becomes axiom-free at the
  hack-blocker layer.
- Removes a chunk of `docs/dependency-trace.md`'s A-deep axiom list.

## Status

Plan only. Discharge requires:
1. Hyperelliptic atlas (prereq, ~3 weeks).
2. Phase 1–5 (~6 weeks).

Not recommended for single-session attempt. Treat as multi-month
project aligned with the broader Hyperelliptic atlas work.
