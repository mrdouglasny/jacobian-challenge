# Construction plans for the 5 data-level axioms

_Drafted 2026-04-23._ The foundation `Challenge.lean` is closed with
all 24 Buzzard sorries discharged as real `def`s / real instances
(§§1–13, §16) plus 10 Prop-level axioms routing to classical theorems
(§§14–15, §17–§24). Below the Buzzard interface, the supporting layer
uses **5 data-level axioms** — each axiomatizes the existence of a
function with specified properties rather than constructing one.

This directory collects a construction plan per axiom: classical math
content, Mathlib prerequisites, phase breakdown, effort estimate.

## Plans

| # | Axiom | Returns | Plan |
|---|---|---|---|
| 1 | `pathIntegralBasepointFunctional` | `X → X → (Ω¹(X) →ₗ[ℂ] ℂ)` | [`path-integral-basepoint.md`](path-integral-basepoint.md) |
| 2 | `loopIntegralToH1` | `H1 X x₀ →+ (Ω¹(X) →ₗ[ℂ] ℂ)` | [`loop-integral-h1.md`](loop-integral-h1.md) |
| 3 | `pullbackOneForm` | `(f : X → Y) → Ω¹(Y) →ₗ[ℂ] Ω¹(X)` | [`pullback-one-form.md`](pullback-one-form.md) |
| 4 | `pushforwardOneForm` | `(f : X → Y) → Ω¹(X) →ₗ[ℂ] Ω¹(Y)` | [`pushforward-one-form.md`](pushforward-one-form.md) |
| 5 | `localOrder` | `(f : X → Y) → X → Y → ℕ` | [`local-order.md`](local-order.md) |

## Shared prerequisites

Several plans share underlying infrastructure. Building it once unlocks
multiple discharges.

| Prereq | Nature | Enables |
|---|---|---|
| **Multi-chart path integration** (`pathIntegralAnalyticArc` — sum of chart-local integrals over a partition) | ~200 LOC | #1 (at chart level) and #2 (before descent) |
| **Homotopy invariance** of path integral (Cauchy on chart disks + Stokes on rectangle) | ~300 LOC | #2 (to descend to H₁) |
| **Chart-cocycle pullback/pushforward** (functoriality at the `X → ℂ → ℂ` level) | ~150 LOC | #3 and #4 |
| **Holomorphic-order-at-point** for maps between complex 1-manifolds (Taylor-series order) | ~150 LOC | #5 (and indirectly #4 for finite-cover structure) |

## Dependency graph between plans

```
  #1 pathIntegralBasepointFunctional        ─┬─ multi-chart path integration
  #2 loopIntegralToH1                       ─┘  + homotopy invariance
                                                
  #3 pullbackOneForm   ─── cotangent cocycle pullback
  #4 pushforwardOneForm ── trace (needs finite-cover + local order #5)
                                                
  #5 localOrder ─── Taylor-series / Mittag-Leffler at a point
```

#5 is a prereq for #4's finite-cover trace construction. #1 and #2
share path-integration infrastructure. #3 is independent of the rest
structurally (pure chart-cocycle).

## Total discharge estimate

| Plan | Effort (focused contributor) | Blocking? |
|---|---|---|
| #1 + #2 (bundled) | ~2 weeks | Unblocks `ofCurve`, `periodMap` fully |
| #3 | ~1 week | Unblocks `pushforwardImpl` ambient construction |
| #4 (after #5) | ~1 week | Unblocks `pullbackImpl` ambient construction |
| #5 | ~1 week | Unblocks `degreeImpl` (currently uses Classical.choose on AX_BranchLocus; could be more structural) |

**Total: ~5–6 weeks** to retire all 5 data-level axioms to real `def`s,
via a single focused contributor. Parallelizes somewhat: #1+#2 can run
alongside #3+#4+#5.

## Consequence

Once these 5 plans are discharged, the foundation closes under the
stricter rule "**every definition is a real `def`; every axiom is a
Prop-level classical theorem.**" The remaining axioms would be exactly
the 7 Prop-level ones (`AX_FiniteDimOneForms`,
`AX_pathIntegral_local_antiderivative`, the two lattice-preservation,
`AX_PeriodLattice`, `instPeriodLatticeDiscrete`, `AX_BranchLocus`) —
each a classical theorem citable by textbook.

That is the tightest foundation claim achievable without discharging
the deep classical theorems themselves (Riemann-Roch, Serre duality,
Riemann bilinear, Abel's theorem), which belong to a separate theorem
workstream entirely.
