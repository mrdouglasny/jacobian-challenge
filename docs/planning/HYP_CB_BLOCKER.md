# Hyperelliptic `PeriodCycleBasis` witness — gap ledger

Status as of 2026-06-10, branch `feat/hyperelliptic-cyclebasis`.
Companion to `CYCLEBASIS_ALTERNATIVES.md` (direction 2a) and the running
log `HYP_CB_PROGRESS.log`. Every gap below is carried as an **explicit
named hypothesis** in the Lean sources — no sorries, no new axioms were
introduced by this workstream.

## What is DONE (foundations landed)

| Piece | File | Status |
|---|---|---|
| Generic moving-chart ⇒ `IsAnalyticArcStrong` constructor (+ arc/loop packagers) | `Jacobians/RiemannSurface/AnalyticArcMovingChart.lean` | proven |
| Loop conjugation (rebasing) + connector-cancelling periods | `Jacobians/RiemannSurface/LoopConjugation.lean` | proven |
| Continuous sqrt of analytic is analytic (local branch + sign argument) | `Jacobians/GeneralResults/SqrtBranch.lean` (`analyticAt_of_sq_eq_analytic`) | proven |
| Constructive global sqrt branch `y₀·exp(½∫g′/g)` | `Jacobians/GeneralResults/SqrtBranch.lean` (`exists_sqrt_branch`) | proven |
| `SqrtArcData` + lift to `HyperellipticOdd` with strong analyticity; chart readout `extChartAt_toOdd` | `Jacobians/ProjectiveCurve/Hyperelliptic/CycleLoops.lean` | proven |
| Branch existence for any analytic root-avoiding x-arc (`exists_sqrtArcData`) | same | proven |
| Concrete base arcs `circleX` / `segmentX` (entire, circle closed) | same | proven |
| M3 arc-level period reduction (integrand `= coeff·x′`; period `= ∫₀¹ coeff·x′`) | same + `CycleBasisWitness.lean` (`loop_period_eq`, `arcPeriodVec_loop_fst/snd`) | proven |
| `BranchCutSystem` bundle + based loops + conditional witness `nonempty_periodCycleBasis_of_branchCutSystem` | `Jacobians/ProjectiveCurve/Hyperelliptic/CycleBasisWitness.lean` | proven (conditional) |

Design fact that makes all of this cheap: on the `y ≠ 0` locus the
preferred atlas chart is the x-projection, and through
`lift_openEmbedding_apply` the moving-chart readout of a sqrt-lifted curve
**is** the base x-plane arc (the `rfl` at `CycleLoops.lean`,
`extChartAt_toOdd`). Analyticity and periods never see the `y`-coordinate
except through the form coefficient.

## Gap ledger (named hypotheses, in dependency order)

### G-A. Branch closure around a circle (sqrt monodromy) — M1 residue

*Where:* `SqrtArcData.toOddLoop` hypothesis `hy : D.y 1 = D.y 0`;
`BranchCutSystem.cycle_closed_y`.

*Content:* by `exists_sqrtArcData` the branch is
`y₀·exp(½ L(t))`, `L(t) = ∫₀ᵗ (f∘x)′/(f∘x)`, so closure is exactly
`exp(½ L(1)) = 1`, i.e. `L(1) ∈ 4πi·ℤ`. By the argument principle
`L(1) = 2πi · (number of roots of f enclosed by the circle)`, so closure
holds **iff the circle encloses an even number of branch points** — true
for the aᵢ/bᵢ circles around branch-point *pairs*.

*Discharge route:* `L(1)` is an explicit interval integral of a rational
function along `circleX`; relate to `∮ g′/g` over `circleMap` and use
Mathlib's residue/winding machinery
(`Complex.integral_circle_div_sub_of_differentiable_on` family /
`circleIntegral` API) plus factorization of `f` over ℂ
(`Polynomial.roots`). Self-contained complex analysis, independent of the
SVK package. Estimated: days-to-a-week of focused work.

### G-B. Circle layout enclosing exactly the branch-point pairs — M1 residue

*Where:* instantiating `BranchCutSystem.cycle` with `ofCircle` data.

*Content:* an enumeration `e₁, …, e_{2g+1}` of the roots of `f` and
centers/radii such that circle `aᵢ` encloses exactly `{e_{2i−1}, e_{2i}}`
(and the `bᵢ` system interleaves). For arbitrary squarefree `f` the roots
are in general position; the classical construction picks a generic
direction, orders roots, and takes thin ellipse-like loops — for *circles*
one needs `|e_{2i−1} − e_{2i}|`-based balls avoiding the other roots,
which exist only after re-pairing roots by proximity (or replacing
circles by smooth Jordan curves built from `segmentX`+half-`circleX`
pieces via `AnalyticArc.trans`). Pure plane geometry + finite
combinatorics; no manifold content. The constructors deliberately accept
*any* analytic closed base arc, so this layout work is orthogonal.

### G-C. H₁ basis + Hurewicz tie — M2 core (awaits SVK/covering package)

*Where:* hypotheses `isBasis`, `tie` of
`nonempty_periodCycleBasis_of_branchCutSystem`.

*Content:* the classes of the 2g conjugated branch-cut loops form a
ℤ-basis of `H1 (HyperellipticOdd H h) basePoint`, with `isBasis i =
loopToHomology (loop i)`. Needs:
1. π₁ of ℂ minus `2g+1` points is free on the loop classes (SVK-style;
   the port's proven `VanKampen.lean` two-open method is the de-risked
   skeleton — see CYCLEBASIS_ALTERNATIVES §2a/§3);
2. the double-cover/monodromy description of π₁ of the total space
   (covering machinery exists: `HyperellipticAffine.sqMap_covering`,
   `Mathlib.Topology.Homotopy.Lifting`), plus the one-point
   compactification step at the branch point at infinity;
3. abelianization + rank bookkeeping, and the **analytic-genus gate**:
   the index type is `Fin (2 * genus (HyperellipticOdd H h))` with
   `genus` = dim of the holomorphic-form space, so the count needs
   `genus (HyperellipticOdd H h) = H.genus` (`AX_Hyperelliptic_genus`
   territory; #167's `OddForm` coefficient layer is the path to
   exhibiting the g independent forms `x^k dx/y`).

This is the research-grade half; everything in this workstream was
arranged so that G-C is consumed **only** through the two hypothesis
slots of the final theorem.

### G-D. Arc-level R1/R2 for the branch-cut periods — M3 residue

*Where:* hypotheses `hR1`, `hR2` of
`nonempty_periodCycleBasis_of_branchCutSystem`.

*Content:* by `arcPeriodVec_loop_fst/snd` every period entry is the
explicit x-plane integral `∫₀¹ coeff·x′`; R1/R2 are then identities /
positivity of finite sums of such integrals. Discharge routes (either):
* the Kirov port's proven boundary-word engine
  (`riemann_R1_of_boundaryWord`, `riemann_R2_posDef_of_boundaryWord`)
  once a cut-surface/polygon presentation of the hyperelliptic surface is
  in place; or
* direct computation for the explicit form basis `x^k dx / y` after
  `AX_Hyperelliptic_genus` pins the form space — branch-cut period
  matrices à la Riemann (classical, computational, no topology).

### G-E. Even model — not started

The even hyperelliptic model (`HyperellipticEvenProj`, `[Fact (¬ Odd …)]`
chain, two points at infinity) has the same x-projection structure; the
`SqrtArcData` layer is model-independent up to the chart readout lemma,
which must be re-proven against the `EvenAtlas` charts. Deferred until
the odd-model witness closes end-to-end.

## Consumption map

```
exists_sqrtArcData ──┐
circleX/segmentX ────┤            ┌─ G-A (closure) ─┐
                     ├─ SqrtArcData┤                 ├─ BranchCutSystem ─┐
analyticAt_of_sq_eq ─┘            └─ G-B (layout) ──┘                    │
                                                                          ├─ nonempty_periodCycleBasis_of_branchCutSystem
AnalyticArcMovingChart ─ toOddArc/toOddLoop                               │
LoopConjugation ──────── loop (rebased)          G-C (isBasis+tie) ──────┤
loop_period_eq ───────── arcPeriodVec reduction  G-D (R1/R2) ───────────┘
```
