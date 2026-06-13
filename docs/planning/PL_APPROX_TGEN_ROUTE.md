# PL-approximation route to T-GEN (`feat/tgen-pl-approx`)

**Status (2026-06-13):** keystone primitive + analytic packaging + reduction
landed, sorry-free, standard-3. T-GEN now reduces to **one elementary
chart-local-homotopy lemma** (`ChartFlatHomotopyWall`), strictly weaker than the
prior `{Whitney, Grauert}` pair. The wall itself is the single remaining step.

## The insight (validated)

Our `AnalyticArc`/`AnalyticLoop` is **piecewise**-real-analytic (analytic on open
cells; corners allowed). A loop that is **straight-line-in-charts on each cell of
a chart-ball subdivision** is therefore *already* an `AnalyticLoop`: the chart
readout per cell is an affine `flatSegment`, real-analytic on all of ℝ. No Whitney
smoothing, no Grauert global analyticity. **Task-1 verdict: PL fits
`IsAnalyticArcStrong` cleanly** — verified by compiling the affine-flatSegment
witness analyticity, and by reusing the already-proven
`BridgePathArc.concatChartFlatPathAuxAnalyticArc`.

## Landed (all `#print axioms = [propext, Classical.choice, Quot.sound]`)

- `Jacobians/RiemannSurface/SubintervalHomotopy.lean`
  - `Path.homotopyOfPartialEquivLocalOn` / `Path.homotopic_of_partialEquivLocalOn`
    — **the keystone primitive**: two paths that agree outside `(a,b)` and on
    `[a,b]` both lie in one `PartialEquiv` `e`'s source with connecting segments in
    `e.target` are homotopic rel endpoints, via a homotopy that is the chart
    straight-line homotopy inside `[a,b]` and stationary (`= f`) outside.
    Continuity by `continuous_piecewise` over the closed support cell
    `univ ×ˢ Icc a b`, frontier `{t=a}∪{t=b}` where `f=g` collapses the segment.
  - `Path.homotopic_of_extChartLocalOn` — the `extChartAt` specialisation.
- `Jacobians/RiemannSurface/PLApproxGeneration.lean`
  - `flatAnalyticLoopOfSubdivision` — the chart-flat concatenation of a loop's
    chart-ball subdivision, packaged as an `AnalyticLoop X x₀`.
  - `loopToPath_flatAnalyticLoopOfSubdivision` — its underlying path is exactly
    `S.concatChartFlatPath`.
  - `continuousLoopHasAnalyticRep_of_chartFlatHomotopyWall` and
    `analyticLoopsGenerateH1_of_chartFlatHomotopyWall` — the reduction: T-GEN
    follows from `ChartFlatHomotopyWall`.

## The single remaining lemma

```
def ChartFlatHomotopyWall (x₀ : X) : Prop :=
  ∀ p : Path x₀ x₀, ∃ S : Jacobians.Bridge.PathChartBallSubdivision p,
    (S.concatChartFlatPath).Homotopic p
```

Every continuous loop is homotopic rel endpoints to the chart-flat concatenation
of some chart-ball subdivision of itself. Pure chart-local straight-line homotopy
— no analyticity.

### Why it is not yet discharged: the parametrisation mismatch

`S.concatChartFlatPath` is `chartFlatPath 0 |>.trans (chartFlatPath 1) |>.trans …`
— **dyadic** parametrisation (`Path.trans` halves). The given `p` runs on its own
breakpoints `[t_k, t_{k+1}]`. The keystone primitive
(`homotopic_of_extChartLocalOn`) needs **shared parametrisation** on each cell, so
it does not apply directly across the dyadic-vs-original mismatch.

### Two completion routes (each one multi-lemma)

**Route A — uniform parametrisation.** Build `flatExtend : ℝ → X` on `p`'s OWN
breakpoints (cell `n` = affine-reparametrised chart segment in `chart n`), prove it
`IsAnalyticArcStrong` over `{t_k}` (affine witness, already verified analytic), and
chain `homotopic_of_extChartLocalOn` cell-by-cell against `p` via
`Path.homotopic_of_chain`. The chain is uniform-parametrisation so the primitive
applies verbatim. Cost: rebuild `flatExtend` (a multi-cell `Set.piecewise`) + its
continuity at breakpoints + its `IsAnalyticArcStrong`. Watch degenerate cells
`t_n = t_{n+1}` (`homotopic_of_chain` over `Fin`).

**Route B — dyadic reparam bridge.** Reuse the existing dyadic
`concatChartFlatPath`/`concatChartFlatPathAuxAnalyticArc`. Prove the missing
Mathlib lemma `p ≃ (affine-cell-reparam concat of p)` (via `Path.Homotopy.reparam`
matching the nested-`trans` dyadic parametrisation to `p`'s cells), then compare
to `concatChartFlatPathAux k` cell-wise by induction with `Path.Homotopic.hcomp`
and the *whole-subpath* `homotopic_of_extChartLocal` (each sub-path lies entirely
in one chart). Cost: the reparam-split lemma is delicate — note
`Path.truncate t₀ t₁` is *constant-then-sweep-then-constant*, NOT a clean cell
sweep, so an affine cell sub-path `fun s => p.extend (t_k + s·(t_{k+1}-t_k))` must
be built explicitly.

Route A avoids all reparam/`hcomp`/truncation bookkeeping at the cost of rebuilding
`flatExtend`; Route B reuses the analytic arc at the cost of the Mathlib-absent
reparam-split. Both are mechanical but multi-lemma.

## Net effect

This collapses `TGenFinalReduction.lean`'s `{Whitney, Grauert}` two-wall state to a
single, strictly-weaker, purely-topological wall, and proves the entire
analytic-loop packaging unconditionally. Discharging `ChartFlatHomotopyWall`
closes T-GEN unconditionally (standard-3), making Buzzard's 24 headlines
axiom-free modulo the mechanical rewiring through
`analyticLoopsGenerateH1_of_chartFlatHomotopyWall`.

(Instances used: `[T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
[IsManifold 𝓘(ℂ) ω X]` — all hold for any compact connected Riemann surface; the
`T2`/`Connected` come from reusing the Bridge chart-flat machinery, NOT from any
extra mathematical assumption.)
