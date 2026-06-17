/-
# Piecewise-linear-in-charts route to (AAW) / T-GEN

The **PL-approximation** discharge of the analytic-approximation wall
(`ContinuousLoopHasAnalyticRep`, `AnalyticApproxGeneration.lean`) — the residual
that closes the topological residual **T-GEN** (`AnalyticLoopsGenerateH1`).

## The insight

Our `AnalyticArc`/`AnalyticLoop` is **piecewise**-real-analytic (analytic only on
the open cells of a finite partition; corners at partition points are allowed). So
a loop that is **straight-line-in-charts on each cell of a chart-ball
subdivision** is *already* an `AnalyticLoop` — its chart readout per cell is an
affine `flatSegment`, real-analytic on all of ℝ (cf. `AnalyticArcMovingChart`,
`BridgePathArc.chartFlatAnalyticArc`). No Whitney smoothing and no Grauert global
analyticity are needed; both were believed to be the wall but are not, because the
target is *piecewise*-analytic.

## What this file proves (sorry-free, standard-3)

* `flatAnalyticLoopOfSubdivision` — the chart-flat concatenation of any chart-ball
  subdivision of a loop, packaged as an `AnalyticLoop X x₀` (reusing the proven
  `concatChartFlatPathAuxAnalyticArc`).
* `loopToPath_flatAnalyticLoopOfSubdivision` — its underlying path is exactly
  `S.concatChartFlatPath`.
* `continuousLoopHasAnalyticRep_of_chartFlatHomotopyWall` — **the reduction**:
  T-GEN's residual `ContinuousLoopHasAnalyticRep` follows from the single
  *elementary topological* statement `ChartFlatHomotopyWall` (every continuous
  loop is homotopic rel endpoints to the chart-flat concatenation of some
  subdivision of itself), via the chart-local straight-line homotopy of
  `SubintervalHomotopy.lean`. The analytic-loop packaging is fully discharged
  here; the residual is now a pure chart-local homotopy (no analyticity).

This replaces the two-wall state `{Whitney, Grauert}` of `TGenFinalReduction.lean`
with a **single elementary chart-local-homotopy wall**.

No new axiom; nothing depends on `AX_PeriodCycleBasis`.
-/
import Jacobians.Bridge.BridgePathArc
import Jacobians.RiemannSurface.SubintervalHomotopy
import Jacobians.RiemannSurface.AnalyticApproxGeneration

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open unitInterval
open Jacobians.Bridge
open Jacobians.Axioms (loopToPath)

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The chart-flat analytic loop of a subdivision -/

noncomputable def flatAnalyticArcOfSubdivision {x₀ : X} (γ : Path x₀ x₀)
    (S : Jacobians.Bridge.PathChartBallSubdivision γ) : AnalyticArc X :=
  S.concatChartFlatPathAuxAnalyticArc S.lastIndex

omit [T2Space X] [ConnectedSpace X] in
theorem flatAnalyticArcOfSubdivision_extend_zero {x₀ : X} (γ : Path x₀ x₀)
    (S : Jacobians.Bridge.PathChartBallSubdivision γ) :
    (flatAnalyticArcOfSubdivision γ S).extend 0 = x₀ := by
  rw [flatAnalyticArcOfSubdivision,
    congrFun (S.concatChartFlatPathAuxAnalyticArc_extend S.lastIndex) 0,
    Path.extend_zero]
  simp [S.t_zero]

omit [T2Space X] [ConnectedSpace X] in
theorem flatAnalyticArcOfSubdivision_extend_one {x₀ : X} (γ : Path x₀ x₀)
    (S : Jacobians.Bridge.PathChartBallSubdivision γ) :
    (flatAnalyticArcOfSubdivision γ S).extend 1 = x₀ := by
  rw [flatAnalyticArcOfSubdivision,
    congrFun (S.concatChartFlatPathAuxAnalyticArc_extend S.lastIndex) 1,
    Path.extend_one]
  have hlast : S.t (S.lastIndex + 1) = 1 :=
    S.eq_one_of_lastIndex_le (Nat.le_succ S.lastIndex)
  simp [hlast]

/-- The chart-flat concatenation of a loop's subdivision, packaged as an
`AnalyticLoop` based at `x₀`. -/
noncomputable def flatAnalyticLoopOfSubdivision {x₀ : X} (γ : Path x₀ x₀)
    (S : Jacobians.Bridge.PathChartBallSubdivision γ) : AnalyticLoop X x₀ where
  arc := flatAnalyticArcOfSubdivision γ S
  start_eq := flatAnalyticArcOfSubdivision_extend_zero γ S
  end_eq := flatAnalyticArcOfSubdivision_extend_one γ S

omit [T2Space X] [ConnectedSpace X] in
/-- The underlying path of the flat analytic loop is exactly the chart-flat
concatenation `S.concatChartFlatPath`. -/
theorem loopToPath_flatAnalyticLoopOfSubdivision {x₀ : X} (γ : Path x₀ x₀)
    (S : Jacobians.Bridge.PathChartBallSubdivision γ) :
    loopToPath (flatAnalyticLoopOfSubdivision γ S) = S.concatChartFlatPath := by
  ext t
  change (flatAnalyticArcOfSubdivision γ S).extend (t : ℝ) = S.concatChartFlatPath t
  rw [flatAnalyticArcOfSubdivision,
    congrFun (S.concatChartFlatPathAuxAnalyticArc_extend S.lastIndex) (t : ℝ),
    Jacobians.Bridge.PathChartBallSubdivision.concatChartFlatPath, Path.cast_coe,
    Path.extend_extends' _ ⟨t.val, t.2⟩]

/-- **Named residual (PL homotopy wall).** Every continuous loop is homotopic rel
endpoints to the chart-flat (piecewise-linear-in-charts) concatenation of *some*
chart-ball subdivision of itself. This is a purely topological chart-local
straight-line homotopy statement — no smoothing, no global analyticity — and is
the single remaining input for the unconditional PL discharge of
`ContinuousLoopHasAnalyticRep`. -/
def ChartFlatHomotopyWall (x₀ : X) : Prop :=
  ∀ p : Path x₀ x₀, ∃ S : Jacobians.Bridge.PathChartBallSubdivision p,
    (S.concatChartFlatPath).Homotopic p

omit [T2Space X] [ConnectedSpace X] in
/-- **PL discharge of (AAW), modulo the chart-flat homotopy wall.** Under
`ChartFlatHomotopyWall`, every continuous loop has a piecewise-analytic
representative: `ContinuousLoopHasAnalyticRep x₀`. The analytic-loop packaging is
fully proved (reusing the chart-flat analytic arc); the only input is the
elementary chart-local homotopy. -/
theorem continuousLoopHasAnalyticRep_of_chartFlatHomotopyWall {x₀ : X}
    (hwall : ChartFlatHomotopyWall x₀) :
    ContinuousLoopHasAnalyticRep x₀ := by
  intro p
  obtain ⟨S, hS⟩ := hwall p
  refine ⟨flatAnalyticLoopOfSubdivision p S, ?_⟩
  rw [loopToPath_flatAnalyticLoopOfSubdivision]
  exact hS

omit [T2Space X] [ConnectedSpace X] in
/-- **T-GEN reduces to the chart-flat homotopy wall (general `X`).** Composing the
PL discharge with the K0 keystone bridge: under `ChartFlatHomotopyWall x₀`, the
homology classes of piecewise-analytic loops ℤ-span `H1 X x₀`
(`AnalyticLoopsGenerateH1 x₀` = T-GEN). The *only* remaining input is the single
elementary chart-local-homotopy statement — strictly weaker than the
`{Whitney, Grauert}` pair of `TGenFinalReduction.lean` (no smoothing, no global
real-analyticity; just a straight-line homotopy in charts). Sorry-free,
standard-3, independent of `AX_PeriodCycleBasis`. -/
theorem analyticLoopsGenerateH1_of_chartFlatHomotopyWall {x₀ : X}
    (hwall : ChartFlatHomotopyWall x₀) :
    AnalyticLoopsGenerateH1 x₀ :=
  analyticLoopsGenerateH1_of_analyticRep
    (continuousLoopHasAnalyticRep_of_chartFlatHomotopyWall hwall)

end Jacobians.RiemannSurface
