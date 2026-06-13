/-
# Unconditional discharge of `ChartFlatHomotopyWall`

This file proves the single remaining elementary topological lemma that closes
**T-GEN** (`AnalyticLoopsGenerateH1`) unconditionally:

  `ChartFlatHomotopyWall x₀` — every continuous loop `p : Path x₀ x₀` is
  homotopic rel endpoints to the chart-flat (piecewise-linear-in-charts)
  concatenation `S.concatChartFlatPath` of some chart-ball subdivision `S` of `p`.

## Strategy (Route ii: dyadic `hcomp` induction + one reparametrisation)

`S.concatChartFlatPath` is the **dyadic** nested-`Path.trans` concatenation of the
per-cell chart-straight-line pieces `S.chartFlatPath n`. We do NOT try to match
its dyadic parametrisation to `p`'s breakpoints directly. Instead:

* `pCell n` — `p` restricted and affinely reparametrised to the cell
  `[S.t n, S.t (n+1)]`, built explicitly (NOT via `Path.truncate`, which is
  constant-then-sweep-then-constant).
* per cell, `S.chartFlatPath n` and `pCell n` both lie **entirely** in one chart's
  source, with the connecting chart segments inside the (convex) chart-ball target,
  so they are homotopic rel endpoints by the whole-path chart-local homotopy
  `Path.homotopic_of_partialEquivLocal`.
* `pAux k` — the dyadic concatenation of `pCell 0, …, pCell k`, recursed exactly
  like `S.concatChartFlatPathAux`. By induction with `Path.Homotopic.hcomp`,
  `S.concatChartFlatPathAux k ≃ pAux k`.
* endgame: `pAux S.lastIndex = p.reparam φ` for the dyadic reparametrisation `φ`
  (the same dyadic tree on affine `I`-segments over `p`'s breakpoints), and
  `p.reparam φ ≃ p` by `Path.reparam`. Casting endpoints aligns this with
  `S.concatChartFlatPath ≃ p`.

No new axiom; sorry-free; standard-3.
-/
import Jacobians.Bridge.BridgePath
import Jacobians.RiemannSurface.ChartLocalHomotopy
import Jacobians.RiemannSurface.PLApproxGeneration

open scoped Manifold Topology unitInterval Convex ContDiff
open unitInterval

namespace Jacobians.Bridge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {P₀ P : X}

namespace PathChartBallSubdivision

variable {γ : Path P₀ P} (S : PathChartBallSubdivision γ)

/-! ## The cell sub-path of `p` (affine reparametrisation onto one cell) -/

/-- The affine endpoint-to-endpoint reparametrisation `I → I` onto the `n`th cell:
`s ↦ S.t n + s · (S.t (n+1) - S.t n)`, valued in the unit interval. -/
noncomputable def cellAffine (n : ℕ) (s : unitInterval) : unitInterval :=
  ⟨(S.t n : ℝ) + (s : ℝ) * ((S.t (n + 1) : ℝ) - (S.t n : ℝ)), by
    constructor
    · have h1 : (0 : ℝ) ≤ (S.t n : ℝ) := (S.t n).2.1
      have h2 : (0 : ℝ) ≤ (s : ℝ) * ((S.t (n + 1) : ℝ) - (S.t n : ℝ)) := by
        apply mul_nonneg s.2.1
        have := S.monotone_t (Nat.le_succ n)
        simpa using sub_nonneg.mpr (Subtype.coe_le_coe.mpr this)
      linarith
    · -- t n + s (t(n+1) - t n) = (1-s) t n + s t(n+1) ≤ (1-s)·1 + s·1 = 1
      have hmono : (S.t n : ℝ) ≤ (S.t (n + 1) : ℝ) :=
        Subtype.coe_le_coe.mpr (S.monotone_t (Nat.le_succ n))
      have hle1 : (S.t (n + 1) : ℝ) ≤ 1 := (S.t (n + 1)).2.2
      have hs0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
      have hs1 : (s : ℝ) ≤ 1 := s.2.2
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hmono)]⟩

@[simp] theorem cellAffine_zero (n : ℕ) : S.cellAffine n 0 = S.t n := by
  apply Subtype.ext; simp [cellAffine]

@[simp] theorem cellAffine_one (n : ℕ) : S.cellAffine n 1 = S.t (n + 1) := by
  apply Subtype.ext; simp [cellAffine]

theorem continuous_cellAffine (n : ℕ) : Continuous (S.cellAffine n) := by
  apply Continuous.subtype_mk
  fun_prop

theorem cellAffine_mem_cell (n : ℕ) (s : unitInterval) :
    (S.cellAffine n s : unitInterval) ∈ Set.Icc (S.t n) (S.t (n + 1)) := by
  constructor
  · apply Subtype.coe_le_coe.mp
    show (S.t n : ℝ) ≤ (S.t n : ℝ) + (s : ℝ) * ((S.t (n + 1) : ℝ) - (S.t n : ℝ))
    have hmono : (S.t n : ℝ) ≤ (S.t (n + 1) : ℝ) :=
      Subtype.coe_le_coe.mpr (S.monotone_t (Nat.le_succ n))
    nlinarith [mul_nonneg s.2.1 (sub_nonneg.mpr hmono)]
  · apply Subtype.coe_le_coe.mp
    show (S.t n : ℝ) + (s : ℝ) * ((S.t (n + 1) : ℝ) - (S.t n : ℝ)) ≤ (S.t (n + 1) : ℝ)
    have hmono : (S.t n : ℝ) ≤ (S.t (n + 1) : ℝ) :=
      Subtype.coe_le_coe.mpr (S.monotone_t (Nat.le_succ n))
    nlinarith [mul_nonneg (sub_nonneg.mpr s.2.2) (sub_nonneg.mpr hmono)]

/-- `p` restricted and affinely reparametrised to the `n`th cell `[S.t n, S.t (n+1)]`. -/
noncomputable def pCell (n : ℕ) : Path (γ (S.t n)) (γ (S.t (n + 1))) where
  toFun s := γ (S.cellAffine n s)
  continuous_toFun := γ.continuous.comp (S.continuous_cellAffine n)
  source' := by simp
  target' := by simp

@[simp] theorem pCell_apply (n : ℕ) (s : unitInterval) :
    S.pCell n s = γ (S.cellAffine n s) := rfl

/-! ## Per-cell chart-local homotopy: `chartFlatPath n ≃ pCell n` -/

/-- Every point of `p` on the `n`th cell lies in the assigned chart-ball source. -/
theorem pCell_mem_chartBallSource (n : ℕ) (s : unitInterval) :
    S.pCell n s ∈ chartBallSource (S.chart n) :=
  S.subinterval_subset_chartBall n (S.cellAffine_mem_cell n s)

/-- The chart image of a cell point of `p` lies in the chart-target ball. -/
theorem chart_pCell_mem_ball (n : ℕ) (s : unitInterval) :
    (chartAt ℂ (S.chart n)) (S.pCell n s) ∈
      Metric.ball ((chartAt ℂ (S.chart n)) (S.chart n))
        (chartTargetBallRadius (S.chart n)) :=
  (S.pCell_mem_chartBallSource n s).2

/-- A cell point of `p` lies in the assigned chart source. -/
theorem pCell_mem_chart_source (n : ℕ) (s : unitInterval) :
    S.pCell n s ∈ (chartAt ℂ (S.chart n)).source :=
  (S.pCell_mem_chartBallSource n s).1

/-- The chart image of a flat-segment point lies in the chart-target ball. -/
theorem chart_chartFlatPath_mem_ball (n : ℕ) (s : unitInterval) :
    (chartAt ℂ (S.chart n)) (S.chartFlatPath n s) ∈
      Metric.ball ((chartAt ℂ (S.chart n)) (S.chart n))
        (chartTargetBallRadius (S.chart n)) := by
  have hmem : flatSegment ((chartAt ℂ (S.chart n)) (γ (S.t n)))
      ((chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))) (s : ℝ) ∈
        (chartAt ℂ (S.chart n)).target := S.flatSegment_mem_chart_target n s.2
  have hball : flatSegment ((chartAt ℂ (S.chart n)) (γ (S.t n)))
      ((chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))) (s : ℝ) ∈
        Metric.ball ((chartAt ℂ (S.chart n)) (S.chart n))
          (chartTargetBallRadius (S.chart n)) := by
    have hseg : [(chartAt ℂ (S.chart n)) (γ (S.t n)) -[ℝ]
        (chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))] ⊆
          Metric.ball ((chartAt ℂ (S.chart n)) (S.chart n))
            (chartTargetBallRadius (S.chart n)) :=
      segment_subset_ball (S.left_endpoint_mem_chart_ball n) (S.right_endpoint_mem_chart_ball n)
    exact hseg (flatSegment_mem_segment s.2)
  -- chartFlatPath n s = chart.symm (flatSegment ...), so chart (chartFlatPath n s) = flatSegment ...
  have hrw : (chartAt ℂ (S.chart n)) (S.chartFlatPath n s) =
      flatSegment ((chartAt ℂ (S.chart n)) (γ (S.t n)))
        ((chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))) (s : ℝ) := by
    show (chartAt ℂ (S.chart n)) ((chartAt ℂ (S.chart n)).symm _) = _
    exact (chartAt ℂ (S.chart n)).right_inv hmem
  rw [hrw]; exact hball

/-- A flat-segment point lies in the assigned chart source. -/
theorem chartFlatPath_mem_chart_source (n : ℕ) (s : unitInterval) :
    S.chartFlatPath n s ∈ (chartAt ℂ (S.chart n)).source := by
  show (chartAt ℂ (S.chart n)).symm _ ∈ (chartAt ℂ (S.chart n)).source
  exact (chartAt ℂ (S.chart n)).map_target (S.flatSegment_mem_chart_target n s.2)

/-- **Per-cell chart-local homotopy.** On the `n`th cell, the chart-straight-line
piece `S.chartFlatPath n` is homotopic rel endpoints to the affine restriction
`S.pCell n` of `p`: both lie in one chart's source and the connecting chart
segments stay in the (convex) chart-ball target. -/
theorem chartFlatPath_homotopic_pCell (n : ℕ) :
    (S.chartFlatPath n).Homotopic (S.pCell n) := by
  refine Jacobians.RiemannSurface.Path.homotopic_of_partialEquivLocal
    (S.chartFlatPath n) (S.pCell n) (chartAt ℂ (S.chart n)).toPartialEquiv
    (chartAt ℂ (S.chart n)).continuousOn
    (chartAt ℂ (S.chart n)).continuousOn_symm
    (fun s => S.chartFlatPath_mem_chart_source n s)
    (fun s => S.pCell_mem_chart_source n s)
    (fun s => ?_)
  -- segment between the two chart images stays in the ball ⊆ target
  have hseg : [(chartAt ℂ (S.chart n)) (S.chartFlatPath n s) -[ℝ]
      (chartAt ℂ (S.chart n)) (S.pCell n s)] ⊆
        Metric.ball ((chartAt ℂ (S.chart n)) (S.chart n))
          (chartTargetBallRadius (S.chart n)) :=
    segment_subset_ball (S.chart_chartFlatPath_mem_ball n s) (S.chart_pCell_mem_ball n s)
  exact hseg.trans (chartTargetBall_subset_chart_target (S.chart n))

/-! ## Dyadic concatenation of the cell sub-paths and the `hcomp` induction -/

/-- The dyadic concatenation of the first `k + 1` cell sub-paths of `p`,
recursed exactly like `S.concatChartFlatPathAux`. -/
noncomputable def concatPCellAux (k : ℕ) : Path (γ (S.t 0)) (γ (S.t (k + 1))) := by
  induction k with
  | zero => exact S.pCell 0
  | succ k ih => exact ih.trans (S.pCell (k + 1))

@[simp] theorem concatPCellAux_zero : S.concatPCellAux 0 = S.pCell 0 := rfl

theorem concatPCellAux_succ (k : ℕ) :
    S.concatPCellAux (k + 1) = (S.concatPCellAux k).trans (S.pCell (k + 1)) := rfl

/-- **The dyadic `hcomp` induction.** The chart-flat dyadic concatenation is
homotopic rel endpoints to the dyadic concatenation of the cell sub-paths of `p`,
cell by cell. -/
theorem concatChartFlatPathAux_homotopic_concatPCellAux (k : ℕ) :
    (S.concatChartFlatPathAux k).Homotopic (S.concatPCellAux k) := by
  induction k with
  | zero =>
      simpa [PathChartBallSubdivision.concatChartFlatPathAux, concatPCellAux] using
        S.chartFlatPath_homotopic_pCell 0
  | succ k ih =>
      rw [show S.concatChartFlatPathAux (k + 1)
            = (S.concatChartFlatPathAux k).trans (S.chartFlatPath (k + 1)) from rfl,
          concatPCellAux_succ]
      exact ih.hcomp (S.chartFlatPath_homotopic_pCell (k + 1))

/-! ## Endgame: the cell concatenation is a reparametrisation of `p` -/

/-- The scalar affine cell path `s ↦ S.cellAffine n s : Path (S.t n) (S.t (n+1))`. -/
noncomputable def cellAffinePath (n : ℕ) : Path (S.t n) (S.t (n + 1)) where
  toFun := S.cellAffine n
  continuous_toFun := S.continuous_cellAffine n
  source' := by simp
  target' := by simp

@[simp] theorem cellAffinePath_apply (n : ℕ) (s : unitInterval) :
    S.cellAffinePath n s = S.cellAffine n s := rfl

/-- The scalar dyadic concatenation of the first `k + 1` affine cell paths,
recursed exactly like `S.concatPCellAux`. -/
noncomputable def concatCellAffineAux (k : ℕ) : Path (S.t 0) (S.t (k + 1)) := by
  induction k with
  | zero => exact S.cellAffinePath 0
  | succ k ih => exact ih.trans (S.cellAffinePath (k + 1))

theorem concatCellAffineAux_succ (k : ℕ) :
    S.concatCellAffineAux (k + 1)
      = (S.concatCellAffineAux k).trans (S.cellAffinePath (k + 1)) := rfl

/-- The cell concatenation is `γ` precomposed with the scalar dyadic
reparametrisation: `concatPCellAux k s = γ ((concatCellAffineAux k) s)`. -/
theorem concatPCellAux_eq_comp (k : ℕ) :
    ∀ s : unitInterval, S.concatPCellAux k s = γ (S.concatCellAffineAux k s) := by
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
      intro s
      rw [concatPCellAux_succ, concatCellAffineAux_succ, Path.trans_apply, Path.trans_apply]
      split
      · exact ih _
      · rfl

/-- The scalar dyadic reparametrisation as a continuous `I → I`. -/
noncomputable def reparamFun : unitInterval → unitInterval :=
  ⇑(S.concatCellAffineAux S.lastIndex)

theorem continuous_reparamFun : Continuous S.reparamFun :=
  (S.concatCellAffineAux S.lastIndex).continuous

theorem reparamFun_zero : S.reparamFun 0 = 0 := by
  have h : S.reparamFun 0 = S.t 0 := (S.concatCellAffineAux S.lastIndex).source'
  rw [h, S.t_zero]

theorem reparamFun_one : S.reparamFun 1 = 1 := by
  have hlast : S.t (S.lastIndex + 1) = 1 :=
    S.eq_one_of_lastIndex_le (Nat.le_succ S.lastIndex)
  have h : S.reparamFun 1 = S.t (S.lastIndex + 1) := (S.concatCellAffineAux S.lastIndex).target'
  rw [h, hlast]

/-- Source cast proof: `P₀ = γ (S.t 0)`. -/
theorem castSource_eq : P₀ = γ (S.t 0) := by simp [S.t_zero]

/-- Target cast proof: `P = γ (S.t (lastIndex + 1))`. -/
theorem castTarget_eq : P = γ (S.t (S.lastIndex + 1)) := by
  simp [S.eq_one_of_lastIndex_le (Nat.le_succ S.lastIndex)]

/-- The full cell concatenation, cast to `Path P₀ P`, equals `γ.reparam reparamFun`. -/
theorem concatPCellAux_lastIndex_cast_eq_reparam :
    (S.concatPCellAux S.lastIndex).cast S.castSource_eq S.castTarget_eq
      = γ.reparam S.reparamFun S.continuous_reparamFun S.reparamFun_zero S.reparamFun_one := by
  ext s
  simp only [Path.cast_coe, Path.coe_reparam, Function.comp_apply]
  exact S.concatPCellAux_eq_comp S.lastIndex s

/-- **Endgame.** The full cell concatenation is homotopic rel endpoints to `γ`
(after casting endpoints), via the universal reparametrisation homotopy
`Path.Homotopy.reparam`. -/
theorem concatPCellAux_lastIndex_homotopic_self :
    ((S.concatPCellAux S.lastIndex).cast S.castSource_eq S.castTarget_eq).Homotopic γ := by
  rw [S.concatPCellAux_lastIndex_cast_eq_reparam]
  exact ⟨(Path.Homotopy.reparam γ S.reparamFun S.continuous_reparamFun
      S.reparamFun_zero S.reparamFun_one).symm⟩

/-- **`ChartFlatHomotopyWall` witness for a given subdivision.** The chart-flat
dyadic concatenation of `S` is homotopic rel endpoints to `γ`. -/
theorem concatChartFlatPath_homotopic_self :
    (S.concatChartFlatPath).Homotopic γ := by
  have hcast : S.concatChartFlatPath
      = (S.concatChartFlatPathAux S.lastIndex).cast S.castSource_eq S.castTarget_eq := rfl
  rw [hcast]
  have hstep₁ :
      ((S.concatChartFlatPathAux S.lastIndex).cast S.castSource_eq S.castTarget_eq).Homotopic
        ((S.concatPCellAux S.lastIndex).cast S.castSource_eq S.castTarget_eq) :=
    Path.Homotopic.pathCast
      (S.concatChartFlatPathAux_homotopic_concatPCellAux S.lastIndex)
      S.castSource_eq S.castTarget_eq
  exact hstep₁.trans S.concatPCellAux_lastIndex_homotopic_self

end PathChartBallSubdivision

end Jacobians.Bridge

/-! ## The unconditional discharge of `ChartFlatHomotopyWall` -/

namespace Jacobians.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

omit [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
/-- **`ChartFlatHomotopyWall` holds unconditionally.** Every continuous loop is
homotopic rel endpoints to the chart-flat (piecewise-linear-in-charts)
concatenation of some chart-ball subdivision of itself. -/
theorem chartFlatHomotopyWall (x₀ : X) : ChartFlatHomotopyWall x₀ := by
  intro p
  obtain ⟨S⟩ := Jacobians.Bridge.exists_pathChartBallSubdivision p
  exact ⟨S, S.concatChartFlatPath_homotopic_self⟩

/-- **T-GEN, unconditional.** Every continuous loop has a piecewise-analytic
representative, so the homology classes of piecewise-analytic loops ℤ-span
`H1 X x₀` (`AnalyticLoopsGenerateH1 x₀`). Discharged via the unconditional
`chartFlatHomotopyWall`; no `AX_PeriodCycleBasis`, no Whitney/Grauert, no
analyticity hypothesis. -/
theorem analyticLoopsGenerateH1 (x₀ : X) : AnalyticLoopsGenerateH1 x₀ :=
  analyticLoopsGenerateH1_of_chartFlatHomotopyWall (chartFlatHomotopyWall x₀)

end Jacobians.RiemannSurface
