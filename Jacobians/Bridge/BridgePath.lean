import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bridge path infrastructure

This file will contain the auxiliary manifold/path construction needed to
replace the structural `bridgePath*` axioms in `KirovLineIntegral.lean`.

The first independent piece is the standard cubic reparameterization
`s ↦ 3s^2 - 2s^3`.  It fixes `0` and `1`, maps `[0, 1]` into `[0, 1]`, and
has zero derivative at both endpoints.  These endpoint-flat facts are the
calculus input for smooth concatenation of chart-local straight segments.
-/

namespace Jacobians.Bridge

open scoped Topology ContDiff

/-- The cubic "smoothstep" reparameterization used to flatten segment endpoints. -/
def flatReparam (s : ℝ) : ℝ :=
  3 * s ^ 2 - 2 * s ^ 3

@[simp] theorem flatReparam_zero : flatReparam 0 = 0 := by
  simp [flatReparam]

@[simp] theorem flatReparam_one : flatReparam 1 = 1 := by
  norm_num [flatReparam]

/-- The cubic reparameterization is continuous. -/
theorem continuous_flatReparam : Continuous flatReparam := by
  unfold flatReparam
  fun_prop

/-- The cubic reparameterization is differentiable. -/
theorem differentiable_flatReparam : Differentiable ℝ flatReparam := by
  unfold flatReparam
  fun_prop

/-- The cubic reparameterization is `C^n` for every `n`. -/
theorem contDiff_flatReparam (n : ℕ∞) : ContDiff ℝ n flatReparam := by
  unfold flatReparam
  fun_prop

/-- Derivative of the cubic reparameterization. -/
theorem hasDerivAt_flatReparam (s : ℝ) :
    HasDerivAt flatReparam (6 * s - 6 * s ^ 2) s := by
  unfold flatReparam
  convert (HasDerivAt.sub
    (HasDerivAt.const_mul (3 : ℝ) ((hasDerivAt_id s).pow 2))
    (HasDerivAt.const_mul (2 : ℝ) ((hasDerivAt_id s).pow 3))) using 1
  simp only [id_eq]
  ring_nf

/-- The cubic reparameterization is flat at `0`. -/
theorem hasDerivAt_flatReparam_zero : HasDerivAt flatReparam 0 0 := by
  simpa using hasDerivAt_flatReparam 0

/-- The cubic reparameterization is flat at `1`. -/
theorem hasDerivAt_flatReparam_one : HasDerivAt flatReparam 0 1 := by
  simpa using hasDerivAt_flatReparam 1

/-- Pointwise derivative of the cubic reparameterization. -/
theorem deriv_flatReparam (s : ℝ) :
    deriv flatReparam s = 6 * s - 6 * s ^ 2 :=
  (hasDerivAt_flatReparam s).deriv

@[simp] theorem deriv_flatReparam_zero : deriv flatReparam 0 = 0 := by
  simp [deriv_flatReparam]

@[simp] theorem deriv_flatReparam_one : deriv flatReparam 1 = 0 := by
  norm_num [deriv_flatReparam]

/-- The cubic reparameterization maps the unit interval into itself. -/
theorem flatReparam_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    flatReparam s ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have hs_sq : 0 ≤ s ^ 2 := sq_nonneg s
    have h_factor : 0 ≤ 3 - 2 * s := by nlinarith [hs.2]
    have hprod : 0 ≤ s ^ 2 * (3 - 2 * s) := mul_nonneg hs_sq h_factor
    calc
      0 ≤ s ^ 2 * (3 - 2 * s) := hprod
      _ = flatReparam s := by
        rw [flatReparam]
        ring
  · have hleft_sq : 0 ≤ (1 - s) ^ 2 := sq_nonneg (1 - s)
    have h_factor : 0 ≤ 2 * s + 1 := by nlinarith [hs.1]
    have hprod : 0 ≤ (1 - s) ^ 2 * (2 * s + 1) := mul_nonneg hleft_sq h_factor
    have hdiff : 0 ≤ 1 - flatReparam s := by
      calc
        0 ≤ (1 - s) ^ 2 * (2 * s + 1) := hprod
        _ = 1 - flatReparam s := by
          rw [flatReparam]
          ring
    linarith

/-- The cubic reparameterization sends `[0, 1]` into `[0, 1]`. -/
theorem mapsTo_flatReparam_Icc :
    Set.MapsTo flatReparam (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
  fun _ hs => flatReparam_mem_Icc hs

/-- On `[0, 1]`, the derivative of the cubic reparameterization is nonnegative. -/
theorem deriv_flatReparam_nonneg_of_mem_Icc {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ deriv flatReparam s := by
  rw [deriv_flatReparam]
  have hprod : 0 ≤ s * (1 - s) := mul_nonneg hs.1 (sub_nonneg.mpr hs.2)
  nlinarith [hprod]

/-- The endpoint-flat cubic reparameterization as a self-map of the unit interval. -/
def flatReparamUnit (s : unitInterval) : unitInterval :=
  ⟨flatReparam s, flatReparam_mem_Icc s.2⟩

@[simp] theorem flatReparamUnit_coe (s : unitInterval) :
    (flatReparamUnit s : ℝ) = flatReparam (s : ℝ) :=
  rfl

@[simp] theorem flatReparamUnit_zero : flatReparamUnit 0 = 0 := by
  apply Subtype.ext
  simp [flatReparamUnit]

@[simp] theorem flatReparamUnit_one : flatReparamUnit 1 = 1 := by
  apply Subtype.ext
  simp [flatReparamUnit]

/-- The unit-interval self-map induced by the cubic reparameterization is continuous. -/
theorem continuous_flatReparamUnit : Continuous flatReparamUnit := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_flatReparam.comp continuous_subtype_val

/-! ## Flat affine segments -/

section FlatSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine segment from `a` to `b`, reparameterized by `flatReparam`. -/
def flatSegment (a b : E) (t : ℝ) : E :=
  (1 - flatReparam t) • a + flatReparam t • b

@[simp] theorem flatSegment_zero (a b : E) : flatSegment a b 0 = a := by
  simp [flatSegment]

@[simp] theorem flatSegment_one (a b : E) : flatSegment a b 1 = b := by
  simp [flatSegment]

/-- A flat affine segment is continuous. -/
theorem continuous_flatSegment (a b : E) : Continuous (flatSegment a b) := by
  unfold flatSegment
  have hφ : Continuous flatReparam := continuous_flatReparam
  fun_prop

/-- A flat affine segment is differentiable. -/
theorem differentiable_flatSegment (a b : E) : Differentiable ℝ (flatSegment a b) := by
  unfold flatSegment
  have hφ : Differentiable ℝ flatReparam := differentiable_flatReparam
  fun_prop

/-- A flat affine segment is `C^n` for every `n`. -/
theorem contDiff_flatSegment (n : ℕ∞) (a b : E) : ContDiff ℝ n (flatSegment a b) := by
  unfold flatSegment
  have hφ : ContDiff ℝ n flatReparam := contDiff_flatReparam n
  fun_prop

/-- The flat affine segment has zero velocity at its left endpoint. -/
theorem hasDerivAt_flatSegment_zero (a b : E) :
    HasDerivAt (flatSegment a b) (0 : E) 0 := by
  unfold flatSegment
  have hleft : HasDerivAt (fun t : ℝ => 1 - flatReparam t) 0 0 := by
    simpa using
      HasDerivAt.sub (hasDerivAt_const (0 : ℝ) (1 : ℝ)) hasDerivAt_flatReparam_zero
  simpa using
    HasDerivAt.add (hleft.smul_const a) (hasDerivAt_flatReparam_zero.smul_const b)

/-- The flat affine segment has zero velocity at its right endpoint. -/
theorem hasDerivAt_flatSegment_one (a b : E) :
    HasDerivAt (flatSegment a b) (0 : E) 1 := by
  unfold flatSegment
  have hleft : HasDerivAt (fun t : ℝ => 1 - flatReparam t) 0 1 := by
    simpa using
      HasDerivAt.sub (hasDerivAt_const (1 : ℝ) (1 : ℝ)) hasDerivAt_flatReparam_one
  simpa using
    HasDerivAt.add (hleft.smul_const a) (hasDerivAt_flatReparam_one.smul_const b)

end FlatSegment

/-! ## Topological path source from complex charts -/

section ManifoldPathSource

variable {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]

/-- A connected space charted over `ℂ` is path connected. -/
theorem complex_chartedSpace_pathConnectedSpace : PathConnectedSpace X := by
  haveI : LocPathConnectedSpace X := ChartedSpace.locPathConnectedSpace (H := ℂ) (M := X)
  exact pathConnectedSpace_iff_connectedSpace.mpr inferInstance

/-- Any two points in a connected complex-charted space are joined by a bundled path. -/
theorem exists_path (P₀ P : X) : Nonempty (Path P₀ P) := by
  haveI : PathConnectedSpace X := complex_chartedSpace_pathConnectedSpace (X := X)
  exact ⟨PathConnectedSpace.somePath P₀ P⟩

end ManifoldPathSource

/-! ## Convex chart-ball straightness -/

section ConvexChartBallStraightness

open scoped Convex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A straight segment whose endpoints lie in a convex set stays in that set. -/
theorem segment_subset_of_convex {U : Set E} (hU : Convex ℝ U) {z₀ z₁ : E}
    (hz₀ : z₀ ∈ U) (hz₁ : z₁ ∈ U) :
    [z₀ -[ℝ] z₁] ⊆ U :=
  hU.segment_subset hz₀ hz₁

/-- A straight segment whose endpoints lie in a metric ball stays in that ball. -/
theorem segment_subset_ball {c z₀ z₁ : E} {r : ℝ}
    (hz₀ : z₀ ∈ Metric.ball c r) (hz₁ : z₁ ∈ Metric.ball c r) :
    [z₀ -[ℝ] z₁] ⊆ Metric.ball c r :=
  (convex_ball c r).segment_subset hz₀ hz₁

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The chart target contains a positive-radius ball around the image of its center. -/
theorem exists_ball_subset_chart_target (x : X) :
    ∃ r > 0, Metric.ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target :=
  Metric.isOpen_iff.mp (chartAt ℂ x).open_target ((chartAt ℂ x) x) (mem_chart_target ℂ x)

/-- If a chart-target ball contains both endpoints, the whole segment stays in the chart target. -/
theorem segment_subset_chart_target_of_mem_ball (x : X) {r : ℝ}
    (hr : Metric.ball ((chartAt ℂ x) x) r ⊆ (chartAt ℂ x).target)
    {z₀ z₁ : ℂ}
    (hz₀ : z₀ ∈ Metric.ball ((chartAt ℂ x) x) r)
    (hz₁ : z₁ ∈ Metric.ball ((chartAt ℂ x) x) r) :
    [z₀ -[ℝ] z₁] ⊆ (chartAt ℂ x).target :=
  (segment_subset_ball hz₀ hz₁).trans hr

end ConvexChartBallStraightness

/-! ## Chart-ball subdivision of a path -/

section ChartBallSubdivision

open Set
open scoped Convex unitInterval

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {P₀ P : X}

omit [ChartedSpace ℂ X] in
/-- The image of a bundled path is compact. -/
theorem isCompact_path_range (γ : Path P₀ P) : IsCompact (Set.range γ) := by
  simpa [Set.image_univ] using (isCompact_univ.image (Path.continuous γ))

/-- A chosen chart-target ball radius around the chart image of `x`. -/
noncomputable def chartTargetBallRadius (x : X) : ℝ :=
  Classical.choose (exists_ball_subset_chart_target x)

/-- The chosen chart-target ball radius is positive. -/
theorem chartTargetBallRadius_pos (x : X) : 0 < chartTargetBallRadius x :=
  (Classical.choose_spec (exists_ball_subset_chart_target x)).1

/-- The chosen chart-target ball is contained in the corresponding chart target. -/
theorem chartTargetBall_subset_chart_target (x : X) :
    Metric.ball ((chartAt ℂ x) x) (chartTargetBallRadius x) ⊆ (chartAt ℂ x).target :=
  (Classical.choose_spec (exists_ball_subset_chart_target x)).2

/-- The chart source restricted to the chosen coordinate ball around its center. -/
def chartBallSource (x : X) : Set X :=
  (chartAt ℂ x).source ∩
    (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) (chartTargetBallRadius x)

/-- The chart-ball source is open in `X`. -/
theorem isOpen_chartBallSource (x : X) : IsOpen (chartBallSource x) := by
  exact (chartAt ℂ x).isOpen_inter_preimage Metric.isOpen_ball

/-- The center of a chart-ball source lies in that chart-ball source. -/
theorem mem_chartBallSource_self (x : X) : x ∈ chartBallSource x := by
  constructor
  · exact mem_chart_source ℂ x
  · exact Metric.mem_ball_self (chartTargetBallRadius_pos x)

/-- The pullback to the unit interval of a chart-ball source along a path. -/
def pathChartBallCover (γ : Path P₀ P) (x : X) : Set unitInterval :=
  γ ⁻¹' chartBallSource x

/-- The chart-ball pullback cover consists of open subsets of the unit interval. -/
theorem isOpen_pathChartBallCover (γ : Path P₀ P) (x : X) :
    IsOpen (pathChartBallCover γ x) := by
  exact (Path.continuous γ).isOpen_preimage _ (isOpen_chartBallSource x)

/-- The chart-ball pullback cover covers the whole unit interval. -/
theorem pathChartBallCover_univ_subset_iUnion (γ : Path P₀ P) :
    Set.univ ⊆ ⋃ x : X, pathChartBallCover γ x := by
  intro t _ht
  exact Set.mem_iUnion.mpr ⟨γ t, mem_chartBallSource_self (γ t)⟩

/--
A monotone finite subdivision of a path by chart balls.

Mathlib's interval-refinement lemma naturally returns a monotone sequence which is eventually `1`;
`lastIndex` and `breakpoints` below provide the finite `Fin (N+1)` view.
-/
structure PathChartBallSubdivision (γ : Path P₀ P) where
  /-- Breakpoints as a monotone sequence in the unit interval. -/
  t : ℕ → unitInterval
  /-- The first breakpoint is `0`. -/
  t_zero : t 0 = 0
  /-- Breakpoints are monotone. -/
  monotone_t : Monotone t
  /-- The sequence reaches `1` and then remains there. -/
  eventually_one : ∃ n, ∀ m ≥ n, t m = 1
  /-- A chart center assigned to each subinterval. -/
  chart : ℕ → X
  /-- Each adjacent subinterval maps into the assigned chart ball. -/
  subinterval_subset_chartBall :
    ∀ n, Set.Icc (t n) (t (n + 1)) ⊆ pathChartBallCover γ (chart n)

/-- Every bundled path has a chart-ball subdivision. -/
theorem exists_pathChartBallSubdivision (γ : Path P₀ P) :
    Nonempty (PathChartBallSubdivision γ) := by
  rcases exists_monotone_Icc_subset_open_cover_unitInterval
      (c := pathChartBallCover γ)
      (isOpen_pathChartBallCover γ)
      (pathChartBallCover_univ_subset_iUnion γ) with
    ⟨t, ht0, hmono, heventually, hlocal⟩
  choose chart hchart using hlocal
  exact ⟨{
    t := t
    t_zero := ht0
    monotone_t := hmono
    eventually_one := heventually
    chart := chart
    subinterval_subset_chartBall := hchart }⟩

namespace PathChartBallSubdivision

variable {γ : Path P₀ P} (S : PathChartBallSubdivision γ)

/-- The first index at which the subdivision has reached `1`. -/
noncomputable def lastIndex (S : PathChartBallSubdivision γ) : ℕ := by
  classical exact Nat.find S.eventually_one

/-- All breakpoints after `lastIndex` are equal to `1`. -/
theorem eq_one_of_lastIndex_le (S : PathChartBallSubdivision γ) {m : ℕ}
    (hm : S.lastIndex ≤ m) : S.t m = 1 := by
  classical
  exact (Nat.find_spec S.eventually_one) m hm

@[simp] theorem t_lastIndex (S : PathChartBallSubdivision γ) :
    S.t S.lastIndex = 1 := by
  exact S.eq_one_of_lastIndex_le le_rfl

/-- The finite `Fin (N+1)` view of the subdivision breakpoints. -/
def breakpoints (S : PathChartBallSubdivision γ) : Fin (S.lastIndex + 1) → unitInterval :=
  fun i => S.t i

@[simp] theorem breakpoints_zero (S : PathChartBallSubdivision γ) :
    S.breakpoints ⟨0, Nat.succ_pos S.lastIndex⟩ = 0 := by
  exact S.t_zero

@[simp] theorem breakpoints_last (S : PathChartBallSubdivision γ) :
    S.breakpoints ⟨S.lastIndex, Nat.lt_succ_self S.lastIndex⟩ = 1 := by
  exact S.t_lastIndex

/-- On each subdivision interval, the path lies in the assigned chart source. -/
theorem subinterval_subset_chart_source (n : ℕ) :
    Set.Icc (S.t n) (S.t (n + 1)) ⊆ γ ⁻¹' (chartAt ℂ (S.chart n)).source := by
  intro u hu
  exact (S.subinterval_subset_chartBall n hu).1

/-- On each subdivision interval, the path lies in the assigned chart coordinate ball. -/
theorem subinterval_subset_chart_ball (n : ℕ) :
    Set.Icc (S.t n) (S.t (n + 1)) ⊆
      {u : unitInterval |
        (chartAt ℂ (S.chart n)) (γ u) ∈
          Metric.ball ((chartAt ℂ (S.chart n)) (S.chart n))
            (chartTargetBallRadius (S.chart n))} := by
  intro u hu
  exact (S.subinterval_subset_chartBall n hu).2

/-- The left endpoint of a subdivision interval lies in the assigned chart source. -/
theorem left_endpoint_mem_chart_source (n : ℕ) :
    γ (S.t n) ∈ (chartAt ℂ (S.chart n)).source := by
  exact S.subinterval_subset_chart_source n ⟨le_rfl, S.monotone_t (Nat.le_succ n)⟩

/-- The right endpoint of a subdivision interval lies in the assigned chart source. -/
theorem right_endpoint_mem_chart_source (n : ℕ) :
    γ (S.t (n + 1)) ∈ (chartAt ℂ (S.chart n)).source := by
  exact S.subinterval_subset_chart_source n ⟨S.monotone_t (Nat.le_succ n), le_rfl⟩

/-- The chart image of the left endpoint lies in the assigned chart coordinate ball. -/
theorem left_endpoint_mem_chart_ball (n : ℕ) :
    (chartAt ℂ (S.chart n)) (γ (S.t n)) ∈
      Metric.ball ((chartAt ℂ (S.chart n)) (S.chart n))
        (chartTargetBallRadius (S.chart n)) := by
  exact S.subinterval_subset_chart_ball n ⟨le_rfl, S.monotone_t (Nat.le_succ n)⟩

/-- The chart image of the right endpoint lies in the assigned chart coordinate ball. -/
theorem right_endpoint_mem_chart_ball (n : ℕ) :
    (chartAt ℂ (S.chart n)) (γ (S.t (n + 1))) ∈
      Metric.ball ((chartAt ℂ (S.chart n)) (S.chart n))
        (chartTargetBallRadius (S.chart n)) := by
  exact S.subinterval_subset_chart_ball n ⟨S.monotone_t (Nat.le_succ n), le_rfl⟩

end PathChartBallSubdivision

end ChartBallSubdivision

/-! ## Chart-local flat replacement on one subdivision interval -/

section ChartLocalFlatReplacement

open scoped Convex unitInterval

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {P₀ P : X}

/-- A flat affine segment is a point of the closed segment between its endpoints. -/
theorem flatSegment_mem_segment {a b : ℂ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    flatSegment a b t ∈ [a -[ℝ] b] := by
  rw [show flatSegment a b t = AffineMap.lineMap a b (flatReparam t) by
    simp [flatSegment, AffineMap.lineMap_apply_module]]
  exact lineMap_mem_segment ℝ a b (flatReparam_mem_Icc ht)

namespace PathChartBallSubdivision

variable {γ : Path P₀ P} (S : PathChartBallSubdivision γ)

/-- The chart-coordinate flat segment for a subdivision interval stays in the chart target. -/
theorem flatSegment_mem_chart_target (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    flatSegment ((chartAt ℂ (S.chart n)) (γ (S.t n)))
      ((chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))) s ∈
        (chartAt ℂ (S.chart n)).target := by
  exact segment_subset_chart_target_of_mem_ball (S.chart n)
    (chartTargetBall_subset_chart_target (S.chart n))
    (S.left_endpoint_mem_chart_ball n)
    (S.right_endpoint_mem_chart_ball n)
    (flatSegment_mem_segment hs)

/--
The chart-local flat replacement path on the `n`th subdivision interval.

This is the local piece that will be concatenated in the next layer. It is already continuous,
endpoint-correct, and its coordinate representative is the previously proved flat affine segment.
-/
noncomputable def chartFlatPath (n : ℕ) :
    Path (γ (S.t n)) (γ (S.t (n + 1))) where
  toFun s := (chartAt ℂ (S.chart n)).symm
    (flatSegment ((chartAt ℂ (S.chart n)) (γ (S.t n)))
      ((chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))) (s : ℝ))
  continuous_toFun := by
    have hflat : Continuous fun s : unitInterval =>
        flatSegment ((chartAt ℂ (S.chart n)) (γ (S.t n)))
          ((chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))) (s : ℝ) :=
      (continuous_flatSegment _ _).comp continuous_subtype_val
    have htarget : ∀ s : unitInterval,
        flatSegment ((chartAt ℂ (S.chart n)) (γ (S.t n)))
          ((chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))) (s : ℝ) ∈
            (chartAt ℂ (S.chart n)).target := fun s =>
      S.flatSegment_mem_chart_target n s.2
    exact (chartAt ℂ (S.chart n)).continuousOn_symm.comp_continuous hflat htarget
  source' := by
    simpa using (chartAt ℂ (S.chart n)).left_inv (S.left_endpoint_mem_chart_source n)
  target' := by
    simpa using (chartAt ℂ (S.chart n)).left_inv (S.right_endpoint_mem_chart_source n)

/-- In the interior of a local piece, its subdivision-chart coordinate is the flat segment. -/
theorem chartFlatPath_chart_eventuallyEq_flatSegment_of_mem_Ioo (n : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ((chartAt ℂ (S.chart n)).toFun ∘ (S.chartFlatPath n).extend) =ᶠ[𝓝 s]
      flatSegment ((chartAt ℂ (S.chart n)) (γ (S.t n)))
        ((chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))) := by
  filter_upwards [Icc_mem_nhds hs.1 hs.2] with u hu
  dsimp only [Function.comp_apply]
  rw [Path.extend_apply _ hu]
  exact (chartAt ℂ (S.chart n)).right_inv (S.flatSegment_mem_chart_target n hu)

/-- Away from its endpoints, each local piece is differentiable in its subdivision chart. -/
theorem chartFlatPath_chart_differentiableAt_of_mem_Ioo (n : ℕ) {s : ℝ}
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ
      ((chartAt ℂ (S.chart n)).toFun ∘ (S.chartFlatPath n).extend) s := by
  let a : ℂ := (chartAt ℂ (S.chart n)) (γ (S.t n))
  let b : ℂ := (chartAt ℂ (S.chart n)) (γ (S.t (n + 1)))
  have hdiff : DifferentiableAt ℝ (flatSegment a b) s :=
    (differentiable_flatSegment a b).differentiableAt
  exact hdiff.congr_of_eventuallyEq
    (S.chartFlatPath_chart_eventuallyEq_flatSegment_of_mem_Ioo n hs)

/-- Concatenate the first `k + 1` chart-flat subdivision pieces. -/
noncomputable def concatChartFlatPathAux (k : ℕ) :
    Path (γ (S.t 0)) (γ (S.t (k + 1))) := by
  induction k with
  | zero =>
      exact S.chartFlatPath 0
  | succ k ih =>
      exact ih.trans (S.chartFlatPath (k + 1))

/-- The full chart-flat replacement path for a subdivision. -/
noncomputable def concatChartFlatPath : Path P₀ P :=
  (S.concatChartFlatPathAux S.lastIndex).cast
    (by
      simp [S.t_zero])
    (by
      have hlast : S.t (S.lastIndex + 1) = 1 :=
        S.eq_one_of_lastIndex_le (Nat.le_succ S.lastIndex)
      simp [hlast])

end PathChartBallSubdivision

end ChartLocalFlatReplacement

/-! ## Global bridge-path implementation -/

section BridgePathImpl

open scoped Manifold

variable {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]

/-- The concrete bridge path from `P₀` to `P`, extended constantly outside `[0, 1]`. -/
noncomputable def bridgePathImpl (P₀ P : X) : ℝ → X :=
  let γ : Path P₀ P := (exists_path P₀ P).some
  let S : PathChartBallSubdivision γ := (exists_pathChartBallSubdivision γ).some
  (S.concatChartFlatPath).extend

@[simp] theorem bridgePathImpl_at_zero (P₀ P : X) :
    bridgePathImpl (X := X) P₀ P 0 = P₀ := by
  simp [bridgePathImpl]

@[simp] theorem bridgePathImpl_at_one (P₀ P : X) :
    bridgePathImpl (X := X) P₀ P 1 = P := by
  simp [bridgePathImpl]

/-- The concrete bridge path is continuous as a function on `ℝ`. -/
theorem bridgePathImpl_continuous (P₀ P : X) :
    Continuous (bridgePathImpl (X := X) P₀ P) := by
  dsimp [bridgePathImpl]
  exact Path.continuous_extend _

/--
Chart transitions between complex manifold charts are real-differentiable at points of their
overlap.  This is the outer transition needed when the bridge path is first written in a fixed
subdivision chart and then re-centered at the moving chart `chartAt ℂ (bridgePathImpl P₀ P t)`.
-/
theorem chartAt_comp_chartAt_symm_differentiableAt
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x y : X) {z : ℂ}
    (hz : z ∈ ((chartAt ℂ y).symm ≫ₕ chartAt ℂ x).source) :
    DifferentiableAt ℝ ((chartAt ℂ x).toFun ∘ (chartAt ℂ y).symm) z := by
  have hmem : z ∈ ((extChartAt 𝓘(ℂ) y).symm ≫ extChartAt 𝓘(ℂ) x).source := by
    simpa [ext_coord_change_source, modelWithCornersSelf_coe] using hz
  have hcont :
      ContDiffWithinAt ℂ ω
        (extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) y).symm)
        (Set.range ((𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) : ℂ → ℂ)) z :=
    contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) x y hmem
  have hcontAt :
      ContDiffAt ℂ ω
        (extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) y).symm) z := by
    rw [← contDiffWithinAt_univ]
    simpa [modelWithCornersSelf_coe] using hcont
  have hdC : DifferentiableAt ℂ
      (extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) y).symm) z :=
    hcontAt.differentiableAt (by simp)
  have hdR : DifferentiableAt ℝ
      (extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) y).symm) z :=
    hdC.restrictScalars ℝ
  simpa [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_def] using hdR

-- TODO(layer 3 differentiability): upgrade the proved per-piece interior lemma
-- `PathChartBallSubdivision.chartFlatPath_chart_differentiableAt_of_mem_Ioo` to the
-- Kirov-side chart-local regularity statement for the extended global concatenation.
-- Remaining proof obligations:
-- * handle `Path.extend` at local endpoints, using `hasDerivAt_flatSegment_zero/_one`
--   against the constant extension outside `[0, 1]`;
-- * propagate that endpoint-flat statement through the recursive `Path.trans` joins;
-- * compose with the smooth chart transition from the subdivision chart to `chartAt` at
--   the current bridge-path point.
--
-- The remaining target shape is:
--
-- theorem bridgePathImpl_chart_differentiableAt
--     {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
--     [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) (t : ℝ) :
--     DifferentiableAt ℝ
--       ((chartAt (H := ℂ) (bridgePathImpl (X := X) P₀ P t)).toFun ∘
--         (bridgePathImpl (X := X) P₀ P)) t

end BridgePathImpl

end Jacobians.Bridge
