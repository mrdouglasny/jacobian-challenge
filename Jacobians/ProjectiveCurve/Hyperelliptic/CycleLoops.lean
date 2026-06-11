/-
# Hyperelliptic branch-cut loops: the square-root lift constructor

Foundations for the `PeriodCycleBasis` witness on the odd hyperelliptic
curve `HyperellipticOdd H h` (CYCLEBASIS_ALTERNATIVES.md direction 2a,
milestone M1).

## The construction

A cycle on the double cover `y² = f(x)` is specified by a loop in the
x-plane avoiding the branch locus together with a continuous square-root
branch of `f` along it:

* `SqrtArcData H` — `x, y : ℝ → ℂ` with `x` real-analytic, `y` continuous,
  `y(r)² = f(x(r))`, and `f(x(r)) ≠ 0` (the loop avoids branch points).

The lift `r ↦ (x r, y r)` lands in the smooth locus `y ≠ 0`, where the
preferred chart of the atlas (`affineChartProjX`, lifted through the
one-point compactification by `affineLiftChart`) is the x-projection
itself. Hence **the moving-chart readout of the lifted curve is literally
the base loop `x`** (`extChartAt_toOdd`), and:

* piecewise-real-analyticity of the lift (`IsAnalyticArcStrong`) reduces
  to analyticity of `x` via `isAnalyticArcStrong_of_movingChart`
  — no analyticity of the branch `y` is needed;
* the canonical period integrand reduces to the explicit complex integral
  `form.coeff (x r, y r) (x r) · x'(r)` (`canonicalIntegrand_toOddArc`),
  milestone M3's computable form.

`circleX` provides the concrete base loops (circles around branch-point
pairs); `segmentX` provides connectors for rebasing at a common basepoint
via `AnalyticLoop.conjugate`.

## What is NOT here (named-hypothesis boundary)

The *existence of a closed branch* `y` around a circle enclosing an even
number of branch points (`y 1 = y 0`) is the square-root monodromy
computation; continuous branches exist by covering theory
(`HyperellipticAffine.sqMap_covering`), and closure awaits the
covering/SVK package. Constructors below take the branch as data, never
as a `sorry`. See `docs/planning/HYP_CB_BLOCKER.md`.
-/
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Jacobians.RiemannSurface.AnalyticArcMovingChart
import Jacobians.RiemannSurface.LoopConjugation

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- Data for a square-root lift of an analytic x-plane arc to the
hyperelliptic curve `y² = f(x)`: the base arc `x`, a continuous branch `y`
of `√(f ∘ x)` along it, and avoidance of the branch locus.

The fields are stated on all of `ℝ` (the `AnalyticArc` design extends arcs
beyond `[0, 1]` by a dummy continuation); for circle/segment base arcs the
natural parametrizations are entire, and periodic branches extend with them. -/
structure SqrtArcData (H : HyperellipticData) where
  /-- The base arc in the x-plane. -/
  x : ℝ → ℂ
  /-- The square-root branch of `f ∘ x` along the arc. -/
  y : ℝ → ℂ
  /-- The base arc is real-analytic at every parameter. -/
  x_analytic : ∀ r : ℝ, AnalyticAt ℝ x r
  /-- The branch is continuous (analyticity is automatic in the x-chart and
  never used; see the module docstring). -/
  y_continuous : Continuous y
  /-- The defining branch relation `y(r)² = f(x(r))`. -/
  sq_eq : ∀ r : ℝ, y r ^ 2 = H.f.eval (x r)
  /-- The base arc avoids the branch locus (roots of `f`). -/
  avoids : ∀ r : ℝ, H.f.eval (x r) ≠ 0

namespace SqrtArcData

variable {H : HyperellipticData} (D : SqrtArcData H)

theorem y_ne_zero (r : ℝ) : D.y r ≠ 0 := by
  intro h0
  exact D.avoids r (by rw [← D.sq_eq r, h0]; ring)

theorem x_continuous : Continuous D.x :=
  continuous_iff_continuousAt.mpr fun r => (D.x_analytic r).continuousAt

/-- The lifted curve on the affine hyperelliptic curve. -/
def toAffine : ℝ → HyperellipticAffine H :=
  fun r => ⟨(D.x r, D.y r), D.sq_eq r⟩

@[simp] theorem toAffine_val (r : ℝ) : (D.toAffine r).val = (D.x r, D.y r) :=
  rfl

theorem toAffine_mem_smoothLocusY (r : ℝ) :
    D.toAffine r ∈ HyperellipticAffine.smoothLocusY H :=
  D.y_ne_zero r

theorem continuous_toAffine : Continuous D.toAffine :=
  (D.x_continuous.prodMk D.y_continuous).subtype_mk _

variable (h : Odd H.f.natDegree)

/-- The lifted curve on the compact odd hyperelliptic curve. -/
def toOdd : ℝ → HyperellipticOdd H h :=
  fun r => HyperellipticOdd.coe (D.toAffine r)

theorem continuous_toOdd : Continuous (D.toOdd h) :=
  OnePoint.continuous_coe.comp D.continuous_toAffine

/-- **Chart readout.** In the moving chart of the lifted curve, the lift
reads off as the base x-plane arc: the preferred chart at any point of the
lift is the (lifted) x-projection chart `affineChartProjX`. This is the
device that reduces all analyticity and period computations on the curve
to the x-plane. -/
theorem extChartAt_toOdd (r u : ℝ) :
    (extChartAt 𝓘(ℂ) (D.toOdd h r)) (D.toOdd h u) = D.x u := by
  have hchart : chartAt ℂ (D.toOdd h r) =
      HyperellipticOdd.affineLiftChart (H := H) (h := h) (D.toAffine r) := rfl
  have hlift :
      (HyperellipticOdd.affineLiftChart (H := H) (h := h) (D.toAffine r))
          (D.toOdd h u) =
        (ChartedSpace.chartAt (D.toAffine r) :
            OpenPartialHomeomorph (HyperellipticAffine H) ℂ) (D.toAffine u) :=
    OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  have haff :
      (ChartedSpace.chartAt (D.toAffine r) :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ) (D.toAffine u) =
        D.x u := by
    have hq : D.toAffine r ∈ HyperellipticAffine.smoothLocusY H :=
      D.toAffine_mem_smoothLocusY r
    have : (ChartedSpace.chartAt (D.toAffine r) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ) =
        HyperellipticAffine.affineChartProjX (D.toAffine r) hq :=
      HyperellipticAffine.affineChartAt_of_mem_smoothLocusY _ hq
    rw [this]
    rfl
  calc (extChartAt 𝓘(ℂ) (D.toOdd h r)) (D.toOdd h u)
      = (chartAt ℂ (D.toOdd h r)) (D.toOdd h u) := by
        simp [extChartAt]
    _ = D.x u := by rw [hchart, hlift, haff]

/-- Moving-chart analyticity of the lift: immediate from the chart readout
and analyticity of the base arc. -/
theorem movingChart_analyticAt (r : ℝ) :
    AnalyticAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) (D.toOdd h r)) (D.toOdd h u)) r := by
  have heq : (fun u : ℝ => (extChartAt 𝓘(ℂ) (D.toOdd h r)) (D.toOdd h u)) = D.x :=
    funext fun u => D.extChartAt_toOdd h r u
  rw [heq]
  exact D.x_analytic r

/-- The square-root lift as a piecewise-real-analytic arc on the compact
odd hyperelliptic curve (trivial base partition `{0, 1}`). -/
noncomputable def toOddArc : AnalyticArc (HyperellipticOdd H h) :=
  AnalyticArc.ofMovingChart (D.toOdd h) (D.continuous_toOdd h)
    (D.movingChart_analyticAt h)

@[simp] theorem toOddArc_extend : (D.toOddArc h).extend = D.toOdd h :=
  rfl

/-- The square-root lift of a *closed* base arc with *closed* branch, as an
`AnalyticLoop` based at its own starting point. The branch-closure
hypothesis `hy` is the square-root monodromy input (trivial monodromy around
an even number of branch points); see the module docstring. -/
noncomputable def toOddLoop (hx : D.x 1 = D.x 0) (hy : D.y 1 = D.y 0) :
    AnalyticLoop (HyperellipticOdd H h) (D.toOdd h 0) :=
  AnalyticLoop.ofMovingChart (D.toOdd h) (D.continuous_toOdd h)
    (D.movingChart_analyticAt h)
    (by
      show HyperellipticOdd.coe (D.toAffine 1) = HyperellipticOdd.coe (D.toAffine 0)
      have : D.toAffine 1 = D.toAffine 0 := Subtype.ext (Prod.ext hx hy)
      rw [this])

/-! ## Milestone M3 (arc level): the period integrand in computable form

On a square-root lift the canonical moving-chart period integrand of any
holomorphic 1-form collapses to an explicit complex-valued function of the
base arc: coefficient at the lifted point, read in the x-coordinate, times
`x'(r)`. The period of the cycle is then an ordinary interval integral in
the x-plane — for the hyperelliptic forms `x^k dx / y` this is the
classical branch-cut integral `∫ x(r)^k x'(r) / y(r) dr`. -/

/-- The canonical period integrand of the lifted arc, in computable form. -/
theorem canonicalIntegrand_toOddArc (form : HolomorphicOneForm (HyperellipticOdd H h))
    (r : ℝ) :
    canonicalIntegrand (D.toOddArc h) form r =
      form.coeff (D.toOdd h r) (D.x r) * deriv D.x r := by
  have heq : (fun u : ℝ => (extChartAt 𝓘(ℂ) (D.toOdd h r)) (D.toOdd h u)) = D.x :=
    funext fun u => D.extChartAt_toOdd h r u
  unfold canonicalIntegrand
  rw [toOddArc_extend]
  rw [show (extChartAt 𝓘(ℂ) (D.toOdd h r)) (D.toOdd h r) = D.x r from
    D.extChartAt_toOdd h r r]
  rw [heq]

/-- **The period of a square-root-lifted cycle is an explicit x-plane
integral.** For the hyperelliptic 1-forms this is the classical branch-cut
period `∫₀¹ coeff(x(r), y(r)) · x'(r) dr`. -/
theorem canonicalArcIntegral_toOddArc
    (form : HolomorphicOneForm (HyperellipticOdd H h)) :
    canonicalArcIntegral (D.toOddArc h) form =
      ∫ r in (0 : ℝ)..1, form.coeff (D.toOdd h r) (D.x r) * deriv D.x r := by
  unfold canonicalArcIntegral
  exact intervalIntegral.integral_congr fun r _ =>
    D.canonicalIntegrand_toOddArc h form r

end SqrtArcData

/-! ## Concrete base arcs: circles and segments in the x-plane

The classical aᵢ/bᵢ cycles of the hyperelliptic curve are (conjugated)
lifts of circles in the x-plane enclosing pairs of branch points. The
connectors used for rebasing are lifts of segments. Both parametrizations
are entire, hence satisfy the `x_analytic` field on all of `ℝ`. -/

/-- A circle in the x-plane: `r ↦ c + R · exp(2πi r)` (full turn on `[0,1]`). -/
noncomputable def circleX (c : ℂ) (R : ℝ) : ℝ → ℂ :=
  fun r => c + (R : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))

theorem analyticAt_circleX (c : ℂ) (R : ℝ) (r : ℝ) :
    AnalyticAt ℝ (circleX c R) r := by
  unfold circleX
  have hcoe : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) r :=
    Complex.ofRealCLM.analyticAt r
  have hmul : AnalyticAt ℝ (fun t : ℝ => 2 * Real.pi * Complex.I * (t : ℂ)) r :=
    analyticAt_const.mul hcoe
  have hexp : AnalyticAt ℝ
      (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) r :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp hmul
  exact analyticAt_const.add (analyticAt_const.mul hexp)

@[simp] theorem circleX_zero (c : ℂ) (R : ℝ) : circleX c R 0 = c + R := by
  simp [circleX]

theorem circleX_closed (c : ℂ) (R : ℝ) : circleX c R 1 = circleX c R 0 := by
  unfold circleX
  have h1 : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨1, by push_cast; ring⟩
  have h0 : Complex.exp (2 * Real.pi * Complex.I * ((0 : ℝ) : ℂ)) = 1 := by
    norm_num
  rw [h1, h0]

/-- A segment in the x-plane from `a` to `b`: `r ↦ a + r · (b − a)`. -/
noncomputable def segmentX (a b : ℂ) : ℝ → ℂ :=
  fun r => a + (r : ℂ) * (b - a)

theorem analyticAt_segmentX (a b : ℂ) (r : ℝ) :
    AnalyticAt ℝ (segmentX a b) r := by
  unfold segmentX
  exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt r).mul analyticAt_const)

@[simp] theorem segmentX_zero (a b : ℂ) : segmentX a b 0 = a := by simp [segmentX]

@[simp] theorem segmentX_one (a b : ℂ) : segmentX a b 1 = b := by
  simp [segmentX]

/-- `SqrtArcData` over a circle base arc, given a continuous branch of
`√(f ∘ circle)`. The branch exists by covering theory
(`HyperellipticAffine.sqMap_covering`); its closure after a full turn is the
monodromy input consumed by `SqrtArcData.toOddLoop`. -/
noncomputable def SqrtArcData.ofCircle {H : HyperellipticData} (c : ℂ) (R : ℝ)
    (y : ℝ → ℂ) (hy : Continuous y)
    (hsq : ∀ r : ℝ, y r ^ 2 = H.f.eval (circleX c R r))
    (havoid : ∀ r : ℝ, H.f.eval (circleX c R r) ≠ 0) : SqrtArcData H where
  x := circleX c R
  y := y
  x_analytic := analyticAt_circleX c R
  y_continuous := hy
  sq_eq := hsq
  avoids := havoid

/-- `SqrtArcData` over a segment base arc (a connector), given a continuous
branch of `√(f ∘ segment)`. -/
noncomputable def SqrtArcData.ofSegment {H : HyperellipticData} (a b : ℂ)
    (y : ℝ → ℂ) (hy : Continuous y)
    (hsq : ∀ r : ℝ, y r ^ 2 = H.f.eval (segmentX a b r))
    (havoid : ∀ r : ℝ, H.f.eval (segmentX a b r) ≠ 0) : SqrtArcData H where
  x := segmentX a b
  y := y
  x_analytic := analyticAt_segmentX a b
  y_continuous := hy
  sq_eq := hsq
  avoids := havoid

end Jacobians.ProjectiveCurve
