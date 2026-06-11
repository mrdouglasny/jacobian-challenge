/-
# Period non-degeneracy (B-3): the Forster §21.4 engine

No nonzero ℝ-linear functional on `HolomorphicOneForm X →ₗ[ℂ] ℂ` kills the
period functionals of all closed analytic loops based at `x₀`; equivalently
the ℝ-span of those period functionals is everything.

Route (Forster, *Lectures on Riemann Surfaces*, §21, Lemma 21.4 —
dissection-free): if `Λ` kills all loop periods, the potential
`u(Q) := Λ (∫ over bridgePathArc x₀ Q)` is a *defined* function (no
well-definedness quotient), is locally `const + Re ∘ (holomorphic primitive)`
because Λ kills the correction loops, hence is constant by the maximum
principle (open-mapping dichotomy) on the compact connected surface; the
associated holomorphic 1-form then has vanishing coefficient at every chart
center, hence is zero, hence `Λ = 0`.

Design: `docs/planning/B3_NONDEG_ROUTE.md`.
-/
import Jacobians.RiemannSurface.ChartSegmentArc
import Jacobians.RiemannSurface.ArcAlgebra
import Jacobians.RiemannSurface.LoopIntegral
import Jacobians.Axioms.FiniteDimOneForms

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.Bridge

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The period functionals -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The period functional of a closed analytic loop:
`ω ↦ ∮_γ ω`, as a `ℂ`-linear functional on holomorphic 1-forms. -/
def loopPeriodFunctional (x₀ : X) (γ : AnalyticLoop X x₀) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ :=
  arcPeriodFunctional γ.arc
    fun form => analyticArc_canonicalIntegrand_intervalIntegrable γ.arc form

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
@[simp]
theorem loopPeriodFunctional_apply (x₀ : X) (γ : AnalyticLoop X x₀)
    (form : HolomorphicOneForm X) :
    loopPeriodFunctional x₀ γ form = canonicalArcIntegral γ.arc form :=
  rfl

omit [CompactSpace X] in
/-- The basepoint path-integral functional `ω ↦ ∫_{bridgePathArc x₀ Q} ω`.
A *defined* single-valued lift of the Abel–Jacobi coordinate; its
path-dependence is exactly a loop period. -/
def basepointPeriodFunctional (x₀ Q : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ :=
  arcPeriodFunctional (bridgePathArc x₀ Q)
    fun form =>
      analyticArc_canonicalIntegrand_intervalIntegrable (bridgePathArc x₀ Q) form

omit [CompactSpace X] in
@[simp]
theorem basepointPeriodFunctional_apply (x₀ Q : X)
    (form : HolomorphicOneForm X) :
    basepointPeriodFunctional x₀ Q form =
      canonicalArcIntegral (bridgePathArc x₀ Q) form :=
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The chart-segment period functional `ω ↦ ∫_{chartSegmentArc P Q} ω`. -/
def segmentPeriodFunctional (P : X) {Q : X} (hQ : Q ∈ chartBallSource P) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ :=
  arcPeriodFunctional (chartSegmentArc P hQ)
    fun form =>
      analyticArc_canonicalIntegrand_intervalIntegrable (chartSegmentArc P hQ) form

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
@[simp]
theorem segmentPeriodFunctional_apply (P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) (form : HolomorphicOneForm X) :
    segmentPeriodFunctional P hQ form =
      canonicalArcIntegral (chartSegmentArc P hQ) form :=
  rfl

/-! ## The increment loop and the increment identity -/

omit [CompactSpace X] in
theorem bridge_trans_segment_endpoint (x₀ P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) :
    (bridgePathArc x₀ P).extend 1 = (chartSegmentArc P hQ).extend 0 := by
  simp [bridgePathArc]

omit [CompactSpace X] in
theorem bridge_segment_trans_reverse_endpoint (x₀ P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) :
    ((bridgePathArc x₀ P).trans (chartSegmentArc P hQ)
        (bridge_trans_segment_endpoint x₀ P hQ)).extend 1
      = (bridgePathArc x₀ Q).reverse.extend 0 := by
  simp [bridgePathArc]

/-- The closed correction loop at `x₀`:
`bridge(x₀ → P) ∙ chartSegment(P → Q) ∙ bridge(x₀ → Q)⁻¹`. -/
def incrementLoop (x₀ P : X) {Q : X} (hQ : Q ∈ chartBallSource P) :
    AnalyticLoop X x₀ where
  arc :=
    ((bridgePathArc x₀ P).trans (chartSegmentArc P hQ)
        (bridge_trans_segment_endpoint x₀ P hQ)).trans
      (bridgePathArc x₀ Q).reverse
      (bridge_segment_trans_reverse_endpoint x₀ P hQ)
  start_eq := by simp [bridgePathArc]
  end_eq := by simp [bridgePathArc]

omit [CompactSpace X] in
/-- **Increment identity** (functional level, exact): moving the endpoint of
the basepoint functional from `P` to a chart-ball neighbour `Q` costs the
chart-segment functional, up to the period of the closed `incrementLoop`. -/
theorem basepointPeriodFunctional_increment (x₀ P : X) {Q : X}
    (hQ : Q ∈ chartBallSource P) :
    basepointPeriodFunctional x₀ Q =
      basepointPeriodFunctional x₀ P + segmentPeriodFunctional P hQ -
        loopPeriodFunctional x₀ (incrementLoop x₀ P hQ) := by
  refine LinearMap.ext fun form => ?_
  have hint : ∀ γ : AnalyticArc X,
      IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume 0 1 :=
    fun γ => analyticArc_canonicalIntegrand_intervalIntegrable γ form
  have htrans1 :
      canonicalArcIntegral
          ((bridgePathArc x₀ P).trans (chartSegmentArc P hQ)
            (bridge_trans_segment_endpoint x₀ P hQ)) form =
        canonicalArcIntegral (bridgePathArc x₀ P) form +
          canonicalArcIntegral (chartSegmentArc P hQ) form :=
    canonicalArcIntegral_trans _ _ _ form (hint _) (hint _)
  have htrans2 :
      canonicalArcIntegral (incrementLoop x₀ P hQ).arc form =
        canonicalArcIntegral
            ((bridgePathArc x₀ P).trans (chartSegmentArc P hQ)
              (bridge_trans_segment_endpoint x₀ P hQ)) form +
          canonicalArcIntegral (bridgePathArc x₀ Q).reverse form :=
    canonicalArcIntegral_trans _ _
      (bridge_segment_trans_reverse_endpoint x₀ P hQ) form (hint _) (hint _)
  have hrev :
      canonicalArcIntegral (bridgePathArc x₀ Q).reverse form =
        -canonicalArcIntegral (bridgePathArc x₀ Q) form :=
    canonicalArcIntegral_reverse _ form
  have hloop :
      canonicalArcIntegral (incrementLoop x₀ P hQ).arc form =
        canonicalArcIntegral (bridgePathArc x₀ P) form +
          canonicalArcIntegral (chartSegmentArc P hQ) form -
          canonicalArcIntegral (bridgePathArc x₀ Q) form := by
    rw [htrans2, htrans1, hrev]
    ring
  simp only [LinearMap.sub_apply, LinearMap.add_apply, loopPeriodFunctional_apply,
    basepointPeriodFunctional_apply, segmentPeriodFunctional_apply]
  rw [hloop]
  ring

omit [CompactSpace X] in
/-- The potential increment formula: if `Λ` kills all loop periods at `x₀`,
then the potential `u = Λ ∘ basepointPeriodFunctional x₀` changes across a
chart ball exactly by the `Λ`-value of the chart-segment functional. -/
theorem potential_increment (x₀ : X)
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ γ : AnalyticLoop X x₀, Λ (loopPeriodFunctional x₀ γ) = 0)
    (P : X) {Q : X} (hQ : Q ∈ chartBallSource P) :
    Λ (basepointPeriodFunctional x₀ Q) =
      Λ (basepointPeriodFunctional x₀ P) + Λ (segmentPeriodFunctional P hQ) := by
  rw [basepointPeriodFunctional_increment x₀ P hQ, map_sub, map_add,
    hΛ (incrementLoop x₀ P hQ), sub_zero]

/-! ## `Λ` in coordinates and the associated holomorphic 1-form -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- An ℝ-linear functional applied to a ℂ-scalar multiple, split into real
and imaginary contributions. -/
theorem linMap_apply_complex_smul
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ) (z : ℂ)
    (F : HolomorphicOneForm X →ₗ[ℂ] ℂ) :
    Λ (z • F) = z.re * Λ F + z.im * Λ (Complex.I • F) := by
  have hz : z • F = z.re • F + z.im • (Complex.I • F) := by
    calc z • F = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) • F := by
          rw [Complex.re_add_im]
      _ = (z.re : ℂ) • F + ((z.im : ℂ) * Complex.I) • F := add_smul _ _ _
      _ = z.re • F + z.im • (Complex.I • F) := by
          rw [mul_smul, ← Complex.coe_algebraMap, algebraMap_smul,
            algebraMap_smul]
  rw [hz, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- The complex coefficient vector attached to an ℝ-linear functional on the
dual of the holomorphic 1-forms, against a basis `bω`: `Λ` acts as
`F ↦ Re (∑ j, lamCoeff j * F (bω j))` (see `linMap_apply_eq_re_sum`). -/
def lamCoeff (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ) {n : ℕ}
    (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X)) (j : Fin n) : ℂ :=
  (Λ (bω.coord j) : ℂ) - Complex.I * (Λ (Complex.I • bω.coord j) : ℂ)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
theorem lamCoeff_mul_re (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ) {n : ℕ}
    (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X)) (j : Fin n) (z : ℂ) :
    (lamCoeff Λ bω j * z).re =
      z.re * Λ (bω.coord j) + z.im * Λ (Complex.I • bω.coord j) := by
  simp only [lamCoeff, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- **`Λ` in coordinates.** Every ℝ-linear functional on the dual of the
forms acts as the real part of a ℂ-linear pairing against `lamCoeff`. -/
theorem linMap_apply_eq_re_sum (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ)
    {n : ℕ} (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X))
    (F : HolomorphicOneForm X →ₗ[ℂ] ℂ) :
    Λ F = (∑ j, lamCoeff Λ bω j * F (bω j)).re := by
  conv_lhs => rw [← Module.Basis.sum_dual_apply_smul_coord bω F]
  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [linMap_apply_complex_smul, lamCoeff_mul_re]

/-- The holomorphic 1-form attached to `Λ`: `η = ∑ j, lamCoeff j • bω j`.
`Λ` vanishes identically iff `η = 0` (through `linMap_apply_eq_re_sum`). -/
def lamForm (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ) {n : ℕ}
    (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X)) :
    HolomorphicOneForm X :=
  ∑ j, lamCoeff Λ bω j • bω j

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The chart coefficient family of `lamForm` is the matching combination of
the basis coefficients. -/
theorem lamForm_coeff (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ) {n : ℕ}
    (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X)) (P : X) (z : ℂ) :
    (lamForm Λ bω).coeff P z = ∑ j, lamCoeff Λ bω j * (bω j).coeff P z := by
  classical
  have h : ((lamForm Λ bω : HolomorphicOneForm X) : X → ℂ → ℂ)
      = ∑ j, ((lamCoeff Λ bω j • bω j : HolomorphicOneForm X) : X → ℂ → ℂ) := by
    simp [lamForm]
  calc (lamForm Λ bω).coeff P z
      = ((lamForm Λ bω : HolomorphicOneForm X) : X → ℂ → ℂ) P z := rfl
    _ = (∑ j, ((lamCoeff Λ bω j • bω j : HolomorphicOneForm X) : X → ℂ → ℂ)) P z := by
        rw [h]
    _ = ∑ j, ((lamCoeff Λ bω j • bω j : HolomorphicOneForm X) : X → ℂ → ℂ) P z := by
        simp [Finset.sum_apply]
    _ = ∑ j, lamCoeff Λ bω j * (bω j).coeff P z := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rfl

/-! ## The local holomorphic potential -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- The chosen chart-target ball at `P` as a `PathChartBall` (the canonical
primitive carrier of `DevelopingMap`). -/
def potentialChartBall (P : X) : PathChartBall X where
  p := P
  c := (chartAt ℂ P) P
  r := chartTargetBallRadius P
  ball_subset_target := chartTargetBall_subset_extChartAt_target P

/-- The local holomorphic potential of `Λ` at `P`:
`H_P(z) = ∑ j, lamCoeff j * (primitive of (bω j).coeff P)(z)` on the chosen
chart ball. Its derivative is the coefficient of `lamForm` at `P`. -/
def localPotential (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ) {n : ℕ}
    (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X)) (P : X) : ℂ → ℂ :=
  fun z => ∑ j, lamCoeff Λ bω j *
    pathChartBallPrimitive (bω j) (potentialChartBall P) z

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- On the chart ball, the local potential is a primitive of the coefficient
of `lamForm` at `P`. -/
theorem localPotential_hasDerivAt
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ) {n : ℕ}
    (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X)) (P : X) {z : ℂ}
    (hz : z ∈ Metric.ball ((chartAt ℂ P) P) (chartTargetBallRadius P)) :
    HasDerivAt (localPotential Λ bω P) ((lamForm Λ bω).coeff P z) z := by
  rw [lamForm_coeff]
  exact HasDerivAt.fun_sum fun j _ =>
    (pathChartBallPrimitive_hasDerivAt (bω j) (potentialChartBall P) z hz).const_mul _

omit [CompactSpace X] in
/-- **Local formula for the potential.** Under the loop-period hypothesis,
across the chart ball at `P` the potential `u` is
`u(P) + Re H_P(chart Q) - Re H_P(chart P)`. -/
theorem potential_eq_localPotential (x₀ : X)
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ γ : AnalyticLoop X x₀, Λ (loopPeriodFunctional x₀ γ) = 0)
    {n : ℕ} (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X))
    (P : X) {Q : X} (hQ : Q ∈ chartBallSource P) :
    Λ (basepointPeriodFunctional x₀ Q) =
      Λ (basepointPeriodFunctional x₀ P)
        + ((localPotential Λ bω P) ((chartAt ℂ P) Q)).re
        - ((localPotential Λ bω P) ((chartAt ℂ P) P)).re := by
  rw [potential_increment x₀ Λ hΛ P hQ]
  have hseg : ∀ j, segmentPeriodFunctional P hQ (bω j)
      = pathChartBallPrimitive (bω j) (potentialChartBall P) ((chartAt ℂ P) Q)
        - pathChartBallPrimitive (bω j) (potentialChartBall P) ((chartAt ℂ P) P) := by
    intro j
    rw [segmentPeriodFunctional_apply]
    exact canonicalArcIntegral_chartSegmentArc P hQ (bω j)
      (pathChartBallPrimitive_hasDerivAt (bω j) (potentialChartBall P))
  rw [linMap_apply_eq_re_sum Λ bω (segmentPeriodFunctional P hQ)]
  have hsum : ∑ j, lamCoeff Λ bω j * segmentPeriodFunctional P hQ (bω j)
      = localPotential Λ bω P ((chartAt ℂ P) Q)
        - localPotential Λ bω P ((chartAt ℂ P) P) := by
    rw [localPotential, localPotential, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hseg j, mul_sub]
  rw [hsum, Complex.sub_re]
  ring

end

end Jacobians.RiemannSurface
