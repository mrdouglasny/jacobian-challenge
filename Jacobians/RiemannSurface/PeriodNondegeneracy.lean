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

end

end Jacobians.RiemannSurface
