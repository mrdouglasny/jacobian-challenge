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

/-! ## The maximum principle (open-mapping dichotomy) -/

/-- If an analytic function has a local maximum of its real part, it is
eventually constant (open-mapping dichotomy: otherwise the image of any
neighbourhood is a neighbourhood of the value, which contains points of
strictly larger real part). -/
theorem eventually_const_of_re_isLocalMax {H : ℂ → ℂ} {z₀ : ℂ}
    (hH : AnalyticAt ℂ H z₀)
    (hle : ∀ᶠ z in 𝓝 z₀, (H z).re ≤ (H z₀).re) :
    ∀ᶠ z in 𝓝 z₀, H z = H z₀ := by
  rcases hH.eventually_constant_or_nhds_le_map_nhds with h | h
  · exact h
  · exfalso
    have hmem : {w : ℂ | w.re ≤ (H z₀).re} ∈ Filter.map H (𝓝 z₀) :=
      Filter.mem_map.mpr hle
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (h hmem)
    have hw : H z₀ + ((ε / 2 : ℝ) : ℂ) ∈ Metric.ball (H z₀) ε := by
      rw [Metric.mem_ball, dist_comm, Complex.dist_eq]
      have : H z₀ - (H z₀ + ((ε / 2 : ℝ) : ℂ)) = -((ε / 2 : ℝ) : ℂ) := by ring
      rw [this]
      simpa using (by rw [abs_of_pos hε]; linarith : |ε| / 2 < ε)
    have hre := hball hw
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re] at hre
    linarith

/-! ## Continuity and constancy of the potential -/

/-- Under the loop-period hypothesis the potential
`u(Q) = Λ (basepointPeriodFunctional x₀ Q)` is continuous. -/
theorem continuous_potential (x₀ : X)
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ γ : AnalyticLoop X x₀, Λ (loopPeriodFunctional x₀ γ) = 0) :
    Continuous fun Q : X => Λ (basepointPeriodFunctional x₀ Q) := by
  classical
  rw [continuous_iff_continuousAt]
  intro P
  set bω := Module.finBasis ℂ (HolomorphicOneForm X) with hbω
  have hmodel : ContinuousAt (fun Q : X =>
      Λ (basepointPeriodFunctional x₀ P)
        + ((localPotential Λ bω P) ((chartAt ℂ P) Q)).re
        - ((localPotential Λ bω P) ((chartAt ℂ P) P)).re) P := by
    have hchart : ContinuousAt (fun Q : X => (chartAt ℂ P) Q) P :=
      (chartAt ℂ P).continuousAt (mem_chart_source ℂ P)
    have hH : ContinuousAt (localPotential Λ bω P) ((chartAt ℂ P) P) :=
      (localPotential_hasDerivAt Λ bω P
        (Metric.mem_ball_self (chartTargetBallRadius_pos P))).continuousAt
    exact (continuousAt_const.add
      (Complex.continuous_re.continuousAt.comp (hH.comp hchart))).sub
      continuousAt_const
  refine hmodel.congr ?_
  filter_upwards [(isOpen_chartBallSource P).mem_nhds (mem_chartBallSource_self P)]
    with Q hQ
  exact (potential_eq_localPotential x₀ Λ hΛ bω P hQ).symm

/-- **Constancy of the potential** (maximum principle + clopen argument on
the compact connected surface). -/
theorem potential_constant (x₀ : X)
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ γ : AnalyticLoop X x₀, Λ (loopPeriodFunctional x₀ γ) = 0)
    (Q Q' : X) :
    Λ (basepointPeriodFunctional x₀ Q) = Λ (basepointPeriodFunctional x₀ Q') := by
  classical
  haveI : Nonempty X := ⟨x₀⟩
  set bω := Module.finBasis ℂ (HolomorphicOneForm X) with hbω
  set u : X → ℝ := fun R => Λ (basepointPeriodFunctional x₀ R) with hu
  have hu_cont : Continuous u := continuous_potential x₀ Λ hΛ
  obtain ⟨Pm, -, hPm⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hu_cont.continuousOn
  set S : Set X := {x | u x = u Pm} with hS
  have hS_closed : IsClosed S := isClosed_eq hu_cont continuous_const
  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro P hP
    have hPval : u P = u Pm := hP
    set H := localPotential Λ bω P with hH
    set z₀ := (chartAt ℂ P) P with hz₀
    have hrad := chartTargetBallRadius_pos P
    -- the real part of the local potential has a max at the chart center
    have hre_le : ∀ z ∈ Metric.ball z₀ (chartTargetBallRadius P),
        (H z).re ≤ (H z₀).re := by
      intro z hz
      have hz_target : z ∈ (chartAt ℂ P).target :=
        chartTargetBall_subset_chart_target P hz
      have hQ1_mem : (chartAt ℂ P).symm z ∈ chartBallSource P := by
        refine ⟨(chartAt ℂ P).map_target hz_target, ?_⟩
        show (chartAt ℂ P) ((chartAt ℂ P).symm z) ∈ Metric.ball z₀ _
        rw [(chartAt ℂ P).right_inv hz_target]
        exact hz
      have hformula := potential_eq_localPotential x₀ Λ hΛ bω P hQ1_mem
      rw [(chartAt ℂ P).right_inv hz_target] at hformula
      have hle : u ((chartAt ℂ P).symm z) ≤ u Pm := hPm (Set.mem_univ _)
      have hformula' : u ((chartAt ℂ P).symm z) = u P + (H z).re - (H z₀).re :=
        hformula
      rw [hformula', hPval] at hle
      linarith
    have hH_an : AnalyticAt ℂ H z₀ := by
      have hdiff : DifferentiableOn ℂ H
          (Metric.ball z₀ (chartTargetBallRadius P)) := fun z hz =>
        (localPotential_hasDerivAt Λ bω P hz).differentiableAt.differentiableWithinAt
      exact hdiff.analyticAt (Metric.ball_mem_nhds z₀ hrad)
    have hconst := eventually_const_of_re_isLocalMax hH_an
      (by filter_upwards [Metric.ball_mem_nhds z₀ hrad] with z hz
          exact hre_le z hz)
    -- pull the local constancy back to the surface
    have hchart : ContinuousAt (fun R : X => (chartAt ℂ P) R) P :=
      (chartAt ℂ P).continuousAt (mem_chart_source ℂ P)
    filter_upwards [hchart.tendsto.eventually hconst,
      (isOpen_chartBallSource P).mem_nhds (mem_chartBallSource_self P)]
      with R hR_const hR_mem
    have hformula := potential_eq_localPotential x₀ Λ hΛ bω P hR_mem
    show u R = u Pm
    have hR_const' : localPotential Λ bω P ((chartAt ℂ P) R)
        = localPotential Λ bω P ((chartAt ℂ P) P) := hR_const
    have huP : Λ (basepointPeriodFunctional x₀ P) = u P := rfl
    rw [show u R = Λ (basepointPeriodFunctional x₀ R) from rfl, hformula,
      hR_const', huP, hPval]
    ring
  have hS_univ : S = Set.univ :=
    IsClopen.eq_univ ⟨hS_closed, hS_open⟩ ⟨Pm, rfl⟩
  have hQ : Q ∈ S := hS_univ ▸ Set.mem_univ Q
  have hQ' : Q' ∈ S := hS_univ ▸ Set.mem_univ Q'
  exact (show u Q = u Pm from hQ).trans (show u Q' = u Pm from hQ').symm

/-! ## The form attached to `Λ` vanishes -/

/-- At every point, the coefficient of `lamForm` vanishes at the chart
center: the potential is constant, so the local potential has constant real
part on the chart ball, hence is eventually constant (dichotomy), hence has
vanishing derivative at the center. -/
theorem lamForm_coeff_center_eq_zero (x₀ : X)
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ γ : AnalyticLoop X x₀, Λ (loopPeriodFunctional x₀ γ) = 0)
    {n : ℕ} (bω : Module.Basis (Fin n) ℂ (HolomorphicOneForm X)) (P : X) :
    (lamForm Λ bω).coeff P ((chartAt ℂ P) P) = 0 := by
  classical
  set H := localPotential Λ bω P with hH
  set z₀ := (chartAt ℂ P) P with hz₀
  have hrad := chartTargetBallRadius_pos P
  have hre_const : ∀ z ∈ Metric.ball z₀ (chartTargetBallRadius P),
      (H z).re = (H z₀).re := by
    intro z hz
    have hz_target : z ∈ (chartAt ℂ P).target :=
      chartTargetBall_subset_chart_target P hz
    have hQ1_mem : (chartAt ℂ P).symm z ∈ chartBallSource P := by
      refine ⟨(chartAt ℂ P).map_target hz_target, ?_⟩
      show (chartAt ℂ P) ((chartAt ℂ P).symm z) ∈ Metric.ball z₀ _
      rw [(chartAt ℂ P).right_inv hz_target]
      exact hz
    have hformula := potential_eq_localPotential x₀ Λ hΛ bω P hQ1_mem
    rw [(chartAt ℂ P).right_inv hz_target] at hformula
    have hconst := potential_constant x₀ Λ hΛ ((chartAt ℂ P).symm z) P
    rw [hconst] at hformula
    linarith
  have hH_an : AnalyticAt ℂ H z₀ := by
    have hdiff : DifferentiableOn ℂ H
        (Metric.ball z₀ (chartTargetBallRadius P)) := fun z hz =>
      (localPotential_hasDerivAt Λ bω P hz).differentiableAt.differentiableWithinAt
    exact hdiff.analyticAt (Metric.ball_mem_nhds z₀ hrad)
  have hconst := eventually_const_of_re_isLocalMax hH_an
    (by filter_upwards [Metric.ball_mem_nhds z₀ hrad] with z hz
        exact (hre_const z hz).le)
  have hderiv0 : deriv H z₀ = 0 := by
    rw [Filter.EventuallyEq.deriv_eq hconst]
    exact deriv_const z₀ _
  have hHd : HasDerivAt H ((lamForm Λ bω).coeff P z₀) z₀ :=
    localPotential_hasDerivAt Λ bω P (Metric.mem_ball_self hrad)
  rw [← hHd.deriv]
  exact hderiv0

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- A holomorphic 1-form whose coefficient vanishes at every chart center is
zero: off-target the coefficient is zero by normalization, and on-target the
cocycle expresses it through the coefficient of the back-image point *at its
own chart center*. No identity theorem is needed. -/
theorem HolomorphicOneForm.eq_zero_of_coeff_center_eq_zero
    (form : HolomorphicOneForm X)
    (h : ∀ y : X, form.coeff y ((extChartAt 𝓘(ℂ) y) y) = 0) :
    form = 0 := by
  apply HolomorphicOneForm.ext_of_coeff
  funext x z
  rw [HolomorphicOneForm.coeff_zero]
  show (form : X → ℂ → ℂ) x z = 0
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ) x).target
  · have hmem : (extChartAt 𝓘(ℂ) x).symm z ∈
        (extChartAt 𝓘(ℂ) ((extChartAt 𝓘(ℂ) x).symm z)).source :=
      mem_extChartAt_source _
    have hco := form.2.2.1 x ((extChartAt 𝓘(ℂ) x).symm z) z hz hmem
    have h0 : (form : X → ℂ → ℂ) ((extChartAt 𝓘(ℂ) x).symm z)
        ((extChartAt 𝓘(ℂ) ((extChartAt 𝓘(ℂ) x).symm z))
          ((extChartAt 𝓘(ℂ) x).symm z)) = 0 :=
      h ((extChartAt 𝓘(ℂ) x).symm z)
    rw [hco, h0, zero_mul]
  · exact form.2.2.2 x z hz

/-! ## Headlines -/

/-- **B-3 engine (Forster §21.4, dissection-free): period non-degeneracy.**
No nonzero ℝ-linear functional on `HolomorphicOneForm X →ₗ[ℂ] ℂ` kills the
period functionals of all closed analytic loops based at `x₀`. -/
theorem eq_zero_of_forall_loopPeriodFunctional_eq_zero (x₀ : X)
    (Λ : (HolomorphicOneForm X →ₗ[ℂ] ℂ) →ₗ[ℝ] ℝ)
    (hΛ : ∀ γ : AnalyticLoop X x₀, Λ (loopPeriodFunctional x₀ γ) = 0) :
    Λ = 0 := by
  classical
  set bω := Module.finBasis ℂ (HolomorphicOneForm X) with hbω
  have hform : lamForm Λ bω = 0 := by
    refine HolomorphicOneForm.eq_zero_of_coeff_center_eq_zero _ fun y => ?_
    exact lamForm_coeff_center_eq_zero x₀ Λ hΛ bω y
  have hc : ∀ j, lamCoeff Λ bω j = 0 := by
    have h1 := bω.repr_sum_self fun j => lamCoeff Λ bω j
    rw [show ∑ j, lamCoeff Λ bω j • bω j = lamForm Λ bω from rfl, hform] at h1
    intro j
    have h2 := congrFun h1.symm j
    simpa using h2
  refine LinearMap.ext fun F => ?_
  rw [LinearMap.zero_apply, linMap_apply_eq_re_sum Λ bω F]
  simp [hc]

/-- **B-3 headline: the ℝ-span of the loop period functionals is
everything** — the "no nonzero functional kills all periods" statement in
span form (Forster §21.4). -/
theorem span_loopPeriodFunctional_eq_top (x₀ : X) :
    Submodule.span ℝ (Set.range (loopPeriodFunctional x₀)) = ⊤ := by
  classical
  by_contra hne
  set p : Submodule ℝ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
    Submodule.span ℝ (Set.range (loopPeriodFunctional x₀)) with hp
  obtain ⟨F, -, hF⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  have hquot : p.mkQ F ≠ 0 := by
    rw [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hF
  haveI : Module.Free ℝ ((HolomorphicOneForm X →ₗ[ℂ] ℂ) ⧸ p) :=
    Module.Free.of_divisionRing ℝ _
  haveI : Module.Projective ℝ ((HolomorphicOneForm X →ₗ[ℂ] ℂ) ⧸ p) :=
    Module.Projective.of_free
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℝ
      ((HolomorphicOneForm X →ₗ[ℂ] ℂ) ⧸ p), φ (p.mkQ F) ≠ 0 := by
    by_contra hall
    have hall' : ∀ φ : Module.Dual ℝ
        ((HolomorphicOneForm X →ₗ[ℂ] ℂ) ⧸ p), φ (p.mkQ F) = 0 := fun φ => by
      by_contra hφ0
      exact hall ⟨φ, hφ0⟩
    exact hquot ((Module.forall_dual_apply_eq_zero_iff ℝ (p.mkQ F)).mp hall')
  have h0 : φ.comp p.mkQ = 0 := by
    refine eq_zero_of_forall_loopPeriodFunctional_eq_zero x₀ (φ.comp p.mkQ)
      fun γ => ?_
    have hmem : loopPeriodFunctional x₀ γ ∈ p :=
      Submodule.subset_span ⟨γ, rfl⟩
    simp [LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero p).mpr hmem]
  exact hφ (by simpa using LinearMap.congr_fun h0 F)

end

end Jacobians.RiemannSurface
