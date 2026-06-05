/-
Developing-map primitives for chart-local increments.
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Jacobians.RiemannSurface.HomotopyInvariance

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- B0: the coefficient of a holomorphic one-form has a primitive on any
coordinate ball contained in the fixed chart target. -/
theorem coeff_isExactOn_ball (form : HolomorphicOneForm X) (x₀ : X)
    {c : ℂ} {r : ℝ}
    (hball : Metric.ball c r ⊆ (extChartAt 𝓘(ℂ) x₀).target) :
    Complex.IsExactOn (form.coeff x₀) (Metric.ball c r) := by
  have hdiff : DifferentiableOn ℂ (form.coeff x₀) (Metric.ball c r) :=
    (form.2.1 x₀).differentiableOn.mono hball
  exact hdiff.isExactOn_ball

/-- B0, pointed form: choose the chart-local primitive with a prescribed value
at an arbitrary base coordinate. -/
theorem coeff_exists_primitive_on_ball_with_value
    (form : HolomorphicOneForm X) (x₀ : X) {c xbase y : ℂ} {r : ℝ}
    (hball : Metric.ball c r ⊆ (extChartAt 𝓘(ℂ) x₀).target) :
    ∃ g : ℂ → ℂ, g xbase = y ∧
      ∀ z ∈ Metric.ball c r, HasDerivAt g (form.coeff x₀ z) z :=
  (coeff_isExactOn_ball form x₀ hball).with_val_at xbase y

/-- B1: on a single chart and a ball carrying a primitive `g` of the coefficient,
the canonical arc integral is the endpoint difference of the primitive.

The chart-path regularity hypotheses are exactly the remaining FTC side
conditions used below: right derivatives on the open interval and interval
integrability of the fixed-chart integrand. Continuity of the primitive along
the path is derived from chart continuity and the derivative hypothesis on `g`. -/
theorem canonicalArcIntegral_eq_chartPrimitive_endpoint_sub
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) (x₀ : X)
    {c : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.extend t ∈ (extChartAt 𝓘(ℂ) x₀).source)
    (hpath_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (extChartAt 𝓘(ℂ) x₀) (γ.extend t) ∈ Metric.ball c r)
    (hprimitive : ∀ z ∈ Metric.ball c r, HasDerivAt g (form.coeff x₀ z) z)
    (hchart_hasDeriv_right : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u))
        (deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)) t)
        (Set.Ioi t) t)
    (hintegrable : IntervalIntegrable
      (fun t : ℝ =>
        form.coeff x₀ ((extChartAt 𝓘(ℂ) x₀) (γ.extend t)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)) t)
      MeasureTheory.volume (0 : ℝ) 1) :
    canonicalArcIntegral γ form =
      g ((extChartAt 𝓘(ℂ) x₀) (γ.extend 1)) -
        g ((extChartAt 𝓘(ℂ) x₀) (γ.extend 0)) := by
  let charted : ℝ → ℂ := fun u => (extChartAt 𝓘(ℂ) x₀) (γ.extend u)
  let fixedIntegrand : ℝ → ℂ := fun t => form.coeff x₀ (charted t) * deriv charted t
  have hfixed :
      canonicalArcIntegral γ form = ∫ t in (0 : ℝ)..1, fixedIntegrand t := by
    simpa [charted, fixedIntegrand] using
      canonicalArcIntegral_eq_fixedChart_integral γ form x₀ hsource
  have hFTC :
      (∫ t in (0 : ℝ)..1, fixedIntegrand t) =
        (fun t : ℝ => g (charted t)) 1 - (fun t : ℝ => g (charted t)) 0 := by
    have hcharted_cont : ContinuousOn charted (Set.Icc (0 : ℝ) 1) := by
      simpa [charted] using
        (continuousOn_extChartAt (I := 𝓘(ℂ)) x₀).comp γ.continuous'.continuousOn
          hsource
    have hprimitivePath_cont : ContinuousOn (fun t : ℝ => g (charted t))
        (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact (hprimitive (charted t) (by simpa [charted] using hpath_ball t ht)).continuousAt
        |>.comp_continuousWithinAt (hcharted_cont t ht)
    refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      (f := fun t : ℝ => g (charted t)) (f' := fixedIntegrand)
      (show (0 : ℝ) ≤ 1 by norm_num) ?_ ?_ ?_
    · exact hprimitivePath_cont
    · intro t ht
      have htcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have hprim : HasDerivAt g (form.coeff x₀ (charted t)) (charted t) :=
        hprimitive (charted t) (by simpa [charted] using hpath_ball t htcc)
      have hchart : HasDerivWithinAt charted (deriv charted t) (Set.Ioi t) t := by
        simpa [charted] using hchart_hasDeriv_right t ht
      have hcomp : HasDerivWithinAt (fun u : ℝ => g (charted u))
          (deriv charted t * form.coeff x₀ (charted t)) (Set.Ioi t) t := by
        simpa [Function.comp_def, smul_eq_mul] using
          hprim.scomp_hasDerivWithinAt (x := t) hchart
      simpa [fixedIntegrand, mul_comm] using hcomp
    · simpa [charted, fixedIntegrand] using hintegrable
  calc
    canonicalArcIntegral γ form = ∫ t in (0 : ℝ)..1, fixedIntegrand t := hfixed
    _ = (fun t : ℝ => g (charted t)) 1 - (fun t : ℝ => g (charted t)) 0 := hFTC
    _ = g ((extChartAt 𝓘(ℂ) x₀) (γ.extend 1)) -
        g ((extChartAt 𝓘(ℂ) x₀) (γ.extend 0)) := by
          rfl

/-- A chart together with a coordinate ball contained in its target. -/
structure PathChartBall (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  p : X
  c : ℂ
  r : ℝ
  ball_subset_target : Metric.ball c r ⊆ (extChartAt 𝓘(ℂ) p).target

/-- The parameters whose path values lie in a fixed chart source and whose
coordinates lie in the fixed coordinate ball. -/
def pathChartBallSet (γ : C(unitInterval, X)) (B : PathChartBall X) :
    Set unitInterval :=
  {u | γ u ∈ (chartAt ℂ B.p).source ∧
    (extChartAt 𝓘(ℂ) B.p) (γ u) ∈ Metric.ball B.c B.r}

lemma isOpen_pathChartBallSet (γ : C(unitInterval, X)) (B : PathChartBall X) :
    IsOpen (pathChartBallSet γ B) := by
  have hopenX : IsOpen ((chartAt ℂ B.p).source ∩
      (extChartAt 𝓘(ℂ) B.p) ⁻¹' Metric.ball B.c B.r) := by
    exact isOpen_extChartAt_preimage (I := 𝓘(ℂ)) B.p Metric.isOpen_ball
  simpa [pathChartBallSet, Set.preimage_inter] using hopenX.preimage γ.continuous

lemma pathChartBallSet_cover (γ : C(unitInterval, X)) :
    Set.univ ⊆ ⋃ B : PathChartBall X, pathChartBallSet γ B := by
  intro u _hu
  let p : X := γ u
  let z : ℂ := (extChartAt 𝓘(ℂ) p) p
  have hz_target : z ∈ (extChartAt 𝓘(ℂ) p).target := by
    simp [z, p]
  obtain ⟨r, hr_pos, hr_sub⟩ :=
    (Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := 𝓘(ℂ)) p)) z hz_target
  let B : PathChartBall X :=
    { p := p, c := z, r := r, ball_subset_target := hr_sub }
  refine Set.mem_iUnion.2 ⟨B, ?_⟩
  constructor
  · simp [B, p]
  · exact (show (extChartAt 𝓘(ℂ) B.p) (γ u) ∈ Metric.ball B.c B.r by
      simpa [B, p, z] using (Metric.mem_ball_self (x := z) hr_pos))

/-- A finite subdivision of a continuous path by chart-coordinate balls. -/
structure PathChartBallSubdivision (γ : C(unitInterval, X)) where
  n : ℕ
  t : Fin (n + 1) → unitInterval
  cellBall : Fin n → PathChartBall X
  zero_eq : t 0 = 0
  one_eq : t (Fin.last n) = 1
  monotone_t : Monotone t
  cell_subset :
    ∀ i : Fin n, Set.Icc (t i.castSucc) (t i.succ) ⊆
      pathChartBallSet γ (cellBall i)

namespace PathChartBallSubdivision

lemma left_mem_pathChartBallSet {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) (i : Fin S.n) :
    S.t i.castSucc ∈ pathChartBallSet γ (S.cellBall i) := by
  exact S.cell_subset i ⟨le_rfl, S.monotone_t (Fin.castSucc_le_succ i)⟩

lemma right_mem_pathChartBallSet {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) (i : Fin S.n) :
    S.t i.succ ∈ pathChartBallSet γ (S.cellBall i) := by
  exact S.cell_subset i ⟨S.monotone_t (Fin.castSucc_le_succ i), le_rfl⟩

lemma left_coord_mem_ball {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) (i : Fin S.n) :
    (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ (S.t i.castSucc)) ∈
      Metric.ball (S.cellBall i).c (S.cellBall i).r :=
  (S.left_mem_pathChartBallSet i).2

lemma right_coord_mem_ball {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) (i : Fin S.n) :
    (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ (S.t i.succ)) ∈
      Metric.ball (S.cellBall i).c (S.cellBall i).r :=
  (S.right_mem_pathChartBallSet i).2

end PathChartBallSubdivision

lemma exists_pathChartBallSubdivision (γ : C(unitInterval, X)) :
    Nonempty (PathChartBallSubdivision γ) := by
  classical
  obtain ⟨t, ht_zero, ht_mono, ⟨k, ht_eventually_one⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := pathChartBallSet γ) (isOpen_pathChartBallSet γ) (pathChartBallSet_cover γ)
  let N : ℕ := k + 1
  let cellBall : Fin N → PathChartBall X := fun i => Classical.choose (ht_sub i.val)
  refine ⟨⟨N, (fun i : Fin (N + 1) => t i.val), cellBall, ?_, ?_, ?_, ?_⟩⟩
  · simpa using ht_zero
  · have hlast : t N = 1 := ht_eventually_one N (Nat.le_succ k)
    simpa [N, Fin.val_last] using hlast
  · intro i j hij
    exact ht_mono (Fin.val_le_of_le hij)
  · intro i u hu
    have hsub := Classical.choose_spec (ht_sub i.val)
    have hu' : u ∈ Set.Icc (t i.val) (t (i.val + 1)) := by
      constructor
      · simpa [Fin.val_castSucc] using hu.1
      · simpa [Fin.val_succ] using hu.2
    exact hsub hu'

noncomputable def chosenPathChartBallSubdivision (γ : C(unitInterval, X)) :
    PathChartBallSubdivision γ :=
  Classical.choice (exists_pathChartBallSubdivision γ)

noncomputable def pathChartBallPrimitive (form : HolomorphicOneForm X)
    (B : PathChartBall X) : ℂ → ℂ :=
  Classical.choose (coeff_exists_primitive_on_ball_with_value form B.p
    (xbase := B.c) (y := 0) B.ball_subset_target)

lemma pathChartBallPrimitive_value (form : HolomorphicOneForm X) (B : PathChartBall X) :
    pathChartBallPrimitive form B B.c = 0 := by
  exact (Classical.choose_spec (coeff_exists_primitive_on_ball_with_value form B.p
    (xbase := B.c) (y := 0) B.ball_subset_target)).1

lemma pathChartBallPrimitive_hasDerivAt (form : HolomorphicOneForm X)
    (B : PathChartBall X) :
    ∀ z ∈ Metric.ball B.c B.r,
      HasDerivAt (pathChartBallPrimitive form B) (form.coeff B.p z) z := by
  exact (Classical.choose_spec (coeff_exists_primitive_on_ball_with_value form B.p
    (xbase := B.c) (y := 0) B.ball_subset_target)).2

/-- The endpoint-difference increment for one chart-ball cell of a continuous
path subdivision. -/
noncomputable def developingIncrement (form : HolomorphicOneForm X)
    (γ : C(unitInterval, X)) (S : PathChartBallSubdivision γ) (i : Fin S.n) : ℂ :=
  let B := S.cellBall i
  let g := pathChartBallPrimitive form B
  g ((extChartAt 𝓘(ℂ) B.p) (γ (S.t i.succ))) -
    g ((extChartAt 𝓘(ℂ) B.p) (γ (S.t i.castSucc)))

/-- The developing value associated to one chosen chart-ball subdivision. -/
noncomputable def developingValueOfSubdivision (form : HolomorphicOneForm X)
    (γ : C(unitInterval, X)) (S : PathChartBallSubdivision γ) : ℂ :=
  ∑ i : Fin S.n, developingIncrement form γ S i

/-- B2 definition layer: a choice-based developing value for an arbitrary
continuous path, computed by summing chart-local primitive endpoint
differences on a chart-ball subdivision. -/
noncomputable def developingValue (x₀ : X) (form : HolomorphicOneForm X)
    (γ : C(unitInterval, X)) : ℂ :=
  (fun _ : X =>
    developingValueOfSubdivision form γ (chosenPathChartBallSubdivision γ)) x₀

/-- The continuous-map view of an analytic arc on the unit interval. -/
def analyticArcToContinuousMap (γ : AnalyticArc X) : C(unitInterval, X) where
  toFun := γ.toFun
  continuous_toFun := γ.continuous_toFun

@[simp]
theorem analyticArcToContinuousMap_apply (γ : AnalyticArc X) (t : unitInterval) :
    analyticArcToContinuousMap γ t = γ.extend (t : ℝ) :=
  rfl

@[simp]
theorem analyticArcToContinuousMap_zero (γ : AnalyticArc X) :
    analyticArcToContinuousMap γ 0 = γ.extend 0 :=
  rfl

@[simp]
theorem analyticArcToContinuousMap_one (γ : AnalyticArc X) :
    analyticArcToContinuousMap γ 1 = γ.extend 1 :=
  rfl

/-- Refining a single primitive endpoint difference by an intermediate point
telescopes algebraically. This is the local algebra used in the refinement
part of B2 well-definedness. -/
theorem chartPrimitive_endpoint_sub_split (g : ℂ → ℂ) (a m b : ℂ) :
    g b - g a = (g m - g a) + (g b - g m) := by
  abel

/-- Splitting a chart-ball primitive increment at an intermediate coordinate
point is just the endpoint-difference telescoping identity. -/
theorem pathChartBallPrimitive_endpoint_sub_split
    (form : HolomorphicOneForm X) (B : PathChartBall X) (a m b : ℂ) :
    pathChartBallPrimitive form B b - pathChartBallPrimitive form B a =
      (pathChartBallPrimitive form B m - pathChartBallPrimitive form B a) +
        (pathChartBallPrimitive form B b - pathChartBallPrimitive form B m) := by
  exact chartPrimitive_endpoint_sub_split (pathChartBallPrimitive form B) a m b

/-- If two chart balls use the same chart center, their chosen primitives differ
by a constant on the intersection of the coordinate balls. Consequently their
endpoint differences agree on that intersection. -/
theorem pathChartBallPrimitive_endpoint_sub_eq_of_same_center
    (form : HolomorphicOneForm X) {B₁ B₂ : PathChartBall X}
    (hp : B₁.p = B₂.p) {a b : ℂ}
    (ha₁ : a ∈ Metric.ball B₁.c B₁.r) (hb₁ : b ∈ Metric.ball B₁.c B₁.r)
    (ha₂ : a ∈ Metric.ball B₂.c B₂.r) (hb₂ : b ∈ Metric.ball B₂.c B₂.r) :
    pathChartBallPrimitive form B₁ b - pathChartBallPrimitive form B₁ a =
      pathChartBallPrimitive form B₂ b - pathChartBallPrimitive form B₂ a := by
  classical
  let s : Set ℂ := Metric.ball B₁.c B₁.r ∩ Metric.ball B₂.c B₂.r
  have hs_open : IsOpen s := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hs_preconnected : IsPreconnected s :=
    ((convex_ball B₁.c B₁.r).inter (convex_ball B₂.c B₂.r)).isPreconnected
  have hdiff₁ : DifferentiableOn ℂ (pathChartBallPrimitive form B₁) s := by
    intro z hz
    exact ((pathChartBallPrimitive_hasDerivAt form B₁) z hz.1).differentiableAt
      |>.differentiableWithinAt
  have hdiff₂ : DifferentiableOn ℂ (pathChartBallPrimitive form B₂) s := by
    intro z hz
    exact ((pathChartBallPrimitive_hasDerivAt form B₂) z hz.2).differentiableAt
      |>.differentiableWithinAt
  have hderiv_eq : s.EqOn (deriv (pathChartBallPrimitive form B₁))
      (deriv (pathChartBallPrimitive form B₂)) := by
    intro z hz
    have h₁ := ((pathChartBallPrimitive_hasDerivAt form B₁) z hz.1).deriv
    have h₂ := ((pathChartBallPrimitive_hasDerivAt form B₂) z hz.2).deriv
    calc
      deriv (pathChartBallPrimitive form B₁) z = form.coeff B₁.p z := h₁
      _ = form.coeff B₂.p z := by rw [hp]
      _ = deriv (pathChartBallPrimitive form B₂) z := h₂.symm
  obtain ⟨C, hC⟩ :=
    hs_open.exists_eq_add_of_deriv_eq hs_preconnected hdiff₁ hdiff₂ hderiv_eq
  have ha : a ∈ s := ⟨ha₁, ha₂⟩
  have hb : b ∈ s := ⟨hb₁, hb₂⟩
  have hCa := hC ha
  have hCb := hC hb
  calc
    pathChartBallPrimitive form B₁ b - pathChartBallPrimitive form B₁ a =
        (pathChartBallPrimitive form B₂ b + C) -
          (pathChartBallPrimitive form B₂ a + C) := by
            rw [hCb, hCa]
    _ = pathChartBallPrimitive form B₂ b - pathChartBallPrimitive form B₂ a := by
      abel

/-- Chart-transition form of the overlap-constant lemma.  On any open
preconnected coordinate overlap `U` in the first chart whose transition image
lies in the second chart ball, the primitive in the first chart and the
primitive in the second chart pulled back by the transition differ by a
constant. Hence their endpoint differences agree. -/
theorem pathChartBallPrimitive_endpoint_sub_eq_on_preconnected_overlap
    (form : HolomorphicOneForm X) (B₁ B₂ : PathChartBall X) {U : Set ℂ}
    (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hU_ball₁ : U ⊆ Metric.ball B₁.c B₁.r)
    (hU_ball₂ : ∀ z ∈ U,
      (extChartAt 𝓘(ℂ) B₁.p).symm z ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm z) ∈
          Metric.ball B₂.c B₂.r)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    pathChartBallPrimitive form B₁ b - pathChartBallPrimitive form B₁ a =
      pathChartBallPrimitive form B₂
          ((extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm b)) -
        pathChartBallPrimitive form B₂
          ((extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm a)) := by
  classical
  let T : ℂ → ℂ := (extChartAt 𝓘(ℂ) B₂.p) ∘ (extChartAt 𝓘(ℂ) B₁.p).symm
  let F₁ : ℂ → ℂ := pathChartBallPrimitive form B₁
  let F₂ : ℂ → ℂ := fun z => pathChartBallPrimitive form B₂ (T z)
  have hdiff₁ : DifferentiableOn ℂ F₁ U := by
    intro z hz
    exact ((pathChartBallPrimitive_hasDerivAt form B₁) z (hU_ball₁ hz)).differentiableAt
      |>.differentiableWithinAt
  have hdiff₂ : DifferentiableOn ℂ F₂ U := by
    intro z hz
    let d : ℂ := fderiv ℂ T z 1
    have hz_target : z ∈ (extChartAt 𝓘(ℂ) B₁.p).target :=
      B₁.ball_subset_target (hU_ball₁ hz)
    have hTdiff : DifferentiableAt ℂ T z :=
      chartTransition_differentiableAt (p := B₁.p) (q := B₂.p) hz_target
        (hU_ball₂ z hz).1
    have hTderiv : HasDerivAt T d z := by
      simpa [d] using hTdiff.hasDerivAt
    have hprim₂ : HasDerivAt (pathChartBallPrimitive form B₂)
        (form.coeff B₂.p (T z)) (T z) := by
      simpa [T] using
        (pathChartBallPrimitive_hasDerivAt form B₂)
          ((extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm z))
          (hU_ball₂ z hz).2
    exact (hprim₂.comp z hTderiv).differentiableAt.differentiableWithinAt
  have hderiv_eq : U.EqOn (deriv F₁) (deriv F₂) := by
    intro z hz
    let d : ℂ := fderiv ℂ T z 1
    have hz_target : z ∈ (extChartAt 𝓘(ℂ) B₁.p).target :=
      B₁.ball_subset_target (hU_ball₁ hz)
    have hTdiff : DifferentiableAt ℂ T z :=
      chartTransition_differentiableAt (p := B₁.p) (q := B₂.p) hz_target
        (hU_ball₂ z hz).1
    have hTderiv : HasDerivAt T d z := by
      simpa [d] using hTdiff.hasDerivAt
    have hprim₁ : HasDerivAt F₁ (form.coeff B₁.p z) z := by
      simpa [F₁] using (pathChartBallPrimitive_hasDerivAt form B₁) z (hU_ball₁ hz)
    have hprim₂ : HasDerivAt (pathChartBallPrimitive form B₂)
        (form.coeff B₂.p (T z)) (T z) := by
      simpa [T] using
        (pathChartBallPrimitive_hasDerivAt form B₂)
          ((extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm z))
          (hU_ball₂ z hz).2
    have hcomp : HasDerivAt F₂ (form.coeff B₂.p (T z) * d) z := by
      simpa [F₂] using hprim₂.comp z hTderiv
    have hcocycle : form.coeff B₁.p z = form.coeff B₂.p (T z) * d := by
      have hc := form.2.2.1 B₁.p B₂.p z hz_target (hU_ball₂ z hz).1
      simpa [T, d, Function.comp_def] using hc
    calc
      deriv F₁ z = form.coeff B₁.p z := hprim₁.deriv
      _ = form.coeff B₂.p (T z) * d := hcocycle
      _ = deriv F₂ z := hcomp.deriv.symm
  obtain ⟨C, hC⟩ :=
    hU_open.exists_eq_add_of_deriv_eq hU_preconnected hdiff₁ hdiff₂ hderiv_eq
  have hCa := hC ha
  have hCb := hC hb
  calc
    pathChartBallPrimitive form B₁ b - pathChartBallPrimitive form B₁ a =
        F₁ b - F₁ a := rfl
    _ = (F₂ b + C) - (F₂ a + C) := by rw [hCb, hCa]
    _ = F₂ b - F₂ a := by abel
    _ =
        pathChartBallPrimitive form B₂
            ((extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm b)) -
          pathChartBallPrimitive form B₂
            ((extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm a)) := by
        rfl

/-- Endpoint-difference equality on a path segment when both endpoint
coordinates in the first chart lie in one open preconnected overlap component
whose transition image is contained in the second chart ball. -/
theorem pathChartBallPrimitive_endpoint_sub_eq_at_path_points
    (form : HolomorphicOneForm X) (γ : C(unitInterval, X)) (B₁ B₂ : PathChartBall X)
    {U : Set ℂ}
    (hU_open : IsOpen U) (hU_preconnected : IsPreconnected U)
    (hU_ball₁ : U ⊆ Metric.ball B₁.c B₁.r)
    (hU_ball₂ : ∀ z ∈ U,
      (extChartAt 𝓘(ℂ) B₁.p).symm z ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm z) ∈
          Metric.ball B₂.c B₂.r)
    {u v : unitInterval}
    (hu₁ : u ∈ pathChartBallSet γ B₁) (hv₁ : v ∈ pathChartBallSet γ B₁)
    (huU : (extChartAt 𝓘(ℂ) B₁.p) (γ u) ∈ U)
    (hvU : (extChartAt 𝓘(ℂ) B₁.p) (γ v) ∈ U) :
    pathChartBallPrimitive form B₁ ((extChartAt 𝓘(ℂ) B₁.p) (γ v)) -
        pathChartBallPrimitive form B₁ ((extChartAt 𝓘(ℂ) B₁.p) (γ u)) =
      pathChartBallPrimitive form B₂ ((extChartAt 𝓘(ℂ) B₂.p) (γ v)) -
        pathChartBallPrimitive form B₂ ((extChartAt 𝓘(ℂ) B₂.p) (γ u)) := by
  have hbase :=
    pathChartBallPrimitive_endpoint_sub_eq_on_preconnected_overlap
      (form := form) (B₁ := B₁) (B₂ := B₂)
      hU_open hU_preconnected hU_ball₁ hU_ball₂ huU hvU
  have hu_source : γ u ∈ (extChartAt 𝓘(ℂ) B₁.p).source := by
    simpa [extChartAt_source] using hu₁.1
  have hv_source : γ v ∈ (extChartAt 𝓘(ℂ) B₁.p).source := by
    simpa [extChartAt_source] using hv₁.1
  have hu_transition :
      (extChartAt 𝓘(ℂ) B₂.p)
          ((extChartAt 𝓘(ℂ) B₁.p).symm ((extChartAt 𝓘(ℂ) B₁.p) (γ u))) =
        (extChartAt 𝓘(ℂ) B₂.p) (γ u) := by
    rw [(extChartAt 𝓘(ℂ) B₁.p).left_inv hu_source]
  have hv_transition :
      (extChartAt 𝓘(ℂ) B₂.p)
          ((extChartAt 𝓘(ℂ) B₁.p).symm ((extChartAt 𝓘(ℂ) B₁.p) (γ v))) =
        (extChartAt 𝓘(ℂ) B₂.p) (γ v) := by
    rw [(extChartAt 𝓘(ℂ) B₁.p).left_inv hv_source]
  rw [hu_transition, hv_transition] at hbase
  exact hbase

end Jacobians.RiemannSurface
