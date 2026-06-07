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

private lemma pathChartBallOverlap_isOpen (B₁ B₂ : PathChartBall X) : IsOpen
    ({z : ℂ | z ∈ Metric.ball B₁.c B₁.r ∧
      (extChartAt 𝓘(ℂ) B₁.p).symm z ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm z) ∈
          Metric.ball B₂.c B₂.r}) := by
  classical
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  rcases hz with ⟨hz_ball₁, hz_source₂, hz_ball₂⟩
  let V : Set X := (extChartAt 𝓘(ℂ) B₂.p).source ∩
      (extChartAt 𝓘(ℂ) B₂.p) ⁻¹' Metric.ball B₂.c B₂.r
  have hV_open : IsOpen V := by
    simpa [V, extChartAt_source] using
      (isOpen_extChartAt_preimage (I := 𝓘(ℂ)) B₂.p Metric.isOpen_ball)
  have hz_target₁ : z ∈ (extChartAt 𝓘(ℂ) B₁.p).target :=
    B₁.ball_subset_target hz_ball₁
  have hzV : (extChartAt 𝓘(ℂ) B₁.p).symm z ∈ V := ⟨hz_source₂, hz_ball₂⟩
  have hpre_nhds : (extChartAt 𝓘(ℂ) B₁.p).symm ⁻¹' V ∈ 𝓝 z := by
    exact (continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hz_target₁).preimage_mem_nhds
      (hV_open.mem_nhds hzV)
  obtain ⟨W, hW_sub, hW_open, hzW⟩ := mem_nhds_iff.mp hpre_nhds
  refine ⟨Metric.ball B₁.c B₁.r ∩ W, ?_, Metric.isOpen_ball.inter hW_open,
    ⟨hz_ball₁, hzW⟩⟩
  intro y hy
  rcases hy with ⟨hy_ball, hyW⟩
  have hyV : (extChartAt 𝓘(ℂ) B₁.p).symm y ∈ V := hW_sub hyW
  exact ⟨hy_ball, hyV.1, hyV.2⟩

/-- Endpoint-difference equality for two chart balls on a path segment lying in
both chart-ball sets.  The open preconnected overlap required by
`pathChartBallPrimitive_endpoint_sub_eq_at_path_points` is the connected
component, in the first coordinate chart, of the chart-ball overlap containing
the left endpoint. -/
lemma pathChartBallPrimitive_endpoint_sub_eq_on_path_segment
    (form : HolomorphicOneForm X) (γ : C(unitInterval, X))
    (B₁ B₂ : PathChartBall X) {u v : unitInterval} (huv : u ≤ v)
    (hseg₁ : Set.Icc u v ⊆ pathChartBallSet γ B₁)
    (hseg₂ : Set.Icc u v ⊆ pathChartBallSet γ B₂) :
    pathChartBallPrimitive form B₁ ((extChartAt 𝓘(ℂ) B₁.p) (γ v)) -
        pathChartBallPrimitive form B₁ ((extChartAt 𝓘(ℂ) B₁.p) (γ u)) =
      pathChartBallPrimitive form B₂ ((extChartAt 𝓘(ℂ) B₂.p) (γ v)) -
        pathChartBallPrimitive form B₂ ((extChartAt 𝓘(ℂ) B₂.p) (γ u)) := by
  classical
  let O : Set ℂ := {z : ℂ | z ∈ Metric.ball B₁.c B₁.r ∧
      (extChartAt 𝓘(ℂ) B₁.p).symm z ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm z) ∈
          Metric.ball B₂.c B₂.r}
  let z : unitInterval → ℂ := fun w => (extChartAt 𝓘(ℂ) B₁.p) (γ w)
  have huI : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
  have hvI : v ∈ Set.Icc u v := ⟨huv, le_rfl⟩
  have hsource₁ : ∀ w ∈ Set.Icc u v, γ w ∈ (extChartAt 𝓘(ℂ) B₁.p).source := by
    intro w hw
    simpa [extChartAt_source] using (hseg₁ hw).1
  have hcont_z : ContinuousOn z (Set.Icc u v) := by
    simpa [z] using
      (continuousOn_extChartAt (I := 𝓘(ℂ)) B₁.p).comp γ.continuous.continuousOn
        hsource₁
  have hpre_image : IsPreconnected (z '' Set.Icc u v) := by
    exact isPreconnected_Icc.image z hcont_z
  have himage_sub_O : z '' Set.Icc u v ⊆ O := by
    intro y hy
    rcases hy with ⟨w, hw, rfl⟩
    have hw₁ := hseg₁ hw
    have hw₂ := hseg₂ hw
    have hw_source₁ : γ w ∈ (extChartAt 𝓘(ℂ) B₁.p).source := by
      simpa [extChartAt_source] using hw₁.1
    have hsymm :
        (extChartAt 𝓘(ℂ) B₁.p).symm ((extChartAt 𝓘(ℂ) B₁.p) (γ w)) =
          γ w := by
      exact (extChartAt 𝓘(ℂ) B₁.p).left_inv hw_source₁
    refine ⟨hw₁.2, ?_, ?_⟩
    · rw [hsymm]
      simpa [extChartAt_source] using hw₂.1
    · rw [hsymm]
      exact hw₂.2
  let U : Set ℂ := connectedComponentIn O (z u)
  have hzuO : z u ∈ O := himage_sub_O ⟨u, huI, rfl⟩
  have hzvU : z v ∈ U := by
    have hsub := hpre_image.subset_connectedComponentIn (x := z u) ⟨u, huI, rfl⟩
      himage_sub_O
    exact hsub ⟨v, hvI, rfl⟩
  have hU_open : IsOpen U := by
    exact (pathChartBallOverlap_isOpen (X := X) B₁ B₂).connectedComponentIn
  have hU_pre : IsPreconnected U := by
    simpa [U] using (isPreconnected_connectedComponentIn (x := z u) (F := O))
  have hU_ball₁ : U ⊆ Metric.ball B₁.c B₁.r := by
    intro y hy
    exact (connectedComponentIn_subset O (z u) hy).1
  have hU_ball₂ : ∀ y ∈ U,
      (extChartAt 𝓘(ℂ) B₁.p).symm y ∈ (extChartAt 𝓘(ℂ) B₂.p).source ∧
        (extChartAt 𝓘(ℂ) B₂.p) ((extChartAt 𝓘(ℂ) B₁.p).symm y) ∈
          Metric.ball B₂.c B₂.r := by
    intro y hy
    exact (connectedComponentIn_subset O (z u) hy).2
  have hzuU : z u ∈ U := by
    exact mem_connectedComponentIn hzuO
  have hbase := pathChartBallPrimitive_endpoint_sub_eq_at_path_points
    (form := form) (γ := γ) (B₁ := B₁) (B₂ := B₂)
    hU_open hU_pre hU_ball₁ hU_ball₂
    (hseg₁ huI) (hseg₁ hvI) hzuU hzvU
  simpa [z] using hbase

private lemma no_mem_between_orderEmb_succ_unitInterval (Pset : Finset unitInterval) {m : ℕ}
    (hcard : Pset.card = m + 1) (i : Fin m) {x : unitInterval}
    (hx : x ∈ Pset)
    (hbetween : Pset.orderEmbOfFin hcard i.castSucc < x ∧
      x < Pset.orderEmbOfFin hcard i.succ) : False := by
  have hxrange : x ∈ Set.range (Pset.orderEmbOfFin hcard) := by
    simpa [Finset.range_orderEmbOfFin Pset hcard] using hx
  rcases hxrange with ⟨j, rfl⟩
  have hleft : i.castSucc < j :=
    ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hbetween.1
  have hright : j < i.succ :=
    ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hbetween.2
  have hleft_nat : i.val < j.val := by
    simpa [Fin.lt_def, Fin.val_castSucc] using hleft
  have hright_nat : j.val < i.val + 1 := by
    simpa [Fin.lt_def, Fin.val_succ] using hright
  omega

private lemma exists_subdivision_cell_of_refined_cell {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) {m : ℕ} {Pset : Finset unitInterval}
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hcard : Pset.card = m + 1) (i : Fin m) :
    ∃ j : Fin S.n,
      Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
          (Pset.orderEmbOfFin hcard i.succ) ⊆
        Set.Icc (S.t j.castSucc) (S.t j.succ) := by
  classical
  let a : unitInterval := Pset.orderEmbOfFin hcard i.castSucc
  let b : unitInterval := Pset.orderEmbOfFin hcard i.succ
  have ha_mem : a ∈ Pset := by
    simp [a]
  have hb_mem : b ∈ Pset := by
    simp [b]
  have ha0 : (0 : unitInterval) ≤ a := by
    exact a.2.1
  have hb1 : b ≤ (1 : unitInterval) := by
    exact b.2.2
  have hab_idx : i.castSucc < i.succ := by
    simp [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  have hab : a < b :=
    (Pset.orderEmbOfFin hcard).strictMono hab_idx
  have hno_between : ∀ {x : unitInterval}, x ∈ Pset → ¬ (a < x ∧ x < b) := by
    intro x hx hxbetween
    exact no_mem_between_orderEmb_succ_unitInterval Pset hcard i hx
      (by simpa [a, b] using hxbetween)
  let J : Finset (Fin (S.n + 1)) := Finset.univ.filter (fun k => S.t k ≤ a)
  have hJ_nonempty : J.Nonempty := by
    refine ⟨0, ?_⟩
    simp [J, S.zero_eq, ha0]
  let k : Fin (S.n + 1) := J.max' hJ_nonempty
  have hk_mem : k ∈ J := Finset.max'_mem J hJ_nonempty
  have hk_t_le : S.t k ≤ a := (Finset.mem_filter.mp hk_mem).2
  have hk_not_last : k ≠ Fin.last S.n := by
    intro hk_last
    have hk_eq_one : S.t k = 1 := by
      simpa [hk_last] using S.one_eq
    have hone_le_a : (1 : unitInterval) ≤ a := by
      simpa [hk_eq_one] using hk_t_le
    exact (lt_irrefl a) ((hab.trans_le hb1).trans_le hone_le_a)
  have hk_val_lt : k.val < S.n := by
    have hk_val_le : k.val ≤ S.n := by omega
    have hk_val_ne : k.val ≠ S.n := by
      intro hval
      apply hk_not_last
      exact Fin.ext hval
    omega
  let j : Fin S.n := ⟨k.val, hk_val_lt⟩
  have hjk : j.castSucc = k := by
    exact Fin.ext (by simp [j])
  have hleft : S.t j.castSucc ≤ a := by
    simpa [hjk] using hk_t_le
  have hright : b ≤ S.t j.succ := by
    by_contra hbnot
    have ht_succ_lt_b : S.t j.succ < b := lt_of_not_ge hbnot
    have hsucc_not_le_a : ¬ S.t j.succ ≤ a := by
      intro hsucc_le_a
      have hsucc_memJ : j.succ ∈ J := by
        simp [J, hsucc_le_a]
      have hsucc_le_k : j.succ ≤ k := Finset.le_max' J (j.succ) hsucc_memJ
      have hsucc_val_le : (j.succ).val ≤ k.val := Fin.val_le_of_le hsucc_le_k
      have hsucc_val_le' := hsucc_val_le
      simp [j] at hsucc_val_le'
    have ha_lt_tsucc : a < S.t j.succ := lt_of_not_ge hsucc_not_le_a
    exact hno_between (hPbase j.succ) ⟨ha_lt_tsucc, ht_succ_lt_b⟩
  refine ⟨j, ?_⟩
  intro u hu
  exact ⟨hleft.trans hu.1, hu.2.trans hright⟩

private lemma orderEmb_zero_eq_of_mem {m : ℕ} {Pset : Finset unitInterval}
    (hcard : Pset.card = m + 1) (hzeroP : (0 : unitInterval) ∈ Pset) :
    Pset.orderEmbOfFin hcard 0 = 0 := by
  have hz : 0 < m + 1 := Nat.succ_pos m
  calc
    Pset.orderEmbOfFin hcard 0 =
        Pset.min' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
      simpa using Finset.orderEmbOfFin_zero (s := Pset) hcard hz
    _ = 0 := by
      exact (Finset.min'_eq_iff Pset _ 0).2
        ⟨hzeroP, fun x _hx => (show (0 : unitInterval) ≤ x from x.2.1)⟩

private lemma orderEmb_last_eq_of_mem {m : ℕ} {Pset : Finset unitInterval}
    (hcard : Pset.card = m + 1) (honeP : (1 : unitInterval) ∈ Pset) :
    Pset.orderEmbOfFin hcard (Fin.last m) = 1 := by
  have hz : 0 < m + 1 := Nat.succ_pos m
  calc
    Pset.orderEmbOfFin hcard (Fin.last m) =
        Pset.max' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
      simpa [Fin.last, Nat.succ_eq_add_one] using
        Finset.orderEmbOfFin_last (s := Pset) hcard hz
    _ = 1 := by
      exact (Finset.max'_eq_iff Pset _ 1).2
        ⟨honeP, fun x _hx => (show x ≤ (1 : unitInterval) from x.2.2)⟩

private noncomputable def breakpointIndex {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) {m : ℕ} {Pset : Finset unitInterval}
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hcard : Pset.card = m + 1) (j : Fin (S.n + 1)) : Fin (m + 1) :=
  Classical.choose (by
    have hmem : S.t j ∈ Set.range (Pset.orderEmbOfFin hcard) := by
      simpa [Finset.range_orderEmbOfFin Pset hcard] using hPbase j
    exact hmem)

private lemma breakpointIndex_spec {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) {m : ℕ} {Pset : Finset unitInterval}
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hcard : Pset.card = m + 1) (j : Fin (S.n + 1)) :
    Pset.orderEmbOfFin hcard (breakpointIndex S hPbase hcard j) = S.t j := by
  exact Classical.choose_spec (by
    have hmem : S.t j ∈ Set.range (Pset.orderEmbOfFin hcard) := by
      simpa [Finset.range_orderEmbOfFin Pset hcard] using hPbase j
    exact hmem)

private lemma breakpointIndex_mono {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) {m : ℕ} {Pset : Finset unitInterval}
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hcard : Pset.card = m + 1) :
    Monotone (breakpointIndex S hPbase hcard) := by
  intro i j hij
  apply ((Pset.orderEmbOfFin hcard).le_iff_le).mp
  rw [breakpointIndex_spec S hPbase hcard i, breakpointIndex_spec S hPbase hcard j]
  exact S.monotone_t hij

private lemma breakpointIndex_zero {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) {m : ℕ} {Pset : Finset unitInterval}
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hcard : Pset.card = m + 1) (hzeroP : (0 : unitInterval) ∈ Pset) :
    breakpointIndex S hPbase hcard 0 = 0 := by
  apply (Pset.orderEmbOfFin hcard).injective
  rw [breakpointIndex_spec S hPbase hcard 0, S.zero_eq,
    orderEmb_zero_eq_of_mem hcard hzeroP]

private lemma breakpointIndex_last {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) {m : ℕ} {Pset : Finset unitInterval}
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hcard : Pset.card = m + 1) (honeP : (1 : unitInterval) ∈ Pset) :
    breakpointIndex S hPbase hcard (Fin.last S.n) = Fin.last m := by
  apply (Pset.orderEmbOfFin hcard).injective
  rw [breakpointIndex_spec S hPbase hcard (Fin.last S.n), S.one_eq,
    orderEmb_last_eq_of_mem hcard honeP]

private lemma refinedSubcell_subset_original_cell {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) {m : ℕ} {Pset : Finset unitInterval}
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hcard : Pset.card = m + 1) (j : Fin S.n) {k : ℕ}
    (hk : k ∈ Finset.Ico
      (breakpointIndex S hPbase hcard j.castSucc).val
      (breakpointIndex S hPbase hcard j.succ).val) :
    ∃ hkR : k < m,
      Set.Icc (Pset.orderEmbOfFin hcard (⟨k, Nat.lt_succ_of_lt hkR⟩ : Fin (m + 1)))
          (Pset.orderEmbOfFin hcard (⟨k + 1, Nat.succ_lt_succ hkR⟩ : Fin (m + 1))) ⊆
        Set.Icc (S.t j.castSucc) (S.t j.succ) := by
  classical
  have hki := Finset.mem_Ico.mp hk
  have hidx_le_m : (breakpointIndex S hPbase hcard j.succ).val ≤ m := by
    have hlt := (breakpointIndex S hPbase hcard j.succ).isLt
    omega
  have hkR : k < m := by omega
  refine ⟨hkR, ?_⟩
  intro u hu
  have hleft_idx : (breakpointIndex S hPbase hcard j.castSucc) ≤
      (⟨k, Nat.lt_succ_of_lt hkR⟩ : Fin (m + 1)) := by
    exact Fin.mk_le_mk.mpr hki.1
  have hright_idx : (⟨k + 1, Nat.succ_lt_succ hkR⟩ : Fin (m + 1)) ≤
      breakpointIndex S hPbase hcard j.succ := by
    exact Fin.mk_le_mk.mpr (Nat.succ_le_of_lt hki.2)
  have hleft_val : S.t j.castSucc ≤
      Pset.orderEmbOfFin hcard (⟨k, Nat.lt_succ_of_lt hkR⟩ : Fin (m + 1)) := by
    calc
      S.t j.castSucc =
          Pset.orderEmbOfFin hcard (breakpointIndex S hPbase hcard j.castSucc) := by
        rw [breakpointIndex_spec S hPbase hcard j.castSucc]
      _ ≤ Pset.orderEmbOfFin hcard (⟨k, Nat.lt_succ_of_lt hkR⟩ : Fin (m + 1)) :=
        (Pset.orderEmbOfFin hcard).monotone hleft_idx
  have hright_val :
      Pset.orderEmbOfFin hcard (⟨k + 1, Nat.succ_lt_succ hkR⟩ : Fin (m + 1)) ≤
        S.t j.succ := by
    calc
      Pset.orderEmbOfFin hcard (⟨k + 1, Nat.succ_lt_succ hkR⟩ : Fin (m + 1)) ≤
          Pset.orderEmbOfFin hcard (breakpointIndex S hPbase hcard j.succ) :=
        (Pset.orderEmbOfFin hcard).monotone hright_idx
      _ = S.t j.succ := by
        rw [breakpointIndex_spec S hPbase hcard j.succ]
  exact ⟨hleft_val.trans hu.1, hu.2.trans hright_val⟩

private lemma sum_Ico_adjacent_blocks {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (a : ℕ → ℕ) (n : ℕ) (hmono : Monotone a) :
    (∑ j ∈ Finset.range n, ∑ k ∈ Finset.Ico (a j) (a (j + 1)), f k) =
      ∑ k ∈ Finset.Ico (a 0) (a n), f k := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      exact Finset.sum_Ico_consecutive f (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))

private lemma sum_Ico_sub {G : Type*} [AddCommGroup G] (f : ℕ → G) {m n : ℕ}
    (h : m ≤ n) :
    (∑ k ∈ Finset.Ico m n, (f (k + 1) - f k)) = f n - f m := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      simp [hm]
  | succ n ih =>
      by_cases hmn : m ≤ n
      · rw [Finset.sum_Ico_succ_top hmn, ih hmn]
        abel
      · have hm : m = n + 1 := by omega
        simp [hm]

private noncomputable def subdivisionRefinedByFinset {γ : C(unitInterval, X)}
    (S : PathChartBallSubdivision γ) (Pset : Finset unitInterval)
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hzeroP : (0 : unitInterval) ∈ Pset) (honeP : (1 : unitInterval) ∈ Pset)
    {m : ℕ} (hcard : Pset.card = m + 1) : PathChartBallSubdivision γ := by
  classical
  let cell : Fin m → Fin S.n := fun i =>
    Classical.choose (exists_subdivision_cell_of_refined_cell S hPbase hcard i)
  refine
    { n := m
      t := fun i : Fin (m + 1) => Pset.orderEmbOfFin hcard i
      cellBall := fun i : Fin m => S.cellBall (cell i)
      zero_eq := ?_
      one_eq := ?_
      monotone_t := ?_
      cell_subset := ?_ }
  · exact orderEmb_zero_eq_of_mem hcard hzeroP
  · exact orderEmb_last_eq_of_mem hcard honeP
  · exact (Pset.orderEmbOfFin hcard).monotone
  · intro i u hu
    have hsub : Set.Icc (Pset.orderEmbOfFin hcard i.castSucc)
          (Pset.orderEmbOfFin hcard i.succ) ⊆
        Set.Icc (S.t (cell i).castSucc) (S.t (cell i).succ) :=
      Classical.choose_spec (exists_subdivision_cell_of_refined_cell S hPbase hcard i)
    exact S.cell_subset (cell i) (hsub hu)

private lemma refined_block_sum_eq_increment {γ : C(unitInterval, X)}
    (form : HolomorphicOneForm X) (S : PathChartBallSubdivision γ)
    (Pset : Finset unitInterval)
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hzeroP : (0 : unitInterval) ∈ Pset) (honeP : (1 : unitInterval) ∈ Pset)
    {m : ℕ} (hcard : Pset.card = m + 1) (j : Fin S.n) :
    let R := subdivisionRefinedByFinset S Pset hPbase hzeroP honeP hcard
    let F : ℕ → ℂ := fun k => if hk : k < m then developingIncrement form γ R ⟨k, hk⟩ else 0
    (∑ k ∈ Finset.Ico
        (breakpointIndex S hPbase hcard j.castSucc).val
        (breakpointIndex S hPbase hcard j.succ).val, F k) =
      developingIncrement form γ S j := by
  classical
  intro R F
  let B := S.cellBall j
  let g := pathChartBallPrimitive form B
  let coord : ℕ → ℂ := fun k =>
    if hk : k < m + 1 then
      g ((extChartAt 𝓘(ℂ) B.p) (γ (Pset.orderEmbOfFin hcard ⟨k, hk⟩)))
    else 0
  have hle_idx : (breakpointIndex S hPbase hcard j.castSucc).val ≤
      (breakpointIndex S hPbase hcard j.succ).val := by
    have hmono := breakpointIndex_mono S hPbase hcard (Fin.castSucc_le_succ j)
    exact Fin.val_le_of_le hmono
  have hsum_to_coord :
      (∑ k ∈ Finset.Ico
          (breakpointIndex S hPbase hcard j.castSucc).val
          (breakpointIndex S hPbase hcard j.succ).val, F k) =
        ∑ k ∈ Finset.Ico
          (breakpointIndex S hPbase hcard j.castSucc).val
          (breakpointIndex S hPbase hcard j.succ).val,
          (coord (k + 1) - coord k) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rcases refinedSubcell_subset_original_cell S hPbase hcard j hk with ⟨hkR, hsubS⟩
    let iR : Fin R.n := ⟨k, by simpa [R, subdivisionRefinedByFinset] using hkR⟩
    have hsegS : Set.Icc (R.t iR.castSucc) (R.t iR.succ) ⊆ pathChartBallSet γ B := by
      intro u hu
      have hu' : u ∈ Set.Icc (S.t j.castSucc) (S.t j.succ) := by
        have ht_left : R.t iR.castSucc =
            Pset.orderEmbOfFin hcard (⟨k, Nat.lt_succ_of_lt hkR⟩ : Fin (m + 1)) := by
          simp [R, iR, subdivisionRefinedByFinset]
        have ht_right : R.t iR.succ =
            Pset.orderEmbOfFin hcard (⟨k + 1, Nat.succ_lt_succ hkR⟩ : Fin (m + 1)) := by
          simp [R, iR, subdivisionRefinedByFinset]
        exact hsubS (by simpa [ht_left, ht_right] using hu)
      exact S.cell_subset j hu'
    have hinc_eq := pathChartBallPrimitive_endpoint_sub_eq_on_path_segment
      (form := form) (γ := γ) (B₁ := R.cellBall iR) (B₂ := B)
      (u := R.t iR.castSucc) (v := R.t iR.succ)
      (R.monotone_t (Fin.castSucc_le_succ iR)) (R.cell_subset iR) hsegS
    have hcoord_left : coord k =
        g ((extChartAt 𝓘(ℂ) B.p) (γ (R.t iR.castSucc))) := by
      have hk1 : k ≤ m := Nat.le_of_lt hkR
      simp [coord, hk1, R, iR, subdivisionRefinedByFinset]
    have hcoord_right : coord (k + 1) =
        g ((extChartAt 𝓘(ℂ) B.p) (γ (R.t iR.succ))) := by
      simp [coord, hkR, R, iR, subdivisionRefinedByFinset]
    have hF : F k = developingIncrement form γ R iR := by
      simp [F, hkR, iR]
    calc
      F k = developingIncrement form γ R iR := hF
      _ = coord (k + 1) - coord k := by
        unfold developingIncrement
        rw [hinc_eq, hcoord_left, hcoord_right]
  calc
    (∑ k ∈ Finset.Ico
        (breakpointIndex S hPbase hcard j.castSucc).val
        (breakpointIndex S hPbase hcard j.succ).val, F k) =
        ∑ k ∈ Finset.Ico
          (breakpointIndex S hPbase hcard j.castSucc).val
          (breakpointIndex S hPbase hcard j.succ).val,
          (coord (k + 1) - coord k) := hsum_to_coord
    _ = coord (breakpointIndex S hPbase hcard j.succ).val -
        coord (breakpointIndex S hPbase hcard j.castSucc).val :=
      sum_Ico_sub coord hle_idx
    _ = developingIncrement form γ S j := by
      have hleft_le : (breakpointIndex S hPbase hcard j.castSucc).val ≤ m := by
        have hlt := (breakpointIndex S hPbase hcard j.castSucc).isLt
        omega
      have hright_le : (breakpointIndex S hPbase hcard j.succ).val ≤ m := by
        have hlt := (breakpointIndex S hPbase hcard j.succ).isLt
        omega
      simp [coord, hleft_le, hright_le, developingIncrement, B, g,
        breakpointIndex_spec S hPbase hcard j.castSucc,
        breakpointIndex_spec S hPbase hcard j.succ]

private theorem developingValueOfSubdivision_eq_refinedByFinset {γ : C(unitInterval, X)}
    (form : HolomorphicOneForm X) (S : PathChartBallSubdivision γ)
    (Pset : Finset unitInterval)
    (hPbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hzeroP : (0 : unitInterval) ∈ Pset) (honeP : (1 : unitInterval) ∈ Pset)
    {m : ℕ} (hcard : Pset.card = m + 1) :
    developingValueOfSubdivision form γ S =
      developingValueOfSubdivision form γ
        (subdivisionRefinedByFinset S Pset hPbase hzeroP honeP hcard) := by
  classical
  let R := subdivisionRefinedByFinset S Pset hPbase hzeroP honeP hcard
  let F : ℕ → ℂ := fun k => if hk : k < m then developingIncrement form γ R ⟨k, hk⟩ else 0
  let idx : Fin (S.n + 1) → Fin (m + 1) := breakpointIndex S hPbase hcard
  let a : ℕ → ℕ := fun k => if hk : k < S.n + 1 then (idx ⟨k, hk⟩).val else m
  have hmono_a : Monotone a := by
    intro p q hpq
    by_cases hq : q < S.n + 1
    · have hp : p < S.n + 1 := lt_of_le_of_lt hpq hq
      have hfin : (⟨p, hp⟩ : Fin (S.n + 1)) ≤ ⟨q, hq⟩ := by
        exact hpq
      have hidx := breakpointIndex_mono S hPbase hcard hfin
      have hval := Fin.val_le_of_le hidx
      have hp_le : p ≤ S.n := Nat.lt_succ_iff.mp hp
      have hq_le : q ≤ S.n := Nat.lt_succ_iff.mp hq
      simpa [a, hp_le, hq_le, idx] using hval
    · have hq_le : ¬ q ≤ S.n := by
        intro h
        exact hq (Nat.lt_succ_iff.mpr h)
      have aq : a q = m := by simp [a, hq_le]
      have ap_le_m : a p ≤ m := by
        by_cases hp : p < S.n + 1
        · have hp_le : p ≤ S.n := Nat.lt_succ_iff.mp hp
          have hle : (idx ⟨p, hp⟩).val ≤ m := by
            have hlt := (idx ⟨p, hp⟩).isLt
            omega
          simpa [a, hp_le, idx] using hle
        · have hp_le : ¬ p ≤ S.n := by
            intro h
            exact hp (Nat.lt_succ_iff.mpr h)
          simp [a, hp_le]
      simpa [aq] using ap_le_m
  have ha0 : a 0 = 0 := by
    have hp0 : 0 < S.n + 1 := Nat.succ_pos S.n
    have hidx0 := congrArg Fin.val (breakpointIndex_zero S hPbase hcard hzeroP)
    simpa [a, hp0, idx] using hidx0
  have haN : a S.n = m := by
    have hpN : S.n < S.n + 1 := Nat.lt_succ_self S.n
    have hidxN := congrArg Fin.val (breakpointIndex_last S hPbase hcard honeP)
    simpa [a, hpN, idx, Fin.last] using hidxN
  have hR_sum : developingValueOfSubdivision form γ R = ∑ k ∈ Finset.range m, F k := by
    unfold developingValueOfSubdivision
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    simp [F, hklt, R, subdivisionRefinedByFinset]
  have hblocks : (∑ k ∈ Finset.range m, F k) =
      ∑ j ∈ Finset.range S.n, ∑ k ∈ Finset.Ico (a j) (a (j + 1)), F k := by
    have h := sum_Ico_adjacent_blocks F a S.n hmono_a
    calc
      (∑ k ∈ Finset.range m, F k) = ∑ k ∈ Finset.Ico 0 m, F k := by
        rw [Finset.range_eq_Ico]
      _ = ∑ j ∈ Finset.range S.n, ∑ k ∈ Finset.Ico (a j) (a (j + 1)), F k := by
        simpa [ha0, haN] using h.symm
  have hblock_to_S :
      (∑ j ∈ Finset.range S.n, ∑ k ∈ Finset.Ico (a j) (a (j + 1)), F k) =
        developingValueOfSubdivision form γ S := by
    unfold developingValueOfSubdivision
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < S.n := Finset.mem_range.mp hk
    let j : Fin S.n := ⟨k, hklt⟩
    have hpj_le : k ≤ S.n := Nat.le_of_lt hklt
    have hpj1_le : k + 1 ≤ S.n := Nat.succ_le_of_lt hklt
    have hblock := refined_block_sum_eq_increment form S Pset hPbase hzeroP honeP hcard j
    simpa [a, hpj_le, hpj1_le, idx, F, R, j, hklt, Nat.lt_succ_iff] using hblock
  calc
    developingValueOfSubdivision form γ S =
        ∑ j ∈ Finset.range S.n, ∑ k ∈ Finset.Ico (a j) (a (j + 1)), F k :=
      hblock_to_S.symm
    _ = ∑ k ∈ Finset.range m, F k := hblocks.symm
    _ = developingValueOfSubdivision form γ R := hR_sum.symm

private theorem refinedByFinset_eq_refinedByFinset {γ : C(unitInterval, X)}
    (form : HolomorphicOneForm X) (S T : PathChartBallSubdivision γ)
    (Pset : Finset unitInterval)
    (hSbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset)
    (hTbase : ∀ j : Fin (T.n + 1), T.t j ∈ Pset)
    (hzeroP : (0 : unitInterval) ∈ Pset) (honeP : (1 : unitInterval) ∈ Pset)
    {m : ℕ} (hcard : Pset.card = m + 1) :
    developingValueOfSubdivision form γ
        (subdivisionRefinedByFinset S Pset hSbase hzeroP honeP hcard) =
      developingValueOfSubdivision form γ
        (subdivisionRefinedByFinset T Pset hTbase hzeroP honeP hcard) := by
  classical
  let R₁ := subdivisionRefinedByFinset S Pset hSbase hzeroP honeP hcard
  let R₂ := subdivisionRefinedByFinset T Pset hTbase hzeroP honeP hcard
  let F₁ : ℕ → ℂ := fun k =>
    if hk : k < m then
      developingIncrement form γ R₁
        ⟨k, by simpa [R₁, subdivisionRefinedByFinset] using hk⟩
    else 0
  let F₂ : ℕ → ℂ := fun k =>
    if hk : k < m then
      developingIncrement form γ R₂
        ⟨k, by simpa [R₂, subdivisionRefinedByFinset] using hk⟩
    else 0
  have hR₁_sum : developingValueOfSubdivision form γ R₁ = ∑ k ∈ Finset.range m, F₁ k := by
    unfold developingValueOfSubdivision
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    simp [F₁, hklt, R₁, subdivisionRefinedByFinset]
  have hR₂_sum : developingValueOfSubdivision form γ R₂ = ∑ k ∈ Finset.range m, F₂ k := by
    unfold developingValueOfSubdivision
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    simp [F₂, hklt, R₂, subdivisionRefinedByFinset]
  have hF_eq : ∀ k ∈ Finset.range m, F₁ k = F₂ k := by
    intro k hk
    have hklt : k < m := Finset.mem_range.mp hk
    let i₁ : Fin R₁.n := ⟨k, by simpa [R₁, subdivisionRefinedByFinset] using hklt⟩
    let i₂ : Fin R₂.n := ⟨k, by simpa [R₂, subdivisionRefinedByFinset] using hklt⟩
    have ht_left : R₂.t i₂.castSucc = R₁.t i₁.castSucc := by
      simp [R₁, R₂, i₁, i₂, subdivisionRefinedByFinset]
    have ht_right : R₂.t i₂.succ = R₁.t i₁.succ := by
      simp [R₁, R₂, i₁, i₂, subdivisionRefinedByFinset]
    have hseg₂ : Set.Icc (R₁.t i₁.castSucc) (R₁.t i₁.succ) ⊆
        pathChartBallSet γ (R₂.cellBall i₂) := by
      intro u hu
      exact R₂.cell_subset i₂ (by simpa [ht_left, ht_right] using hu)
    have hinc := pathChartBallPrimitive_endpoint_sub_eq_on_path_segment
      (form := form) (γ := γ) (B₁ := R₁.cellBall i₁) (B₂ := R₂.cellBall i₂)
      (u := R₁.t i₁.castSucc) (v := R₁.t i₁.succ)
      (R₁.monotone_t (Fin.castSucc_le_succ i₁)) (R₁.cell_subset i₁) hseg₂
    have hF₁ : F₁ k = developingIncrement form γ R₁ i₁ := by
      simp [F₁, hklt, i₁]
    have hF₂ : F₂ k = developingIncrement form γ R₂ i₂ := by
      simp [F₂, hklt, i₂]
    calc
      F₁ k = developingIncrement form γ R₁ i₁ := hF₁
      _ = developingIncrement form γ R₂ i₂ := by
        unfold developingIncrement
        rw [ht_left, ht_right, hinc]
      _ = F₂ k := hF₂.symm
  calc
    developingValueOfSubdivision form γ R₁ = ∑ k ∈ Finset.range m, F₁ k := hR₁_sum
    _ = ∑ k ∈ Finset.range m, F₂ k := by
      exact Finset.sum_congr rfl hF_eq
    _ = developingValueOfSubdivision form γ R₂ := hR₂_sum.symm

/-- The developing value computed from a chart-ball subdivision is independent
of the subdivision.  The proof passes through the common refinement obtained by
sorting the union of the two finite breakpoint sets. -/
theorem developingValueOfSubdivision_eq_of_subdivisions
    (form : HolomorphicOneForm X) (γ : C(unitInterval, X))
    (S S' : PathChartBallSubdivision γ) :
    developingValueOfSubdivision form γ S = developingValueOfSubdivision form γ S' := by
  classical
  let baseS : Finset unitInterval := Finset.image S.t Finset.univ
  let baseT : Finset unitInterval := Finset.image S'.t Finset.univ
  let Pset : Finset unitInterval := baseS ∪ baseT
  have hSbase : ∀ j : Fin (S.n + 1), S.t j ∈ Pset := by
    intro j
    simp [Pset, baseS]
  have hTbase : ∀ j : Fin (S'.n + 1), S'.t j ∈ Pset := by
    intro j
    simp [Pset, baseT]
  have hzeroP : (0 : unitInterval) ∈ Pset := by
    have : S.t 0 ∈ Pset := hSbase 0
    simpa [S.zero_eq] using this
  have honeP : (1 : unitInterval) ∈ Pset := by
    have : S.t (Fin.last S.n) ∈ Pset := hSbase (Fin.last S.n)
    simpa [S.one_eq] using this
  have hP_nonempty : Pset.Nonempty := ⟨0, hzeroP⟩
  have hcard_pos : 0 < Pset.card := Finset.card_pos.mpr hP_nonempty
  let m : ℕ := Pset.card - 1
  have hcard : Pset.card = m + 1 := by
    have hsucc := Nat.succ_pred_eq_of_pos hcard_pos
    simpa [m, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using hsucc.symm
  have hSref := developingValueOfSubdivision_eq_refinedByFinset
    (form := form) (S := S) (Pset := Pset) hSbase hzeroP honeP hcard
  have hTref := developingValueOfSubdivision_eq_refinedByFinset
    (form := form) (S := S') (Pset := Pset) hTbase hzeroP honeP hcard
  have hcommon := refinedByFinset_eq_refinedByFinset
    (form := form) (S := S) (T := S') (Pset := Pset)
    hSbase hTbase hzeroP honeP hcard
  calc
    developingValueOfSubdivision form γ S =
        developingValueOfSubdivision form γ
          (subdivisionRefinedByFinset S Pset hSbase hzeroP honeP hcard) := hSref
    _ = developingValueOfSubdivision form γ
          (subdivisionRefinedByFinset S' Pset hTbase hzeroP honeP hcard) := hcommon
    _ = developingValueOfSubdivision form γ S' := hTref.symm

theorem developingValue_eq_developingValueOfSubdivision
    (x₀ : X) (form : HolomorphicOneForm X) (γ : C(unitInterval, X))
    (S : PathChartBallSubdivision γ) :
    developingValue x₀ form γ = developingValueOfSubdivision form γ S := by
  simpa [developingValue] using
    developingValueOfSubdivision_eq_of_subdivisions form γ
      (chosenPathChartBallSubdivision γ) S

/-- Local B2 bridge: for an analytic arc contained in one chart-coordinate
ball, the developing value of its underlying continuous path is the canonical
arc integral, under the same derivative and interval-integrability side
conditions as the chart-primitive FTC lemma `B1`. -/
theorem developingValue_analyticArcToContinuousMap_eq_canonicalArcIntegral_of_pathChartBall
    (x₀ : X) (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (B : PathChartBall X)
    (hpath : ∀ u : unitInterval, u ∈ pathChartBallSet (analyticArcToContinuousMap γ) B)
    (hchart_hasDeriv_right : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (fun u : ℝ => (extChartAt 𝓘(ℂ) B.p) (γ.extend u))
        (deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) B.p) (γ.extend u)) t)
        (Set.Ioi t) t)
    (hintegrable : IntervalIntegrable
      (fun t : ℝ =>
        form.coeff B.p ((extChartAt 𝓘(ℂ) B.p) (γ.extend t)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) B.p) (γ.extend u)) t)
      MeasureTheory.volume (0 : ℝ) 1) :
    developingValue x₀ form (analyticArcToContinuousMap γ) =
      canonicalArcIntegral γ form := by
  classical
  let τ : Fin (1 + 1) → unitInterval := fun i =>
    if i = (0 : Fin (1 + 1)) then 0 else 1
  let S : PathChartBallSubdivision (analyticArcToContinuousMap γ) :=
    { n := 1
      t := τ
      cellBall := fun _ => B
      zero_eq := by
        simp [τ]
      one_eq := by
        simp [τ, Fin.last]
      monotone_t := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp [τ] at hij ⊢
      cell_subset := by
        intro i u _hu
        exact hpath u }
  have hdev :
      developingValue x₀ form (analyticArcToContinuousMap γ) =
        developingValueOfSubdivision form (analyticArcToContinuousMap γ) S :=
    developingValue_eq_developingValueOfSubdivision x₀ form
      (analyticArcToContinuousMap γ) S
  have hsub :
      developingValueOfSubdivision form (analyticArcToContinuousMap γ) S =
        developingIncrement form (analyticArcToContinuousMap γ) S 0 := by
    simp [developingValueOfSubdivision, S]
  have hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.extend t ∈ (extChartAt 𝓘(ℂ) B.p).source := by
    intro t ht
    let u : unitInterval := ⟨t, ht⟩
    have hu := hpath u
    simpa [u, analyticArcToContinuousMap_apply, extChartAt_source] using hu.1
  have hpath_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (extChartAt 𝓘(ℂ) B.p) (γ.extend t) ∈ Metric.ball B.c B.r := by
    intro t ht
    let u : unitInterval := ⟨t, ht⟩
    have hu := hpath u
    simpa [u, analyticArcToContinuousMap_apply] using hu.2
  have hcanon := canonicalArcIntegral_eq_chartPrimitive_endpoint_sub
    (γ := γ) (form := form) (x₀ := B.p) (c := B.c) (r := B.r)
    (g := pathChartBallPrimitive form B)
    hsource hpath_ball (pathChartBallPrimitive_hasDerivAt form B)
    hchart_hasDeriv_right hintegrable
  have hinc :
      developingIncrement form (analyticArcToContinuousMap γ) S 0 =
        canonicalArcIntegral γ form := by
    unfold developingIncrement
    rw [hcanon]
    simp [S, τ]
  calc
    developingValue x₀ form (analyticArcToContinuousMap γ) =
        developingValueOfSubdivision form (analyticArcToContinuousMap γ) S := hdev
    _ = developingIncrement form (analyticArcToContinuousMap γ) S 0 := hsub
    _ = canonicalArcIntegral γ form := hinc

/-- Local B2 bridge with fixed-chart integrability discharged from the strong
analytic-arc structure. The right-derivative hypothesis is still the FTC side
condition of `canonicalArcIntegral_eq_chartPrimitive_endpoint_sub`. -/
theorem developingValue_eq_canonicalArcIntegral_of_pathChartBall_autoIntegrable
    (x₀ : X) (form : HolomorphicOneForm X) (γ : AnalyticArc X)
    (B : PathChartBall X)
    (hpath : ∀ u : unitInterval, u ∈ pathChartBallSet (analyticArcToContinuousMap γ) B)
    (hchart_hasDeriv_right : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt
        (fun u : ℝ => (extChartAt 𝓘(ℂ) B.p) (γ.extend u))
        (deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) B.p) (γ.extend u)) t)
        (Set.Ioi t) t) :
    developingValue x₀ form (analyticArcToContinuousMap γ) =
      canonicalArcIntegral γ form := by
  have hsource : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.extend t ∈ (extChartAt 𝓘(ℂ) B.p).source := by
    intro t ht
    let u : unitInterval := ⟨t, ht⟩
    have hu := hpath u
    simpa [u, analyticArcToContinuousMap_apply, extChartAt_source] using hu.1
  exact developingValue_analyticArcToContinuousMap_eq_canonicalArcIntegral_of_pathChartBall
    x₀ form γ B hpath hchart_hasDeriv_right
    (analyticArc_fixedChartIntegrand_intervalIntegrable γ form B.p hsource)

/-- A continuous loop contained in one chart-coordinate ball has zero
developing value: the one-cell subdivision evaluates to a single primitive
endpoint difference with equal endpoints. -/
theorem developingValue_eq_zero_of_loop_in_pathChartBall
    (x₀ : X) (form : HolomorphicOneForm X) (γ : C(unitInterval, X))
    (B : PathChartBall X)
    (hloop : γ (0 : unitInterval) = γ (1 : unitInterval))
    (himage : ∀ u : unitInterval, u ∈ pathChartBallSet γ B) :
    developingValue x₀ form γ = 0 := by
  classical
  let τ : Fin (1 + 1) → unitInterval := fun i =>
    if i = (0 : Fin (1 + 1)) then 0 else 1
  let S : PathChartBallSubdivision γ :=
    { n := 1
      t := τ
      cellBall := fun _ => B
      zero_eq := by
        simp [τ]
      one_eq := by
        simp [τ, Fin.last]
      monotone_t := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp [τ] at hij ⊢
      cell_subset := by
        intro i u _hu
        exact himage u }
  have hdev :
      developingValue x₀ form γ = developingValueOfSubdivision form γ S :=
    developingValue_eq_developingValueOfSubdivision x₀ form γ S
  have hsub :
      developingValueOfSubdivision form γ S = developingIncrement form γ S 0 := by
    simp [developingValueOfSubdivision, S]
  have hinc : developingIncrement form γ S 0 = 0 := by
    unfold developingIncrement
    simp [S, τ, hloop]
  calc
    developingValue x₀ form γ = developingValueOfSubdivision form γ S := hdev
    _ = developingIncrement form γ S 0 := hsub
    _ = 0 := hinc

end Jacobians.RiemannSurface
