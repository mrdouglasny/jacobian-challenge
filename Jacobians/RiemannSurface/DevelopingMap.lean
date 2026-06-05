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

/-- Refining a single primitive endpoint difference by an intermediate point
telescopes algebraically. This is the local algebra used in the refinement
part of B2 well-definedness. -/
theorem chartPrimitive_endpoint_sub_split (g : ℂ → ℂ) (a m b : ℂ) :
    g b - g a = (g m - g a) + (g b - g m) := by
  abel

end Jacobians.RiemannSurface
