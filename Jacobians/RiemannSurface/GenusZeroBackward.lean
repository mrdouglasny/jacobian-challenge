/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.DevelopingValueAlgebra
import Jacobians.RiemannSurface.HomotopyInvarianceDevelop
import Jacobians.RiemannSurface.ChartSegmentArc
import Jacobians.RiemannSurface.Genus
import Mathlib.Geometry.Manifold.Complex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Simply connected compact Riemann surfaces have genus zero

The backward direction of `AX_genus_eq_zero_iff_homeo` via the developing-map
machinery — **no de Rham theory, no covering spaces**:

* On a simply connected `X`, any two paths between fixed endpoints are
  homotopic (`SimplyConnectedSpace.paths_homotopic`), so by the proven
  homotopy invariance of the developing value
  (`developingValue_homotopy_invariance`) the developing map based at `x₀`,
  `simplyConnectedPrimitive x₀ form`, is a well-defined global function whose
  value along *any* path is path-independent.
* Locally, the developing map is a chart-local holomorphic primitive of the
  form's coefficient plus a constant (`simplyConnectedPrimitive_localRep`),
  hence `MDifferentiable`.
* On a compact connected complex manifold every holomorphic function is
  constant (Mathlib's `MDifferentiable.exists_eq_const_of_compactSpace`), so
  the chart-local primitives are constant, the coefficient vanishes near each
  chart center, and the cotangent cocycle propagates the vanishing to the
  whole coefficient family: `form = 0`.

Main results:

* `holomorphicOneForm_eq_zero_of_simplyConnectedSpace` — every holomorphic
  1-form on a compact simply connected Riemann surface vanishes.
* `genus_eq_zero_of_simplyConnectedSpace` — such a surface has genus `0`.
* `genus_eq_zero_of_homeo_simplyConnected` — genus `0` for any compact
  Riemann surface homeomorphic to a simply connected space.
* `genus_eq_zero_of_homeo_sphere` — the literal backward direction of
  `AX_genus_eq_zero_iff_homeo`, conditional only on the single named input
  `SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`
  (π₁(S²) = 1; not in Mathlib at this pin — the planned van-Kampen
  workstream supplies it).

Note (false-FTC postmortem, pinned issue #82): the well-definedness of the
global primitive is established at the level of homotopy classes through the
developing machinery, never through a single-valued open-path FTC on ℂ.
-/

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.Bridge

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ## The developing value of a path inside a single chart ball -/

/-- The developing value of a path that stays inside a single chart ball is
the endpoint difference of the chosen chart-local primitive. -/
theorem developingValue_eq_primitive_sub_of_single_ball
    (x₀ : X) (form : HolomorphicOneForm X) {a b : X} (γ : Path a b)
    (B : PathChartBall X)
    (hmem : ∀ u : unitInterval,
      u ∈ pathChartBallSet ((γ : Path a b) : C(unitInterval, X)) B) :
    developingValue x₀ form ((γ : Path a b) : C(unitInterval, X)) =
      pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) b) -
        pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) a) := by
  classical
  let S : PathChartBallSubdivision ((γ : Path a b) : C(unitInterval, X)) :=
    { n := 1
      t := ![0, 1]
      cellBall := fun _ => B
      zero_eq := rfl
      one_eq := rfl
      monotone_t := by
        refine Fin.monotone_iff_le_succ.mpr ?_
        intro i
        fin_cases i
        simpa using unitInterval.nonneg'
      cell_subset := fun _ u _ => hmem u }
  rw [developingValue_eq_developingValueOfSubdivision x₀ form _ S]
  have hsum : developingValueOfSubdivision form
      ((γ : Path a b) : C(unitInterval, X)) S =
        developingIncrement form ((γ : Path a b) : C(unitInterval, X)) S 0 := by
    simp [developingValueOfSubdivision]
  rw [hsum]
  have ht0 : S.t (0 : Fin 1).castSucc = 0 := rfl
  have ht1 : S.t (0 : Fin 1).succ = 1 := rfl
  simp only [developingIncrement, ht0, ht1]
  have hγ0 : ((γ : Path a b) : C(unitInterval, X)) (0 : unitInterval) = a := γ.source
  have hγ1 : ((γ : Path a b) : C(unitInterval, X)) (1 : unitInterval) = b := γ.target
  rw [hγ0, hγ1]

/-! ## The canonical chart ball and the in-ball chart segment -/

/-- The canonical chart ball at `p`: the Bridge-layer chart-target ball
(center `chartAt ℂ p p`, radius `chartTargetBallRadius p`), packaged as a
`PathChartBall`. -/
noncomputable def canonicalChartBall (p : X) : PathChartBall X where
  p := p
  c := (chartAt ℂ p) p
  r := chartTargetBallRadius p
  ball_subset_target := chartTargetBall_subset_extChartAt_target p

/-- The chart segment path from `p` to `y ∈ chartBallSource p` stays inside
the canonical chart ball at `p`. -/
theorem chartSegmentPath_mem_pathChartBallSet (p : X) {y : X}
    (hy : y ∈ chartBallSource p) (u : unitInterval) :
    u ∈ pathChartBallSet
      ((chartSegmentPath p hy : Path p y) : C(unitInterval, X))
      (canonicalChartBall p) := by
  have hu : (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 := u.2
  have hext : (chartSegmentPath p hy).extend (u : ℝ) =
      ((chartSegmentPath p hy : Path p y) : C(unitInterval, X)) u := by
    rw [Path.extend_extends _ hu]
  constructor
  · show ((chartSegmentPath p hy : Path p y) : C(unitInterval, X)) u ∈
      (chartAt ℂ (canonicalChartBall p).p).source
    rw [← hext]
    exact chartSegmentPath_extend_mem_chart_source p hy hu
  · show (extChartAt 𝓘(ℂ) (canonicalChartBall p).p)
        (((chartSegmentPath p hy : Path p y) : C(unitInterval, X)) u) ∈
      Metric.ball (canonicalChartBall p).c (canonicalChartBall p).r
    rw [← hext]
    have hcoord := chartSegmentPath_coord_eq p hy hu
    have hball := chartSegment_flatSegment_mem_ball p hy hu
    show (extChartAt 𝓘(ℂ) p) ((chartSegmentPath p hy).extend (u : ℝ)) ∈
      Metric.ball ((chartAt ℂ p) p) (chartTargetBallRadius p)
    have hchart_eq : (extChartAt 𝓘(ℂ) p) ((chartSegmentPath p hy).extend (u : ℝ)) =
        (chartAt ℂ p) ((chartSegmentPath p hy).extend (u : ℝ)) := rfl
    rw [hchart_eq, hcoord]
    exact hball

/-! ## The global primitive on a simply connected surface -/

section SimplyConnected

variable [SimplyConnectedSpace X]

/-- The developing map based at `x₀`: the developing value along the chosen
path from `x₀` to `x`. On a simply connected surface this is independent of
the path (`simplyConnectedPrimitive_eq_developingValue`), making it a global
primitive of `form`. -/
noncomputable def simplyConnectedPrimitive (x₀ : X) (form : HolomorphicOneForm X)
    (x : X) : ℂ :=
  developingValue x₀ form
    ((PathConnectedSpace.somePath x₀ x : Path x₀ x) : C(unitInterval, X))

/-- Path independence: on a simply connected surface, the developing value of
*any* path from `x₀` to `x` computes the developing map. -/
theorem simplyConnectedPrimitive_eq_developingValue (x₀ : X)
    (form : HolomorphicOneForm X) {x : X} (γ : Path x₀ x) :
    simplyConnectedPrimitive x₀ form x =
      developingValue x₀ form ((γ : Path x₀ x) : C(unitInterval, X)) := by
  obtain ⟨H⟩ :=
    SimplyConnectedSpace.paths_homotopic (PathConnectedSpace.somePath x₀ x) γ
  exact developingValue_homotopy_invariance x₀ form H

/-- Local representation: on the canonical chart ball at `p`, the developing
map is the chosen chart-local primitive plus a constant. -/
theorem simplyConnectedPrimitive_localRep (x₀ : X) (form : HolomorphicOneForm X)
    (p : X) {y : X} (hy : y ∈ chartBallSource p) :
    simplyConnectedPrimitive x₀ form y =
      simplyConnectedPrimitive x₀ form p +
        (pathChartBallPrimitive form (canonicalChartBall p)
            ((extChartAt 𝓘(ℂ) p) y) -
          pathChartBallPrimitive form (canonicalChartBall p)
            ((extChartAt 𝓘(ℂ) p) p)) := by
  have hσ := developingValue_eq_primitive_sub_of_single_ball x₀ form
    (chartSegmentPath p hy) (canonicalChartBall p)
    (chartSegmentPath_mem_pathChartBallSet p hy)
  have htrans := devVal_trans x₀ form (PathConnectedSpace.somePath x₀ p)
    (chartSegmentPath p hy)
  have hF := simplyConnectedPrimitive_eq_developingValue x₀ form
    ((PathConnectedSpace.somePath x₀ p).trans (chartSegmentPath p hy))
  rw [hF, htrans, hσ]
  rfl

/-- The developing map on a simply connected surface is holomorphic. -/
theorem mdifferentiable_simplyConnectedPrimitive (x₀ : X)
    (form : HolomorphicOneForm X) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (simplyConnectedPrimitive x₀ form) := by
  intro p
  set g : ℂ → ℂ := pathChartBallPrimitive form (canonicalChartBall p) with hg_def
  -- the eventual local representation
  have hrep : simplyConnectedPrimitive x₀ form =ᶠ[𝓝 p]
      fun y => (simplyConnectedPrimitive x₀ form p - g ((extChartAt 𝓘(ℂ) p) p)) +
        g ((extChartAt 𝓘(ℂ) p) y) := by
    filter_upwards [(isOpen_chartBallSource p).mem_nhds (mem_chartBallSource_self p)]
      with y hy
    rw [simplyConnectedPrimitive_localRep x₀ form p hy]
    ring
  -- the model function is `MDifferentiableAt`
  have hcenter_ball : (extChartAt 𝓘(ℂ) p) p ∈
      Metric.ball (canonicalChartBall p).c (canonicalChartBall p).r :=
    Metric.mem_ball_self (chartTargetBallRadius_pos p)
  have hg_diff : DifferentiableAt ℂ g ((extChartAt 𝓘(ℂ) p) p) :=
    (pathChartBallPrimitive_hasDerivAt form (canonicalChartBall p)
      _ hcenter_ball).differentiableAt
  have hchart : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) p) p :=
    (contMDiffAt_extChartAt (n := ω)).mdifferentiableAt le_top
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun y => g ((extChartAt 𝓘(ℂ) p) y)) p :=
    MDifferentiableAt.comp p hg_diff.mdifferentiableAt hchart
  exact (hcomp.const_add _).congr_of_eventuallyEq hrep

end SimplyConnected

/-! ## The vanishing theorem -/

section Compact

variable [CompactSpace X] [SimplyConnectedSpace X]

/-- **Backward-direction analytic core.** On a compact simply connected
Riemann surface, every holomorphic 1-form is zero.

Route: the developing map is a global holomorphic primitive of the form
(well-defined by homotopy invariance + simple connectivity), constant by
compactness (maximum modulus / Liouville on compact complex manifolds), so
the chart-local primitives are constant, the coefficient vanishes near each
chart center, and the cotangent cocycle propagates the vanishing
everywhere. -/
theorem holomorphicOneForm_eq_zero_of_simplyConnectedSpace
    (form : HolomorphicOneForm X) : form = 0 := by
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  -- the developing map is constant
  haveI : IsManifold 𝓘(ℂ) 1 X :=
    IsManifold.of_le (I := 𝓘(ℂ)) (M := X) (n := ω) (m := 1) (by simp)
  obtain ⟨v, hv⟩ :=
    MDifferentiable.exists_eq_const_of_compactSpace (I := 𝓘(ℂ))
      (mdifferentiable_simplyConnectedPrimitive x₀ form)
  have hvx : ∀ x : X, simplyConnectedPrimitive x₀ form x = v := fun x =>
    congrFun hv x
  -- the coefficient vanishes on each canonical chart ball
  have hcoeff_ball : ∀ p : X, ∀ z ∈ Metric.ball ((chartAt ℂ p) p)
      (chartTargetBallRadius p), form.coeff p z = 0 := by
    intro p z hz
    set g : ℂ → ℂ := pathChartBallPrimitive form (canonicalChartBall p) with hg_def
    -- `g` is constant on the canonical ball
    have hgconst : ∀ w ∈ Metric.ball ((chartAt ℂ p) p) (chartTargetBallRadius p),
        g w = g ((extChartAt 𝓘(ℂ) p) p) := by
      intro w hw
      have hw_target : w ∈ (extChartAt 𝓘(ℂ) p).target :=
        chartTargetBall_subset_extChartAt_target p hw
      set y : X := (extChartAt 𝓘(ℂ) p).symm w with hy_def
      have hy_src : y ∈ (extChartAt 𝓘(ℂ) p).source :=
        (extChartAt 𝓘(ℂ) p).map_target hw_target
      have hyw : (extChartAt 𝓘(ℂ) p) y = w :=
        (extChartAt 𝓘(ℂ) p).right_inv hw_target
      have hyU : y ∈ chartBallSource p := by
        refine ⟨?_, ?_⟩
        · rw [← extChartAt_source 𝓘(ℂ)]
          exact hy_src
        · show (chartAt ℂ p) y ∈ Metric.ball ((chartAt ℂ p) p)
            (chartTargetBallRadius p)
          have : (chartAt ℂ p) y = (extChartAt 𝓘(ℂ) p) y := rfl
          rw [this, hyw]
          exact hw
      have hrep := simplyConnectedPrimitive_localRep x₀ form p hyU
      rw [hvx y, hvx p, hyw] at hrep
      exact sub_eq_zero.mp (self_eq_add_right.mp hrep)
    -- `g` has derivative `form.coeff p z` and is locally constant at `z`
    have hev : g =ᶠ[𝓝 z] fun _ => g ((extChartAt 𝓘(ℂ) p) p) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) hgconst
    have hzero : HasDerivAt g 0 z :=
      (hasDerivAt_const z (g ((extChartAt 𝓘(ℂ) p) p))).congr_of_eventuallyEq hev
    have hderiv : HasDerivAt g (form.coeff p z) z :=
      pathChartBallPrimitive_hasDerivAt form (canonicalChartBall p) z hz
    exact hderiv.unique hzero
  -- propagate by the cotangent cocycle
  obtain ⟨-, hcocy, hoff⟩ := form.2
  apply HolomorphicOneForm.ext_of_coeff
  rw [HolomorphicOneForm.coeff_zero]
  funext x z
  show form.coeff x z = 0
  by_cases hz : z ∈ (extChartAt 𝓘(ℂ) x).target
  · set q : X := (extChartAt 𝓘(ℂ) x).symm z with hq_def
    have hq_src : q ∈ (extChartAt 𝓘(ℂ) q).source := mem_extChartAt_source q
    have h := hcocy x q z hz hq_src
    have hcenter : form.coeff q ((extChartAt 𝓘(ℂ) q) q) = 0 :=
      hcoeff_ball q _ (Metric.mem_ball_self (chartTargetBallRadius_pos q))
    show form.1 x z = 0
    rw [h]
    have : form.1 q ((extChartAt 𝓘(ℂ) q) ((extChartAt 𝓘(ℂ) x).symm z)) =
        form.coeff q ((extChartAt 𝓘(ℂ) q) q) := rfl
    rw [this, hcenter, zero_mul]
  · exact hoff x z hz

/-- On a compact simply connected Riemann surface, the space of holomorphic
1-forms is a subsingleton. -/
theorem subsingleton_holomorphicOneForm_of_simplyConnectedSpace :
    Subsingleton (HolomorphicOneForm X) :=
  subsingleton_of_forall_eq 0 holomorphicOneForm_eq_zero_of_simplyConnectedSpace

end Compact

/-! ## Genus statements -/

/-- A compact simply connected Riemann surface has genus zero. -/
theorem genus_eq_zero_of_simplyConnectedSpace [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [SimplyConnectedSpace X] : genus X = 0 := by
  haveI := subsingleton_holomorphicOneForm_of_simplyConnectedSpace (X := X)
  exact Module.finrank_eq_zero_of_subsingleton

/-- Simple connectivity transports along a homeomorphism. -/
theorem simplyConnectedSpace_of_homeomorph {Y : Type*} [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (h : X ≃ₜ Y) : SimplyConnectedSpace X :=
  h.toHomotopyEquiv.simplyConnectedSpace

/-- A compact Riemann surface homeomorphic to a simply connected space has
genus zero. -/
theorem genus_eq_zero_of_homeo_simplyConnected [T2Space X] [CompactSpace X]
    [ConnectedSpace X] {Y : Type*} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (h : X ≃ₜ Y) : genus X = 0 := by
  haveI : SimplyConnectedSpace X := simplyConnectedSpace_of_homeomorph h
  exact genus_eq_zero_of_simplyConnectedSpace

/-- **Backward direction of `AX_genus_eq_zero_iff_homeo`**, reduced to the
single named topological input `SimplyConnectedSpace S²` (π₁(S²) = 1; not in
Mathlib at this pin — supplied by the planned van-Kampen workstream). A
compact Riemann surface homeomorphic to the 2-sphere has genus zero. -/
theorem genus_eq_zero_of_homeo_sphere [T2Space X] [CompactSpace X]
    [ConnectedSpace X]
    (hS : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    genus X = 0 := by
  obtain ⟨e⟩ := h
  haveI := hS
  exact genus_eq_zero_of_homeo_simplyConnected e

end Jacobians.RiemannSurface
