/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.Bridge.KirovDolbeaultTrace
import Jacobians.Bridge.KirovLineIntegral
import Jacobians.RiemannSurface.LoopLattice
import Jacobians.Axioms.PeriodLatticeBase
import KirovDolbeault.PeriodLattice

/-!
# Bridge: developing values vs the Kirov-Dolbeault port's line integrals

The keystone analytic comparison behind the lattice-comparison inclusions
between our `periodLatticeInBasis` (chart-ball developing values over `H1`)
and the Dolbeault port's `truePeriodLattice` (moving-chart `lineIntegral`s
over `IsClosedSmoothLoop`s):

* `port_lineIntegral_bridgeKD` — the port's `lineIntegral` of a bridged form
  is (definitionally) the vendored Kirov line integral of the Montel-bridged
  form, so the entire `Bridge/KirovLineIntegral.lean` chart toolbox applies.
* `lineIntegral_cell_eq_primitive_sub` — **cell FTC**: on a parameter
  interval whose image stays inside one `PathChartBall`, the port line
  integral of a bridged form equals the endpoint difference of the
  chart-ball primitive (`pathChartBallPrimitive`). This is the same local
  computation as `DevelopingBridge.lean` (HI-0), but against the port's
  moving-chart integrand instead of `canonicalIntegrand`.

Idea credit: the lattice-bridge architecture (reducing #31/#191 to the
`truePeriodLattice` ↔ `periodLatticeInBasis` comparison) follows daouid's
closed PR #191; the comparison itself is proven here rather than assumed.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory

namespace Jacobians.Bridge

open Jacobians.RiemannSurface

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The Dolbeault port's `pathSpeed` agrees definitionally with the vendored
Kirov `pathSpeed` (both are `fderiv ℝ ((chartAt (γ t)).toFun ∘ γ) t 1`). -/
theorem port_pathSpeed_eq (γ : ℝ → Y) (t : ℝ) :
    _root_.Jacobians.pathSpeed γ t = Jacobians.Vendor.Kirov.pathSpeed γ t := rfl

/-- The port's `lineIntegral` of a KD-bridged form is the vendored Kirov line
integral of the Montel-bridged form: `kdFormAlign` is the identity on the
common underlying `ContMDiffSection` type, and the two `lineIntegral`s have
identical definitions. -/
theorem port_lineIntegral_bridgeKD (form : HolomorphicOneForm Y) (γ : ℝ → Y) :
    _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) γ =
      Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form) γ := rfl

/-- **Cell FTC.** If `γ : ℝ → Y` is continuous, chart-differentiable on
`[a, b]`, and its image on `[a, b]` stays inside the chart ball `B` (source
membership + coordinates in the metric ball), then the moving-chart line
integral of the bridged form over `[a, b]` is the endpoint difference of the
chart-ball primitive of `form` on `B`. -/
theorem lineIntegral_cell_eq_primitive_sub
    (form : HolomorphicOneForm Y) (B : PathChartBall Y) (γ : ℝ → Y) {a b : ℝ}
    (hab : a ≤ b) (hcont : Continuous γ)
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)
    (hmem : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt ℂ B.p).source ∧
      (extChartAt 𝓘(ℂ) B.p) (γ t) ∈ Metric.ball B.c B.r)
    (hint : IntervalIntegrable
      (fun t => (bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t))
      MeasureTheory.volume a b) :
    ∫ t in a..b, (bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t) =
      pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) (γ b)) -
        pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) (γ a)) := by
  classical
  set p : Y := B.p
  set g : ℂ → ℂ := pathChartBallPrimitive form B with hg_def
  set u : ℝ → ℂ := fun t => (extChartAt 𝓘(ℂ, ℂ) p) (γ t) with hu_def
  -- The composite `F = g ∘ u` has the moving-chart integrand as derivative on `[a, b]`.
  have key : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => g (u s))
        ((bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨hsrc_chart, hball⟩ := hmem t ht
    have hsrc_p : γ t ∈ (extChartAt 𝓘(ℂ, ℂ) p).source := by
      rwa [extChartAt_source]
    have hsrc_self : γ t ∈ (extChartAt 𝓘(ℂ, ℂ) (γ t)).source :=
      mem_extChartAt_source (γ t)
    -- Step 1: differentiability of the fixed-chart coordinate path `u` at `t`.
    have hu_diff : DifferentiableAt ℝ u t := by
      set w := chartAt (H := ℂ) (γ t) with hw_def
      set gX : ℝ → ℂ := w.toFun ∘ γ with hgX_def
      set floc : ℂ → ℂ := fun z => (extChartAt 𝓘(ℂ, ℂ) p) (w.symm z) with hfloc_def
      have hγt_w : γ t ∈ w.source := mem_chart_source ℂ (γ t)
      have hev : ∀ᶠ s in 𝓝 t, γ s ∈ w.source :=
        (hcont.continuousAt).eventually (w.open_source.mem_nhds hγt_w)
      have h_eq : u =ᶠ[𝓝 t] floc ∘ gX := by
        filter_upwards [hev] with s hs
        simp only [hu_def, hfloc_def, hgX_def, Function.comp_apply]
        congr 1
        exact (w.left_inv hs).symm
      have hf_mdiff : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (extChartAt 𝓘(ℂ, ℂ) p) (γ t) := by
        apply mdifferentiableAt_extChartAt
        rwa [← extChartAt_source (I := 𝓘(ℂ, ℂ))]
      have hf_loc_diff_ℂ : DifferentiableAt ℂ floc (gX t) := by
        have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
        rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
        convert h1 using 2
      have hf_loc_diff_ℝ : DifferentiableAt ℝ floc (gX t) :=
        hf_loc_diff_ℂ.restrictScalars ℝ
      have hgX_diff : DifferentiableAt ℝ gX t := hdiff t ht
      exact (Filter.EventuallyEq.differentiableAt_iff h_eq).mpr
        (hf_loc_diff_ℝ.comp t hgX_diff)
    -- Step 2: `u` has derivative `fderiv ℝ u t 1`, which is the chart image of `pathSpeed`.
    have hu_deriv : HasDerivAt u (fderiv ℝ u t 1) t := hu_diff.hasDerivAt
    have hspeed : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) p) (γ t)
        (Jacobians.Vendor.Kirov.pathSpeed γ t) = fderiv ℝ u t 1 := by
      have h := mfderiv_extChartAt_apply_pathSpeed (x := p) (γ := γ) (t := t)
        hcont.continuousAt (hdiff t ht) hsrc_p
      simpa [hu_def] using h
    -- Step 3: primitive has the coefficient as ℂ-derivative at `u t`.
    have hg_deriv : HasDerivAt g (form.coeff p (u t)) (u t) :=
      pathChartBallPrimitive_hasDerivAt form B (u t) hball
    -- Step 4: chain rule (scalar tower ℝ ⊆ ℂ).
    have hF : HasDerivAt (fun s => g (u s))
        ((fderiv ℝ u t 1) • form.coeff p (u t)) t :=
      hg_deriv.scomp t hu_deriv
    -- Step 5: identify the derivative with the moving-chart integrand.
    have hswap : (bridgeForm form).toFun (γ t) = BridgeForm.rawCLM form p (γ t) := by
      change BridgeForm.rawCLM form (γ t) (γ t) = BridgeForm.rawCLM form p (γ t)
      exact BridgeForm.rawCLM_swap_chart form hsrc_self hsrc_p
    have hval : (bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t) =
        form.coeff p (u t) * (fderiv ℝ u t 1) := by
      rw [hswap]
      show (form.coeff p ((extChartAt 𝓘(ℂ, ℂ) p) (γ t))) •
          ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) p) (γ t))
            (Jacobians.Vendor.Kirov.pathSpeed γ t)) =
        form.coeff p (u t) * (fderiv ℝ u t 1)
      rw [hspeed]
      rfl
    rw [hval]
    convert hF using 1
    simp [smul_eq_mul]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt key hint
  simpa [hu_def] using hFTC

/-! ## Developing value = port line integral, for closed `C¹` loops -/

/-- The continuous-map restriction of a loop `γ : ℝ → Y` to the unit
interval. -/
def loopToContinuousMap (γ : ℝ → Y) (hγ : Continuous γ) : C(unitInterval, Y) :=
  ⟨fun u => γ (u : ℝ), hγ.comp continuous_subtype_val⟩

/-- The `Path` view of a closed loop. -/
def loopToPath (γ : ℝ → Y) (hγ : _root_.Jacobians.IsClosedSmoothLoop γ) :
    Path (γ 0) (γ 0) where
  toFun u := γ (u : ℝ)
  continuous_toFun := hγ.cont.comp continuous_subtype_val
  source' := by simp
  target' := by simpa using hγ.closed.symm

@[simp] theorem loopToPath_coe (γ : ℝ → Y) (hγ : _root_.Jacobians.IsClosedSmoothLoop γ) :
    ((loopToPath γ hγ : Path (γ 0) (γ 0)) : C(unitInterval, Y)) =
      loopToContinuousMap γ hγ.cont := rfl

/-- **Developing value = moving-chart line integral** for a closed `C¹` loop
(the port's `IsClosedSmoothLoop`): subdivide by chart balls, apply the cell
FTC on each cell, and compare with the developing increments. -/
theorem developingValue_eq_lineIntegral_of_isClosedSmoothLoop
    (form : HolomorphicOneForm Y) (γ : ℝ → Y)
    (hγ : _root_.Jacobians.IsClosedSmoothLoop γ) (x₀ : Y) :
    developingValue x₀ form (loopToContinuousMap γ hγ.cont) =
      Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form) γ := by
  classical
  set γc : C(unitInterval, Y) := loopToContinuousMap γ hγ.cont with hγc_def
  set S := chosenPathChartBallSubdivision γc with hS_def
  set f : ℝ → ℂ := fun t =>
    (bridgeForm form).toFun (γ t) (Jacobians.Vendor.Kirov.pathSpeed γ t) with hf_def
  -- Global integrability of the moving-chart integrand from `velCont`.
  have hint01 : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    have h := _root_.Jacobians.intervalIntegrable_form_pathSpeed_of_velContinuous
      (bridgeKDFormEquiv form) γ hγ.velCont
    exact h
  -- The subdivision points as a real-valued sequence.
  set A : ℕ → ℝ := fun k => (S.t ⟨min k S.n, by omega⟩ : ℝ) with hA_def
  have hA_mono : ∀ j k, j ≤ k → A j ≤ A k := by
    intro j k hjk
    exact S.monotone_t (by simp [Fin.le_def]; omega)
  have hA_mem : ∀ k, A k ∈ Set.Icc (0 : ℝ) 1 := fun k => (S.t _).2
  have hA0 : A 0 = 0 := by
    have : (⟨min 0 S.n, by omega⟩ : Fin (S.n + 1)) = 0 := by
      ext; simp
    rw [hA_def]
    simp only [this, S.zero_eq]
    rfl
  have hAn : A S.n = 1 := by
    have : (⟨min S.n S.n, by omega⟩ : Fin (S.n + 1)) = Fin.last S.n := by
      ext; simp
    rw [hA_def]
    simp only [this, S.one_eq]
    rfl
  -- Cell-wise integrability.
  have hint_cell : ∀ k < S.n, IntervalIntegrable f MeasureTheory.volume (A k) (A (k + 1)) := by
    intro k hk
    refine hint01.mono_set ?_
    rw [Set.uIcc_of_le (hA_mono k (k + 1) (by omega)), Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc (hA_mem k).1 (hA_mem (k + 1)).2
  -- Per-cell FTC.
  have hcell : ∀ i : Fin S.n,
      (∫ t in A i.val..A (i.val + 1), f t) = developingIncrement form γc S i := by
    intro i
    have h1 : (⟨min i.val S.n, by omega⟩ : Fin (S.n + 1)) = i.castSucc := by
      ext
      simp [Nat.min_eq_left i.isLt.le]
    have h2 : (⟨min (i.val + 1) S.n, by omega⟩ : Fin (S.n + 1)) = i.succ := by
      ext
      simp [Nat.min_eq_left i.isLt]
    have hAi : A i.val = (S.t i.castSucc : ℝ) := by
      simp only [hA_def, h1]
    have hAi1 : A (i.val + 1) = (S.t i.succ : ℝ) := by
      simp only [hA_def, h2]
    set a : ℝ := (S.t i.castSucc : ℝ)
    set b : ℝ := (S.t i.succ : ℝ)
    have hab : a ≤ b := S.monotone_t (Fin.castSucc_le_succ i)
    have h01 : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 :=
      Set.Icc_subset_Icc (S.t i.castSucc).2.1 (S.t i.succ).2.2
    have hmem : ∀ t ∈ Set.Icc a b, γ t ∈ (chartAt ℂ (S.cellBall i).p).source ∧
        (extChartAt 𝓘(ℂ) (S.cellBall i).p) (γ t) ∈
          Metric.ball (S.cellBall i).c (S.cellBall i).r := by
      intro t ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := h01 ht
      set u : unitInterval := ⟨t, ht01⟩ with hu_def
      have hu_cell : u ∈ Set.Icc (S.t i.castSucc) (S.t i.succ) := by
        constructor
        · exact Subtype.coe_le_coe.mp ht.1
        · exact Subtype.coe_le_coe.mp ht.2
      have huB := S.cell_subset i hu_cell
      exact huB
    have hdiff : ∀ t ∈ Set.Icc a b,
        DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t := by
      intro t ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := h01 ht
      exact hγ.diff t (by rwa [Set.uIcc_of_le zero_le_one])
    have hintab : IntervalIntegrable f MeasureTheory.volume a b := by
      have := hint_cell i.val i.isLt
      rwa [hAi, hAi1] at this
    have hFTC := lineIntegral_cell_eq_primitive_sub form (S.cellBall i) γ hab
      hγ.cont hdiff hmem hintab
    rw [hAi, hAi1]
    rw [hFTC]
    rfl
  -- Assemble: developing value = sum of increments = sum of cell integrals
  -- = the full line integral.
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := MeasureTheory.volume) (a := A) (f := f) hint_cell
  calc developingValue x₀ form γc
      = developingValueOfSubdivision form γc S :=
        developingValue_eq_developingValueOfSubdivision x₀ form γc S
    _ = ∑ i : Fin S.n, developingIncrement form γc S i := rfl
    _ = ∑ i : Fin S.n, ∫ t in A i.val..A (i.val + 1), f t := by
        refine Finset.sum_congr rfl (fun i _ => (hcell i).symm)
    _ = ∑ k ∈ Finset.range S.n, ∫ t in A k..A (k + 1), f t :=
        Fin.sum_univ_eq_sum_range (fun k => ∫ t in A k..A (k + 1), f t) S.n
    _ = ∫ t in A 0..A S.n, f t := hsum
    _ = ∫ t in (0 : ℝ)..1, f t := by rw [hA0, hAn]
    _ = Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form) γ := rfl

/-! ## Anchored chart-ball subdivisions

For the converse direction (a smooth representative of a continuous loop)
we need subdivisions whose chart balls are *anchored*: the ball's center is
the chart image of its base point, so that chart-affine hops through the
base point stay inside the ball. The generic cover construction
(`pathChartBallSet_cover`) already produces anchored balls. -/

/-- A `PathChartBall` whose center is the chart image of its base point. -/
def IsAnchoredBall (B : PathChartBall Y) : Prop :=
  B.c = extChartAt 𝓘(ℂ) B.p B.p

/-- Every continuous path admits a chart-ball subdivision with anchored
balls (same Lebesgue-cover construction as
`exists_pathChartBallSubdivision`, restricted to the anchored sub-family). -/
theorem exists_anchored_pathChartBallSubdivision (γ : C(unitInterval, Y)) :
    ∃ S : Jacobians.RiemannSurface.PathChartBallSubdivision γ,
      ∀ i, IsAnchoredBall (S.cellBall i) := by
  classical
  have hopen : ∀ B : {B : PathChartBall Y // IsAnchoredBall B},
      IsOpen (pathChartBallSet γ B.val) := fun B => isOpen_pathChartBallSet γ B.val
  have hcover : Set.univ ⊆
      ⋃ B : {B : PathChartBall Y // IsAnchoredBall B}, pathChartBallSet γ B.val := by
    intro u _hu
    let p : Y := γ u
    let z : ℂ := (extChartAt 𝓘(ℂ) p) p
    have hz_target : z ∈ (extChartAt 𝓘(ℂ) p).target := by
      simp [z, p]
    obtain ⟨r, hr_pos, hr_sub⟩ :=
      (Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := 𝓘(ℂ)) p)) z hz_target
    let B : PathChartBall Y :=
      { p := p, c := z, r := r, ball_subset_target := hr_sub }
    refine Set.mem_iUnion.2 ⟨⟨B, rfl⟩, ?_, ?_⟩
    · simp [B, p]
    · exact (show (extChartAt 𝓘(ℂ) B.p) (γ u) ∈ Metric.ball B.c B.r by
        simpa [B, p, z] using (Metric.mem_ball_self (x := z) hr_pos))
  obtain ⟨t, ht_zero, ht_mono, ⟨k, ht_eventually_one⟩, ht_sub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun B : {B : PathChartBall Y // IsAnchoredBall B} =>
        pathChartBallSet γ B.val) hopen hcover
  let N : ℕ := k + 1
  let cb : Fin N → {B : PathChartBall Y // IsAnchoredBall B} :=
    fun i => Classical.choose (ht_sub i.val)
  refine ⟨⟨N, (fun i : Fin (N + 1) => t i.val), fun i => (cb i).val,
    ?_, ?_, ?_, ?_⟩, fun i => (cb i).2⟩
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

/-! ## Chart-ball hops with computed line integrals -/

private lemma mem_chartAt_target_of_extChartAt {p : Y} {z : ℂ}
    (h : z ∈ (extChartAt 𝓘(ℂ) p).target) : z ∈ (chartAt ℂ p).target := by
  simpa [extChartAt_target] using h

private lemma extChartAt_apply_eq_chartAt (p x : Y) :
    (extChartAt 𝓘(ℂ) p) x = (chartAt ℂ p) x := rfl

/-- Membership of the affine segment from the (anchored) center to a ball
point: convexity of the metric ball. -/
private lemma affine_seg_mem_ball {c w : ℂ} {r : ℝ} (hw : w ∈ Metric.ball c r)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 - (s : ℂ)) * c + (s : ℂ) * w ∈ Metric.ball c r := by
  have hdist : dist ((1 - (s : ℂ)) * c + (s : ℂ) * w) c = s * dist w c := by
    rw [dist_eq_norm, dist_eq_norm]
    have : (1 - (s : ℂ)) * c + (s : ℂ) * w - c = (s : ℂ) * (w - c) := by ring
    rw [this, norm_mul]
    simp [abs_of_nonneg hs.1]
  rw [Metric.mem_ball, hdist]
  calc s * dist w c ≤ 1 * dist w c := by
        have := dist_nonneg (x := w) (y := c)
        nlinarith [hs.2]
    _ = dist w c := one_mul _
    _ < r := Metric.mem_ball.mp hw

/-- A point of an anchored ball is a valid hop target from the ball's base
point. -/
private lemma hopValid_of_anchored {B : PathChartBall Y} (hB : IsAnchoredBall B)
    {x : Y} (hx_src : x ∈ (chartAt ℂ B.p).source)
    (hx_ball : (extChartAt 𝓘(ℂ) B.p) x ∈ Metric.ball B.c B.r) :
    _root_.Jacobians.HopValid B.p x := by
  refine ⟨hx_src, ?_⟩
  intro s hs
  have hcenter : (chartAt ℂ B.p) B.p = B.c := by
    rw [← extChartAt_apply_eq_chartAt]
    exact hB.symm
  have hx_coord : (chartAt ℂ B.p) x ∈ Metric.ball B.c B.r := hx_ball
  have hmem : (1 - (s : ℂ)) * B.c + (s : ℂ) * (chartAt ℂ B.p) x ∈
      Metric.ball B.c B.r := affine_seg_mem_ball hx_coord hs
  rw [hcenter]
  exact mem_chartAt_target_of_extChartAt (B.ball_subset_target hmem)

/-- **Hop FTC.** The line integral of a bridged form along the smoothstep
chart-ball hop from the (anchored) base point to a ball point is the
primitive increment from the center to the point's coordinates. -/
private lemma lineIntegral_hop (form : HolomorphicOneForm Y)
    {B : PathChartBall Y} (hB : IsAnchoredBall B)
    {x : Y} (hx_src : x ∈ (chartAt ℂ B.p).source)
    (hx_ball : (extChartAt 𝓘(ℂ) B.p) x ∈ Metric.ball B.c B.r) :
    Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form)
        (_root_.Jacobians.ChartBallPathSmooth B.p x) =
      pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x) -
        pathChartBallPrimitive form B B.c := by
  classical
  set σ : ℝ → Y := _root_.Jacobians.ChartBallPathSmooth B.p x with hσ_def
  have hop := hopValid_of_anchored hB hx_src hx_ball
  have hsm : _root_.Jacobians.IsSmoothPath B.p x σ :=
    _root_.Jacobians.OfCurveSkeleton.isSmoothPath_ChartBallPathSmooth B.p x hx_src hop.2
  have hcenter : (chartAt ℂ B.p) B.p = B.c := by
    rw [← extChartAt_apply_eq_chartAt]
    exact hB.symm
  -- The hop stays in the chart ball.
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, σ t ∈ (chartAt ℂ B.p).source ∧
      (extChartAt 𝓘(ℂ) B.p) (σ t) ∈ Metric.ball B.c B.r := by
    intro t _ht
    set s : ℝ := _root_.Jacobians.smoothStep01 t with hs_def
    have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := _root_.Jacobians.smoothStep01_mem_unit t
    have hw : (1 - (s : ℂ)) * (chartAt ℂ B.p) B.p + (s : ℂ) * (chartAt ℂ B.p) x ∈
        Metric.ball B.c B.r := by
      rw [hcenter]
      exact affine_seg_mem_ball hx_ball hs01
    have hw_target : (1 - (s : ℂ)) * (chartAt ℂ B.p) B.p + (s : ℂ) * (chartAt ℂ B.p) x ∈
        (chartAt ℂ B.p).target :=
      mem_chartAt_target_of_extChartAt (B.ball_subset_target hw)
    have hσt : σ t = (chartAt ℂ B.p).symm
        ((1 - (s : ℂ)) * (chartAt ℂ B.p) B.p + (s : ℂ) * (chartAt ℂ B.p) x) := rfl
    constructor
    · rw [hσt]
      exact (chartAt ℂ B.p).map_target hw_target
    · rw [hσt, extChartAt_apply_eq_chartAt, (chartAt ℂ B.p).right_inv hw_target]
      exact hw
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (σ t)).toFun ∘ σ) t := by
    intro t ht
    exact hsm.diff t (by rwa [Set.uIcc_of_le zero_le_one])
  have hint : IntervalIntegrable
      (fun t => (bridgeForm form).toFun (σ t) (Jacobians.Vendor.Kirov.pathSpeed σ t))
      MeasureTheory.volume 0 1 :=
    _root_.Jacobians.intervalIntegrable_form_pathSpeed_of_velContinuous
      (bridgeKDFormEquiv form) σ hsm.velCont
  have hFTC := lineIntegral_cell_eq_primitive_sub form B σ zero_le_one
    hsm.cont hdiff hmem hint
  have hσ0 : σ 0 = B.p := hsm.start
  have hσ1 : σ 1 = x := hsm.finish
  calc Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form) σ
      = ∫ t in (0:ℝ)..1,
          (bridgeForm form).toFun (σ t) (Jacobians.Vendor.Kirov.pathSpeed σ t) := rfl
    _ = pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) (σ 1)) -
          pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) (σ 0)) := hFTC
    _ = pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x) -
          pathChartBallPrimitive form B B.c := by
        rw [hσ0, hσ1, hB]

end Jacobians.Bridge
