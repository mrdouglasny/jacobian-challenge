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

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
/-- The Dolbeault port's `pathSpeed` agrees definitionally with the vendored
Kirov `pathSpeed` (both are `fderiv ℝ ((chartAt (γ t)).toFun ∘ γ) t 1`). -/
theorem port_pathSpeed_eq (γ : ℝ → Y) (t : ℝ) :
    _root_.Jacobians.pathSpeed γ t = Jacobians.Vendor.Kirov.pathSpeed γ t := rfl

omit [Nonempty Y] in
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
      change (form.coeff p ((extChartAt 𝓘(ℂ, ℂ) p) (γ t))) •
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

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] in
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
      simp
    have h2 : (⟨min (i.val + 1) S.n, by omega⟩ : Fin (S.n + 1)) = i.succ := by
      ext
      simp
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

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] in
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

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
private lemma mem_chartAt_target_of_extChartAt {p : Y} {z : ℂ}
    (h : z ∈ (extChartAt 𝓘(ℂ) p).target) : z ∈ (chartAt ℂ p).target := by
  simpa [extChartAt_target] using h

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [IsManifold 𝓘(ℂ, ℂ) ω Y] in
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

omit [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] in
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
      = ∫ t in (0 : ℝ)..1,
          (bridgeForm form).toFun (σ t) (Jacobians.Vendor.Kirov.pathSpeed σ t) := rfl
    _ = pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) (σ 1)) -
          pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) (σ 0)) := hFTC
    _ = pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x) -
          pathChartBallPrimitive form B B.c := by
        rw [hσ0, hσ1, hB]

/-! ## Line-integral path algebra for smooth paths (general forms)

The port's `lineIntegral_reverse` is already form-generic; the
`_of_smooth` concatenation wrapper below replays
`periodVec_concat_of_smooth` with an arbitrary form (integrability comes
from `velCont` instead of the basis-form `integrable` field). -/

private theorem port_lineIntegral_concat_of_smooth
    (α : _root_.Jacobians.HolomorphicOneForms Y) {P Q R : Y} {g₁ g₂ : ℝ → Y}
    (h₁ : _root_.Jacobians.IsSmoothPath P Q g₁)
    (h₂ : _root_.Jacobians.IsSmoothPath Q R g₂) :
    _root_.Jacobians.lineIntegral α (_root_.Jacobians.concat g₁ g₂) =
      _root_.Jacobians.lineIntegral α g₁ + _root_.Jacobians.lineIntegral α g₂ := by
  have hint₁ : IntervalIntegrable
      (fun u => α.toFun (g₁ u) (_root_.Jacobians.pathSpeed g₁ u)) MeasureTheory.volume 0 1 :=
    _root_.Jacobians.intervalIntegrable_form_pathSpeed_of_velContinuous α g₁ h₁.velCont
  have hint₂ : IntervalIntegrable
      (fun u => α.toFun (g₂ u) (_root_.Jacobians.pathSpeed g₂ u)) MeasureTheory.volume 0 1 :=
    _root_.Jacobians.intervalIntegrable_form_pathSpeed_of_velContinuous α g₂ h₂.velCont
  have h_ae_neq : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ≠ (1 / 2 : ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  refine _root_.Jacobians.lineIntegral_concat α g₁ g₂ hint₁ hint₂ ?_ ?_ ?_ ?_
  · -- left-half integrability of the concat integrand
    have h_shift : IntervalIntegrable
        (fun t => α.toFun (g₁ (2 * t)) (_root_.Jacobians.pathSpeed g₁ (2 * t)))
        MeasureTheory.volume 0 (1 / 2) := by
      have h_mul := hint₁.comp_mul_left (c := 2)
      convert h_mul using 2; norm_num
    refine (h_shift.const_mul (2 : ℂ)).congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    have h_lt : t < 1 / 2 := lt_of_le_of_ne ht.2 h_neq
    have h_2t_uIcc : 2 * t ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨by linarith [ht.1], by linarith⟩
    have h_ca : _root_.Jacobians.concat g₁ g₂ t = g₁ (2 * t) :=
      _root_.Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
    have h_ps : _root_.Jacobians.pathSpeed (_root_.Jacobians.concat g₁ g₂) t =
        2 * _root_.Jacobians.pathSpeed g₁ (2 * t) :=
      _root_.Jacobians.pathSpeed_concat_left _ _ t h_lt (h₁.diff (2 * t) h_2t_uIcc)
    change (2 : ℂ) * α.toFun (g₁ (2 * t)) (_root_.Jacobians.pathSpeed g₁ (2 * t)) =
      α.toFun (_root_.Jacobians.concat g₁ g₂ t)
        (_root_.Jacobians.pathSpeed (_root_.Jacobians.concat g₁ g₂) t)
    rw [h_ca, h_ps]
    have h_lin := (α.toFun (g₁ (2 * t))).map_smul (2 : ℂ) (_root_.Jacobians.pathSpeed g₁ (2 * t))
    simp only [smul_eq_mul] at h_lin
    exact h_lin.symm
  · -- right-half integrability of the concat integrand
    have h_shift : IntervalIntegrable
        (fun t => α.toFun (g₂ (2 * t)) (_root_.Jacobians.pathSpeed g₂ (2 * t)))
        MeasureTheory.volume 0 (1 / 2) := by
      have h_mul := hint₂.comp_mul_left (c := 2)
      convert h_mul using 2; norm_num
    have h_shift_2 : IntervalIntegrable
        (fun t => α.toFun (g₂ (2 * t - 1)) (_root_.Jacobians.pathSpeed g₂ (2 * t - 1)))
        MeasureTheory.volume (1 / 2) 1 := by
      have h_sub := h_shift.comp_sub_right (1 / 2)
      rw [show (0 : ℝ) + 1 / 2 = 1 / 2 from by norm_num,
        show (1 / 2 : ℝ) + 1 / 2 = 1 from by norm_num] at h_sub
      have h_fn_eq : (fun t : ℝ => α.toFun (g₂ (2 * (t - 1 / 2)))
            (_root_.Jacobians.pathSpeed g₂ (2 * (t - 1 / 2)))) =
          (fun t : ℝ => α.toFun (g₂ (2 * t - 1)) (_root_.Jacobians.pathSpeed g₂ (2 * t - 1))) := by
        funext t; rw [show (2 : ℝ) * (t - 1 / 2) = 2 * t - 1 from by ring]
      rw [h_fn_eq] at h_sub; exact h_sub
    refine (h_shift_2.const_mul (2 : ℂ)).congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t _h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    have h_gt : 1 / 2 < t := ht.1
    have h_2tm1_uIcc : 2 * t - 1 ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨by linarith, by linarith [ht.2]⟩
    have h_ca : _root_.Jacobians.concat g₁ g₂ t = g₂ (2 * t - 1) :=
      _root_.Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
    have h_ps : _root_.Jacobians.pathSpeed (_root_.Jacobians.concat g₁ g₂) t =
        2 * _root_.Jacobians.pathSpeed g₂ (2 * t - 1) :=
      _root_.Jacobians.pathSpeed_concat_right _ _ t h_gt (h₂.diff (2 * t - 1) h_2tm1_uIcc)
    change (2 : ℂ) * α.toFun (g₂ (2 * t - 1)) (_root_.Jacobians.pathSpeed g₂ (2 * t - 1)) =
      α.toFun (_root_.Jacobians.concat g₁ g₂ t)
        (_root_.Jacobians.pathSpeed (_root_.Jacobians.concat g₁ g₂) t)
    rw [h_ca, h_ps]
    have h_lin := 
        (α.toFun (g₂ (2 * t - 1))).map_smul (2 : ℂ) (_root_.Jacobians.pathSpeed g₂ (2 * t - 1))
    simp only [smul_eq_mul] at h_lin
    exact h_lin.symm
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    have h_lt : t < 1 / 2 := lt_of_le_of_ne ht.2 h_neq
    have h_2t_uIcc : 2 * t ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨by linarith [ht.1], by linarith⟩
    have h_ca : _root_.Jacobians.concat g₁ g₂ t = g₁ (2 * t) :=
      _root_.Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
    have h_ps : _root_.Jacobians.pathSpeed (_root_.Jacobians.concat g₁ g₂) t =
        2 * _root_.Jacobians.pathSpeed g₁ (2 * t) :=
      _root_.Jacobians.pathSpeed_concat_left _ _ t h_lt (h₁.diff (2 * t) h_2t_uIcc)
    change α.toFun (_root_.Jacobians.concat g₁ g₂ t)
        (_root_.Jacobians.pathSpeed (_root_.Jacobians.concat g₁ g₂) t) =
      (2 : ℂ) * α.toFun (g₁ (2 * t)) (_root_.Jacobians.pathSpeed g₁ (2 * t))
    rw [h_ca, h_ps]
    have h_lin := (α.toFun (g₁ (2 * t))).map_smul (2 : ℂ) (_root_.Jacobians.pathSpeed g₁ (2 * t))
    simp only [smul_eq_mul] at h_lin
    exact h_lin
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t _h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    have h_gt : 1 / 2 < t := ht.1
    have h_2tm1_uIcc : 2 * t - 1 ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨by linarith, by linarith [ht.2]⟩
    have h_ca : _root_.Jacobians.concat g₁ g₂ t = g₂ (2 * t - 1) :=
      _root_.Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
    have h_ps : _root_.Jacobians.pathSpeed (_root_.Jacobians.concat g₁ g₂) t =
        2 * _root_.Jacobians.pathSpeed g₂ (2 * t - 1) :=
      _root_.Jacobians.pathSpeed_concat_right _ _ t h_gt (h₂.diff (2 * t - 1) h_2tm1_uIcc)
    change α.toFun (_root_.Jacobians.concat g₁ g₂ t)
        (_root_.Jacobians.pathSpeed (_root_.Jacobians.concat g₁ g₂) t) =
      (2 : ℂ) * α.toFun (g₂ (2 * t - 1)) (_root_.Jacobians.pathSpeed g₂ (2 * t - 1))
    rw [h_ca, h_ps]
    have h_lin := 
        (α.toFun (g₂ (2 * t - 1))).map_smul (2 : ℂ) (_root_.Jacobians.pathSpeed g₂ (2 * t - 1))
    simp only [smul_eq_mul] at h_lin
    exact h_lin

private theorem port_lineIntegral_reverse_of_smooth
    (α : _root_.Jacobians.HolomorphicOneForms Y) {P Q : Y} {g : ℝ → Y}
    (h : _root_.Jacobians.IsSmoothPath P Q g) :
    _root_.Jacobians.lineIntegral α (_root_.Jacobians.reverse g) =
      -_root_.Jacobians.lineIntegral α g := by
  refine _root_.Jacobians.lineIntegral_reverse α g ?_
  intro t ht
  have h1t : 1 - t ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht ⊢
    exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
  exact h.diff (1 - t) h1t

/-- The zero-velocity smooth segment `x → B.p → x'` through the anchor of an
anchored chart ball, together with its computed line integral. -/
private theorem exists_segment_through_anchor
    {B : PathChartBall Y} (hB : IsAnchoredBall B) {x x' : Y}
    (hx_src : x ∈ (chartAt ℂ B.p).source)
    (hx_ball : (extChartAt 𝓘(ℂ) B.p) x ∈ Metric.ball B.c B.r)
    (hx'_src : x' ∈ (chartAt ℂ B.p).source)
    (hx'_ball : (extChartAt 𝓘(ℂ) B.p) x' ∈ Metric.ball B.c B.r) :
    ∃ g : ℝ → Y, _root_.Jacobians.IsSmoothPath x x' g ∧
      _root_.Jacobians.pathSpeed g 0 = 0 ∧ _root_.Jacobians.pathSpeed g 1 = 0 ∧
      ∀ form : HolomorphicOneForm Y,
        _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) g =
          pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x') -
            pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x) := by
  classical
  have hu : _root_.Jacobians.HopValid B.p x := hopValid_of_anchored hB hx_src hx_ball
  have hv : _root_.Jacobians.HopValid B.p x' := hopValid_of_anchored hB hx'_src hx'_ball
  obtain ⟨hu_sm, hu_v0, hu_v1⟩ := _root_.Jacobians.zeroVelHop hu
  obtain ⟨hv_sm, hv_v0, hv_v1⟩ := _root_.Jacobians.zeroVelHop hv
  have h0uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
  have h1uIcc : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
  have hrev_sm : _root_.Jacobians.IsSmoothPath x B.p
      (_root_.Jacobians.reverse (_root_.Jacobians.ChartBallPathSmooth B.p x)) := hu_sm.reverse
  have hrev_v0 : _root_.Jacobians.pathSpeed
      (_root_.Jacobians.reverse (_root_.Jacobians.ChartBallPathSmooth B.p x)) 0 = 0 := by
    rw [_root_.Jacobians.pathSpeed_reverse _ 0
        (by rw [show (1 : ℝ)-0 = 1 from by norm_num]; exact hu_sm.diff 1 h1uIcc),
      show (1 : ℝ)-0 = 1 from by norm_num, hu_v1, neg_zero]
  have hrev_v1 : _root_.Jacobians.pathSpeed
      (_root_.Jacobians.reverse (_root_.Jacobians.ChartBallPathSmooth B.p x)) 1 = 0 := by
    rw [_root_.Jacobians.pathSpeed_reverse _ 1
        (by rw [show (1 : ℝ)-1 = 0 from by norm_num]; exact hu_sm.diff 0 h0uIcc),
      show (1 : ℝ)-1 = 0 from by norm_num, hu_v0, neg_zero]
  set g : ℝ → Y := _root_.Jacobians.concat
    (_root_.Jacobians.reverse (_root_.Jacobians.ChartBallPathSmooth B.p x))
    (_root_.Jacobians.ChartBallPathSmooth B.p x') with hg_def
  have hg_sm : _root_.Jacobians.IsSmoothPath x x' g :=
    hrev_sm.concat hv_sm hrev_v1 hv_v0
  refine ⟨g, hg_sm, ?_, ?_, ?_⟩
  · have hd : DifferentiableAt ℝ
        ((chartAt (H := ℂ) ((_root_.Jacobians.reverse
            (_root_.Jacobians.ChartBallPathSmooth B.p x)) (2 * 0))).toFun ∘
          _root_.Jacobians.reverse (_root_.Jacobians.ChartBallPathSmooth B.p x)) (2 * 0) := by
      rw [show (2 : ℝ) * 0 = 0 from by norm_num]; exact hrev_sm.diff 0 h0uIcc
    rw [hg_def, _root_.Jacobians.pathSpeed_concat_left _ _ 0 (by norm_num) hd,
      show (2 : ℝ) * 0 = 0 from by norm_num, hrev_v0, mul_zero]
  · have hd : DifferentiableAt ℝ
        ((chartAt (H := ℂ) ((_root_.Jacobians.ChartBallPathSmooth B.p x') (2 * 1 - 1))).toFun ∘
          _root_.Jacobians.ChartBallPathSmooth B.p x') (2 * 1 - 1) := by
      rw [show (2 : ℝ) * 1 - 1 = 1 from by norm_num]; exact hv_sm.diff 1 h1uIcc
    rw [hg_def, _root_.Jacobians.pathSpeed_concat_right _ _ 1 (by norm_num) hd,
      show (2 : ℝ) * 1 - 1 = 1 from by norm_num, hv_v1, mul_zero]
  · intro form
    have hconcat := port_lineIntegral_concat_of_smooth (bridgeKDFormEquiv form)
      hrev_sm hv_sm
    have hrev := port_lineIntegral_reverse_of_smooth (bridgeKDFormEquiv form) hu_sm
    have hhop_x := lineIntegral_hop form hB hx_src hx_ball
    have hhop_x' := lineIntegral_hop form hB hx'_src hx'_ball
    have hconv : ∀ δ : ℝ → Y, _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) δ =
        Jacobians.Vendor.Kirov.lineIntegral (bridgeForm form) δ :=
      fun δ => port_lineIntegral_bridgeKD form δ
    rw [hg_def] at *
    calc _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form)
          (_root_.Jacobians.concat
            (_root_.Jacobians.reverse (_root_.Jacobians.ChartBallPathSmooth B.p x))
            (_root_.Jacobians.ChartBallPathSmooth B.p x'))
        = _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form)
            (_root_.Jacobians.reverse (_root_.Jacobians.ChartBallPathSmooth B.p x)) +
          _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form)
            (_root_.Jacobians.ChartBallPathSmooth B.p x') := hconcat
      _ = -_root_.Jacobians.lineIntegral (bridgeKDFormEquiv form)
            (_root_.Jacobians.ChartBallPathSmooth B.p x) +
          _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form)
            (_root_.Jacobians.ChartBallPathSmooth B.p x') := by rw [hrev]
      _ = -(pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x) -
            pathChartBallPrimitive form B B.c) +
          (pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x') -
            pathChartBallPrimitive form B B.c) := by
          rw [hconv, hconv, hhop_x, hhop_x']
      _ = pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x') -
            pathChartBallPrimitive form B ((extChartAt 𝓘(ℂ) B.p) x) := by ring

/-! ## The chain glue with computed line integrals -/

/-- n-piece zero-velocity glue carrying the line-integral values: a chain of
zero-velocity smooth segments with known line integrals glues to a single
zero-velocity smooth path whose line integral is the sum. Replays the port's
`exists_zeroVel_smoothPath_aux` with the integral bookkeeping added. -/
private theorem exists_zeroVel_chain_with_integral (v : ℕ → Y)
    (inc : ℕ → HolomorphicOneForm Y → ℂ) :
    ∀ m, (∀ k, k < m → ∃ g, _root_.Jacobians.IsSmoothPath (v k) (v (k + 1)) g ∧
          _root_.Jacobians.pathSpeed g 0 = 0 ∧ _root_.Jacobians.pathSpeed g 1 = 0 ∧
          ∀ form : HolomorphicOneForm Y,
            _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) g = inc k form) →
      ∃ g, _root_.Jacobians.IsSmoothPath (v 0) (v m) g ∧
        _root_.Jacobians.pathSpeed g 0 = 0 ∧ _root_.Jacobians.pathSpeed g 1 = 0 ∧
        ∀ form : HolomorphicOneForm Y,
          _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) g =
            ∑ k ∈ Finset.range m, inc k form := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨fun _ => v 0, _root_.Jacobians.isSmoothPath_const (v 0),
      by rw [_root_.Jacobians.pathSpeed_const], by rw [_root_.Jacobians.pathSpeed_const],
      fun form => ?_⟩
    have hzero : ∀ t : ℝ, (bridgeKDFormEquiv form).toFun ((fun _ => v 0) t)
        (_root_.Jacobians.pathSpeed (fun _ : ℝ => v 0) t) = 0 := by
      intro t
      rw [_root_.Jacobians.pathSpeed_const]
      exact map_zero _
    change (∫ t in (0 : ℝ)..1, (bridgeKDFormEquiv form).toFun ((fun _ => v 0) t)
        (_root_.Jacobians.pathSpeed (fun _ : ℝ => v 0) t)) = _
    simp_rw [hzero]
    simp
  | succ m ih =>
    intro hstep
    obtain ⟨g, hg_sm, hg_v0, hg_v1, hg_val⟩ := ih (fun k hk => hstep k (by omega))
    obtain ⟨g', hg'_sm, hg'_v0, hg'_v1, hg'_val⟩ := hstep m (by omega)
    have h0uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
    have h1uIcc : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
    refine ⟨_root_.Jacobians.concat g g', hg_sm.concat hg'_sm hg_v1 hg'_v0, ?_, ?_, ?_⟩
    · have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (g (2 * 0))).toFun ∘ g) (2 * 0) := by
        rw [show (2 : ℝ) * 0 = 0 from by norm_num]; exact hg_sm.diff 0 h0uIcc
      rw [_root_.Jacobians.pathSpeed_concat_left g g' 0 (by norm_num) hd,
        show (2 : ℝ) * 0 = 0 from by norm_num, hg_v0, mul_zero]
    · have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (g' (2 * 1 - 1))).toFun ∘ g') (2 * 1 - 1)
      := by
        rw [show (2 : ℝ) * 1 - 1 = 1 from by norm_num]; exact hg'_sm.diff 1 h1uIcc
      rw [_root_.Jacobians.pathSpeed_concat_right g g' 1 (by norm_num) hd,
        show (2 : ℝ) * 1 - 1 = 1 from by norm_num, hg'_v1, mul_zero]
    · intro form
      rw [port_lineIntegral_concat_of_smooth (bridgeKDFormEquiv form) hg_sm hg'_sm,
        hg_val form, hg'_val form, Finset.sum_range_succ]

/-! ## The main converse: smooth representative with matching developing values -/

/-- **Smooth-loop representative of a continuous loop, with matching
developing values.** Given any continuous loop `δ` at `y`, there is a closed
`C¹` loop `γ'` (the port's `IsClosedSmoothLoop`) based at `y` whose
moving-chart line integral of every bridged holomorphic 1-form equals the
developing value of `δ`. Construction: anchored chart-ball subdivision of
`δ`; replace each cell by the zero-velocity chart-affine segment through the
cell's anchor; the per-cell line integral is the developing increment by the
hop FTC, and the increments telescope to `developingValue`. (No homotopy
between `δ` and `γ'` is needed: both sides are computed against the same
chart-ball primitives.) -/
theorem exists_isClosedSmoothLoop_lineIntegral_eq_developingValue
    (y : Y) (δ : Path y y) :
    ∃ γ' : ℝ → Y, _root_.Jacobians.IsClosedSmoothLoop γ' ∧ γ' 0 = y ∧
      ∀ form : HolomorphicOneForm Y,
        _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) γ' =
          developingValue y form (δ : C(unitInterval, Y)) := by
  classical
  set γc : C(unitInterval, Y) := (δ : C(unitInterval, Y)) with hγc_def
  obtain ⟨S, hS⟩ := exists_anchored_pathChartBallSubdivision γc
  -- Vertices of the subdivision.
  set v : ℕ → Y := fun k => γc (S.t ⟨min k S.n, by omega⟩) with hv_def
  have hv0 : v 0 = y := by
    have h0 : (⟨min 0 S.n, by omega⟩ : Fin (S.n + 1)) = 0 := by ext; simp
    rw [hv_def]
    simp only [h0, S.zero_eq]
    simp [hγc_def, δ.source]
  have hvn : v S.n = y := by
    have hn : (⟨min S.n S.n, by omega⟩ : Fin (S.n + 1)) = Fin.last S.n := by ext; simp
    rw [hv_def]
    simp only [hn, S.one_eq]
    simp [hγc_def, δ.target]
  -- Per-cell zero-velocity segments through the anchors.
  have hstep : ∀ k (hk : k < S.n), ∃ g, _root_.Jacobians.IsSmoothPath (v k) (v (k + 1)) g ∧
      _root_.Jacobians.pathSpeed g 0 = 0 ∧ _root_.Jacobians.pathSpeed g 1 = 0 ∧
      ∀ form : HolomorphicOneForm Y,
        _root_.Jacobians.lineIntegral (bridgeKDFormEquiv form) g =
          developingIncrement form γc S ⟨k, hk⟩ := by
    intro k hk
    have h1 : (⟨min k S.n, by omega⟩ : Fin (S.n + 1)) = (⟨k, hk⟩ : Fin S.n).castSucc := by
      ext; simp [Nat.min_eq_left hk.le]
    have h2 : (⟨min (k + 1) S.n, by omega⟩ : Fin (S.n + 1)) = (⟨k, hk⟩ : Fin S.n).succ := by
      ext; simp [Nat.min_eq_left hk]
    have hvk : v k = γc (S.t (⟨k, hk⟩ : Fin S.n).castSucc) := by
      rw [hv_def]; simp only [h1]
    have hvk1 : v (k + 1) = γc (S.t (⟨k, hk⟩ : Fin S.n).succ) := by
      rw [hv_def]; simp only [h2]
    have hleft := S.left_mem_pathChartBallSet (⟨k, hk⟩ : Fin S.n)
    have hright := S.right_mem_pathChartBallSet (⟨k, hk⟩ : Fin S.n)
    obtain ⟨g, hg_sm, hg0, hg1, hgval⟩ :=
      exists_segment_through_anchor (hS (⟨k, hk⟩ : Fin S.n))
        (x := γc (S.t (⟨k, hk⟩ : Fin S.n).castSucc))
        (x' := γc (S.t (⟨k, hk⟩ : Fin S.n).succ))
        hleft.1 hleft.2 hright.1 hright.2
    refine ⟨g, ?_, hg0, hg1, fun form => ?_⟩
    · rwa [hvk, hvk1]
    · rw [hgval form]
      rfl
  obtain ⟨g, hg_sm, _hg0, _hg1, hg_val⟩ :=
    exists_zeroVel_chain_with_integral v
      (fun k form => if hk : k < S.n then developingIncrement form γc S ⟨k, hk⟩ else 0)
      S.n
      (fun k hk => by
        obtain ⟨g, h1, h2, h3, h4⟩ := hstep k hk
        exact ⟨g, h1, h2, h3, fun form => by rw [h4 form]; simp [hk]⟩)
  have hg_start : g 0 = y := by rw [hg_sm.start, hv0]
  have hg_end : g 1 = y := by rw [hg_sm.finish, hvn]
  refine ⟨g, ⟨hg_start.trans hg_end.symm, hg_sm.cont, hg_sm.diff, hg_sm.velCont⟩,
    hg_start, fun form => ?_⟩
  rw [hg_val form,
    developingValue_eq_developingValueOfSubdivision y form γc S]
  have hsum : developingValueOfSubdivision form γc S =
      ∑ i : Fin S.n, developingIncrement form γc S i := rfl
  rw [hsum]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => if hk : k < S.n then developingIncrement form γc S ⟨k, hk⟩ else 0) S.n]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.isLt]

end Jacobians.Bridge
