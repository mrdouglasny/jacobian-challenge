/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.MeroVanish

/-!
# R6c — the global-correction evaluation engine (non-isolated marked point)

The W1 piece of the Čech↔tail dictionary route (`docs/planning/DICT_ROUTE.md`): the
evaluation of the fine-sheaf residue functional on a coboundary whose marked simple-pole
point `b` may lie in SEVERAL cover sets — the case the marked engine
(`resFunctional_eq_neg_residue_of_mero_coboundary`) excludes via `MLIsolated`.

## The global-cutoff-subtraction mechanism (discovery D3)

A presentation `h` of the cocycle `w` (`w i j = h j − h i` on overlaps) is replaced by
`h̃ := h − (H, H, …, H)` for a GLOBAL scalar `H` (the cutoff `θ·h_{j₀}` in the
application): constant cochains have zero coboundary, so `w` is unchanged, while at `b`
the matching principal parts cancel and `h̃` is SMOOTH there.  The price: `h̃` is no
longer holomorphic where `dθ ≠ 0`; the discrepancy `∂̄h̃_i = −∂̄H` is COMMON to all
charts.  Consequences for the R5/R6 engine skeleton:

* curvature relocation + reinsertion kill: UNCHANGED (they consume only smoothness);
* the per-chart Stokes term dies for EVERY chart (vanish-engine style — the marked-chart
  R0 evaluation disappears, and with it the isolation requirement);
* the Leibniz split gains ONE explicit term per chart, `−∫ ρ̃_j·(∂̄H̃_j)·g̃_j`
  (`corrFam`, with the junk value at the marked coordinate repaired to `0`);
* the correction terms form a `(1,1)` family (`isOneOneCoeff_corrFam`), collapse by the
  R4 relocation lemma + `∑ρ ≡ 1` to a single chart-`j₀` integral (`corrC`), and are
  evaluated by the GENERAL R0 atom `integral_dbar_smearedSimplePole` (no local constancy
  of the weight is needed — discovery D1) to `−π·r`.

## Main declarations

* `corrFam` / `corrC` — the repaired correction family and its chart-`j₀` planar cut.
* `isOneOneCoeff_corrFam` — the correction family is `(1,1)`.
* `integral_pouCoeff_glueCoeff_corr_split` — the Leibniz split with the explicit
  correction term.
* `sum_integral_pouCoeff_corrFam` — the relocation collapse `∑_j ∫ρ̃_j·corr_j = ∫corrC`.
* `integral_corrC_eq_neg_pi_residue` — the final R0 evaluation `∫corrC = −π·r`.
* `resFunctional_eq_neg_residue_of_global_correction` — **the headline**:
  `resFunctional 𝔇 t = −r` with NO isolation hypothesis on the marked point.
-/

open Complex Filter MeasureTheory
open scoped Manifold ContDiff Topology Classical Real
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.FineResidue

open Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

variable {𝔇 : ChartDiskCover X}

/-! ### The repaired correction family -/

/-- **The repaired correction family** `∂̄H̃·g`: the chart-`i` read of `∂̄H` against the
`dz`-slot, with the junk value at the marked coordinate `chartMap i b` replaced by `0`
(`∂̄` of the singular read is undefined there; on a punctured neighbourhood it vanishes
honestly when `H` is holomorphic near `b` off `b`). -/
noncomputable def corrFam (𝔇 : ChartDiskCover X) (H : X → ℂ)
    (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (b : X) : 𝔇.toFiniteCover.ι → ℂ → ℂ :=
  fun i z =>
    if b ∈ (𝔇.U i : Set X) ∧ z = chartMap 𝔇 i b then 0
    else DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)) z * g i z

theorem corrFam_apply (H : X → ℂ) (g : 𝔇.toFiniteCover.ι → ℂ → ℂ) (b : X)
    (i : 𝔇.toFiniteCover.ι) (z : ℂ) :
    corrFam 𝔇 H g b i z
      = if b ∈ (𝔇.U i : Set X) ∧ z = chartMap 𝔇 i b then 0
        else DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)) z * g i z := rfl

section Clearances

variable {H : X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} {j₀ : 𝔇.toFiniteCover.ι} {b : X}

/-- A global scalar vanishing near `x` has chart-`i` read vanishing near the coordinate. -/
theorem hread_eventually_zero {i : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i : Set X)) (h0 : ∀ᶠ y in 𝓝 x, H y = 0) :
    ∀ᶠ ζ in 𝓝 (chartMap 𝔇 i x), H ((chartAt ℂ (𝔇.center i)).symm ζ) = 0 := by
  have hsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hx
  have hzt : chartMap 𝔇 i x ∈ (chartAt ℂ (𝔇.center i)).target :=
    (chartAt ℂ (𝔇.center i)).map_source hsrc
  have hcont : ContinuousAt (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) :=
    (chartAt ℂ (𝔇.center i)).continuousAt_symm hzt
  have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
    (chartAt ℂ (𝔇.center i)).left_inv hsrc
  have h0' : ∀ᶠ y in 𝓝 ((chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x)), H y = 0 := by
    rw [hli]
    exact h0
  exact hcont.eventually h0'

/-- `∂̄` of the chart read vanishes near the coordinate of a point where `H` locally
vanishes. -/
theorem dbar_hread_eventually_zero {i : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i : Set X)) (h0 : ∀ᶠ y in 𝓝 x, H y = 0) :
    ∀ᶠ ζ in 𝓝 (chartMap 𝔇 i x),
      DbarDisk.dbar (fun ξ => H ((chartAt ℂ (𝔇.center i)).symm ξ)) ζ = 0 := by
  filter_upwards [(hread_eventually_zero hx h0).eventually_nhds] with ζ hζ
  exact dbar_eq_zero_of_eventuallyEq_zero hζ

/-- **The cross-chart holomorphy transport**: if the chart-`j₀` read of `H` is
ℂ-differentiable at the coordinates of punctured-neighbourhood points of `b`, then in
EVERY chart containing `b` the read's `∂̄` vanishes on a punctured neighbourhood of the
marked coordinate (relocate through the analytic transition). -/
theorem dbar_hread_eventually_zero_near_marked (hb : b ∈ (𝔇.U j₀ : Set X))
    {i : 𝔇.toFiniteCover.ι} (hbi : b ∈ (𝔇.U i : Set X))
    (hH0 : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x)) :
    ∀ᶠ z in 𝓝[≠] (chartMap 𝔇 i b),
      DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)) z = 0 := by
  have hbsrc : b ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hbi
  have hzt : chartMap 𝔇 i b ∈ (chartAt ℂ (𝔇.center i)).target :=
    (chartAt ℂ (𝔇.center i)).map_source hbsrc
  have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i b) = b :=
    (chartAt ℂ (𝔇.center i)).left_inv hbsrc
  have hctend : Tendsto (chartAt ℂ (𝔇.center i)).symm
      (𝓝[≠] (chartMap 𝔇 i b)) (𝓝[≠] b) := by
    have h := (chartAt ℂ (𝔇.center i)).symm.tendsto_nhdsNE (x := chartMap 𝔇 i b)
      (by simpa using hzt)
    rwa [hli] at h
  have hov : ∀ᶠ x in 𝓝[≠] b, x ∈ ((𝔇.U i ⊓ 𝔇.U j₀ : Opens X) : Set X) :=
    eventually_nhdsWithin_of_eventually_nhds
      ((𝔇.U i ⊓ 𝔇.U j₀ : Opens X).isOpen.mem_nhds ⟨hbi, hb⟩)
  have hri : ∀ᶠ z in 𝓝[≠] (chartMap 𝔇 i b),
      chartMap 𝔇 i ((chartAt ℂ (𝔇.center i)).symm z) = z := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    filter_upwards [(chartAt ℂ (𝔇.center i)).open_target.mem_nhds hzt] with z hz
    exact (chartAt ℂ (𝔇.center i)).right_inv hz
  filter_upwards [hctend.eventually hH0, hctend.eventually hov, hri] with z hdiff hxov hzri
  set x := (chartAt ℂ (𝔇.center i)).symm z with hxdef
  -- the chart-`i` read agrees near `z` with the chart-`j₀` read through the transition
  have hev : (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ))
      =ᶠ[𝓝 z] fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm (transitionMap 𝔇 i j₀ ζ)) := by
    have h1 := symm_transitionMap_eventuallyEq 𝔇 (j := i) (k := j₀) (x := x) hxov
    rw [hzri] at h1
    filter_upwards [h1] with ζ hζ
    rw [hζ]
  have htr : AnalyticAt ℂ (transitionMap 𝔇 i j₀) z := by
    have h1 := transitionMap_analyticAt 𝔇 (x := x) hxov.1 hxov.2
    rwa [hzri] at h1
  have htc : transitionMap 𝔇 i j₀ z = chartMap 𝔇 j₀ x := by
    have h1 := transitionMap_chartMap 𝔇 (x := x) (k := j₀) hxov.1
    rwa [hzri] at h1
  have hcomp : DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm (transitionMap 𝔇 i j₀ ζ))) z := by
    have hbase : DifferentiableAt ℂ (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ))
        (transitionMap 𝔇 i j₀ z) := by
      rw [htc]
      exact hdiff
    exact hbase.comp z htr.differentiableAt
  have hdz : DifferentiableAt ℂ (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)) z :=
    hcomp.congr_of_eventuallyEq hev
  exact DbarDisk.dbar_eq_zero_of_differentiableAt hdz

/-- The correction family vanishes on a FULL neighbourhood of the marked coordinate
(punctured holomorphy + the repair at the point). -/
theorem corrFam_eventually_zero_near_marked (hb : b ∈ (𝔇.U j₀ : Set X))
    {i : 𝔇.toFiniteCover.ι} (hbi : b ∈ (𝔇.U i : Set X))
    (hH0 : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x)) :
    ∀ᶠ z in 𝓝 (chartMap 𝔇 i b), corrFam 𝔇 H g b i z = 0 := by
  have h1 := dbar_hread_eventually_zero_near_marked hb hbi hH0
  rw [eventually_nhdsWithin_iff] at h1
  filter_upwards [h1] with z hz
  by_cases hzα : z = chartMap 𝔇 i b
  · rw [corrFam_apply, if_pos ⟨hbi, hzα⟩]
  · rw [corrFam_apply, if_neg (fun hc => hzα hc.2), hz (by simpa using hzα), zero_mul]

/-- The correction family vanishes near the coordinates of points off `tsupport H`. -/
theorem corrFam_eventually_zero_of_notMem_tsupport {i : 𝔇.toFiniteCover.ι} {x : X}
    (hx : x ∈ (𝔇.U i : Set X)) (hxs : x ∉ tsupport H) :
    ∀ᶠ z in 𝓝 (chartMap 𝔇 i x), corrFam 𝔇 H g b i z = 0 := by
  have h0 : ∀ᶠ y in 𝓝 x, H y = 0 := by
    filter_upwards [(isClosed_tsupport H).isOpen_compl.mem_nhds hxs] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  filter_upwards [dbar_hread_eventually_zero hx h0] with z hz
  rw [corrFam_apply]
  split_ifs with hc
  · rfl
  · rw [hz, zero_mul]

/-- **The correction family is a `(1,1)` chart-coefficient family**: smooth at chart
points (locally zero near the marked coordinate; `∂̄` of a smooth read times the analytic
slot elsewhere) and satisfying the `normSq φ′` overlap law (`∂̄` contributes `conj φ′` by
the chain rule, the slot contributes `φ′`). -/
theorem isOneOneCoeff_corrFam (hb : b ∈ (𝔇.U j₀ : Set X))
    (hHsm : ∀ x : X, x ≠ b → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) H x)
    (hH0 : ∀ᶠ x in 𝓝[≠] b, DifferentiableAt ℂ
      (fun ζ => H ((chartAt ℂ (𝔇.center j₀)).symm ζ)) (chartMap 𝔇 j₀ x))
    (hg : IsOneZeroCoeff 𝔇 g) :
    IsOneOneCoeff 𝔇 (corrFam 𝔇 H g b) := by
  have hreadCD : ∀ (i : 𝔇.toFiniteCover.ι) (x : X), x ∈ (𝔇.U i : Set X) → x ≠ b →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ))
        (chartMap 𝔇 i x) := by
    intro i x hx hxb
    have hsrc : x ∈ (chartAt ℂ (𝔇.center i)).source := mem_chartSource_of_mem_U 𝔇 hx
    have hli : (chartAt ℂ (𝔇.center i)).symm (chartMap 𝔇 i x) = x :=
      (chartAt ℂ (𝔇.center i)).left_inv hsrc
    refine contDiffAt_chartSymmRead_of_contMDiffAt
      ((chartAt ℂ (𝔇.center i)).map_source hsrc) ?_
    rw [hli]
    exact hHsm x hxb
  constructor
  · -- smoothness at chart points
    intro i x hx
    by_cases hxb : x = b
    · subst hxb
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
        (corrFam_eventually_zero_near_marked hb hx hH0)
    · have hdb : ContDiffAt ℝ (⊤ : ℕ∞)
          (DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center i)).symm ζ)))
          (chartMap 𝔇 i x) :=
        ChartDiskCover.contDiffAt_dbar_chartDisk (hreadCD i x hx hxb)
      have hgc : ContDiffAt ℝ (⊤ : ℕ∞) (g i) (chartMap 𝔇 i x) :=
        ((hg.1 i x hx).restrictScalars (𝕜 := ℝ)).contDiffAt
      refine (hdb.mul hgc).congr_of_eventuallyEq ?_
      by_cases hbi : b ∈ (𝔇.U i : Set X)
      · have hne : chartMap 𝔇 i x ≠ chartMap 𝔇 i b := fun hc =>
          hxb ((chartAt ℂ (𝔇.center i)).injOn (mem_chartSource_of_mem_U 𝔇 hx)
            (mem_chartSource_of_mem_U 𝔇 hbi) hc)
        filter_upwards [isOpen_compl_singleton.mem_nhds
          (by simpa using hne : chartMap 𝔇 i x ∈ ({chartMap 𝔇 i b}ᶜ : Set ℂ))] with z hz
        rw [corrFam_apply, if_neg (fun hc => (by simpa using hz : z ≠ chartMap 𝔇 i b) hc.2)]
      · filter_upwards with z
        rw [corrFam_apply, if_neg (fun hc => hbi hc.1)]
  · -- the overlap law
    intro p q x hx
    have hxp : x ∈ (𝔇.U p : Set X) := hx.1
    have hxq : x ∈ (𝔇.U q : Set X) := hx.2
    have htend : Tendsto (transitionMap 𝔇 p q) (𝓝 (chartMap 𝔇 p x))
        (𝓝 (chartMap 𝔇 q x)) := by
      have hc := (transitionMap_analyticAt 𝔇 hxp hxq).continuousAt
      rwa [ContinuousAt, transitionMap_chartMap 𝔇 hxp] at hc
    by_cases hxb : x = b
    · -- both sides vanish near the respective marked coordinates
      subst hxb
      have h1 := corrFam_eventually_zero_near_marked (g := g) hb hxp hH0
      have h2 := corrFam_eventually_zero_near_marked (g := g) hb hxq hH0
      unfold OneOneLawAt
      filter_upwards [h1, htend.eventually h2] with z hz1 hz2
      rw [hz1, hz2, zero_mul]
    · -- generic law via the `∂̄` chain rule and the slot law
      have hzqt : chartMap 𝔇 q x ∈ (chartAt ℂ (𝔇.center q)).target :=
        (chartAt ℂ (𝔇.center q)).map_source (mem_chartSource_of_mem_U 𝔇 hxq)
      have hsrcp : x ∈ (chartAt ℂ (𝔇.center p)).source := mem_chartSource_of_mem_U 𝔇 hxp
      have hlip : (chartAt ℂ (𝔇.center p)).symm (chartMap 𝔇 p x) = x :=
        (chartAt ℂ (𝔇.center p)).left_inv hsrcp
      have hcontp : ContinuousAt (chartAt ℂ (𝔇.center p)).symm (chartMap 𝔇 p x) :=
        (chartAt ℂ (𝔇.center p)).continuousAt_symm
          ((chartAt ℂ (𝔇.center p)).map_source hsrcp)
      -- the symm-read point stays near `x`, hence off `b`, eventually
      have hxnb : ∀ᶠ z in 𝓝 (chartMap 𝔇 p x),
          (chartAt ℂ (𝔇.center p)).symm z ≠ b := by
        have hxmem : x ∈ ({b}ᶜ : Set X) := by simpa using hxb
        have h0 : ∀ᶠ y in 𝓝 ((chartAt ℂ (𝔇.center p)).symm (chartMap 𝔇 p x)),
            y ∈ ({b}ᶜ : Set X) := by
          rw [hlip]
          exact isOpen_compl_singleton.mem_nhds hxmem
        filter_upwards [hcontp.eventually h0] with z hz
        simpa using hz
      -- read agreement through the transition, smoothness of the `q`-read, target
      -- membership, the slot law, and `≠`-marked-coordinate guards
      have hFev : (fun ζ => H ((chartAt ℂ (𝔇.center p)).symm ζ))
          =ᶠ[𝓝 (chartMap 𝔇 p x)]
            fun ζ => H ((chartAt ℂ (𝔇.center q)).symm (transitionMap 𝔇 p q ζ)) := by
        filter_upwards [symm_transitionMap_eventuallyEq 𝔇 hx] with ζ hζ
        rw [hζ]
      have hguardp : ∀ᶠ z in 𝓝 (chartMap 𝔇 p x),
          ¬ (b ∈ (𝔇.U p : Set X) ∧ z = chartMap 𝔇 p b) := by
        by_cases hbp : b ∈ (𝔇.U p : Set X)
        · have hne : chartMap 𝔇 p x ≠ chartMap 𝔇 p b := fun hc =>
            hxb ((chartAt ℂ (𝔇.center p)).injOn hsrcp
              (mem_chartSource_of_mem_U 𝔇 hbp) hc)
          filter_upwards [isOpen_compl_singleton.mem_nhds
            (by simpa using hne : chartMap 𝔇 p x ∈ ({chartMap 𝔇 p b}ᶜ : Set ℂ))] with z hz
          exact fun hc => (by simpa using hz : z ≠ chartMap 𝔇 p b) hc.2
        · filter_upwards with z
          exact fun hc => hbp hc.1
      have hguardq : ∀ᶠ z in 𝓝 (chartMap 𝔇 p x),
          ¬ (b ∈ (𝔇.U q : Set X) ∧ transitionMap 𝔇 p q z = chartMap 𝔇 q b) := by
        by_cases hbq : b ∈ (𝔇.U q : Set X)
        · have hne : chartMap 𝔇 q x ≠ chartMap 𝔇 q b := fun hc =>
            hxb ((chartAt ℂ (𝔇.center q)).injOn (mem_chartSource_of_mem_U 𝔇 hxq)
              (mem_chartSource_of_mem_U 𝔇 hbq) hc)
          filter_upwards [htend.eventually (isOpen_compl_singleton.mem_nhds
            (by simpa using hne : chartMap 𝔇 q x ∈ ({chartMap 𝔇 q b}ᶜ : Set ℂ)))] with z hz
          exact fun hc => (by simpa using hz : transitionMap 𝔇 p q z ≠ chartMap 𝔇 q b) hc.2
        · filter_upwards with z
          exact fun hc => hbq hc.1
      -- smoothness of the `q`-read near the relocated coordinate, as an eventual fact
      have hqsm : ∀ᶠ z in 𝓝 (chartMap 𝔇 p x), DifferentiableAt ℝ
          (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ)) (transitionMap 𝔇 p q z) := by
        have hCD : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ)) (chartMap 𝔇 q x) :=
          hreadCD q x hxq hxb
        have hCD1 : ContDiffAt ℝ 1
            (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ)) (chartMap 𝔇 q x) :=
          hCD.of_le (by exact_mod_cast le_top)
        have h1 : ∀ᶠ w in 𝓝 (chartMap 𝔇 q x), DifferentiableAt ℝ
            (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ)) w := by
          filter_upwards [hCD1.eventually (by simp)] with w hw
          exact hw.differentiableAt one_ne_zero
        exact htend.eventually h1
      unfold OneOneLawAt
      filter_upwards [hFev.eventuallyEq_nhds, hguardp, hguardq, hqsm,
        (transitionMap_analyticAt 𝔇 hxp hxq).eventually_analyticAt,
        hg.2 p q x hx] with z hzF hgp hgq hqd hzan hzg
      rw [corrFam_apply, corrFam_apply, if_neg hgp, if_neg hgq]
      have h1 : DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center p)).symm ζ)) z
          = DbarDisk.dbar
              (fun ζ => H ((chartAt ℂ (𝔇.center q)).symm (transitionMap 𝔇 p q ζ))) z :=
        dbar_congr_of_eventuallyEq hzF
      have h2 := dbar_comp (f := fun ζ => H ((chartAt ℂ (𝔇.center q)).symm ζ))
        (φ := transitionMap 𝔇 p q) hqd hzan.differentiableAt
      rw [Function.comp_def] at h2
      have hns : ((normSq (deriv (transitionMap 𝔇 p q) z) : ℝ) : ℂ)
          = deriv (transitionMap 𝔇 p q) z
              * (starRingEnd ℂ) (deriv (transitionMap 𝔇 p q) z) :=
        (Complex.mul_conj _).symm
      rw [h1, h2, hzg, hns]
      ring

end Clearances

/-! ### The Leibniz split with the explicit correction term -/

section CorrSplit

variable {S : Finset X} {w : 𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ}
    {h : 𝔇.toFiniteCover.ι → X → ℂ} {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}
    {H : X → ℂ} {b : X}

/-- **The Leibniz step with the common `∂̄`-discrepancy kept explicit** (per chart): for a
presentation `h` whose chart reads satisfy `∂̄h̃_i = −∂̄H̃_i` off `S ∪ {b}` (the
`h + H`-holomorphy hypothesis `hhol'`), the `j`-th summand of the residue integral equals
the PoU-reinserted curvature terms MINUS the Stokes term MINUS the correction term
`∫ ρ̃_j·(∂̄H̃_j·g̃_j)`.  This is `integral_pouCoeff_glueCoeff_mero_split` with the
holomorphy of `h` replaced by the global-correction shape. -/
theorem integral_pouCoeff_glueCoeff_corr_split
    (hiso : ∀ a ∈ S, ∃ j₁, MLIsolated 𝔇 j₁ a)
    (hsm : SmoothOnSetsOff 𝔇 (S : Set X) h) (hδ : IsCoboundaryOn 𝔇 w h)
    (hg : IsOneZeroCoeff 𝔇 g)
    (htmem : IsOneOneCoeff 𝔇 (glueCoeff 𝔇 w g))
    (hcorr : IsOneOneCoeff 𝔇 (corrFam 𝔇 H g b))
    (hsmH : ∀ x : X, x ≠ b → ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) H x)
    (hhol' : ∀ i, ∀ x ∈ (𝔇.U i : Set X), x ∉ (S : Set X) → x ≠ b →
      DifferentiableAt ℂ (fun z => h i ((chartAt ℂ (𝔇.center i)).symm z)
        + H ((chartAt ℂ (𝔇.center i)).symm z)) (chartMap 𝔇 i x))
    (j : 𝔇.toFiniteCover.ι) :
    ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
      = (∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)))
        - (∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z)
        - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by
  -- the a.e. pointwise Leibniz identity (off the bad coordinates of `insert b S`)
  have hpt : ∀ z : ℂ, z ∉ badCoords 𝔇 (insert b S) j →
      pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z
        = DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
          - DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
          - pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by
    intro z hzT
    by_cases hzU : z ∈ chartMap 𝔇 j '' (𝔇.U j : Set X)
    · obtain ⟨x, hxU, rfl⟩ := hzU
      have hxbS : x ∉ insert b S := fun hx =>
        hzT ((chartMap_mem_badCoords_iff 𝔇 hxU).mpr hx)
      have hxb : x ≠ b := fun hc => hxbS (hc ▸ Finset.mem_insert_self b S)
      have hxS : x ∉ (S : Set X) := fun hx =>
        hxbS (Finset.mem_insert_of_mem hx)
      have hxsrc : x ∈ (chartAt ℂ (𝔇.center j)).source := mem_chartSource_of_mem_U 𝔇 hxU
      have hzt : chartMap 𝔇 j x ∈ (chartAt ℂ (𝔇.center j)).target :=
        (chartAt ℂ (𝔇.center j)).map_source hxsrc
      have hcont : ContinuousAt (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) :=
        (chartAt ℂ (𝔇.center j)).symm.continuousAt
          (by rwa [(chartAt ℂ (𝔇.center j)).symm_source])
      have hli : (chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x) = x :=
        (chartAt ℂ (𝔇.center j)).left_inv hxsrc
      have hovU : ((𝔇.U j : Opens X) : Set X)
          ∈ 𝓝 ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x)) := by
        rw [hli]
        exact (𝔇.U j).isOpen.mem_nhds hxU
      -- the Forster collapse, read in chart-`j` coordinates
      have hsplit_ev : splitCoeff 𝔇 w j =ᶠ[𝓝 (chartMap 𝔇 j x)]
          fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)
            - pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) := by
        filter_upwards [hcont.preimage_mem_nhds hovU] with ζ hζ
        rw [splitCoeff_apply, pouSplit_eq_of_coboundary 𝔇 hδ hζ]
      have hBd : DifferentiableAt ℝ
          (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) :=
        (contDiffAt_pouAverageRead_off hsm hxU hxS).differentiableAt (by simp)
      have hgd : DifferentiableAt ℝ (g j) (chartMap 𝔇 j x) :=
        ((hg.1 j x hxU).restrictScalars (𝕜 := ℝ)).differentiableAt
      -- the chart reads of `h j` and `H`
      have hHrd : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun ζ => H ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
        refine contDiffAt_chartSymmRead_of_contMDiffAt hzt ?_
        rw [hli]
        exact hsmH x hxb
      have hhd : DifferentiableAt ℝ
          (fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
        have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
          refine contDiffAt_chartSymmRead_of_contMDiffAt hzt ?_
          rw [hli]
          exact hsm j x hxU hxS
        exact h1.differentiableAt (by simp)
      -- the common-discrepancy law `∂̄h̃_j = −∂̄H̃_j` at the good point
      have hdbar_h : DbarDisk.dbar
            (fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x)
          = - DbarDisk.dbar
              (fun ζ => H ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x) := by
        have hsplit : (fun ζ => h j ((chartAt ℂ (𝔇.center j)).symm ζ))
            = fun ζ => (h j ((chartAt ℂ (𝔇.center j)).symm ζ)
                + H ((chartAt ℂ (𝔇.center j)).symm ζ))
              - H ((chartAt ℂ (𝔇.center j)).symm ζ) := by
          funext ζ
          ring
        rw [hsplit, DbarOpenDisk.dbar_sub
            ((hhol' j x hxU hxS hxb).restrictScalars ℝ)
            (hHrd.differentiableAt (by simp)),
          DbarDisk.dbar_eq_zero_of_differentiableAt (hhol' j x hxU hxS hxb), zero_sub]
      have hdbar_split : DbarDisk.dbar (splitCoeff 𝔇 w j) (chartMap 𝔇 j x)
          = - DbarDisk.dbar
              (fun ζ => H ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x)
            - DbarDisk.dbar
              (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) := by
        rw [dbar_congr_of_eventuallyEq hsplit_ev, DbarOpenDisk.dbar_sub hhd hBd, hdbar_h]
      have hdbarB : DbarDisk.dbar
            (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
            (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ))
              (chartMap 𝔇 j x) * g j (chartMap 𝔇 j x) := by
        rw [dbar_mul hBd hgd,
          DbarDisk.dbar_eq_zero_of_differentiableAt (hg.1 j x hxU).differentiableAt,
          mul_zero, add_zero]
      have hdbarPB : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) (chartMap 𝔇 j x)
          = DbarDisk.dbar (pouCoeff 𝔇 j) (chartMap 𝔇 j x)
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm (chartMap 𝔇 j x))
                  * g j (chartMap 𝔇 j x))
            + pouCoeff 𝔇 j (chartMap 𝔇 j x)
              * DbarDisk.dbar
                  (fun ζ => pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)
                  (chartMap 𝔇 j x) :=
        dbar_mul ((contDiff_pouCoeff 𝔇 j).differentiable (by simp) _)
          ((contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS).differentiableAt (by simp))
      -- the repaired correction value at the good point
      have hcorrv : corrFam 𝔇 H g b j (chartMap 𝔇 j x)
          = DbarDisk.dbar (fun ζ => H ((chartAt ℂ (𝔇.center j)).symm ζ)) (chartMap 𝔇 j x)
              * g j (chartMap 𝔇 j x) := by
        rw [corrFam_apply]
        refine if_neg ?_
        rintro ⟨hbU, hzb⟩
        exact hzT (hzb ▸ (chartMap_mem_badCoords_iff 𝔇 hbU).mpr (Finset.mem_insert_self b S))
      rw [glueCoeff_apply, hdbar_split, hdbarPB, hdbarB, hcorrv]
      ring
    · have hzs : z ∉ chartMap 𝔇 j '' tsupport (cechPoU 𝔇 j) := fun hc =>
        hzU (Set.image_mono (fun y hy => cechPoU_subordinate 𝔇 j hy) hc)
      have hP0 : pouCoeff 𝔇 j z = 0 := Set.indicator_of_notMem hzU _
      have hD0 : DbarDisk.dbar (pouCoeff 𝔇 j) z = 0 :=
        dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hzs
      have hPB0 : DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z = 0 := by
        refine dbar_eq_zero_of_eventuallyEq_zero ?_
        filter_upwards [(isCompact_image_tsupport_cechPoU 𝔇
          j).isClosed.isOpen_compl.mem_nhds hzs] with ζ hζ
        rw [pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hζ, zero_mul]
      rw [hP0, hD0, hPB0, zero_mul, zero_mul, zero_mul]
      ring
  -- integrability bookkeeping
  have hIt : Integrable fun z => pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z :=
    integrable_pouCoeff_mul 𝔇 htmem j
  have hIcorr : Integrable fun z => pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z :=
    integrable_pouCoeff_mul 𝔇 hcorr j
  have hYcd : ContDiff ℝ (⊤ : ℕ∞) fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) := by
    refine contDiff_of_chartImage_clearance 𝔇 (j := j) ?_ ?_
    · rintro z ⟨x, hxU, rfl⟩
      by_cases hxS : x ∈ (S : Set X)
      · obtain ⟨j₁, hj₁⟩ := hiso x hxS
        have hj : j = j₁ := eq_isolated_index hj₁ hxU
        subst hj
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [eventually_dbar_pouCoeff_zero_near_iso hj₁] with w' hw'
        rw [hw', zero_mul]
      · exact (ChartDiskCover.contDiffAt_dbar_chartDisk
          (contDiff_pouCoeff 𝔇 j).contDiffAt).mul
          (contDiffAt_pouAverageRead_mul_off hsm hg hxU hxS)
    · intro z hz
      rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul]
  have hYcs : HasCompactSupport fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    (DbarDisk.hasCompactSupport_dbar (hasCompactSupport_pouCoeff 𝔇 j)).mul_right
  have hIY : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z) :=
    hYcd.continuous.integrable_of_hasCompactSupport hYcs
  -- the bad coordinates are volume-negligible
  have hane : ∀ᵐ z : ℂ ∂volume, z ∉ badCoords 𝔇 (insert b S) j := by
    refine ae_iff.mpr ?_
    have hset : {z : ℂ | ¬ z ∉ badCoords 𝔇 (insert b S) j}
        = ((badCoords 𝔇 (insert b S) j : Finset ℂ) : Set ℂ) := by
      ext z
      simp
    rw [hset]
    exact (badCoords 𝔇 (insert b S) j).finite_toSet.measure_zero _
  have hF : Integrable fun z => DbarDisk.dbar (pouCoeff 𝔇 j) z
      * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
      - pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := hIY.sub hIt
  have e2 : (∫ z, (DbarDisk.dbar (pouCoeff 𝔇 j) z
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
        - pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z))
      = (∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
        - ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z := integral_sub hIY hIt
  have hkey : ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
      = ((∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
            * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
        - ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z)
        - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by
    calc ∫ z, DbarDisk.dbar (fun ζ => pouCoeff 𝔇 j ζ
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm ζ) * g j ζ)) z
        = ∫ z, ((DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
              - pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z)
            - pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z) := by
          refine integral_congr_ae ?_
          filter_upwards [hane] with z hz
          linear_combination hpt z hz
      _ = (∫ z, (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
              - pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z))
            - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := integral_sub hF hIcorr
      _ = ((∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
            - ∫ z, pouCoeff 𝔇 j z * glueCoeff 𝔇 w g j z)
            - ∫ z, pouCoeff 𝔇 j z * corrFam 𝔇 H g b j z := by rw [e2]
  -- PoU reinsertion of the curvature term
  have hreins : (∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
        * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z))
      = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
          * (DbarDisk.dbar (pouCoeff 𝔇 j) z
              * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
    calc ∫ z, DbarDisk.dbar (pouCoeff 𝔇 j) z
          * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)
        = ∫ z, ∑ k, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
            * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [← Finset.sum_mul, sum_rhoC_apply, one_mul]
      _ = ∑ k, ∫ z, rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
            * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) := by
          refine integral_finsetSum Finset.univ fun k _ => ?_
          have hcd : ContDiff ℝ (⊤ : ℕ∞) fun z =>
              rhoC 𝔇 k ((chartAt ℂ (𝔇.center j)).symm z)
                * (DbarDisk.dbar (pouCoeff 𝔇 j) z
                    * (pouAverage 𝔇 h ((chartAt ℂ (𝔇.center j)).symm z) * g j z)) :=
            contDiff_of_chartImage_clearance 𝔇
              (fun z hz => (contDiffAt_chartSymmRead (rhoC 𝔇 k).contMDiff
                (chartMap_image_U_subset_target 𝔇 j hz)).mul hYcd.contDiffAt)
              (fun z hz => by
                rw [dbar_pouCoeff_eq_zero_of_notMem_image_tsupport 𝔇 hz, zero_mul, mul_zero])
          exact hcd.continuous.integrable_of_hasCompactSupport hYcs.mul_left
  rw [← hreins]
  linear_combination hkey

end CorrSplit

end Jacobians.Dolbeault.FineResidue
