/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.MeromorphicFunctionField
import Jacobians.ProjectiveCurve.Line
import Jacobians.Vendor.Wallace.HolomorphicForms.HolomorphicMap

/-!
# From global meromorphic functions to the Riemann sphere

This file starts the construction of the map from a nonzero global
meromorphic function to `ℙ¹(ℂ)`.

The value at a non-pole is defined by the punctured-neighborhood limit of the
meromorphic germ, not by the representative's raw value.  This is necessary
because `MeromorphicFunctionField X` is a quotient by punctured-germ equality,
and Mathlib's `MeromorphicAt` intentionally ignores the value at the point.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Filter OnePoint

open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.ProjectiveLine
open Jacobians.Vendor.Wallace.HolomorphicForms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

namespace Jacobians.RiemannSurface
namespace MeromorphicFunctionField

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

private lemma chart0_coe_apply (w : ℂ) :
    chart0 ((w : ℂ) : ProjectiveLine) = w := by
  simpa [chart0] using
    (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      (f := ((↑) : ℂ → OnePoint ℂ)) (h := OnePoint.isOpenEmbedding_coe (X := ℂ)) (x := w))

private lemma chart1_coe_apply (w : ℂ) :
    chart1 ((w : ℂ) : ProjectiveLine) = w⁻¹ := by
  simp [chart1, OnePoint.elim_some]

private lemma chart1_infty_apply :
    chart1 (∞ : ProjectiveLine) = 0 := by
  simp [chart1]

private lemma chartAt_coe_eq_chart0 (w : ℂ) :
    chartAt ℂ ((w : ℂ) : ProjectiveLine) = chart0 := by
  change ProjectiveLine.chartAt ((w : ℂ) : ProjectiveLine) = chart0
  rw [ProjectiveLine.chartAt, if_neg (OnePoint.coe_ne_infty w)]

private lemma chartAt_infty_eq_chart1 :
    chartAt ℂ (∞ : ProjectiveLine) = chart1 := by
  change ProjectiveLine.chartAt (∞ : ProjectiveLine) = chart1
  rw [ProjectiveLine.chartAt, if_pos rfl]

/-- In a chart, a representative has a finite punctured-neighborhood limit at
every non-pole. -/
private theorem regularValueRep_exists (f : Rep X) (p : X)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) :
    ∃ c : ℂ,
      Tendsto ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (𝓝[≠] (chartAt ℂ p p)) (𝓝 c) := by
  have hf :
      MeromorphicAt ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (chartAt ℂ p p) := by
    have h := f.meromorphicAt p
    unfold MeromorphicAtX at h
    rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h
  have h_nonpole' :
      0 ≤ meromorphicOrderAt ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (chartAt ℂ p p) := by
    simpa [orderAt_eq_chartAt] using h_nonpole
  exact tendsto_nhds_of_meromorphicOrderAt_nonneg hf h_nonpole'

/-- The finite value of a representative at a non-pole, defined as the
punctured-neighborhood limit of its chart-local germ.  At poles the value is
irrelevant junk. -/
private noncomputable def regularValueRep (f : Rep X) (p : X) : ℂ :=
  if h : 0 ≤ orderAt p (f : X → ℂ) then
    Classical.choose (regularValueRep_exists f p h)
  else
    0

private theorem regularValueRep_spec (f : Rep X) (p : X)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) :
    Tendsto ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
      (𝓝[≠] (chartAt ℂ p p)) (𝓝 (regularValueRep f p)) := by
  rw [regularValueRep, dif_pos h_nonpole]
  exact Classical.choose_spec (regularValueRep_exists f p h_nonpole)

private theorem regularValueRep_eq_of_tendsto_chart (f : Rep X) {p : X}
    (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hp : p ∈ e.source)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) {c : ℂ}
    (hc : Tendsto ((f : X → ℂ) ∘ e.symm) (𝓝[≠] (e p)) (𝓝 c)) :
    regularValueRep f p = c := by
  refine tendsto_nhds_unique (regularValueRep_spec f p h_nonpole) ?_
  let τ : ℂ → ℂ := e ∘ (chartAt ℂ p).symm
  have hτ_an : AnalyticAt ℂ τ (chartAt ℂ p p) := by
    simpa [τ] using
      analyticAt_transition_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas p) he (mem_chart_source ℂ p) hp
  have hτ_nhds :
      Tendsto τ (𝓝 (chartAt ℂ p p)) (𝓝 (e p)) := by
    have hcont := hτ_an.continuousAt
    change Tendsto τ (𝓝 (chartAt ℂ p p)) (𝓝 (τ (chartAt ℂ p p))) at hcont
    simpa [τ, Function.comp_apply, (chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using
      hcont
  have hsymm :
      Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p)) (𝓝 p) := by
    have hcont := (chartAt ℂ p).continuousAt_symm
      ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    change Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p))
      (𝓝 ((chartAt ℂ p).symm (chartAt ℂ p p))) at hcont
    simpa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using hcont
  have hsrc :
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), (chartAt ℂ p).symm z ∈ e.source :=
    hsymm.eventually (e.open_source.mem_nhds hp)
  have htgt :
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), z ∈ (chartAt ℂ p).target :=
    (chartAt ℂ p).open_target.mem_nhds
      ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  have hτ_ne :
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), τ z ≠ e p := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hsrc, htgt] with z hzsrc hztgt hz_ne hτ_eq
    have hsymm_eq : (chartAt ℂ p).symm z = p := by
      have h := congrArg e.symm hτ_eq
      simpa [τ, Function.comp_apply, e.left_inv hzsrc, e.left_inv hp] using h
    have hz_eq : z = chartAt ℂ p p := by
      calc
        z = chartAt ℂ p ((chartAt ℂ p).symm z) := ((chartAt ℂ p).right_inv hztgt).symm
        _ = chartAt ℂ p p := by rw [hsymm_eq]
    exact hz_ne hz_eq
  have hτ :
      Tendsto τ (𝓝[≠] (chartAt ℂ p p)) (𝓝[≠] (e p)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hτ_nhds.mono_left nhdsWithin_le_nhds, hτ_ne⟩
  have hcomp := hc.comp hτ
  refine hcomp.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hsrc] with z hzsrc
  simp [τ, Function.comp_def, e.left_inv hzsrc]

private theorem orderAt_nonneg_of_local_chart_model (f : Rep X)
    (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {z₀ z : ℂ} {U : Set ℂ}
    {G : ℂ → ℂ} (hUopen : IsOpen U) (hzU : z ∈ U) (hztgt : z ∈ e.target)
    (hz_ne : z ≠ z₀)
    (hG_an : AnalyticAt ℂ G z)
    (hFG : ∀ y ∈ U, y ≠ z₀ → ((f : X → ℂ) ∘ e.symm) y = G y) :
    0 ≤ orderAt (e.symm z) (f : X → ℂ) := by
  have hq_source : e.symm z ∈ e.source := e.map_target hztgt
  have hFG_nhds : ((f : X → ℂ) ∘ e.symm) =ᶠ[𝓝 z] G := by
    have hzne_mem : ({z₀}ᶜ : Set ℂ) ∈ 𝓝 z :=
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hz_ne)
    filter_upwards [hUopen.mem_nhds hzU, hzne_mem] with y hyU hyne
    exact hFG y hyU (by simpa using hyne)
  have hFG_nhdsNE :
      ((f : X → ℂ) ∘ e.symm) =ᶠ[𝓝[≠] z] G :=
    hFG_nhds.filter_mono nhdsWithin_le_nhds
  have h_order :
      orderAt (e.symm z) (f : X → ℂ) =
        meromorphicOrderAt ((f : X → ℂ) ∘ e.symm) z := by
    simpa [e.right_inv hztgt] using
      orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas
        (p := e.symm z) (f : X → ℂ) e he hq_source
  rw [h_order, meromorphicOrderAt_congr hFG_nhdsNE]
  exact hG_an.meromorphicOrderAt_nonneg

private theorem regularValueRep_eq_of_local_chart_model (f : Rep X)
    (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {z₀ z : ℂ} {U : Set ℂ}
    {G : ℂ → ℂ} (hUopen : IsOpen U) (hzU : z ∈ U) (hztgt : z ∈ e.target)
    (hz_ne : z ≠ z₀)
    (hG_an : AnalyticAt ℂ G z)
    (hFG : ∀ y ∈ U, y ≠ z₀ → ((f : X → ℂ) ∘ e.symm) y = G y) :
    regularValueRep f (e.symm z) = G z := by
  have hq_source : e.symm z ∈ e.source := e.map_target hztgt
  have hFG_nhds : ((f : X → ℂ) ∘ e.symm) =ᶠ[𝓝 z] G := by
    have hzne_mem : ({z₀}ᶜ : Set ℂ) ∈ 𝓝 z :=
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hz_ne)
    filter_upwards [hUopen.mem_nhds hzU, hzne_mem] with y hyU hyne
    exact hFG y hyU (by simpa using hyne)
  have hFG_nhdsNE :
      ((f : X → ℂ) ∘ e.symm) =ᶠ[𝓝[≠] z] G :=
    hFG_nhds.filter_mono nhdsWithin_le_nhds
  have h_order :
      orderAt (e.symm z) (f : X → ℂ) =
        meromorphicOrderAt ((f : X → ℂ) ∘ e.symm) z := by
    simpa [e.right_inv hztgt] using
      orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas
        (p := e.symm z) (f : X → ℂ) e he hq_source
  have h_nonpole : 0 ≤ orderAt (e.symm z) (f : X → ℂ) := by
    rw [h_order, meromorphicOrderAt_congr hFG_nhdsNE]
    exact hG_an.meromorphicOrderAt_nonneg
  have hG_tendsto : Tendsto G (𝓝[≠] z) (𝓝 (G z)) :=
    hG_an.continuousAt.continuousWithinAt.tendsto
  have hF_tendsto :
      Tendsto ((f : X → ℂ) ∘ e.symm) (𝓝[≠] z) (𝓝 (G z)) :=
    hG_tendsto.congr' hFG_nhdsNE.symm
  exact regularValueRep_eq_of_tendsto_chart f e he hq_source h_nonpole
    (by simpa [e.right_inv hztgt] using hF_tendsto)

private theorem regularValueRep_congr {f g : Rep X} (hfg : Rep.Rel f g) (p : X)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) :
    regularValueRep f p = regularValueRep g p := by
  have h_order : orderAt p (f : X → ℂ) = orderAt p (g : X → ℂ) :=
    Rep.rel_orderAt hfg p
  have h_nonpole_g : 0 ≤ orderAt p (g : X → ℂ) := by
    rwa [← h_order]
  have hf_lim := regularValueRep_spec f p h_nonpole
  have hg_lim := regularValueRep_spec g p h_nonpole_g
  exact tendsto_nhds_unique (hf_lim.congr' (hfg p)) hg_lim

/-- Representative-level map to `ℙ¹(ℂ)`: poles go to `∞`; non-poles go to
the punctured-germ limit. -/
private noncomputable def toP1Rep (f : Rep X) : X → ProjectiveLine :=
  fun p =>
    if orderAt p (f : X → ℂ) < 0 then
      (∞ : ProjectiveLine)
    else
      ((regularValueRep f p : ℂ) : ProjectiveLine)

private theorem toP1Rep_congr {f g : Rep X} (hfg : Rep.Rel f g) :
    toP1Rep f = toP1Rep g := by
  funext p
  have h_order : orderAt p (f : X → ℂ) = orderAt p (g : X → ℂ) :=
    Rep.rel_orderAt hfg p
  by_cases hpole : orderAt p (f : X → ℂ) < 0
  · have hpole_g : orderAt p (g : X → ℂ) < 0 := by
      rwa [← h_order]
    simp [toP1Rep, hpole, hpole_g]
  · have hpole_g : ¬ orderAt p (g : X → ℂ) < 0 := by
      rwa [← h_order]
    have h_nonpole : 0 ≤ orderAt p (f : X → ℂ) := not_lt.mp hpole
    have h_value : regularValueRep f p = regularValueRep g p :=
      regularValueRep_congr hfg p h_nonpole
    simp [toP1Rep, hpole, hpole_g, h_value]

private theorem toP1Rep_chartLocal_nonpole (f : Rep X) (p : X)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) :
    ∃ φ : ℂ → ℂ,
      AnalyticAt ℂ φ (chartAt ℂ p p) ∧
      (chartAt ℂ (toP1Rep f p) ∘ toP1Rep f ∘ (chartAt ℂ p).symm)
        =ᶠ[𝓝 (chartAt ℂ p p)] φ ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p),
        toP1Rep f ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (toP1Rep f p)).source := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let z₀ : ℂ := e p
  let F : ℂ → ℂ := (f : X → ℂ) ∘ e.symm
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hf_mer : MeromorphicAt F z₀ := by
    have h := f.meromorphicAt p
    unfold MeromorphicAtX at h
    rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (f.order_ne_top p)
  have hn_nonneg : 0 ≤ n := by
    have h' : (0 : WithTop ℤ) ≤ (n : WithTop ℤ) := by
      simpa [hn] using h_nonpole
    exact_mod_cast h'
  have horderF : meromorphicOrderAt F z₀ = n := by
    simpa [F, z₀, e, orderAt_eq_chartAt] using hn.symm
  obtain ⟨g, hg_an, _hg_ne, hFG₀⟩ := (meromorphicOrderAt_eq_int_iff hf_mer).1 horderF
  let G : ℂ → ℂ := fun z => (z - z₀) ^ n * g z
  have hG_an_z₀ : AnalyticAt ℂ G z₀ := by
    have hpow : AnalyticAt ℂ (fun z : ℂ => (z - z₀) ^ n) z₀ :=
      (analyticAt_id.sub analyticAt_const).zpow_nonneg hn_nonneg
    exact hpow.mul hg_an
  have hFG : F =ᶠ[𝓝[≠] z₀] G := by
    filter_upwards [hFG₀] with z hz
    simpa [G, smul_eq_mul] using hz
  have hFG_nhds : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → F z = G z := by
    change ∀ᶠ z in 𝓝[≠] z₀, F z = G z at hFG
    rwa [eventually_nhdsWithin_iff] at hFG
  obtain ⟨U, hUsub, hUopen, hz₀U⟩ := mem_nhds_iff.mp hFG_nhds
  have hF_tendsto_z₀ : Tendsto F (𝓝[≠] z₀) (𝓝 (G z₀)) :=
    hG_an_z₀.continuousAt.continuousWithinAt.tendsto.congr' hFG.symm
  have hrv_p : regularValueRep f p = G z₀ :=
    regularValueRep_eq_of_tendsto_chart f e he hp_source h_nonpole
      (by simpa [F, z₀] using hF_tendsto_z₀)
  have hp_notpole : ¬ orderAt p (f : X → ℂ) < 0 := not_lt.mpr h_nonpole
  have htoP1_p : toP1Rep f p = ((G z₀ : ℂ) : ProjectiveLine) := by
    simp [toP1Rep, hp_notpole, hrv_p]
  have hchart_target : chartAt ℂ (toP1Rep f p) = chart0 := by
    rw [htoP1_p]
    exact chartAt_coe_eq_chart0 (G z₀)
  have htarget : ∀ᶠ z in 𝓝 z₀, z ∈ e.target :=
    e.open_target.mem_nhds (e.map_source hp_source)
  have hG_an_event : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ G z :=
    (isOpen_analyticAt ℂ G).mem_nhds hG_an_z₀
  have hrep_eq :
      ∀ᶠ z in 𝓝 z₀, toP1Rep f (e.symm z) = ((G z : ℂ) : ProjectiveLine) := by
    filter_upwards [hUopen.mem_nhds hz₀U, htarget, hG_an_event] with z hzU hztgt hGz
    by_cases hz : z = z₀
    · subst hz
      simpa [z₀, e.left_inv hp_source] using htoP1_p
    · have hnonpole_z : 0 ≤ orderAt (e.symm z) (f : X → ℂ) :=
        orderAt_nonneg_of_local_chart_model f e he hUopen hzU hztgt hz hGz
          (fun y hyU hyne => hUsub hyU hyne)
      have hrv_z : regularValueRep f (e.symm z) = G z :=
        regularValueRep_eq_of_local_chart_model f e he hUopen hzU hztgt hz hGz
          (fun y hyU hyne => hUsub hyU hyne)
      have hnotpole_z : ¬ orderAt (e.symm z) (f : X → ℂ) < 0 :=
        not_lt.mpr hnonpole_z
      simp [toP1Rep, hnotpole_z, hrv_z]
  refine ⟨G, hG_an_z₀, ?_, ?_⟩
  · filter_upwards [hrep_eq] with z hz
    change chartAt ℂ (toP1Rep f p) (toP1Rep f (e.symm z)) = G z
    rw [hchart_target, hz]
    exact chart0_coe_apply (G z)
  · filter_upwards [hrep_eq] with z hz
    rw [hz, hchart_target]
    change ((G z : ℂ) : ProjectiveLine) ∈ chart0.source
    simp [chart0]

private theorem toP1Rep_chartLocal_pole (f : Rep X) (p : X)
    (hpole : orderAt p (f : X → ℂ) < 0) :
    ∃ φ : ℂ → ℂ,
      AnalyticAt ℂ φ (chartAt ℂ p p) ∧
      (chartAt ℂ (toP1Rep f p) ∘ toP1Rep f ∘ (chartAt ℂ p).symm)
        =ᶠ[𝓝 (chartAt ℂ p p)] φ ∧
      (∀ᶠ z in 𝓝 (chartAt ℂ p p),
        toP1Rep f ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (toP1Rep f p)).source) ∧
      analyticOrderNatAt φ (chartAt ℂ p p) =
        Int.toNat (-(orderAt p (f : X → ℂ)).untop₀) := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let z₀ : ℂ := e p
  let F : ℂ → ℂ := (f : X → ℂ) ∘ e.symm
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
    IsManifold.chart_mem_maximalAtlas p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hf_mer : MeromorphicAt F z₀ := by
    have h := f.meromorphicAt p
    unfold MeromorphicAtX at h
    rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (f.order_ne_top p)
  have hn_neg : n < 0 := by
    have h' : (n : WithTop ℤ) < (0 : WithTop ℤ) := by
      simpa [hn] using hpole
    exact_mod_cast h'
  let k : ℕ := Int.toNat (-n)
  have hk_int : (k : ℤ) = -n := by
    exact Int.toNat_of_nonneg (neg_nonneg.mpr hn_neg.le)
  have hk_pos : 0 < k := by
    by_contra hk
    have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk
    have hneg_zero : (-n : ℤ) = 0 := by
      simpa [hk_zero] using hk_int.symm
    omega
  have horderF : meromorphicOrderAt F z₀ = n := by
    simpa [F, z₀, e, orderAt_eq_chartAt] using hn.symm
  obtain ⟨g, hg_an, hg_ne, hFG₀⟩ := (meromorphicOrderAt_eq_int_iff hf_mer).1 horderF
  let Gmer : ℂ → ℂ := fun z => (z - z₀) ^ n * g z
  let H : ℂ → ℂ := fun z => (z - z₀) ^ k * (g z)⁻¹
  have hginv_an : AnalyticAt ℂ (fun z => (g z)⁻¹) z₀ := hg_an.inv hg_ne
  have hH_an : AnalyticAt ℂ H z₀ := by
    have hpow : AnalyticAt ℂ (fun z : ℂ => (z - z₀) ^ k) z₀ :=
      (analyticAt_id.sub analyticAt_const).pow k
    exact hpow.mul hginv_an
  have hH_z₀ : H z₀ = 0 := by
    simp [H, sub_self, zero_pow hk_pos.ne']
  have hFG : F =ᶠ[𝓝[≠] z₀] Gmer := by
    filter_upwards [hFG₀] with z hz
    simpa [Gmer, smul_eq_mul] using hz
  have hFG_nhds : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → F z = Gmer z := by
    change ∀ᶠ z in 𝓝[≠] z₀, F z = Gmer z at hFG
    rwa [eventually_nhdsWithin_iff] at hFG
  obtain ⟨U, hUsub, hUopen, hz₀U⟩ := mem_nhds_iff.mp hFG_nhds
  have htoP1_p : toP1Rep f p = (∞ : ProjectiveLine) := by
    simp [toP1Rep, hpole]
  have hchart_target : chartAt ℂ (toP1Rep f p) = chart1 := by
    rw [htoP1_p]
    exact chartAt_infty_eq_chart1
  have htarget : ∀ᶠ z in 𝓝 z₀, z ∈ e.target :=
    e.open_target.mem_nhds (e.map_source hp_source)
  have hg_an_event : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z :=
    (isOpen_analyticAt ℂ g).mem_nhds hg_an
  have hg_ne_event : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 :=
    (hg_an.continuousAt.ne_iff_eventually_ne continuousAt_const).1 hg_ne
  have hrep_eq :
      ∀ᶠ z in 𝓝 z₀,
        chart1 (toP1Rep f (e.symm z)) = H z ∧
        toP1Rep f (e.symm z) ∈ chart1.source := by
    filter_upwards [hUopen.mem_nhds hz₀U, htarget, hg_an_event, hg_ne_event] with
      z hzU hztgt hgz_an hgz_ne
    by_cases hz : z = z₀
    · subst hz
      constructor
      · simpa [z₀, e.left_inv hp_source, htoP1_p, hH_z₀] using chart1_infty_apply
      · simp [z₀, e.left_inv hp_source, htoP1_p, chart1]
    · have hGmer_an_z : AnalyticAt ℂ Gmer z := by
        have hbase : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
        have hpow : AnalyticAt ℂ (fun y : ℂ => (y - z₀) ^ n) z :=
          (analyticAt_id.sub analyticAt_const).zpow hbase
        exact hpow.mul hgz_an
      have hnonpole_z : 0 ≤ orderAt (e.symm z) (f : X → ℂ) :=
        orderAt_nonneg_of_local_chart_model f e he hUopen hzU hztgt hz hGmer_an_z
          (fun y hyU hyne => hUsub hyU hyne)
      have hrv_z : regularValueRep f (e.symm z) = Gmer z :=
        regularValueRep_eq_of_local_chart_model f e he hUopen hzU hztgt hz hGmer_an_z
          (fun y hyU hyne => hUsub hyU hyne)
      have hnotpole_z : ¬ orderAt (e.symm z) (f : X → ℂ) < 0 :=
        not_lt.mpr hnonpole_z
      have htoP1_z : toP1Rep f (e.symm z) = ((Gmer z : ℂ) : ProjectiveLine) := by
        simp [toP1Rep, hnotpole_z, hrv_z]
      have hbase : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
      have hGmer_ne : Gmer z ≠ 0 := by
        simp [Gmer, zpow_ne_zero n hbase, hgz_ne]
      constructor
      · rw [htoP1_z, chart1_coe_apply]
        have hpow_eq : (((z - z₀) ^ n)⁻¹ : ℂ) = (z - z₀) ^ k := by
          calc
            (((z - z₀) ^ n)⁻¹ : ℂ) = (z - z₀) ^ (-n) := by
              rw [← zpow_neg]
            _ = (z - z₀) ^ (k : ℤ) := by
              rw [hk_int]
            _ = (z - z₀) ^ k := by
              rw [zpow_natCast]
        calc
          (Gmer z)⁻¹ = (((z - z₀) ^ n * g z)⁻¹ : ℂ) := rfl
          _ = (g z)⁻¹ * ((z - z₀) ^ n)⁻¹ := by rw [mul_inv_rev]
          _ = ((z - z₀) ^ n)⁻¹ * (g z)⁻¹ := by rw [mul_comm]
          _ = (z - z₀) ^ k * (g z)⁻¹ := by rw [hpow_eq]
          _ = H z := by rfl
      · rw [htoP1_z]
        change ((Gmer z : ℂ) : ProjectiveLine) ∈ chart1.source
        simp [chart1, hGmer_ne]
  have hH_order : analyticOrderNatAt H z₀ = k := by
    have hunit_ne : (fun z : ℂ => (g z)⁻¹) z₀ ≠ 0 := inv_ne_zero hg_ne
    have hH_eq :
        H =ᶠ[𝓝 z₀] fun z : ℂ => (z - z₀) ^ k • (fun z : ℂ => (g z)⁻¹) z := by
      filter_upwards [] with z
      simp [H, smul_eq_mul]
    have hH_order_enat : analyticOrderAt H z₀ = (k : ℕ∞) := by
      exact hH_an.analyticOrderAt_eq_natCast.mpr
        ⟨(fun z : ℂ => (g z)⁻¹), hginv_an, hunit_ne, hH_eq⟩
    simp [analyticOrderNatAt, hH_order_enat]
  have horder_toNat :
      Int.toNat (-(orderAt p (f : X → ℂ)).untop₀) = k := by
    rw [← hn]
    simp [WithTop.untop₀_coe, k]
  refine ⟨H, hH_an, ?_, ?_, ?_⟩
  · filter_upwards [hrep_eq] with z hz
    change chartAt ℂ (toP1Rep f p) (toP1Rep f (e.symm z)) = H z
    rw [hchart_target]
    exact hz.1
  · filter_upwards [hrep_eq] with z hz
    rw [hchart_target]
    exact hz.2
  · rw [hH_order, horder_toNat]

private theorem toP1Rep_contMDiffAt_of_chartLocal (f : Rep X) (p : X) {φ : ℂ → ℂ}
    (hφ : AnalyticAt ℂ φ (chartAt ℂ p p))
    (hchart :
      (chartAt ℂ (toP1Rep f p) ∘ toP1Rep f ∘ (chartAt ℂ p).symm)
        =ᶠ[𝓝 (chartAt ℂ p p)] φ)
    (hsrc :
      ∀ᶠ z in 𝓝 (chartAt ℂ p p),
        toP1Rep f ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (toP1Rep f p)).source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (toP1Rep f) p := by
  let H : X → ℂ := chartAt ℂ (toP1Rep f p) ∘ toP1Rep f
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hcoord_cd :
      ContDiffAt ℂ ω (H ∘ e.symm) (e p) := by
    have hφ_cd : ContDiffAt ℂ ω φ (chartAt ℂ p p) := hφ.contDiffAt
    refine hφ_cd.congr_of_eventuallyEq ?_
    simpa [H, e, Function.comp_assoc] using hchart
  have hH_cont : ContinuousAt H p := by
    have h := OpenPartialHomeomorph.continuousAt_iff_continuousAt_comp_right
      (e := (chartAt ℂ p).symm) (f := H) (x := p)
      (show p ∈ (chartAt ℂ p).symm.target from hp_source)
    have hcoord_cont : ContinuousAt (H ∘ (chartAt ℂ p).symm) (chartAt ℂ p p) := by
      simpa [H, e] using hcoord_cd.continuousAt
    exact h.mpr hcoord_cont
  have hsrc_p :
      toP1Rep f ⁻¹' (chartAt ℂ (toP1Rep f p)).source ∈ 𝓝 p := by
    have h := (chartAt ℂ p).eventually_nhds'
      (fun x => toP1Rep f x ∈ (chartAt ℂ (toP1Rep f p)).source)
      (mem_chart_source ℂ p)
    exact h.mp hsrc
  have hcont : ContinuousAt (toP1Rep f) p := by
    exact ((chartAt ℂ (toP1Rep f p)).continuousAt_iff_continuousAt_comp_left hsrc_p).mpr
      hH_cont
  rw [contMDiffAt_iff]
  refine ⟨hcont, ?_⟩
  simpa [H, e, contDiffWithinAt_univ, ModelWithCorners.range_eq_target,
    extChartAt_eq_chartAt, extChartAt_symm_eq_chartAt_symm, Function.comp_assoc] using hcoord_cd

private theorem toP1Rep_contMDiffAt (f : Rep X) (p : X) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (toP1Rep f) p := by
  by_cases hpole : orderAt p (f : X → ℂ) < 0
  · obtain ⟨φ, hφ, hchart, hsrc, _horder⟩ := toP1Rep_chartLocal_pole f p hpole
    exact toP1Rep_contMDiffAt_of_chartLocal f p hφ hchart hsrc
  · have h_nonpole : 0 ≤ orderAt p (f : X → ℂ) := not_lt.mp hpole
    obtain ⟨φ, hφ, hchart, hsrc⟩ := toP1Rep_chartLocal_nonpole f p h_nonpole
    exact toP1Rep_contMDiffAt_of_chartLocal f p hφ hchart hsrc

private theorem toP1Rep_contMDiff (f : Rep X) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toP1Rep f) :=
  fun p => toP1Rep_contMDiffAt f p

private theorem mapAnalyticOrderAt_toP1Rep_pole (f : Rep X) (p : X)
    (hpole : orderAt p (f : X → ℂ) < 0) :
    mapAnalyticOrderAt (toP1Rep f) p =
      Int.toNat (-(orderAt p (f : X → ℂ)).untop₀) := by
  obtain ⟨φ, _hφ, hchart, _hsrc, horder⟩ := toP1Rep_chartLocal_pole f p hpole
  let z₀ : ℂ := chartAt ℂ p p
  have htoP1_p : toP1Rep f p = (∞ : ProjectiveLine) := by
    simp [toP1Rep, hpole]
  have hchart' : chartLocalAt (toP1Rep f) p =ᶠ[𝓝 z₀] φ := by
    simpa [chartLocalAt, z₀, Function.comp_assoc] using hchart
  have hlocal_z₀ : chartLocalAt (toP1Rep f) p z₀ = 0 := by
    simp [chartLocalAt, z₀, Function.comp_def, htoP1_p, chartAt_infty_eq_chart1,
      chart1_infty_apply, (chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  have hφ_z₀ : φ z₀ = 0 := by
    rw [← hchart'.self_of_nhds, hlocal_z₀]
  have hsub :
      (fun t => chartLocalAt (toP1Rep f) p t -
        chartLocalAt (toP1Rep f) p (chartAt ℂ p p)) =ᶠ[𝓝 z₀] φ := by
    filter_upwards [hchart'] with t ht
    simp [z₀, ht, hlocal_z₀]
  unfold mapAnalyticOrderAt analyticOrderNatAt
  rw [analyticOrderAt_congr hsub]
  simpa [z₀] using horder

/-- The meromorphic function's map to the Riemann sphere.  Poles map to `∞`;
non-poles map to the punctured-germ limit in the finite chart. -/
noncomputable def toP1 (f : MeromorphicFunctionField X) : X → ProjectiveLine :=
  Quotient.lift (fun f : Rep X => toP1Rep f)
    (fun _ _ hfg => toP1Rep_congr hfg) f

@[simp]
theorem toP1_mk (f : Rep X) :
    toP1 (Quotient.mk (Rep.setoid (X := X)) f) = toP1Rep f := rfl

theorem toP1_contMDiff (f : MeromorphicFunctionField X) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toP1 f) := by
  refine Quotient.inductionOn f ?_
  intro f
  simpa [toP1_mk] using toP1Rep_contMDiff f

theorem toP1_eq_infty_iff (f : MeromorphicFunctionField X) (p : X) :
    toP1 f p = (∞ : ProjectiveLine) ↔ orderAtMF p f < 0 := by
  refine Quotient.inductionOn f ?_
  intro f
  by_cases hpole : orderAt p (f : X → ℂ) < 0
  · simp [toP1, toP1Rep, orderAtMF, hpole]
  · simp [toP1, toP1Rep, orderAtMF, hpole]

theorem mapAnalyticOrderAt_toP1 (f : MeromorphicFunctionField X) {p : X}
    (hp : toP1 f p = (∞ : ProjectiveLine)) :
    mapAnalyticOrderAt (toP1 f) p =
      Int.toNat (-(orderAtMF p f).untop₀) := by
  revert hp
  refine Quotient.inductionOn f ?_
  intro f hp
  have hpole : orderAt p (f : X → ℂ) < 0 := by
    have h := (toP1_eq_infty_iff
      (Quotient.mk (Rep.setoid (X := X)) f) p).1 hp
    simpa [orderAtMF] using h
  simpa [toP1_mk, orderAtMF] using mapAnalyticOrderAt_toP1Rep_pole f p hpole

theorem toP1_infty_fiber_finite (f : MeromorphicFunctionField X) :
    (toP1 f ⁻¹' ({(∞ : ProjectiveLine)} : Set ProjectiveLine)).Finite := by
  refine (orderSupport_finite f).subset ?_
  intro p hp
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hp
  rw [Set.mem_setOf_eq]
  exact (toP1_eq_infty_iff f p).1 hp |>.ne

theorem toP1_infty_weightedFiberSum (f : MeromorphicFunctionField X) :
    (toP1_infty_fiber_finite f).toFinset.sum (mapAnalyticOrderAt (toP1 f)) =
      (toP1_infty_fiber_finite f).toFinset.sum
        (fun p => Int.toNat (-(orderAtMF p f).untop₀)) := by
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hp_fiber : p ∈ toP1 f ⁻¹' ({(∞ : ProjectiveLine)} : Set ProjectiveLine) := by
    simpa [Set.Finite.mem_toFinset] using hp
  have hp_infty : toP1 f p = (∞ : ProjectiveLine) := by
    simpa using hp_fiber
  exact mapAnalyticOrderAt_toP1 f hp_infty

/-- Nonconstancy of a meromorphic-function-field element as seen by its
associated map to `ℙ¹(ℂ)`. -/
def Nonconstant (f : MeromorphicFunctionField X) : Prop :=
  ¬ ∃ y₀ : ProjectiveLine, ∀ x : X, toP1 f x = y₀

theorem toP1_nonconst {f : MeromorphicFunctionField X} (hf : Nonconstant f) :
    ¬ ∃ y₀ : ProjectiveLine, ∀ x : X, toP1 f x = y₀ :=
  hf

end MeromorphicFunctionField
end Jacobians.RiemannSurface
