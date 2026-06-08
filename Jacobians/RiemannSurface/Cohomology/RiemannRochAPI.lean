/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace
import Jacobians.Axioms.RiemannRoch
import Jacobians.Axioms.SerreDuality
import Jacobians.GeneralResults.ChartTransition
import Jacobians.RiemannSurface.Cohomology.RiemannRochFinite
import Jacobians.RiemannSurface.Cohomology.DegreeTheorem

/-!
# Riemann-Roch API in terms of the germ-quotient space `L(D)`

This file states the textbook Riemann-Roch consequences directly for the
germ-quotient definition
`riemannRochSpace D = L(D) = {f | div(f) + D >= 0}` from
`Jacobians.RiemannSurface.Cohomology.RiemannRochSpace`.

The statement anchors here are vetted against the textbook form. Some bridges
still use the axiom-level cohomology package, while the high-degree corollary is
now discharged through the negative-degree Riemann-Roch-space theorem.

References: Forster, *Lectures on Riemann Surfaces*, sections 16/17; Miranda,
Ch. VI; Mumford, *Algebraic Geometry I*, Ch. II.
-/

noncomputable section

set_option linter.unusedSectionVars false

open scoped Manifold Topology ContDiff
open Filter

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

open Set Metric in
/-- Local copy of the axiom-free Liouville theorem from
`Axioms/HyperellipticLiouville.lean`, avoiding that file's downstream
aggregate imports in this low-level API. -/
private theorem liouville_compact_complex_manifold_for_h0
    (M : Type*) [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
    (f : M → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ c : ℂ, ∀ x : M, f x = c := by
  have hcont : Continuous f := hf.continuous
  obtain ⟨p₀, -, hp₀⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty (α := M))
    hcont.norm.continuousOn
  have hp₀' : ∀ x, ‖f x‖ ≤ ‖f p₀‖ := fun x => hp₀ (mem_univ x)
  refine ⟨f p₀, ?_⟩
  set S : Set M := {x | f x = f p₀} with hS
  have hSne : S.Nonempty := ⟨p₀, rfl⟩
  have hScl : IsClosed S := isClosed_eq hcont continuous_const
  have hSop : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    set φ := extChartAt 𝓘(ℂ) q with hφ
    have hqs : q ∈ φ.source := mem_extChartAt_source q
    have hqsymm : φ.symm (φ q) = q := φ.left_inv hqs
    have hc_mem : φ q ∈ φ.target := mem_extChartAt_target q
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target q) (φ q) hc_mem
    have hFdiff : DifferentiableOn ℂ (f ∘ φ.symm) (ball (φ q) r) := by
      have h1 : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ.symm φ.target :=
        (contMDiffOn_extChartAt_symm q).mdifferentiableOn WithTop.top_ne_zero
      have hf_on : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f univ := hf.mdifferentiableOn
      have h2 : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ φ.symm) φ.target :=
        hf_on.comp h1 (mapsTo_univ _ _)
      exact (mdifferentiableOn_iff_differentiableOn.mp h2).mono hball
    have hmax : IsMaxOn (norm ∘ (f ∘ φ.symm)) (ball (φ q) r) (φ q) := by
      intro z _
      simp only [Function.comp_apply]
      calc ‖f (φ.symm z)‖ ≤ ‖f p₀‖ := hp₀' _
        _ = ‖f q‖ := by rw [hq]
        _ = ‖f (φ.symm (φ q))‖ := by rw [hqsymm]
    have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm isPreconnected_ball
      isOpen_ball hFdiff (mem_ball_self hr) hmax
    have hN : φ ⁻¹' (ball (φ q) r) ∈ 𝓝 q :=
      (continuousAt_extChartAt q).preimage_mem_nhds (ball_mem_nhds _ hr)
    have hsrc : φ.source ∈ 𝓝 q := extChartAt_source_mem_nhds q
    have hsub : φ.source ∩ φ ⁻¹' (ball (φ q) r) ⊆ S := by
      rintro x ⟨hxs, hxb⟩
      have hx := heq hxb
      have hxx : φ.symm (φ x) = x := φ.left_inv hxs
      change f x = f p₀
      have hfx : f (φ.symm (φ x)) = f (φ.symm (φ q)) := hx
      rw [hxx, hqsymm, hq] at hfx
      exact hfx
    exact Filter.mem_of_superset (Filter.inter_mem hsrc hN) hsub
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hScl, hSop⟩ hSne
  intro x
  have hxS : x ∈ S := hSuniv ▸ mem_univ x
  exact hxS

/-- `h^0(D)` is the complex dimension of the concrete Riemann-Roch space
`L(D) = H^0(X, O(D))`, as in Forster sections 16/17 and Miranda VI. Its
carrier is the meromorphic germ quotient, not raw functions. The
finite-dimensionality assertion making this finrank semantically faithful is
recorded separately in `riemannRochSpace_finiteDimensional`. -/
noncomputable abbrev h0 (D : Divisor X) : ℕ :=
  Module.finrank ℂ (riemannRochSpace D)

/-- Constant functions are meromorphic in every coordinate chart. -/
private theorem meromorphicAtX_const (c : ℂ) (p : X) :
    MeromorphicAtX (fun _ : X => c) p := by
  simp [MeromorphicAtX, Function.comp_def]

/-- The Wallace order of a nonzero constant is zero. -/
private theorem orderAt_const_of_ne_zero {c : ℂ} (hc : c ≠ 0) (p : X) :
    orderAt p (fun _ : X => c) = 0 := by
  classical
  rw [orderAt]
  simpa [Function.comp_def, hc] using
    (meromorphicOrderAt_const ((extChartAt 𝓘(ℂ) p) p) c)

/-- The bundled constant meromorphic function. -/
private def constMeroFunction (c : ℂ) : MeroFunctions X :=
  ⟨fun _ : X => c, meromorphicAtX_const c⟩

private def constMeroFunctionLinear : ℂ →ₗ[ℂ] MeroFunctions X where
  toFun := constMeroFunction
  map_add' := by
    intro a b
    ext x
    rfl
  map_smul' := by
    intro a b
    ext x
    simp [constMeroFunction, smul_eq_mul]

private theorem constMeroFunction_mem_riemannRoch_zero (c : ℂ) :
    (Submodule.Quotient.mk (constMeroFunction (X := X) c) : MeroField X) ∈
      riemannRochSpace (0 : Divisor X) := by
  intro p
  by_cases hc : c = 0
  · subst c
    change (0 : WithTop ℤ) ≤ orderAt p (0 : X → ℂ)
    rw [orderAt_zero]
    exact le_top
  · simp [constMeroFunction, orderAtField_mk, orderAt_const_of_ne_zero hc]

private noncomputable def constRRSZeroLinear :
    ℂ →ₗ[ℂ] riemannRochSpace (0 : Divisor X) :=
  (((GermZero X).mkQ).comp (constMeroFunctionLinear (X := X))).codRestrict
    (riemannRochSpace (0 : Divisor X))
    (fun c => by
      simpa [Submodule.mkQ_apply] using
        constMeroFunction_mem_riemannRoch_zero (X := X) c)

private theorem regularValue_exists (f : MeroFunctions X) (p : X)
    (h_nonpole : 0 ≤ orderAt p (f : X → ℂ)) :
    ∃ c : ℂ,
      Tendsto ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (𝓝[≠] (chartAt ℂ p p)) (𝓝 c) := by
  have hf :
      MeromorphicAt ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (chartAt ℂ p p) := by
    have h := f.property p
    unfold MeromorphicAtX at h
    rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h
  have h_nonpole' :
      0 ≤ meromorphicOrderAt ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        (chartAt ℂ p p) := by
    simpa [orderAt_eq_chartAt] using h_nonpole
  exact tendsto_nhds_of_meromorphicOrderAt_nonneg hf h_nonpole'

/-- The holomorphic value of a non-pole meromorphic germ, defined by punctured
coordinate-neighborhood limit rather than by the raw representative value. -/
private noncomputable def regularValue (f : MeroFunctions X)
    (h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ)) (p : X) : ℂ :=
  Classical.choose (regularValue_exists f p (h_nonneg p))

private theorem regularValue_spec (f : MeroFunctions X)
    (h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ)) (p : X) :
    Tendsto ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
      (𝓝[≠] (chartAt ℂ p p)) (𝓝 (regularValue f h_nonneg p)) :=
  Classical.choose_spec (regularValue_exists f p (h_nonneg p))

private theorem regularValue_eq_of_tendsto_chart (f : MeroFunctions X)
    (h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ))
    (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) (⊤ : WithTop ℕ∞) X) {p : X}
    (hp : p ∈ e.source) {c : ℂ}
    (hc : Tendsto ((f : X → ℂ) ∘ e.symm) (𝓝[≠] (e p)) (𝓝 c)) :
    regularValue f h_nonneg p = c := by
  refine tendsto_nhds_unique (regularValue_spec f h_nonneg p) ?_
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

private theorem regularValue_eq_of_local_chart_model (f : MeroFunctions X)
    (h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ))
    (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) (⊤ : WithTop ℕ∞) X)
    {z₀ z : ℂ} {U : Set ℂ} {G : ℂ → ℂ}
    (hUopen : IsOpen U) (hzU : z ∈ U) (hztgt : z ∈ e.target)
    (hz_ne : z ≠ z₀) (hG_an : AnalyticAt ℂ G z)
    (hFG : ∀ y ∈ U, y ≠ z₀ → ((f : X → ℂ) ∘ e.symm) y = G y) :
    regularValue f h_nonneg (e.symm z) = G z := by
  have hq_source : e.symm z ∈ e.source := e.map_target hztgt
  have hFG_nhds : ((f : X → ℂ) ∘ e.symm) =ᶠ[𝓝 z] G := by
    have hzne_mem : ({z₀}ᶜ : Set ℂ) ∈ 𝓝 z :=
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa using hz_ne)
    filter_upwards [hUopen.mem_nhds hzU, hzne_mem] with y hyU hyne
    exact hFG y hyU (by simpa using hyne)
  have hFG_nhdsNE :
      ((f : X → ℂ) ∘ e.symm) =ᶠ[𝓝[≠] z] G :=
    hFG_nhds.filter_mono nhdsWithin_le_nhds
  have hG_tendsto : Tendsto G (𝓝[≠] z) (𝓝 (G z)) :=
    hG_an.continuousAt.continuousWithinAt.tendsto
  have hF_tendsto :
      Tendsto ((f : X → ℂ) ∘ e.symm) (𝓝[≠] z) (𝓝 (G z)) :=
    hG_tendsto.congr' hFG_nhdsNE.symm
  exact regularValue_eq_of_tendsto_chart f h_nonneg e he hq_source
    (by simpa [e.right_inv hztgt] using hF_tendsto)

private theorem regularValue_chartLocal_of_order_ne_top (f : MeroFunctions X)
    (h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ))
    (h_ne_top : ∀ p : X, orderAt p (f : X → ℂ) ≠ ⊤) (p : X) :
    ∃ G : ℂ → ℂ,
      AnalyticAt ℂ G (chartAt ℂ p p) ∧
      ((regularValue f h_nonneg) ∘ (chartAt ℂ p).symm)
        =ᶠ[𝓝 (chartAt ℂ p p)] G ∧
      ((f : X → ℂ) ∘ (chartAt ℂ p).symm)
        =ᶠ[𝓝[≠] (chartAt ℂ p p)] G := by
  classical
  let e : OpenPartialHomeomorph X ℂ := chartAt ℂ p
  let z₀ : ℂ := e p
  let F : ℂ → ℂ := (f : X → ℂ) ∘ e.symm
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) (⊤ : WithTop ℕ∞) X :=
    IsManifold.chart_mem_maximalAtlas p
  have hp_source : p ∈ e.source := mem_chart_source ℂ p
  have hf_mer : MeromorphicAt F z₀ := by
    have h := f.property p
    unfold MeromorphicAtX at h
    rwa [extChartAt_symm_eq_chartAt_symm, extChartAt_eq_chartAt] at h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (h_ne_top p)
  have hn_nonneg : 0 ≤ n := by
    have h' : (0 : WithTop ℤ) ≤ (n : WithTop ℤ) := by
      simpa [hn] using h_nonneg p
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
  have hrv_p : regularValue f h_nonneg p = G z₀ :=
    regularValue_eq_of_tendsto_chart f h_nonneg e he hp_source
      (by simpa [F, z₀] using hF_tendsto_z₀)
  have htarget : ∀ᶠ z in 𝓝 z₀, z ∈ e.target :=
    e.open_target.mem_nhds (e.map_source hp_source)
  have hG_an_event : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ G z :=
    (isOpen_analyticAt ℂ G).mem_nhds hG_an_z₀
  have hvalue_eq :
      ∀ᶠ z in 𝓝 z₀, regularValue f h_nonneg (e.symm z) = G z := by
    filter_upwards [hUopen.mem_nhds hz₀U, htarget, hG_an_event] with z hzU hztgt hGz
    by_cases hz : z = z₀
    · subst z
      simpa [z₀, e.left_inv hp_source] using hrv_p
    · exact regularValue_eq_of_local_chart_model f h_nonneg e he hUopen hzU hztgt hz hGz
        (fun y hyU hyne => hUsub hyU hyne)
  refine ⟨G, hG_an_z₀, ?_, ?_⟩
  · simpa [e, z₀] using hvalue_eq
  · simpa [F, e, z₀] using hFG

private theorem regularValue_mdifferentiableAt (f : MeroFunctions X)
    (h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ))
    (h_ne_top : ∀ p : X, orderAt p (f : X → ℂ) ≠ ⊤) (p : X) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (regularValue f h_nonneg) p := by
  obtain ⟨G, hG_an, hchart, _hFG⟩ :=
    regularValue_chartLocal_of_order_ne_top f h_nonneg h_ne_top p
  let φ := extChartAt 𝓘(ℂ) p
  have hchart_ext :
      ((regularValue f h_nonneg) ∘ φ.symm) =ᶠ[𝓝 (φ p)] G := by
    simpa [φ, extChartAt_eq_chartAt, extChartAt_symm_eq_chartAt_symm] using hchart
  have hlocal_an : AnalyticAt ℂ ((regularValue f h_nonneg) ∘ φ.symm) (φ p) :=
    hG_an.congr hchart_ext.symm
  have hlocal_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ((regularValue f h_nonneg) ∘ φ.symm) (φ p) :=
    hlocal_an.differentiableAt.mdifferentiableAt
  have hφ_mdiff :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑φ) p :=
    Jacobians.GeneralResults.chart_mdiff (M := X) p (mem_extChartAt_source (I := 𝓘(ℂ)) p)
  have hcomp :
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (((regularValue f h_nonneg) ∘ φ.symm) ∘ ⇑φ) p :=
    hlocal_mdiff.comp p hφ_mdiff
  have heq :
      (regularValue f h_nonneg) =ᶠ[𝓝 p]
        (((regularValue f h_nonneg) ∘ φ.symm) ∘ ⇑φ) := by
    have hsrc : φ.source ∈ 𝓝 p :=
      IsOpen.mem_nhds (isOpen_extChartAt_source p) (by
        simp [φ])
    filter_upwards [hsrc] with x hx
    simp [Function.comp_def, φ.left_inv hx]
  exact hcomp.congr_of_eventuallyEq heq

private theorem regularValue_mdifferentiable (f : MeroFunctions X)
    (h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ))
    (h_ne_top : ∀ p : X, orderAt p (f : X → ℂ) ≠ ⊤) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (regularValue f h_nonneg) :=
  fun p => regularValue_mdifferentiableAt f h_nonneg h_ne_top p

private theorem orderAt_sub_const_eq_top_of_regularValue_const (f : MeroFunctions X)
    (h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ))
    (h_ne_top : ∀ p : X, orderAt p (f : X → ℂ) ≠ ⊤) {c : ℂ}
    (hc : ∀ x : X, regularValue f h_nonneg x = c) (p : X) :
    orderAt p ((f : X → ℂ) - fun _ : X => c) = ⊤ := by
  obtain ⟨G, _hG_an, hreg, hFG⟩ :=
    regularValue_chartLocal_of_order_ne_top f h_nonneg h_ne_top p
  rw [orderAt_eq_chartAt]
  refine meromorphicOrderAt_eq_top_iff.mpr ?_
  have hreg_ne :
      ((regularValue f h_nonneg) ∘ (chartAt ℂ p).symm)
        =ᶠ[𝓝[≠] (chartAt ℂ p p)] G :=
    hreg.filter_mono nhdsWithin_le_nhds
  filter_upwards [hFG, hreg_ne] with z hFz hRz
  change (((f : X → ℂ) ∘ (chartAt ℂ p).symm) z) - c = 0
  have hr : regularValue f h_nonneg ((chartAt ℂ p).symm z) = c :=
    hc ((chartAt ℂ p).symm z)
  have hr' : ((regularValue f h_nonneg) ∘ (chartAt ℂ p).symm) z = c := by
    simpa [Function.comp_def] using hr
  rw [hFz, ← hRz, hr', sub_self]

private theorem orderAt_nonneg_of_mem_riemannRoch_zero {f : MeroFunctions X}
    (hmem :
      (Submodule.Quotient.mk f : MeroField X) ∈ riemannRochSpace (0 : Divisor X)) :
    ∀ p : X, 0 ≤ orderAt p (f : X → ℂ) := by
  intro p
  have hp := hmem p
  simpa [orderAtField_mk] using hp

private theorem constRRSZeroLinear_injective :
    Function.Injective (constRRSZeroLinear (X := X)) := by
  intro c d hcd
  have hq :
      (Submodule.Quotient.mk (constMeroFunction (X := X) c) : MeroField X) =
        Submodule.Quotient.mk (constMeroFunction (X := X) d) := by
    exact congrArg Subtype.val hcd
  have hmem : constMeroFunction (X := X) c - constMeroFunction (X := X) d ∈ GermZero X :=
    (Submodule.Quotient.eq (GermZero X)).1 hq
  by_contra hne
  let p : X := Classical.choice (inferInstance : Nonempty X)
  have htop := hmem p
  have hconst :
      orderAt p (((constMeroFunction (X := X) c - constMeroFunction (X := X) d :
        MeroFunctions X) : X → ℂ)) = 0 := by
    change orderAt p (fun _ : X => c - d) = 0
    exact orderAt_const_of_ne_zero (sub_ne_zero.mpr hne) p
  rw [hconst] at htop
  simp at htop

private theorem exists_const_mk_eq_of_mem (F : MeroField X)
    (hF : F ∈ riemannRochSpace (0 : Divisor X)) :
    ∃ c : ℂ,
      (Submodule.Quotient.mk (constMeroFunction (X := X) c) : MeroField X) = F := by
  revert hF
  refine Submodule.Quotient.induction_on (GermZero X) F ?_
  intro f hmem
  by_cases hzero : (Submodule.Quotient.mk f : MeroField X) = 0
  · refine ⟨0, ?_⟩
    rw [hzero]
    exact (Submodule.Quotient.mk_eq_zero (GermZero X)).2 (by
      intro p
      change orderAt p (0 : X → ℂ) = ⊤
      exact orderAt_zero (X := X) p)
  · have h_nonneg : ∀ p : X, 0 ≤ orderAt p (f : X → ℂ) :=
      orderAt_nonneg_of_mem_riemannRoch_zero (X := X) hmem
    have hexists : ∃ p : X, orderAt p (f : X → ℂ) ≠ ⊤ := by
      by_contra hnone
      apply hzero
      exact (Submodule.Quotient.mk_eq_zero (GermZero X)).2 (by
        intro p
        by_contra hp
        exact hnone ⟨p, hp⟩)
    have h_ne_top : ∀ p : X, orderAt p (f : X → ℂ) ≠ ⊤ :=
      orderAt_ne_top_of_exists f.property hexists
    obtain ⟨c, hc⟩ :=
      liouville_compact_complex_manifold_for_h0 X (regularValue f h_nonneg)
        (regularValue_mdifferentiable f h_nonneg h_ne_top)
    refine ⟨c, ?_⟩
    have hgerm : f - constMeroFunction (X := X) c ∈ GermZero X := by
      intro p
      simpa [constMeroFunction] using
        orderAt_sub_const_eq_top_of_regularValue_const f h_nonneg h_ne_top hc p
    exact ((Submodule.Quotient.eq (GermZero X)).2 hgerm).symm

private theorem constRRSZeroLinear_surjective :
    Function.Surjective (constRRSZeroLinear (X := X)) := by
  intro F
  obtain ⟨c, hc⟩ := exists_const_mk_eq_of_mem (X := X) F.1 F.2
  refine ⟨c, ?_⟩
  ext
  simpa [constRRSZeroLinear, Submodule.mkQ_apply] using hc


/-- **Base case** for finiteness: `L(0) ≅ ℂ` (the constants), via the
`constRRSZeroLinear` bijection proved above. -/
theorem finiteDimensional_riemannRochSpace_zero :
    FiniteDimensional ℂ (riemannRochSpace (0 : Divisor X)) :=
  (LinearEquiv.ofBijective (constRRSZeroLinear (X := X))
    ⟨constRRSZeroLinear_injective (X := X),
      constRRSZeroLinear_surjective (X := X)⟩).finiteDimensional

/-- **Finiteness of Riemann–Roch spaces (Forster §14, H⁰ side).** On a compact
connected Riemann surface, `L(D) = riemannRochSpace D` is finite-dimensional over
`ℂ` for every divisor `D`. **Discharged** (formerly an axiom) by the elementary
`ℓ(D) ≤ 1 + deg D⁺` route (`RiemannRochFinite.lean`, issue #116), from the
`L(0) = ℂ` base case above. Supplies the `[FiniteDimensional H0]` instance
`AX_RiemannRoch` needs; the H1 side is derived via Serre.

Reference: Forster §14; Miranda Ch. VI. -/
@[instance] theorem riemannRochSpace_finiteDimensional (D : Divisor X) :
    FiniteDimensional ℂ (riemannRochSpace D) :=
  finiteDimensional_riemannRochSpace_of_base finiteDimensional_riemannRochSpace_zero D


/-- `H⁰(O_D)` is finite-dimensional (the pin, transported across the definitional
`H0 (ofDivisor D) ≃ₗ riemannRochSpace D`). -/
instance instFiniteDimensional_H0_ofDivisor (D : Divisor X) :
    FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D)) :=
  (H0_equiv_riemannRochSpace D).some.symm.finiteDimensional

/-- `H¹(O_D)` is finite-dimensional, **derived** from the `L(D)`-finiteness pin
via Serre duality: `H¹(O_D) ≃ₗ Dual (H⁰(O(K−D)))`, and the dual of a
finite-dimensional space is finite-dimensional. -/
instance instFiniteDimensional_H1_ofDivisor (D : Divisor X) :
    FiniteDimensional ℂ (H1 (LineBundle.ofDivisor D)) :=
  (AX_SerreDuality D).some.symm.finiteDimensional

/-- Riemann-Roch in pure `L(D)` terms (Forster section 17; Miranda VI;
Mumford II.2):

`h^0(D) - h^0(K_X - D) = deg D + 1 - g`.

This is the strong form obtained from the usual `h^0(D) - h^1(D)` statement by
Serre duality, identifying `H^1(O(D))` with the dual of `H^0(O(K_X - D))`, and
then using `H0_equiv_riemannRochSpace` for both divisors. -/
theorem riemannRoch (D : Divisor X) :
    (h0 D : ℤ) - (h0 (canonicalDivisor X - D) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ) := by
  have hRR := AX_RiemannRoch D
  have hH0 : Module.finrank ℂ (H0 (LineBundle.ofDivisor D)) = h0 D :=
    (H0_equiv_riemannRochSpace D).some.finrank_eq
  have hH1 : Module.finrank ℂ (H1 (LineBundle.ofDivisor D)) =
      h0 (canonicalDivisor X - D) := by
    rw [(AX_SerreDuality D).some.finrank_eq, Subspace.dual_finrank_eq,
      (H0_equiv_riemannRochSpace (canonicalDivisor X - D)).some.finrank_eq]
  rw [hH0, hH1] at hRR
  exact hRR

/-- Global holomorphic functions on a compact connected Riemann surface are
constant (Forster section 16; Miranda VI): `L(0) = C`, so `h^0(0) = 1`. -/
theorem h0_zero :
    h0 (0 : Divisor X) = 1 := by
  let e : ℂ ≃ₗ[ℂ] riemannRochSpace (0 : Divisor X) :=
    LinearEquiv.ofBijective (constRRSZeroLinear (X := X))
      ⟨constRRSZeroLinear_injective (X := X), constRRSZeroLinear_surjective (X := X)⟩
  change Module.finrank ℂ (riemannRochSpace (0 : Divisor X)) = 1
  rw [← e.finrank_eq, Module.finrank_self]

/-- Holomorphic differentials have dimension the genus (Forster sections 16/17;
Miranda VI; Mumford II.2): `H^0(K_X) ~= C^g`, hence `h^0(K_X) = g`. -/
theorem h0_canonical :
    h0 (canonicalDivisor X) = genus X := by
  have h := riemannRoch (0 : Divisor X)
  rw [sub_zero, h0_zero, map_zero] at h
  omega

/-- Textbook canonical degree formula (Forster section 17; Miranda VI):
`deg K_X = 2g - 2`. The genus is a natural number in this development, so it is
cast to `Int` before forming the divisor-degree identity. -/
theorem canonicalDivisor_deg :
    Divisor.deg X (canonicalDivisor X) = 2 * (genus X : ℤ) - 2 := by
  -- Riemann–Roch at `D = K`: `h⁰(K) − h⁰(0) = deg K + 1 − g`, with `h⁰(K) = g`
  -- and `h⁰(0) = 1`, gives `deg K = 2g − 2`.
  have h := riemannRoch (canonicalDivisor X)
  simp only [sub_self, h0_zero, h0_canonical, Nat.cast_one] at h
  omega

/-- Consistency bridge to the existing axiom-level Riemann-Roch package.

Given the `AX_RiemannRoch` numerical statement, the `AX_SerreDuality`
identification
`H^1(O(D)) ~= H^0(O(K_X - D))^*`, and the two comparison equivalences
`H0_equiv_riemannRochSpace`, one obtains the pure `L(D)` form stated in
`riemannRoch`. This theorem is only a statement anchor; its body is deferred. -/
theorem riemannRoch_consistent_with_AX (D : Divisor X)
    [FiniteDimensional ℂ (H0 (LineBundle.ofDivisor D))]
    [FiniteDimensional ℂ (H1 (LineBundle.ofDivisor D))]
    [FiniteDimensional ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)))]
    (hAX :
      (Module.finrank ℂ (H0 (LineBundle.ofDivisor D)) : ℤ) -
        (Module.finrank ℂ (H1 (LineBundle.ofDivisor D)) : ℤ) =
          Divisor.deg X D + 1 - (genus X : ℤ))
    (hSerre :
      Nonempty
        (H1 (LineBundle.ofDivisor D) ≃ₗ[ℂ]
          Module.Dual ℂ (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)))))
    (hD : Nonempty (H0 (LineBundle.ofDivisor D) ≃ₗ[ℂ] riemannRochSpace D))
    (hKD :
      Nonempty
        (H0 (LineBundle.ofDivisor (canonicalDivisor X - D)) ≃ₗ[ℂ]
          riemannRochSpace (canonicalDivisor X - D))) :
    (h0 D : ℤ) - (h0 (canonicalDivisor X - D) : ℤ) =
      Divisor.deg X D + 1 - (genus X : ℤ) := by
  sorry

/-- High-degree Riemann-Roch corollary (Forster section 17; Miranda VI): if
`deg D > 2g - 2`, then `H^1(O(D)) = 0`, equivalently `L(K_X - D) = 0`, so
`h^0(D) = deg D + 1 - g`. The left side is stated over `Int` because divisor
degrees are integer-valued. -/
theorem h0_of_deg_gt (D : Divisor X) :
    2 * (genus X : ℤ) - 2 < Divisor.deg X D →
      (h0 D : ℤ) = Divisor.deg X D + 1 - (genus X : ℤ) := by
  intro hD
  have hKD_neg : Divisor.deg X (canonicalDivisor X - D) < 0 := by
    rw [map_sub, canonicalDivisor_deg]
    omega
  have hKD_bot : riemannRochSpace (canonicalDivisor X - D) = ⊥ :=
    riemannRochSpace_eq_bot_of_deg_neg' hKD_neg
  have hKD_h0 : h0 (canonicalDivisor X - D) = 0 := by
    unfold h0
    rw [hKD_bot]
    simp
  simpa [hKD_h0] using riemannRoch D

/-- Single-point positive-genus corollary (Forster section 17; Miranda VI):
for `g > 0`, the Riemann-Roch space `L(P)` has dimension one, i.e. only
constant meromorphic functions have at most one simple pole at `P`.

This formulation uses the divisor `(P)` as `FreeAbelianGroup.of p`; the
positive-genus hypothesis excludes the genus-zero case where `h^0(P) = 2`. -/
theorem h0_point_eq_one_of_genus_pos (p : X) (hg : 0 < genus X) :
    h0 (FreeAbelianGroup.of p : Divisor X) = 1 := by
  sorry

end Jacobians.RiemannSurface
