/-
# Bridge equivalence: cocycle 1-forms ↔ Kirov's bundle-section 1-forms

This file upgrades `bridgeForm` from an injective linear map to a linear
isomorphism by constructing the section-to-cocycle inverse. The inverse reads
the scalar local representative of a Kirov cotangent-bundle section in each
chart and normalizes it to zero off the chart target, matching
`HolomorphicOneForm`'s cocycle representation.
-/

import Submission.Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.Bridge

open scoped Manifold ContDiff Bundle Topology
open Jacobians.RiemannSurface
open Jacobians.Vendor.Kirov.Montel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace BridgeFormEquiv

/-- The chart-local coefficient of a Kirov bundle-section form, normalized to
zero off the chosen chart target. -/
noncomputable def sectionCoeff
    (α : Jacobians.Vendor.Kirov.HolomorphicOneForms X) : X → ℂ → ℂ := by
  classical
  exact fun x z =>
    if z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target then
      localRep α x ((extChartAt 𝓘(ℂ, ℂ) x).symm z)
    else
      0

theorem sectionCoeff_apply_of_mem
    (α : Jacobians.Vendor.Kirov.HolomorphicOneForms X) {x : X} {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target) :
    sectionCoeff α x z = localRep α x ((extChartAt 𝓘(ℂ, ℂ) x).symm z) := by
  have hz' : z ∈ (chartAt ℂ x).target := by
    simpa [extChartAt] using hz
  simp [sectionCoeff, extChartAt, hz']

theorem sectionCoeff_apply_of_not_mem
    (α : Jacobians.Vendor.Kirov.HolomorphicOneForms X) {x : X} {z : ℂ}
    (hz : z ∉ (extChartAt 𝓘(ℂ, ℂ) x).target) :
    sectionCoeff α x z = 0 := by
  have hz' : z ∉ (chartAt ℂ x).target := by
    simpa [extChartAt] using hz
  simp [sectionCoeff, extChartAt, hz']

theorem sectionCoeff_zero_off_target
    (α : Jacobians.Vendor.Kirov.HolomorphicOneForms X) :
    IsZeroOffChartTarget X (sectionCoeff α) := by
  intro x z hz
  exact sectionCoeff_apply_of_not_mem α hz

theorem sectionCoeff_holomorphic
    (α : Jacobians.Vendor.Kirov.HolomorphicOneForms X) :
    IsHolomorphicOneFormCoeff X (sectionCoeff α) := by
  intro x
  have h : AnalyticOn ℂ (sectionCoeff α x) (chartAt ℂ x).target :=
    (localRep_analyticOn_chartTarget α x).congr (fun z hz => by
      have hz_ext : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target := by
        simpa [extChartAt] using hz
      rw [sectionCoeff_apply_of_mem α hz_ext]
      simp [extChartAt])
  simpa [extChartAt] using h

theorem chartTransitionFactor_eq_fderiv (x y q : X)
    (hqx : q ∈ (extChartAt 𝓘(ℂ, ℂ) x).source)
    (hqy : q ∈ (extChartAt 𝓘(ℂ, ℂ) y).source) :
    chartTransitionFactor (X := X) y x q =
      fderiv ℂ
        ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm)
        ((extChartAt 𝓘(ℂ, ℂ) x) q) 1 := by
  set z : ℂ := (extChartAt 𝓘(ℂ, ℂ) x) q with hz_def
  have hz_tgt : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target :=
    (extChartAt 𝓘(ℂ, ℂ) x).map_source hqx
  have hsymm : (extChartAt 𝓘(ℂ, ℂ) x).symm z = q :=
    (extChartAt 𝓘(ℂ, ℂ) x).left_inv hqx
  have hsymm_chart : (chartAt ℂ x).symm z = q := by
    simpa [extChartAt] using hsymm
  have hqx_chart : q ∈ (chartAt ℂ x).source := by
    simpa [extChartAt] using hqx
  have hqy_chart : q ∈ (chartAt ℂ y).source := by
    simpa [extChartAt] using hqy
  have hqx_base :
      q ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have hqy_base :
      q ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have hmdiff_y : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (extChartAt 𝓘(ℂ, ℂ) y) q := by
    apply mdifferentiableAt_extChartAt
    rwa [← extChartAt_source (I := 𝓘(ℂ, ℂ))]
  have hmdiff_symm_within : MDifferentiableWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (extChartAt 𝓘(ℂ, ℂ) x).symm (Set.range (𝓘(ℂ, ℂ))) z :=
    mdifferentiableWithinAt_extChartAt_symm hz_tgt
  have hmdiff_symm : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (extChartAt 𝓘(ℂ, ℂ) x).symm z := by
    have hrange : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
      ModelWithCorners.range_eq_univ _
    rw [← mdifferentiableWithinAt_univ, ← hrange]
    exact hmdiff_symm_within
  have hchain :
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z =
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) q).comp
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z) := by
    have h0 := mfderiv_comp_of_eq hmdiff_y hmdiff_symm hsymm
    rw [hsymm] at h0
    exact h0
  have hsymm_mfderiv :
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z =
        mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (extChartAt 𝓘(ℂ, ℂ) x).symm (Set.range (𝓘(ℂ, ℂ))) z := by
    have hrange : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ :=
      ModelWithCorners.range_eq_univ _
    rw [hrange, mfderivWithin_univ]
  have hmfd_y :
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).continuousLinearMapAt ℂ q =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) q :=
    TangentBundle.continuousLinearMapAt_trivializationAt hqy_chart
  have hsymm_x :
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).symmL ℂ q =
        mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
          (extChartAt 𝓘(ℂ, ℂ) x).symm (Set.range (𝓘(ℂ, ℂ)))
          ((extChartAt 𝓘(ℂ, ℂ) x) q) :=
    TangentBundle.symmL_trivializationAt hqx_chart
  unfold chartTransitionFactor
  rw [Bundle.Trivialization.coordChangeL_apply
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x)
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y)
    ⟨hqx_base, hqy_base⟩ 1]
  have hsymmL_apply :
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).symm q 1 =
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).symmL ℂ q 1 := rfl
  rw [hsymmL_apply]
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := ℂ)
    (e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y)
    (b := q)
    hqy_base
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).symmL ℂ q 1)]
  change
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).continuousLinearMapAt ℂ q
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).symmL ℂ q 1) =
      fderiv ℂ
        ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1
  rw [hmfd_y, hsymm_x, ← hz_def, ← hsymm_mfderiv]
  change
      ((mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) q).comp
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z)) (1 : ℂ) =
      fderiv ℂ
        ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z (1 : ℂ)
  rw [← hchain, mfderiv_eq_fderiv]
  rfl

theorem sectionCoeff_cocycle
    (α : Jacobians.Vendor.Kirov.HolomorphicOneForms X) :
    SatisfiesCotangentCocycle X (sectionCoeff α) := by
  intro x y z hz hy
  set q : X := (extChartAt 𝓘(ℂ, ℂ) x).symm z with hq_def
  have hqx : q ∈ (extChartAt 𝓘(ℂ, ℂ) x).source := by
    rw [hq_def]
    exact (extChartAt 𝓘(ℂ, ℂ) x).map_target hz
  have hqy : q ∈ (extChartAt 𝓘(ℂ, ℂ) y).source := by
    rw [hq_def]
    exact hy
  have hy_tgt :
      (extChartAt 𝓘(ℂ, ℂ) y) q ∈ (extChartAt 𝓘(ℂ, ℂ) y).target :=
    (extChartAt 𝓘(ℂ, ℂ) y).map_source hqy
  have hy_symm : (extChartAt 𝓘(ℂ, ℂ) y).symm ((extChartAt 𝓘(ℂ, ℂ) y) q) = q :=
    (extChartAt 𝓘(ℂ, ℂ) y).left_inv hqy
  have hqx_chart : q ∈ (chartAt ℂ x).source := by
    simpa [extChartAt] using hqx
  have hqy_chart : q ∈ (chartAt ℂ y).source := by
    simpa [extChartAt] using hqy
  have hqx_base :
      q ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have hqy_base :
      q ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have hlocal :
      localRep α x q =
        chartTransitionFactor (X := X) y x q * localRep α y q :=
    localRep_chart_transition α y x q hqx_base hqy_base
  have hx_q : (extChartAt 𝓘(ℂ, ℂ) x) q = z := by
    rw [hq_def]
    exact (extChartAt 𝓘(ℂ, ℂ) x).right_inv hz
  rw [sectionCoeff_apply_of_mem α hz]
  rw [sectionCoeff_apply_of_mem α hy_tgt, hy_symm]
  rw [show (extChartAt 𝓘(ℂ, ℂ) x).symm z = q from hq_def.symm]
  rw [hlocal, chartTransitionFactor_eq_fderiv x y q hqx hqy]
  rw [hx_q]
  ring_nf

/-- The inverse linear map: read each Kirov section in local chart
coordinates and package those coefficients as a cocycle 1-form. -/
noncomputable def inverseForm :
    Jacobians.Vendor.Kirov.HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForm X where
  toFun α :=
    ⟨sectionCoeff α,
      sectionCoeff_holomorphic α,
      sectionCoeff_cocycle α,
      sectionCoeff_zero_off_target α⟩
  map_add' α β := by
    apply HolomorphicOneForm.ext_of_coeff
    funext x z
    show sectionCoeff (α + β) x z = (sectionCoeff α + sectionCoeff β) x z
    by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target
    · rw [sectionCoeff_apply_of_mem (α + β) hz,
        Pi.add_apply, Pi.add_apply,
        sectionCoeff_apply_of_mem α hz,
        sectionCoeff_apply_of_mem β hz]
      exact localRep_add α β x ((extChartAt 𝓘(ℂ, ℂ) x).symm z)
    · rw [sectionCoeff_apply_of_not_mem (α + β) hz,
        Pi.add_apply, Pi.add_apply,
        sectionCoeff_apply_of_not_mem α hz,
        sectionCoeff_apply_of_not_mem β hz]
      simp
  map_smul' c α := by
    apply HolomorphicOneForm.ext_of_coeff
    funext x z
    show sectionCoeff (c • α) x z = (c • sectionCoeff α) x z
    by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target
    · rw [sectionCoeff_apply_of_mem (c • α) hz,
        Pi.smul_apply, Pi.smul_apply,
        sectionCoeff_apply_of_mem α hz]
      exact localRep_smul c α x ((extChartAt 𝓘(ℂ, ℂ) x).symm z)
    · rw [sectionCoeff_apply_of_not_mem (c • α) hz,
        Pi.smul_apply, Pi.smul_apply,
        sectionCoeff_apply_of_not_mem α hz]
      simp

theorem bridgeForm_inverseForm
    (α : Jacobians.Vendor.Kirov.HolomorphicOneForms X) :
    bridgeForm (inverseForm α) = α := by
  apply ContMDiffSection.ext
  intro y
  change BridgeForm.rawCLM (inverseForm α) y y = α.toFun y
  unfold BridgeForm.rawCLM
  have hy_tgt : (extChartAt 𝓘(ℂ, ℂ) y) y ∈ (extChartAt 𝓘(ℂ, ℂ) y).target :=
    mem_extChartAt_target y
  change sectionCoeff α y ((extChartAt 𝓘(ℂ, ℂ) y) y) •
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) y = α.toFun y
  rw [sectionCoeff_apply_of_mem α hy_tgt]
  rw [(extChartAt 𝓘(ℂ, ℂ) y).left_inv (mem_extChartAt_source y)]
  have hy_chart : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hy_base :
      y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  have hmfd :
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).continuousLinearMapAt ℂ y =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) y) y :=
    TangentBundle.continuousLinearMapAt_trivializationAt hy_chart
  have hcoe :
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).continuousLinearEquivAt
        ℂ y hy_base : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) =
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y).continuousLinearMapAt ℂ y :=
    Bundle.Trivialization.coe_continuousLinearEquivAt_eq'
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y) hy_base
  have htoFun := toFun_eq_localRep_smul α y y hy_base
  rw [← hmfd, ← hcoe]
  exact htoFun.symm

theorem inverseForm_bridgeForm (form : HolomorphicOneForm X) :
    inverseForm (bridgeForm form) = form :=
  bridgeForm_injective (by rw [bridgeForm_inverseForm])

end BridgeFormEquiv

/-- The canonical linear isomorphism between the cocycle representation of
holomorphic one-forms and Kirov's cotangent-bundle-section representation. -/
noncomputable def bridgeFormEquiv :
    HolomorphicOneForm X ≃ₗ[ℂ] Jacobians.Vendor.Kirov.HolomorphicOneForms X :=
  LinearEquiv.ofLinear (bridgeForm : HolomorphicOneForm X →ₗ[ℂ] _)
    BridgeFormEquiv.inverseForm
    (by
      apply LinearMap.ext
      intro α
      exact BridgeFormEquiv.bridgeForm_inverseForm α)
    (by
      apply LinearMap.ext
      intro form
      exact BridgeFormEquiv.inverseForm_bridgeForm form)

end Jacobians.Bridge
