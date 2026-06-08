import Mathlib
import Jacobians.ProjectiveCurve.PlaneCurve
import Jacobians.ProjectiveCurve.PlaneCurve.Atlas

open scoped Manifold Topology ContDiff

namespace Jacobians.ProjectiveCurve

lemma PlaneCurve_nhdsWithin_compl_singleton_neBot (H : PlaneCurveData) (x : PlaneCurve H) :
    (nhdsWithin x {x}ᶜ).NeBot := by
  let e := chartAt H x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have h_map := e.map_nhdsWithin_preimage_eq hx {e x}ᶜ
  have h_eq : nhdsWithin x (e ⁻¹' {e x}ᶜ) = nhdsWithin x {x}ᶜ := by
    refine nhdsWithin_eq_nhdsWithin' (e.open_source.mem_nhds hx) ?_
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, hy2⟩
      intro h_eq
      apply hy1
      rw [h_eq]
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, hy2⟩
      intro h_eq
      apply hy1
      exact e.injOn hy2 hx h_eq
  rw [← h_eq]
  rw [← Filter.map_neBot_iff e]
  rw [h_map]
  exact NormedField.nhdsNE_neBot (e x)

theorem dense_range_toPlaneCurve (H : PlaneCurveData) :
    Dense (Set.range (PlaneCurveAffine.toPlaneCurve H)) := by
  have h_ne : ∀ x : PlaneCurve H, (nhdsWithin x {x}ᶜ).NeBot :=
    PlaneCurve_nhdsWithin_compl_singleton_neBot H
  haveI : ∀ x : PlaneCurve H, (nhdsWithin x {x}ᶜ).NeBot := h_ne
  rw [range_toPlaneCurve_eq_compl_infinityPoints H]
  rw [Set.compl_eq_univ_diff]
  exact Dense.diff_finite dense_univ (infinityPoints_finite H)

noncomputable instance PlaneCurve.instConnectedSpace (H : PlaneCurveData) :
    ConnectedSpace (PlaneCurve H) := by
  have _hAff : ConnectedSpace (PlaneCurveAffine H) :=
    PlaneCurveAffine.AX_PlaneCurveAffine_connected H
  have hRange : IsConnected (Set.range (PlaneCurveAffine.toPlaneCurve H)) :=
    isConnected_range (continuous_toPlaneCurve H)
  have hDense : Dense (Set.range (PlaneCurveAffine.toPlaneCurve H)) :=
    dense_range_toPlaneCurve H
  have hUniv : IsConnected (Set.univ : Set (PlaneCurve H)) :=
    hDense.closure_eq ▸ hRange.closure
  exact connectedSpace_iff_univ.mpr hUniv

end Jacobians.ProjectiveCurve
