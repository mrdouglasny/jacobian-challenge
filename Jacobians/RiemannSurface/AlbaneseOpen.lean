import Mathlib
import Jacobians.Axioms.AbelJacobiMap
import Jacobians.RiemannSurface.PeriodDiscretenessKirovRoute
import Jacobians.Bridge.KirovDolbeaultPeriods

open scoped Manifold ContDiff Topology
open Jacobians Jacobians.RiemannSurface Jacobians.AbelianVariety Jacobians.Axioms

namespace Jacobians.RiemannSurface

theorem ofCurveImpl_sub_eq_primitive {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (Qstar Q : X)
    (hQ_src : Q ∈ (chartAt ℂ Qstar).source)
    (hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 - s) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar
            + s • (extChartAt 𝓘(ℂ, ℂ) Qstar) Q ∈
          (extChartAt 𝓘(ℂ, ℂ) Qstar).target) :
    ofCurveImpl X x₀ Q - ofCurveImpl X x₀ Qstar =
      ULift.up (QuotientAddGroup.mk' (periodLatticeInBasis X (Classical.arbitrary X)
        (jacobianBasis X)).toAddSubgroup
        (fun i => formChartPrimitive Qstar (jacobianBasis X i) ((chartAt ℂ Qstar) Q))) := by
  have h_sub_eq : (QuotientAddGroup.mk' (periodLatticeInBasis X (Classical.arbitrary X)
        (jacobianBasis X)).toAddSubgroup (ofCurveAmbient X x₀ Q - ofCurveAmbient X x₀ x₀)) -
      QuotientAddGroup.mk' (periodLatticeInBasis X (Classical.arbitrary X)
        (jacobianBasis X)).toAddSubgroup (ofCurveAmbient X x₀ Qstar - ofCurveAmbient X x₀ x₀) =
    QuotientAddGroup.mk' (periodLatticeInBasis X (Classical.arbitrary X)
      (jacobianBasis X)).toAddSubgroup (ofCurveAmbient X x₀ Q - ofCurveAmbient X x₀ Qstar) := by
    rw [← map_sub]
    congr 1
    ext i
    simp only [Pi.sub_apply]
    ring
  unfold ofCurveImpl
  change ULift.up (
    QuotientAddGroup.mk' (periodLatticeInBasis X (Classical.arbitrary X)
      (jacobianBasis X)).toAddSubgroup (ofCurveAmbient X x₀ Q - ofCurveAmbient X x₀ x₀) -
    QuotientAddGroup.mk' (periodLatticeInBasis X (Classical.arbitrary X)
      (jacobianBasis X)).toAddSubgroup (ofCurveAmbient X x₀ Qstar - ofCurveAmbient X x₀ x₀)
  ) = ULift.up (QuotientAddGroup.mk' (periodLatticeInBasis X (Classical.arbitrary X)
    (jacobianBasis X)).toAddSubgroup (fun i => formChartPrimitive Qstar
      (jacobianBasis X i) ((chartAt ℂ Qstar) Q)))
  congr 1
  rw [h_sub_eq]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  have h_mem := aux_ofCurveAmbient_chartLine_mem (X := X) x₀ Qstar Q
    (by simpa using hQ_src) hseg
  have h_int_eq : ∀ i, ∫ t in (0 : ℝ)..1,
            (jacobianBasis X i).coeff Qstar
              ((1 - (t : ℂ)) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar
                + (t : ℂ) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Q)
              * ((extChartAt 𝓘(ℂ, ℂ) Qstar) Q
                - (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar) =
          formChartPrimitive Qstar (jacobianBasis X i) ((chartAt ℂ Qstar) Q) := by
    intro i
    rw [formChartPrimitive]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht' := hseg t ht
    have ht'' : (1 - (t : ℂ)) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Qstar
        + (t : ℂ) • (extChartAt 𝓘(ℂ, ℂ) Qstar) Q ∈ (chartAt ℂ Qstar).target := by
      simpa [extChartAt] using ht'
    rw [← formChartCoeff_eq_coeff Qstar (jacobianBasis X i) ht'']
    congr 2
    simp [extChartAt, smul_eq_mul]
    ring
  simp_rw [h_int_eq] at h_mem
  have h_eq : (fun i => ofCurveAmbient X x₀ Q i - (ofCurveAmbient X x₀ Qstar i +
        formChartPrimitive Qstar (jacobianBasis X i) ((chartAt ℂ Qstar) Q))) =
      ofCurveAmbient X x₀ Q - ofCurveAmbient X x₀ Qstar -
        (fun i => formChartPrimitive Qstar (jacobianBasis X i) ((chartAt ℂ Qstar) Q)) := by
    ext i
    simp only [Pi.sub_apply]
    ring
  rw [h_eq] at h_mem
  exact h_mem

lemma ulift_up_sum {α : Type*} [AddCommMonoid α] {β : Type*} (s : Finset β) (f : β → α) :
    ULift.up (∑ x ∈ s, f x) = ∑ x ∈ s, ULift.up (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih]
    rfl

theorem J_jacobiMap_eq_sum {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X)
    (a : Fin (genus X) → X) (z : Fin (genus X) → ℂ)
    (hz : ∀ j, z j ∈ (chartAt ℂ (a j)).target)
    (hseg : ∀ j, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (1 - s) • (extChartAt 𝓘(ℂ, ℂ) (a j)) (a j)
          + s • (extChartAt 𝓘(ℂ, ℂ) (a j)) ((chartAt ℂ (a j)).symm (z j)) ∈
        (extChartAt 𝓘(ℂ, ℂ) (a j)).target) :
    ULift.up (QuotientAddGroup.mk' (periodLatticeInBasis X (Classical.arbitrary X)
      (jacobianBasis X)).toAddSubgroup (jacobiMap (jacobianBasis X) a z)) =
      ∑ j, (ofCurveImpl X x₀ ((chartAt ℂ (a j)).symm (z j)) - ofCurveImpl X x₀ (a j)) := by
  let L := (periodLatticeInBasis X (Classical.arbitrary X) (jacobianBasis X)).toAddSubgroup
  have h_diff (j : Fin (genus X)) :
      ofCurveImpl X x₀ ((chartAt ℂ (a j)).symm (z j)) - ofCurveImpl X x₀ (a j) =
        ULift.up (QuotientAddGroup.mk' L (fun i => formChartPrimitive (a j)
          (jacobianBasis X i) (z j))) := by
    have h_sub := ofCurveImpl_sub_eq_primitive x₀ (a j) ((chartAt ℂ (a j)).symm (z j))
      ((chartAt ℂ (a j)).map_target (hz j)) (hseg j)
    rw [h_sub]
    congr 2
    ext i
    rw [OpenPartialHomeomorph.right_inv _ (hz j)]
  rw [Finset.sum_congr rfl (fun j _ => h_diff j)]
  symm
  refine (ulift_up_sum _ _).symm.trans ?_
  congr 1
  dsimp only [L]
  rw [← map_sum]
  congr 1
  ext i
  simp only [Finset.sum_apply]
  rfl

theorem curve_image_subgroup_isOpen {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) (h : 0 < genus X) :
    ∃ U : Set (Jacobian X), IsOpen U ∧ U.Nonempty ∧
      U ⊆ (AddSubgroup.closure (Set.range (ofCurveImpl X x₀)) : Set (Jacobian X)) := by
  have _ := h
  let b := jacobianBasis X
  obtain ⟨a, hainj, hdet, hG0, hmap⟩ := exists_jacobiMap_map_nhds b
  have h_ball (j : Fin (genus X)) : ∃ r > 0,
      Metric.ball ((chartAt ℂ (a j)) (a j)) r ⊆ (chartAt ℂ (a j)).target := by
    have h_open := (chartAt ℂ (a j)).open_target
    have h_mem := (chartAt ℂ (a j)).map_source (ChartedSpace.mem_chart_source (a j))
    exact Metric.isOpen_iff.mp h_open _ h_mem
  let r (j : Fin (genus X)) : ℝ := Classical.choose (h_ball j)
  have hr_pos (j : Fin (genus X)) : 0 < r j := (Classical.choose_spec (h_ball j)).1
  have h_ball_sub (j : Fin (genus X)) :
      Metric.ball ((chartAt ℂ (a j)) (a j)) (r j) ⊆ (chartAt ℂ (a j)).target :=
    (Classical.choose_spec (h_ball j)).2
  let V : Set (Fin (genus X) → ℂ) := Set.pi Set.univ
    (fun j => Metric.ball ((chartAt ℂ (a j)) (a j)) (r j))
  have hV_nhds : V ∈ nhds (jacobiCenter a) := by
    apply set_pi_mem_nhds
    · exact Set.finite_univ
    · intro j _
      exact Metric.ball_mem_nhds _ (hr_pos j)
  have hV_map := hmap V hV_nhds
  let W := jacobiMap b a '' V
  let U₀ := interior W
  have h0_in_U₀ : (0 : Fin (genus X) → ℂ) ∈ U₀ := mem_interior_iff_mem_nhds.mpr hV_map
  let L := (periodLatticeInBasis X (Classical.arbitrary X) b).toAddSubgroup
  let proj : (Fin (genus X) → ℂ) → JacobianAmbient X := QuotientAddGroup.mk' L
  let U_amb := proj '' U₀
  have h_open_proj : IsOpenMap proj := Jacobians.Vendor.Kirov.ZLatticeQuotient.isOpenMap_mk L
  have h_open_amb : IsOpen U_amb := h_open_proj U₀ isOpen_interior
  have h_open_ulift : IsOpenMap (ULift.up : JacobianAmbient X → Jacobian X) :=
    (Homeomorph.ulift (X := JacobianAmbient X)).symm.isOpenMap
  let U := ULift.up '' U_amb
  have hU_open : IsOpen U := h_open_ulift U_amb h_open_amb
  have hU_ne : U.Nonempty := ⟨ULift.up (proj 0),
    Set.mem_image_of_mem _ (Set.mem_image_of_mem _ h0_in_U₀)⟩
  refine ⟨U, hU_open, hU_ne, ?_⟩
  rintro u ⟨w, ⟨z₀, hz₀_U₀, rfl⟩, rfl⟩
  have hz₀_W : z₀ ∈ W := interior_subset hz₀_U₀
  obtain ⟨z, hz_V, rfl⟩ := hz₀_W
  have hz_in_ball (j : Fin (genus X)) :
      z j ∈ Metric.ball ((chartAt ℂ (a j)) (a j)) (r j) := by
    simpa using hz_V j (Set.mem_univ j)
  have hz_in_target (j : Fin (genus X)) : z j ∈ (chartAt ℂ (a j)).target :=
    h_ball_sub j (hz_in_ball j)
  have h_seg_in (j : Fin (genus X)) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      (1 - s) • (extChartAt 𝓘(ℂ, ℂ) (a j)) (a j) +
        s • (extChartAt 𝓘(ℂ, ℂ) (a j)) ((chartAt ℂ (a j)).symm (z j)) ∈
      (extChartAt 𝓘(ℂ, ℂ) (a j)).target := by
    have h_ext : (extChartAt 𝓘(ℂ, ℂ) (a j)) ((chartAt ℂ (a j)).symm (z j)) = z j := by
      simp only [extChartAt, OpenPartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
        OpenPartialHomeomorph.toFun_eq_coe]
      exact OpenPartialHomeomorph.right_inv _ (hz_in_target j)
    have h_ext_center : (extChartAt 𝓘(ℂ, ℂ) (a j)) (a j) = (chartAt ℂ (a j)) (a j) := by
      simp only [extChartAt, OpenPartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
        OpenPartialHomeomorph.toFun_eq_coe]
    have h_ext_target : (extChartAt 𝓘(ℂ, ℂ) (a j)).target = (chartAt ℂ (a j)).target := by
      simp only [extChartAt, OpenPartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl]
    rw [h_ext, h_ext_center, h_ext_target]
    refine h_ball_sub j ?_
    exact convex_ball ((chartAt ℂ (a j)) (a j)) (r j)
      (Metric.mem_ball_self (hr_pos j)) (hz_in_ball j)
      (by linarith [hs.2]) (by linarith [hs.1]) (by linarith)
  have h_eq_sum : ULift.up (proj (jacobiMap b a z)) =
      ∑ j, (ofCurveImpl X x₀ ((chartAt ℂ (a j)).symm (z j)) - ofCurveImpl X x₀ (a j)) :=
    J_jacobiMap_eq_sum x₀ a z hz_in_target h_seg_in
  rw [h_eq_sum]
  let H : AddSubgroup (Jacobian X) := AddSubgroup.closure (Set.range (ofCurveImpl X x₀))
  let f := fun j => ofCurveImpl X x₀ ((chartAt ℂ (a j)).symm (z j)) - ofCurveImpl X x₀ (a j)
  have hf (j : Fin (genus X)) : f j ∈ H := by
    dsimp only [f]
    apply H.sub_mem
    · exact AddSubgroup.subset_closure ⟨_, rfl⟩
    · exact AddSubgroup.subset_closure ⟨_, rfl⟩
  have h_sum_s (s : Finset (Fin (genus X))) : (∑ j ∈ s, f j) ∈ H := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact H.zero_mem
    | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact H.add_mem (hf j) ih
  exact h_sum_s Finset.univ

end Jacobians.RiemannSurface

