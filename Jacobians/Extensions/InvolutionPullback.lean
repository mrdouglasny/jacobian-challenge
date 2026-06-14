import Jacobians.Extensions.HyperellipticOdd

open scoped Manifold ContDiff Topology
open Jacobians Jacobians.ProjectiveCurve Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve.HyperellipticOdd
open Jacobians.Axioms Jacobians.Extensions.HyperellipticOdd

noncomputable local instance (H : HyperellipticData) [Fact (Odd H.f.natDegree)] :
    ChartedSpace ℂ (OnePoint (HyperellipticAffine H)) :=
  show ChartedSpace ℂ (OnePoint (HyperellipticAffine H)) from @instChartedSpace H Fact.out

noncomputable local instance (H : HyperellipticData) [Fact (Odd H.f.natDegree)] :
    IsManifold 𝓘(ℂ, ℂ) ω (OnePoint (HyperellipticAffine H)) :=
  show IsManifold 𝓘(ℂ, ℂ) ω (OnePoint (HyperellipticAffine H)) from @instIsManifold H Fact.out

-- Declare the axioms
lemma t_neg (H : HyperellipticData) (w : ℂ) :
    InfinityInverse.t H (-w) = - InfinityInverse.t H w := by
  unfold InfinityInverse.t
  rw [neg_sq]
  ring

lemma source_neg (H : HyperellipticData) (w : ℂ)
    (hw : w ∈ (InfinityInverse.tLocalHomeomorph H).source) :
    -w ∈ (InfinityInverse.tLocalHomeomorph H).source := by
  unfold InfinityInverse.tLocalHomeomorph at hw ⊢
  rcases hw with ⟨⟨h_w, ⟨_, h_neg_w⟩⟩, h_US⟩
  refine ⟨⟨h_neg_w, ⟨h_neg_w, ?_⟩⟩, ?_⟩
  · change - (-w) ∈ (HasStrictFDerivAt.toOpenPartialHomeomorph (InfinityInverse.t H)
      (InfinityInverse.tLocalHomeomorph_hd H)).source
    rw [neg_neg]
    exact h_w
  · have h_US_neg : -w ∈ InfinityInverse.U_S H ↔ w ∈ InfinityInverse.U_S H := by
      change H.f.leadingCoeff⁻¹ * H.f.reverse.eval ((-w) ^ 2) ∈
        InfinityInverse.slitPlane ↔
          H.f.leadingCoeff⁻¹ * H.f.reverse.eval (w ^ 2) ∈
            InfinityInverse.slitPlane
      rw [neg_sq]
    rwa [h_US_neg]

lemma target_neg (H : HyperellipticData) (z : ℂ)
    (hz : z ∈ (InfinityInverse.tLocalHomeomorph H).target) :
    -z ∈ (InfinityInverse.tLocalHomeomorph H).target := by
  unfold InfinityInverse.tLocalHomeomorph at hz ⊢
  rcases hz with ⟨⟨hz_target, hz_source_symm⟩, hz_US⟩
  rcases hz_source_symm with ⟨h_w_source, h_neg_w_source⟩
  let e := HasStrictFDerivAt.toOpenPartialHomeomorph (InfinityInverse.t H)
    (InfinityInverse.tLocalHomeomorph_hd H)
  have h_coe : (⇑e : ℂ → ℂ) = InfinityInverse.t H :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe (InfinityInverse.tLocalHomeomorph_hd H)
  have h_app_neg : e (- e.symm z) = InfinityInverse.t H (- e.symm z) := by
    change ⇑e (- e.symm z) = _; rw [h_coe]
  have h_app_pos : e (e.symm z) = InfinityInverse.t H (e.symm z) := by
    change ⇑e (e.symm z) = _; rw [h_coe]
  have h_eq_neg_z : e (- e.symm z) = -z := by
    rw [h_app_neg, t_neg H, ← h_app_pos, e.right_inv hz_target]
  have h_neg_z_target : -z ∈ e.target := by
    rw [← h_eq_neg_z]
    exact e.map_source h_neg_w_source
  have h_symm_eq : e.symm (-z) = - e.symm z := by
    have h_in_source : e.symm (-z) ∈ e.source := e.map_target h_neg_z_target
    have h_inj := e.injOn h_in_source h_neg_w_source
    apply h_inj
    rw [e.right_inv h_neg_z_target, h_eq_neg_z]
  refine ⟨⟨h_neg_z_target, ?_⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [h_symm_eq]
      exact h_neg_w_source
    · rw [h_symm_eq]
      change - (- e.symm z) ∈ e.source
      rw [neg_neg]
      exact h_w_source
  · change ⇑(e.restrOpen (e.source ∩ (fun x => -x) ⁻¹' e.source) _).symm (-z) ∈
      InfinityInverse.U_S H
    rw [OpenPartialHomeomorph.coe_restrOpen_symm, h_symm_eq]
    have h_US_neg : - e.symm z ∈ InfinityInverse.U_S H ↔ e.symm z ∈ InfinityInverse.U_S H := by
      change H.f.leadingCoeff⁻¹ * H.f.reverse.eval ((- e.symm z) ^ 2) ∈
        InfinityInverse.slitPlane ↔
          H.f.leadingCoeff⁻¹ * H.f.reverse.eval ((e.symm z) ^ 2) ∈
            InfinityInverse.slitPlane
      rw [neg_sq]
    rwa [h_US_neg]

theorem AX_invol_mem_V (H : HyperellipticData) (q : HyperellipticAffine H)
    (hq : q ∈ HyperellipticOdd.V H) :
    q.invol ∈ HyperellipticOdd.V H := by
  dsimp [HyperellipticOdd.V] at hq ⊢
  rcases hq with ⟨hq1, hq2, hq3⟩
  refine ⟨hq1, neg_ne_zero.mpr hq2, ?_⟩
  have h_eq : -q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹ =
      - (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹) := by ring
  rw [h_eq]
  exact source_neg H _ hq3

theorem AX_hyperellipticOddCoeff_neg (H : HyperellipticData) (h : Odd H.f.natDegree)
    (g : Polynomial ℂ) (z : ℂ) :
    @hyperellipticOddCoeff H h g (OnePoint.infty : HyperellipticOdd H h) (-z) =
      @hyperellipticOddCoeff H h g (OnePoint.infty : HyperellipticOdd H h) z := by
  unfold hyperellipticOddCoeff
  dsimp [OnePoint.elim]
  by_cases hz : z ∈ (infinityChart H h).target
  · have hz_tLocal : z ∈ (InfinityInverse.tLocalHomeomorph H).target := hz
    have h_neg_z_tLocal : -z ∈ (InfinityInverse.tLocalHomeomorph H).target :=
      target_neg H z hz_tLocal
    have h_neg_z : -z ∈ (infinityChart H h).target := h_neg_z_tLocal
    rw [if_pos hz, if_pos h_neg_z]
    by_cases hz0 : z = 0
    · rw [hz0, neg_zero]
    · have h_neg_z0 : -z ≠ 0 := neg_ne_zero.mpr hz0
      rw [if_neg hz0, if_neg h_neg_z0]
      let e := HasStrictFDerivAt.toOpenPartialHomeomorph (InfinityInverse.t H)
        (InfinityInverse.tLocalHomeomorph_hd H)
      have h_coe : (⇑e : ℂ → ℂ) = InfinityInverse.t H :=
        HasStrictFDerivAt.toOpenPartialHomeomorph_coe (InfinityInverse.tLocalHomeomorph_hd H)
      have h_app_neg : e (- e.symm z) = InfinityInverse.t H (- e.symm z) := by
        change ⇑e (- e.symm z) = _; rw [h_coe]
      have h_app_pos : e (e.symm z) = InfinityInverse.t H (e.symm z) := by
        change ⇑e (e.symm z) = _; rw [h_coe]
      have hz_target_e : z ∈ e.target := by
        have hz' : z ∈ (InfinityInverse.tLocalHomeomorph H).target := hz
        unfold InfinityInverse.tLocalHomeomorph at hz'
        exact hz'.1.1
      have h_neg_w_source : - e.symm z ∈ e.source := by
        have hz' : z ∈ (InfinityInverse.tLocalHomeomorph H).target := hz
        unfold InfinityInverse.tLocalHomeomorph at hz'
        exact hz'.1.2.2
      have h_eq_neg_z : e (- e.symm z) = -z := by
        rw [h_app_neg, t_neg H, ← h_app_pos, e.right_inv hz_target_e]
      have h_neg_z_target : -z ∈ e.target := by
        rw [← h_eq_neg_z]
        exact e.map_source h_neg_w_source
      have h_symm_eq : e.symm (-z) = - e.symm z := by
        have h_in_source : e.symm (-z) ∈ e.source := e.map_target h_neg_z_target
        have h_inj := e.injOn h_in_source h_neg_w_source
        apply h_inj
        rw [e.right_inv h_neg_z_target, h_eq_neg_z]
      have h_symm_t_eq : (InfinityInverse.tLocalHomeomorph H).symm (-z) =
          - (InfinityInverse.tLocalHomeomorph H).symm z := by
        unfold InfinityInverse.tLocalHomeomorph
        rw [OpenPartialHomeomorph.coe_restrOpen_symm,
          OpenPartialHomeomorph.coe_restrOpen_symm, h_symm_eq]
      unfold infinityInverseMap
      unfold InfinityInverse.infinityInverseMap
      rw [dif_pos ⟨h_neg_z_tLocal, h_neg_z0⟩, dif_pos ⟨hz_tLocal, hz0⟩]
      dsimp
      have h_symm_t_eq' : ((InfinityInverse.tLocalHomeomorph H).symm (-z))⁻¹ ^ 2 =
          ((InfinityInverse.tLocalHomeomorph H).symm z)⁻¹ ^ 2 := by
        rw [h_symm_t_eq, inv_neg, neg_sq]
      rw [h_symm_t_eq']
      rfl
  · have h_neg_z : -z ∉ (infinityChart H h).target := by
      intro hc
      have h_neg_neg : -(-z) ∈ (infinityChart H h).target := by
        have hc_tLocal : -z ∈ (InfinityInverse.tLocalHomeomorph H).target := hc
        have h_neg_neg_tLocal := target_neg H (-z) hc_tLocal
        exact h_neg_neg_tLocal
      rw [neg_neg] at h_neg_neg
      exact hz h_neg_neg
    rw [if_neg hz, if_neg h_neg_z]
    rfl


lemma σ_source (H : HyperellipticData) [Fact (Odd H.f.natDegree)] (p : HyperellipticOdd H Fact.out)
    (hp : p ∈ (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source) :
    hyperellipticInvolution H Fact.out p ∈
      (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source := by
  have h_chart : (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source =
      (infinityChart H Fact.out).source := by
    rw [extChartAt_source]
    change (chartAt (H := H) (h := Fact.out)
      (OnePoint.infty : HyperellipticOdd H Fact.out)).source = _
    rw [chartAt_infty]
  have h_chart' : (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source =
      (infinityChart H Fact.out).source := by
    rw [extChartAt_source]
    change (chartAt (H := H) (h := Fact.out)
      (OnePoint.infty : HyperellipticOdd H Fact.out)).source = _
    rw [chartAt_infty]
  rw [h_chart] at hp
  rw [h_chart']
  change p ∈ { (OnePoint.infty : HyperellipticOdd H Fact.out) } ∪
    (coe : HyperellipticAffine H → HyperellipticOdd H Fact.out) '' V H at hp
  change hyperellipticInvolution H Fact.out p ∈ { (OnePoint.infty : HyperellipticOdd H Fact.out) } ∪
    (coe : HyperellipticAffine H → HyperellipticOdd H Fact.out) '' V H
  rcases hp with (hp | hp)
  · have hp_eq : p = OnePoint.infty := Set.mem_singleton_iff.mp hp
    rw [hp_eq]
    left
    change (OnePoint.infty : HyperellipticOdd H Fact.out) ∈ _
    exact Set.mem_singleton _
  · right
    rcases hp with ⟨q, hq, rfl⟩
    use q.invol
    refine ⟨AX_invol_mem_V H q hq, ?_⟩
    change hyperellipticInvolution H Fact.out (coe q : HyperellipticOdd H Fact.out) = coe (q.invol)
    rfl

theorem pullback_coeff_eq
    (H : HyperellipticData) [Fact (Odd H.f.natDegree)] (g : Polynomial ℂ)
    (x : HyperellipticOdd H Fact.out) (z : ℂ) :
    (pullbackOneForm (hyperellipticInvolution H Fact.out)
        (hyperellipticInvolution_contMDiff H Fact.out)
        (hyperellipticOddForm H g)).coeff x z =
      - (hyperellipticOddForm H g).coeff x z := by
  by_cases hdeg : g.natDegree < (H.f.natDegree - 1) / 2
  · by_cases hz : z ∈ (extChartAt 𝓘(ℂ) x).target
    · induction x using HyperellipticOdd.rec with
      | infty_val =>
        change (pullbackOneForm (hyperellipticInvolution H Fact.out)
            (hyperellipticInvolution_contMDiff H Fact.out)
            (hyperellipticOddForm H g)).coeff OnePoint.infty z =
          - (hyperellipticOddForm H g).coeff OnePoint.infty z
        have hRel := pullbackOneForm_isPullbackCoeffRel
          (hyperellipticInvolution H Fact.out)
          (hyperellipticInvolution_contMDiff H Fact.out)
          (hyperellipticOddForm H g)
        have h_src : (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm z ∈
            (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source :=
          PartialEquiv.map_target _ hz
        have h_in_source :=
          σ_source H
            ((extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm z)
            h_src
        have h_eq := hRel OnePoint.infty OnePoint.infty z hz h_in_source
        rw [h_eq]
        have hz_target_eq :
            (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).target =
            (InfinityInverse.tLocalHomeomorph H).target := by
          rw [extChartAt_target]
          simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id_eq,
            Set.range_id, Set.inter_univ]
          change (chartAt (H := H) (h := Fact.out)
            (OnePoint.infty : HyperellipticOdd H Fact.out)).target = _
          rw [chartAt_infty]
          rfl
        have h_eq_on : ⇑(extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)) ∘
            hyperellipticInvolution H Fact.out ∘
            ⇑(extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm =ᶠ[𝓝 z]
            (fun w => -w) := by
          have h_target_open :
              IsOpen (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).target :=
            isOpen_extChartAt_target _
          have h_nhds := h_target_open.mem_nhds hz
          filter_upwards [h_nhds] with w hw
          have hw' : w ∈ (InfinityInverse.tLocalHomeomorph H).target := hz_target_eq ▸ hw
          exact @hyperellipticInvolution_extChartAt_infty H Fact.out w hw'
        have h_fderiv : fderiv ℂ
            (⇑(extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)) ∘
             hyperellipticInvolution H Fact.out ∘
             ⇑(extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm) z =
            fderiv ℂ (fun w => -w) z :=
          h_eq_on.fderiv_eq
        change (hyperellipticOddForm H g).coeff OnePoint.infty
            ((extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out))
              (hyperellipticInvolution H Fact.out
                ((extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm z))) *
          (fderiv ℂ (⇑(extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)) ∘
            hyperellipticInvolution H Fact.out ∘
            ⇑(extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm) z 1) = _
        rw [h_fderiv]
        have h_fderiv_neg : (fderiv ℂ (fun w : ℂ => -w) z) 1 = -1 := by
          have h_fderiv_at : HasFDerivAt (fun w : ℂ => -w) (-ContinuousLinearMap.id ℂ ℂ) z := by
            exact (-ContinuousLinearMap.id ℂ ℂ).hasFDerivAt
          rw [h_fderiv_at.fderiv]
          rfl
        rw [h_fderiv_neg]
        have h_coeff_eq : (hyperellipticOddForm H g).coeff OnePoint.infty =
            @hyperellipticOddCoeff H Fact.out g OnePoint.infty := by
          rw [hyperellipticOddForm_coeff_of_lt H hdeg]
        rw [h_coeff_eq]
        have h_chart_val : (extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out))
            (hyperellipticInvolution H Fact.out
              ((extChartAt 𝓘(ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm z)) = -z :=
          @hyperellipticInvolution_extChartAt_infty H Fact.out z (hz_target_eq ▸ hz)
        rw [h_chart_val]
        rw [AX_hyperellipticOddCoeff_neg H Fact.out g z]
        ring
      | coe_val a =>
        sorry
    · have h1 : (pullbackOneForm (hyperellipticInvolution H Fact.out)
          (hyperellipticInvolution_contMDiff H Fact.out)
          (hyperellipticOddForm H g)).coeff x z = 0 :=
        (pullbackOneForm (hyperellipticInvolution H Fact.out)
          (hyperellipticInvolution_contMDiff H Fact.out)
          (hyperellipticOddForm H g)).2.2.2 x z hz
      have h2 : (hyperellipticOddForm H g).coeff x z = 0 :=
        (hyperellipticOddForm H g).2.2.2 x z hz
      rw [h1, h2, neg_zero]
  · have hg0 : hyperellipticOddForm H g = 0 := by
      unfold hyperellipticOddForm
      rw [dif_neg hdeg]
    rw [hg0]
    simp

theorem pullback_hyperellipticInvolution_eq_neg_proof
    (H : HyperellipticData) [Fact (Odd H.f.natDegree)] :
    pullbackOneForm (hyperellipticInvolution H Fact.out)
        (hyperellipticInvolution_contMDiff H Fact.out)
      = (-LinearMap.id : HolomorphicOneForm (HyperellipticOdd H Fact.out) →ₗ[ℂ]
          HolomorphicOneForm (HyperellipticOdd H Fact.out)) := by
  ext form x z
  rcases AX_HyperellipticOddOneForm_eq_form H form with ⟨g, hdeg, hg⟩
  rw [hg]
  rw [pullback_coeff_eq]
  have hRHS : ((-LinearMap.id : HolomorphicOneForm (HyperellipticOdd H Fact.out) →ₗ[ℂ]
      HolomorphicOneForm (HyperellipticOdd H Fact.out)) (hyperellipticOddForm H g)).coeff x z =
      - (hyperellipticOddForm H g).coeff x z := rfl
  exact hRHS
