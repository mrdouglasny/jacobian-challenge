import Jacobians.ProjectiveCurve.Hyperelliptic.InvolutionOdd
import Jacobians.ProjectiveCurve.Hyperelliptic.OddForm
import Jacobians.Axioms.AbelJacobiMap


open scoped Manifold ContDiff Topology
open Jacobians Jacobians.ProjectiveCurve Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve.HyperellipticOdd Jacobians.ProjectiveCurve.HyperellipticAffine
open Jacobians.Axioms

noncomputable local instance (H : HyperellipticData) [Fact (Odd H.f.natDegree)] :
    ChartedSpace ℂ (OnePoint (HyperellipticAffine H)) :=
  show ChartedSpace ℂ (OnePoint (HyperellipticAffine H)) from @instChartedSpace H Fact.out

noncomputable local instance (H : HyperellipticData) [Fact (Odd H.f.natDegree)] :
    IsManifold 𝓘(ℂ, ℂ) ω (OnePoint (HyperellipticAffine H)) :=
  show IsManifold 𝓘(ℂ, ℂ) ω (OnePoint (HyperellipticAffine H)) from @instIsManifold H Fact.out

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
    (hp : p ∈ (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source) :
    hyperellipticInvolution H Fact.out p ∈
      (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source := by
  have h_chart : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source =
      (infinityChart H Fact.out).source := by
    rw [extChartAt_source]
    change (chartAt (H := H) (h := Fact.out)
      (OnePoint.infty : HyperellipticOdd H Fact.out)).source = _
    rw [chartAt_infty]
  have h_chart' : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source =
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
  · by_cases hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target
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
        have h_src : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm z ∈
            (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).source :=
          PartialEquiv.map_target _ hz
        have h_in_source :=
          σ_source H
            ((extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm z)
            h_src
        have h_eq := hRel OnePoint.infty OnePoint.infty z hz h_in_source
        rw [h_eq]
        have hz_target_eq :
            (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).target =
            (InfinityInverse.tLocalHomeomorph H).target := by
          rw [extChartAt_target]
          simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
            Set.range_id, Set.inter_univ]
          change (chartAt (H := H) (h := Fact.out)
            (OnePoint.infty : HyperellipticOdd H Fact.out)).target = _
          rw [chartAt_infty]
          rfl
        have h_eq_on : ⇑(extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)) ∘
            hyperellipticInvolution H Fact.out ∘
            ⇑(extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm =ᶠ[𝓝 z]
            (fun w => -w) := by
          have h_target_open :
              IsOpen (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).target :=
            isOpen_extChartAt_target _
          have h_nhds := h_target_open.mem_nhds hz
          filter_upwards [h_nhds] with w hw
          have hw' : w ∈ (InfinityInverse.tLocalHomeomorph H).target := hz_target_eq ▸ hw
          exact @hyperellipticInvolution_extChartAt_infty H Fact.out w hw'
        have h_fderiv : fderiv ℂ
            (⇑(extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)) ∘
             hyperellipticInvolution H Fact.out ∘
             ⇑(extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm) z =
            fderiv ℂ (fun w => -w) z :=
          h_eq_on.fderiv_eq
        change (hyperellipticOddForm H g).coeff OnePoint.infty
            ((extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out))
              (hyperellipticInvolution H Fact.out
                ((extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm z))) *
          (fderiv ℂ (⇑(extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)) ∘
            hyperellipticInvolution H Fact.out ∘
            ⇑(extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm) z 1) = _
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
        have h_chart_val : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out))
            (hyperellipticInvolution H Fact.out
              ((extChartAt 𝓘(ℂ, ℂ) (OnePoint.infty : HyperellipticOdd H Fact.out)).symm z)) = -z :=
          @hyperellipticInvolution_extChartAt_infty H Fact.out z (hz_target_eq ▸ hz)
        rw [h_chart_val]
        rw [AX_hyperellipticOddCoeff_neg H Fact.out g z]
        ring
      | coe_val a =>
        have h_src : (extChartAt 𝓘(ℂ, ℂ) (coe a)).symm z ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a)).source :=
          PartialEquiv.map_target _ hz
        rw [extChartAt_source] at h_src
        change _ ∈ (affineLiftChart a).source at h_src
        rw [affineLiftChart_source] at h_src
        rcases h_src with ⟨q_aff, hq_src, hq_eq⟩
        by_cases haY : a ∈ HyperellipticAffine.smoothLocusY H
        · have hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a)).symm
          z) ∈ (extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol)).source := by
            rw [← hq_eq]
            change (coe q_aff.invol : HyperellipticOdd H Fact.out) ∈
              (extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol)).source
            exact mem_extChartAt_source _
          have hRel := pullbackOneForm_isPullbackCoeffRel
            (hyperellipticInvolution H Fact.out)
            (hyperellipticInvolution_contMDiff H Fact.out)
            (hyperellipticOddForm H g)
          have h_eq := hRel (coe a) (coe q_aff.invol) z hz hy_src
          rw [h_eq]
          have hq_Y : q_aff ∈ HyperellipticAffine.smoothLocusY H := by
            have h_src' : q_aff.val.2 ∈
              (HyperellipticAffine.squareLocalHomeomorph a haY).source := by
              change q_aff ∈ (HyperellipticAffine.affineChartAt a).source at hq_src
              rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a haY] at hq_src
              exact hq_src
            have h_ne : q_aff.val.2 ≠ 0 := by
              intro hc
              have h0 : (0 : ℂ) ∈ (HyperellipticAffine.squareLocalHomeomorph a haY).source :=
                hc ▸ h_src'
              exact HyperellipticAffine.squareLocalHomeomorph_zero_notMem_source a haY h0
            exact h_ne
          have hq_invol_Y : q_aff.invol ∈ HyperellipticAffine.smoothLocusY H := by
            change q_aff.invol.val.2 ≠ 0
            simp only [HyperellipticAffine.invol_val, neg_ne_zero]
            exact hq_Y
          have h_z_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a)) ((extChartAt 𝓘(ℂ, ℂ) (coe a)).symm z) = z :=
            PartialEquiv.right_inv _ hz
          have h_q_val_1 : q_aff.val.1 = z := by
            rw [← hq_eq] at h_z_eq
            change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding
              OnePoint.isOpenEmbedding_coe) (coe q_aff : HyperellipticOdd H Fact.out) = z at h_z_eq
            erw [OpenPartialHomeomorph.lift_openEmbedding_apply] at h_z_eq
            rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY a haY] at h_z_eq
            exact h_z_eq
          have h_eval_eq : (extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol : HyperellipticOdd H
            Fact.out)) (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
              HyperellipticOdd H Fact.out)).symm z)) = z := by
            have hw_eq : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
              HyperellipticOdd H Fact.out)).symm z) = coe q_aff.invol := by
              rw [← hq_eq]
              rfl
            rw [hw_eq]
            change ((HyperellipticAffine.affineChartAt q_aff.invol).lift_openEmbedding
              OnePoint.isOpenEmbedding_coe) (coe q_aff.invol : HyperellipticOdd H Fact.out) = z
            erw [OpenPartialHomeomorph.lift_openEmbedding_apply]
            rw [HyperellipticAffine.affineChartAt_of_mem_smoothLocusY q_aff.invol hq_invol_Y]
            change q_aff.invol.val.1 = z
            rw [HyperellipticAffine.invol_val]
            exact h_q_val_1
          have h_eq_on : ⇑(extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol : HyperellipticOdd H Fact.out)) ∘
              hyperellipticInvolution H Fact.out ∘
              ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm =ᶠ[𝓝 z]
              (fun w => w) := by
            have h_cont_symm : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H
              Fact.out)).symm z :=
              (continuousOn_extChartAt_symm (coe a : HyperellipticOdd H
                Fact.out)).continuousAt (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz)
            have h_invol_cont : Continuous (hyperellipticInvolution H Fact.out) :=
              (hyperellipticInvolution_contMDiff H Fact.out).continuous
            have h_open_source : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol :
              HyperellipticOdd H Fact.out)).source :=
              isOpen_extChartAt_source _
            have h_pre1 : IsOpen (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ)
              (coe q_aff.invol : HyperellipticOdd H Fact.out)).source) :=
              h_open_source.preimage h_invol_cont
            have h_pre2 : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹'
              (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol :
                HyperellipticOdd H Fact.out)).source) ∈ 𝓝 z :=
              h_cont_symm.preimage_mem_nhds (h_pre1.mem_nhds hy_src)
            have h_nhds : ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target ∩
                (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹'
                  (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol
                    : HyperellipticOdd H Fact.out)).source)) ∈ 𝓝 z :=
              Filter.inter_mem (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz) h_pre2
            filter_upwards [h_nhds] with w hw
            obtain ⟨hw_target, hw_src⟩ := hw
            simp only [Function.comp_apply]
            have hp_w_src : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w
              ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source :=
              PartialEquiv.map_target _ hw_target
            rw [extChartAt_source] at hp_w_src
            change _ ∈ (affineLiftChart a).source at hp_w_src
            rw [affineLiftChart_source] at hp_w_src
            rcases hp_w_src with ⟨q_w, hq_w_src, hq_w_eq⟩
            have h_LHS : (extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol : HyperellipticOdd H Fact.out))
              (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
                HyperellipticOdd H Fact.out)).symm w)) = q_w.invol.val.1 := by
              rw [← hq_w_eq]
              change (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some q_aff.invol : OnePoint
                (HyperellipticAffine H))) (OnePoint.some q_w.invol : OnePoint
                  (HyperellipticAffine H)) = q_w.invol.val.1
              have h_symm : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some q_aff.invol : OnePoint
                (HyperellipticAffine H))) =
                  (chartAt ℂ (OnePoint.some q_aff.invol : OnePoint (HyperellipticAffine
                    H))).toPartialEquiv := by
                simp
              rw [h_symm]
              have h_chart_eq : _root_.chartAt ℂ (OnePoint.some q_aff.invol : OnePoint
                (HyperellipticAffine H)) =
                  Jacobians.ProjectiveCurve.HyperellipticOdd.chartAt (H := H) (h :=
                    Fact.out) (OnePoint.some q_aff.invol : OnePoint (HyperellipticAffine H)) := rfl
              rw [h_chart_eq]
              rw [chartAt_coe (H := H) (h := Fact.out) q_aff.invol]
              change ((affineLiftChart (h :=
                Fact.out) q_aff.invol).toPartialEquiv) (OnePoint.some q_w.invol : OnePoint
                  (HyperellipticAffine H)) = q_w.invol.val.1
              unfold affineLiftChart
              have h_chart_eq2 : ChartedSpace.chartAt q_aff.invol =
                Jacobians.ProjectiveCurve.HyperellipticAffine.affineChartAt (H :=
                  H) q_aff.invol := rfl
              rw [h_chart_eq2]
              rw [affineChartAt_of_mem_smoothLocusY q_aff.invol hq_invol_Y]
              change ((affineChartProjX q_aff.invol hq_invol_Y).lift_openEmbedding
                OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w.invol : OnePoint
                  (HyperellipticAffine H)) = q_w.invol.val.1
              erw [OpenPartialHomeomorph.lift_openEmbedding_apply]
              rfl
            have h_RHS : w = q_w.val.1 := by
              have h_w_eq : w =
                (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ,
                  ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w) := by
                rw [PartialEquiv.right_inv _ hw_target]
              rw [h_w_eq, ← hq_w_eq]
              change (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some a : OnePoint (HyperellipticAffine H)))
                (OnePoint.some q_w : OnePoint (HyperellipticAffine H)) = q_w.val.1
              have h_symm : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some a : OnePoint
                (HyperellipticAffine H))) =
                  (chartAt ℂ (OnePoint.some a : OnePoint (HyperellipticAffine
                    H))).toPartialEquiv := by
                simp
              rw [h_symm]
              have h_chart_eq : _root_.chartAt ℂ (OnePoint.some a : OnePoint
                (HyperellipticAffine H)) =
                  Jacobians.ProjectiveCurve.HyperellipticOdd.chartAt (H := H) (h :=
                    Fact.out) (OnePoint.some a : OnePoint (HyperellipticAffine H)) := rfl
              rw [h_chart_eq]
              rw [chartAt_coe (H := H) (h := Fact.out) a]
              change ((affineLiftChart (h :=
                Fact.out) a).toPartialEquiv) (OnePoint.some q_w : OnePoint
                  (HyperellipticAffine H)) = q_w.val.1
              unfold affineLiftChart
              have h_chart_eq2 : ChartedSpace.chartAt a =
                Jacobians.ProjectiveCurve.HyperellipticAffine.affineChartAt (H := H) a := rfl
              rw [h_chart_eq2]
              rw [affineChartAt_of_mem_smoothLocusY a haY]
              change ((affineChartProjX a haY).lift_openEmbedding
                OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w : OnePoint
                  (HyperellipticAffine H)) = q_w.val.1
              erw [OpenPartialHomeomorph.lift_openEmbedding_apply]
              rfl
            rw [h_LHS, h_RHS]
            rw [HyperellipticAffine.invol_val]
          have h_fderiv : fderiv ℂ
              (⇑(extChartAt 𝓘(ℂ, ℂ) (coe q_aff.invol : HyperellipticOdd H Fact.out)) ∘
               hyperellipticInvolution H Fact.out ∘
               ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm) z =
              fderiv ℂ (fun w => w) z :=
            h_eq_on.fderiv_eq
          have h_fderiv_id : (fderiv ℂ (fun w : ℂ => w) z) 1 = 1 := by
            have h_fderiv_at : HasFDerivAt (fun w : ℂ => w) (ContinuousLinearMap.id ℂ ℂ) z := by
              exact (ContinuousLinearMap.id ℂ ℂ).hasFDerivAt
            rw [h_fderiv_at.fderiv]
            rfl
          have h_coeff_neg : hyperellipticAffineCoeff g q_aff.invol z =
            - hyperellipticAffineCoeff g a z := by
            have ha_coeff : hyperellipticAffineCoeff g a z = g.eval z / q_aff.val.2 := by
              have h_eq_proj : hyperellipticAffineCoeff g a z = affineProjXCoeff g a haY z := by
                simp [hyperellipticAffineCoeff, haY]
              rw [h_eq_proj]
              unfold affineProjXCoeff
              have hzt : z ∈
                ((affineChartProjX a haY) : OpenPartialHomeomorph (HyperellipticAffine H)
                  ℂ).target := by
                have hz' := hz
                rw [extChartAt_target] at hz'
                change z ∈
                  (modelWithCornersSelf ℂ ℂ).symm ⁻¹' (chartAt ℂ (OnePoint.some a : OnePoint
                    (HyperellipticAffine H))).target ∩ Set.range (modelWithCornersSelf ℂ ℂ) at hz'
                have h_chart_eq : _root_.chartAt ℂ (OnePoint.some a : OnePoint
                  (HyperellipticAffine H)) =
                    Jacobians.ProjectiveCurve.HyperellipticOdd.chartAt (H := H) (h :=
                      Fact.out) (OnePoint.some a : OnePoint (HyperellipticAffine H)) := rfl
                rw [h_chart_eq] at hz'
                rw [chartAt_coe] at hz'
                simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
                  Set.range_id, Set.inter_univ] at hz'
                unfold affineLiftChart at hz'
                rw [OpenPartialHomeomorph.lift_openEmbedding_target] at hz'
                have h_chart_eq2 : ChartedSpace.chartAt a =
                  Jacobians.ProjectiveCurve.HyperellipticAffine.affineChartAt (H := H) a := rfl
                rw [h_chart_eq2] at hz'
                rw [affineChartAt_of_mem_smoothLocusY a haY] at hz'
                exact hz'
              rw [if_pos hzt]
              have h_snd := affineChartProjX_symm_apply_snd a haY hzt
              have hq_eq_aff : q_aff = (affineChartProjX a haY).symm z := by
                have hq_eq' : (coe q_aff : HyperellipticOdd H Fact.out) =
                  coe ((affineChartProjX a haY).symm z) := by
                  change (OnePoint.some q_aff : OnePoint (HyperellipticAffine H)) =
                    coe ((affineChartProjX a haY).symm z)
                  change (OnePoint.some q_aff : OnePoint (HyperellipticAffine H)) =
                    (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some a : OnePoint (HyperellipticAffine
                      H))).symm z at hq_eq
                  have h_symm : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some a : OnePoint
                    (HyperellipticAffine H))).symm z =
                      (chartAt ℂ (OnePoint.some a : OnePoint (HyperellipticAffine H))).symm z := by
                    simp
                  rw [h_symm] at hq_eq
                  have h_chart_eq : _root_.chartAt ℂ (OnePoint.some a : OnePoint
                    (HyperellipticAffine H)) =
                      Jacobians.ProjectiveCurve.HyperellipticOdd.chartAt (H := H) (h :=
                        Fact.out) (OnePoint.some a : OnePoint (HyperellipticAffine H)) := rfl
                  rw [h_chart_eq] at hq_eq
                  rw [chartAt_coe (H := H) (h := Fact.out) a] at hq_eq
                  change (OnePoint.some q_aff : OnePoint (HyperellipticAffine H)) =
                    (affineLiftChart a).symm z at hq_eq
                  rw [hq_eq]
                  unfold affineLiftChart
                  have h_chart_eq2 : ChartedSpace.chartAt a =
                    Jacobians.ProjectiveCurve.HyperellipticAffine.affineChartAt (H := H) a := rfl
                  rw [h_chart_eq2]
                  rw [affineChartAt_of_mem_smoothLocusY a haY]
                  rfl
                exact OnePoint.isOpenEmbedding_coe.injective hq_eq'
              rw [← hq_eq_aff] at h_snd
              rw [← h_snd]
            have hinvol_coeff : hyperellipticAffineCoeff g q_aff.invol z =
              g.eval z / (-q_aff.val.2) := by
              have h_eq_proj : hyperellipticAffineCoeff g q_aff.invol z =
                affineProjXCoeff g q_aff.invol hq_invol_Y z := by
                simp [hyperellipticAffineCoeff, hq_invol_Y]
              rw [h_eq_proj]
              unfold affineProjXCoeff
              have hzt : z ∈
                ((affineChartProjX q_aff.invol hq_invol_Y) : OpenPartialHomeomorph
                  (HyperellipticAffine H) ℂ).target := by
                have h_mem : q_aff.invol ∈ (affineChartProjX q_aff.invol hq_invol_Y).source :=
                  HyperellipticAffine.affineChartProjX_mem_source q_aff.invol hq_invol_Y
                have h_img := OpenPartialHomeomorph.map_source _ h_mem
                change q_aff.invol.val.1 ∈ _ at h_img
                rw [HyperellipticAffine.invol_val] at h_img
                rwa [h_q_val_1] at h_img
              rw [if_pos hzt]
              have h_mem : q_aff.invol ∈ (affineChartProjX q_aff.invol hq_invol_Y).source :=
                HyperellipticAffine.affineChartProjX_mem_source q_aff.invol hq_invol_Y
              have h_snd := affineChartProjX_symm_apply_snd q_aff.invol hq_invol_Y hzt
              rw [← h_snd]
              have h_left :=
                OpenPartialHomeomorph.left_inv (affineChartProjX q_aff.invol hq_invol_Y) h_mem
              change (affineChartProjX q_aff.invol hq_invol_Y).symm q_aff.invol.val.1 =
                q_aff.invol at h_left
              have h_invol_val1 : q_aff.invol.val.1 = z := by
                rw [HyperellipticAffine.invol_val]
                exact h_q_val_1
              rw [h_invol_val1] at h_left
              rw [h_left]
              rw [HyperellipticAffine.invol_val]
            rw [ha_coeff, hinvol_coeff]
            field_simp
          rw [h_eval_eq]
          rw [h_fderiv, h_fderiv_id, mul_one]
          have h_coeff_eq1 : (hyperellipticOddForm H g).coeff (coe q_aff.invol) z =
              hyperellipticAffineCoeff g q_aff.invol z := by
            have h_eq_odd : (hyperellipticOddForm H g).coeff (coe q_aff.invol) z =
                @hyperellipticOddCoeff H Fact.out g (coe q_aff.invol) z := by
              rw [hyperellipticOddForm_coeff_of_lt H hdeg]
            rw [h_eq_odd]
            rfl
          have h_coeff_eq2 : (hyperellipticOddForm H g).coeff (coe a) z =
              hyperellipticAffineCoeff g a z := by
            have h_eq_odd : (hyperellipticOddForm H g).coeff (coe a) z =
                @hyperellipticOddCoeff H Fact.out g (coe a) z := by
              rw [hyperellipticOddForm_coeff_of_lt H hdeg]
            rw [h_eq_odd]
            rfl
          rw [h_coeff_eq1, h_coeff_neg, h_coeff_eq2]
        · have haY0 : a.val.2 = 0 := by
            simpa [HyperellipticAffine.smoothLocusY] using haY
          have haX : a ∈ HyperellipticAffine.smoothLocusX H :=
            HyperellipticAffine.mem_smoothLocusX_of_y_eq_zero H haY0
          have hy_src : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
            HyperellipticOdd H Fact.out)).symm z) ∈
              (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source := by
            rw [← hq_eq]
            change (coe q_aff.invol : HyperellipticOdd H Fact.out) ∈
              (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source
            rw [extChartAt_source]
            change (coe q_aff.invol : HyperellipticOdd H Fact.out) ∈ (affineLiftChart a).source
            rw [affineLiftChart_source]
            refine ⟨q_aff.invol, ?_, rfl⟩
            change q_aff.invol ∈ (HyperellipticAffine.affineChartAt a).source
            rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY a haY]
            change q_aff.invol.val.1 ∈ (polynomialLocalHomeomorph a haX).source
            rw [HyperellipticAffine.invol_val]
            change q_aff.val.1 ∈ (polynomialLocalHomeomorph a haX).source
            change q_aff ∈ (affineChartProjY a haX).source
            change q_aff ∈ (HyperellipticAffine.affineChartAt a).source at hq_src
            rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY a haY] at hq_src
            exact hq_src
          have hRel := pullbackOneForm_isPullbackCoeffRel
            (hyperellipticInvolution H Fact.out)
            (hyperellipticInvolution_contMDiff H Fact.out)
            (hyperellipticOddForm H g)
          have h_eq := hRel (coe a) (coe a) z hz hy_src
          rw [h_eq]
          have h_z_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a)) ((extChartAt 𝓘(ℂ, ℂ) (coe a)).symm z) = z :=
            PartialEquiv.right_inv _ hz
          have h_q_val_2 : q_aff.val.2 = z := by
            rw [← hq_eq] at h_z_eq
            change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding
              OnePoint.isOpenEmbedding_coe) (coe q_aff : HyperellipticOdd H Fact.out) = z at h_z_eq
            erw [OpenPartialHomeomorph.lift_openEmbedding_apply] at h_z_eq
            rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY a haY] at h_z_eq
            exact h_z_eq
          have h_eval_eq : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out))
            (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd
              H Fact.out)).symm z)) = -z := by
            have hw_eq : hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
              HyperellipticOdd H Fact.out)).symm z) = coe q_aff.invol := by
              rw [← hq_eq]
              rfl
            rw [hw_eq]
            change ((HyperellipticAffine.affineChartAt a).lift_openEmbedding
              OnePoint.isOpenEmbedding_coe) (coe q_aff.invol : HyperellipticOdd H Fact.out) = -z
            erw [OpenPartialHomeomorph.lift_openEmbedding_apply]
            rw [HyperellipticAffine.affineChartAt_of_not_mem_smoothLocusY a haY]
            change q_aff.invol.val.2 = -z
            rw [HyperellipticAffine.invol_val]
            rw [h_q_val_2]
          rw [h_eval_eq]
          have h_eq_on : ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ∘
              hyperellipticInvolution H Fact.out ∘
              ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm =ᶠ[𝓝 z]
              (fun w => -w) := by
            have h_cont_symm : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H
              Fact.out)).symm z :=
              (continuousOn_extChartAt_symm (coe a : HyperellipticOdd H
                Fact.out)).continuousAt (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz)
            have h_invol_cont : Continuous (hyperellipticInvolution H Fact.out) :=
              (hyperellipticInvolution_contMDiff H Fact.out).continuous
            have h_open_source : IsOpen (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H
              Fact.out)).source :=
              isOpen_extChartAt_source _
            have h_pre1 : IsOpen (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ)
              (coe a : HyperellipticOdd H Fact.out)).source) :=
              h_open_source.preimage h_invol_cont
            have h_pre2 : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹'
              (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe a :
                HyperellipticOdd H Fact.out)).source) ∈ 𝓝 z :=
              h_cont_symm.preimage_mem_nhds (h_pre1.mem_nhds hy_src)
            have h_nhds : ((extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).target ∩
                (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm ⁻¹'
                  (hyperellipticInvolution H Fact.out ⁻¹' (extChartAt 𝓘(ℂ, ℂ) (coe a :
                    HyperellipticOdd H Fact.out)).source)) ∈ 𝓝 z :=
              Filter.inter_mem (IsOpen.mem_nhds (isOpen_extChartAt_target _) hz) h_pre2
            filter_upwards [h_nhds] with w hw
            obtain ⟨hw_target, hw_src⟩ := hw
            simp only [Function.comp_apply]
            have hp_w_src : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w
              ∈ (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).source :=
              PartialEquiv.map_target _ hw_target
            rw [extChartAt_source] at hp_w_src
            change _ ∈ (affineLiftChart a).source at hp_w_src
            rw [affineLiftChart_source] at hp_w_src
            rcases hp_w_src with ⟨q_w, hq_w_src, hq_w_eq⟩
            have h_LHS : (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out))
              (hyperellipticInvolution H Fact.out ((extChartAt 𝓘(ℂ, ℂ) (coe a :
                HyperellipticOdd H Fact.out)).symm w)) = q_w.invol.val.2 := by
              rw [← hq_w_eq]
              change (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some a : OnePoint (HyperellipticAffine H)))
                (OnePoint.some q_w.invol : OnePoint (HyperellipticAffine H)) = q_w.invol.val.2
              have h_symm : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some a : OnePoint
                (HyperellipticAffine H))) =
                  (chartAt ℂ (OnePoint.some a : OnePoint (HyperellipticAffine
                    H))).toPartialEquiv := by
                simp
              rw [h_symm]
              have h_chart_eq : _root_.chartAt ℂ (OnePoint.some a : OnePoint
                (HyperellipticAffine H)) =
                  Jacobians.ProjectiveCurve.HyperellipticOdd.chartAt (H := H) (h :=
                    Fact.out) (OnePoint.some a : OnePoint (HyperellipticAffine H)) := rfl
              rw [h_chart_eq]
              rw [chartAt_coe (H := H) (h := Fact.out) a]
              change ((affineLiftChart (h :=
                Fact.out) a).toPartialEquiv) (OnePoint.some q_w.invol : OnePoint
                  (HyperellipticAffine H)) = q_w.invol.val.2
              unfold affineLiftChart
              have h_chart_eq2 : ChartedSpace.chartAt a =
                Jacobians.ProjectiveCurve.HyperellipticAffine.affineChartAt (H := H) a := rfl
              rw [h_chart_eq2]
              rw [affineChartAt_of_not_mem_smoothLocusY a haY]
              change ((a.affineChartProjY haX).lift_openEmbedding
                OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w.invol : OnePoint
                  (HyperellipticAffine H)) = q_w.invol.val.2
              erw [OpenPartialHomeomorph.lift_openEmbedding_apply]
              rfl
            have h_RHS : w = q_w.val.2 := by
              have h_w_eq : w =
                (extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ((extChartAt 𝓘(ℂ,
                  ℂ) (coe a : HyperellipticOdd H Fact.out)).symm w) := by
                rw [PartialEquiv.right_inv _ hw_target]
              rw [h_w_eq, ← hq_w_eq]
              change (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some a : OnePoint (HyperellipticAffine H)))
                (OnePoint.some q_w : OnePoint (HyperellipticAffine H)) = q_w.val.2
              have h_symm : (extChartAt 𝓘(ℂ, ℂ) (OnePoint.some a : OnePoint
                (HyperellipticAffine H))) =
                  (chartAt ℂ (OnePoint.some a : OnePoint (HyperellipticAffine
                    H))).toPartialEquiv := by
                simp
              rw [h_symm]
              have h_chart_eq : _root_.chartAt ℂ (OnePoint.some a : OnePoint
                (HyperellipticAffine H)) =
                  Jacobians.ProjectiveCurve.HyperellipticOdd.chartAt (H := H) (h :=
                    Fact.out) (OnePoint.some a : OnePoint (HyperellipticAffine H)) := rfl
              rw [h_chart_eq]
              rw [chartAt_coe (H := H) (h := Fact.out) a]
              change ((affineLiftChart (h :=
                Fact.out) a).toPartialEquiv) (OnePoint.some q_w : OnePoint
                  (HyperellipticAffine H)) = q_w.val.2
              unfold affineLiftChart
              have h_chart_eq2 : ChartedSpace.chartAt a =
                Jacobians.ProjectiveCurve.HyperellipticAffine.affineChartAt (H := H) a := rfl
              rw [h_chart_eq2]
              rw [affineChartAt_of_not_mem_smoothLocusY a haY]
              change ((a.affineChartProjY haX).lift_openEmbedding
                OnePoint.isOpenEmbedding_coe) (OnePoint.some q_w : OnePoint
                  (HyperellipticAffine H)) = q_w.val.2
              erw [OpenPartialHomeomorph.lift_openEmbedding_apply]
              rfl
            rw [h_LHS, h_RHS]
            rw [HyperellipticAffine.invol_val]
          have h_fderiv : fderiv ℂ
              (⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)) ∘
               hyperellipticInvolution H Fact.out ∘
               ⇑(extChartAt 𝓘(ℂ, ℂ) (coe a : HyperellipticOdd H Fact.out)).symm) z =
              fderiv ℂ (fun w => -w) z :=
            h_eq_on.fderiv_eq
          have h_fderiv_neg : (fderiv ℂ (fun w : ℂ => -w) z) 1 = -1 := by
            have h_fderiv_at : HasFDerivAt (fun w : ℂ => -w) (-ContinuousLinearMap.id ℂ ℂ) z := by
              exact (-ContinuousLinearMap.id ℂ ℂ).hasFDerivAt
            rw [h_fderiv_at.fderiv]
            rfl
          rw [h_fderiv, h_fderiv_neg]
          have h_coeff_eq : (hyperellipticOddForm H g).coeff (coe a) (-z) =
            (hyperellipticOddForm H g).coeff (coe a) z := by
            have h1 : (hyperellipticOddForm H g).coeff (coe a) (-z) =
              hyperellipticAffineCoeff g a (-z) := by
              rw [hyperellipticOddForm_coeff_of_lt H hdeg]
              rfl
            have h2 : (hyperellipticOddForm H g).coeff (coe a) z =
              hyperellipticAffineCoeff g a z := by
              rw [hyperellipticOddForm_coeff_of_lt H hdeg]
              rfl
            rw [h1, h2]
            have ha_coeff_eq : hyperellipticAffineCoeff g a (-z) =
              affineProjYCoeff g a haX (-z) := by
              simp [hyperellipticAffineCoeff, haY]
            have ha_coeff_eq' : hyperellipticAffineCoeff g a z = affineProjYCoeff g a haX z := by
              simp [hyperellipticAffineCoeff, haY]
            rw [ha_coeff_eq, ha_coeff_eq']
            have ha_coeff_even : affineProjYCoeff g a haX (-z) = affineProjYCoeff g a haX z := by
              unfold affineProjYCoeff
              have h_target_eq : -z ∈
                ((affineChartProjY a haX) : OpenPartialHomeomorph (HyperellipticAffine H)
                  ℂ).target ↔ z ∈
                    ((affineChartProjY a haX) : OpenPartialHomeomorph (HyperellipticAffine H)
                      ℂ).target := by
                change -z ∈ (affineChartProjY a haX).target ↔ z ∈ (affineChartProjY a haX).target
                have h_neg_sq : (-z) ^ 2 = z ^ 2 := by ring
                change (-z) ^ 2 ∈ (polynomialLocalHomeomorph a haX).target ↔ z ^ 2 ∈
                  (polynomialLocalHomeomorph a haX).target
                rw [h_neg_sq]
              by_cases hzT : z ∈
                ((affineChartProjY a haX) : OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
              · have h_neg_zT : -z ∈
                ((affineChartProjY a haX) : OpenPartialHomeomorph (HyperellipticAffine H)
                  ℂ).target := by
                  rwa [h_target_eq]
                rw [if_pos h_neg_zT, if_pos hzT]
                have h_neg_sq : (-z) ^ 2 = z ^ 2 := by ring
                rw [h_neg_sq]
              · have h_neg_zT : -z ∉ ((affineChartProjY a haX) : OpenPartialHomeomorph
                (HyperellipticAffine H) ℂ).target := by
                  rwa [h_target_eq]
                rw [if_neg h_neg_zT, if_neg hzT]
            rw [ha_coeff_even]
          rw [h_coeff_eq]
          ring
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

theorem pullback_hyperellipticOddForm_eq_neg
    (H : HyperellipticData) [Fact (Odd H.f.natDegree)] (g : Polynomial ℂ) :
    pullbackOneForm (hyperellipticInvolution H Fact.out)
        (hyperellipticInvolution_contMDiff H Fact.out)
        (hyperellipticOddForm H g) =
      - hyperellipticOddForm H g := by
  apply HolomorphicOneForm.ext_of_coeff
  ext x z
  rw [pullback_coeff_eq]
  rfl

