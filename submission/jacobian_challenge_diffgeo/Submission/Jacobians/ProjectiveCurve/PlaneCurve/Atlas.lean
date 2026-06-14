import Mathlib
import Submission.Jacobians.ProjectiveCurve.PlaneCurve
import Submission.Jacobians.ProjectiveCurve.PlaneCurve.AffineChart

open MvPolynomial
open scoped Manifold Topology ContDiff

namespace Jacobians.ProjectiveCurve

noncomputable local instance instSetoid : Setoid { v : Fin 3 → ℂ // v ≠ 0 } :=
  projectivizationSetoid ℂ (Fin 3 → ℂ)

instance instTopologicalSpaceProjectivization :
    TopologicalSpace (Projectivization ℂ (Fin 3 → ℂ)) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (Fin 3 → ℂ))))

attribute [local instance] instTopologicalSpaceProjectivization

def Projectivization.U (i : Fin 3) : Set (Projectivization ℂ (Fin 3 → ℂ)) :=
  { p | ∃ v, ∃ hv, Projectivization.mk ℂ v hv = p ∧ v i ≠ 0 }

theorem isOpen_U (i : Fin 3) : IsOpen (Projectivization.U i) := by
  change IsOpen { p : Quotient instSetoid |
    ∃ v, ∃ hv, Projectivization.mk ℂ v hv = p ∧ v i ≠ 0 }
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  have h_eq : Quotient.mk' ⁻¹'
      { p : Quotient instSetoid |
        ∃ v, ∃ hv, Projectivization.mk ℂ v hv = p ∧ v i ≠ 0 } =
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val i ≠ 0 } := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv, h_mk, h_vi⟩
      have h_mk' : Projectivization.mk ℂ v hv =
          Projectivization.mk ℂ x.val x.property := h_mk
      rw [Projectivization.mk_eq_mk_iff ℂ v x.val hv x.property] at h_mk'
      rcases h_mk' with ⟨c, hc⟩
      intro h_zero
      apply h_vi
      have h_eval := congr_fun hc i
      change (c : ℂ) • x.val i = v i at h_eval
      rw [smul_eq_mul] at h_eval
      rw [h_zero, mul_zero] at h_eval
      exact h_eval.symm
    · intro h_xi
      refine ⟨x.val, x.property, ?_, h_xi⟩
      rfl
  rw [h_eq]
  have h_pre : { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val i ≠ 0 } =
      (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val i) ⁻¹' { z : ℂ | z ≠ 0 } := rfl
  rw [h_pre]
  refine IsOpen.preimage ?_ isOpen_compl_singleton
  exact (continuous_apply i).comp continuous_subtype_val

lemma mem_U_iff_representative_ne_zero (v : Fin 3 → ℂ) (hv : v ≠ 0) (i : Fin 3) :
    Projectivization.mk ℂ v hv ∈ Projectivization.U i ↔ v i ≠ 0 := by
  constructor
  · rintro ⟨v', hv', h_mk, h_vi⟩
    have h_mk_symm := h_mk.symm
    rw [Projectivization.mk_eq_mk_iff ℂ v v' hv hv'] at h_mk_symm
    rcases h_mk_symm with ⟨c, hc⟩
    intro hz
    have h_eval := congr_fun hc i
    change (c : ℂ) * v' i = v i at h_eval
    rw [← h_eval] at hz
    rcases mul_eq_zero.mp hz with hc0 | h_v'0
    · exact (c.ne_zero hc0).elim
    · contradiction
  · intro h
    exact ⟨v, hv, rfl, h⟩

theorem rep_ne_zero_of_mem_U (p : Projectivization ℂ (Fin 3 → ℂ)) (i : Fin 3)
    (hp : p ∈ Projectivization.U i) : p.rep i ≠ 0 := by
  rcases hp with ⟨v, hv, h_mk, h_vi⟩
  have h_eq : Projectivization.mk ℂ p.rep (Projectivization.rep_nonzero p) =
              Projectivization.mk ℂ v hv := by
    rw [Projectivization.mk_rep, h_mk]
  rw [Projectivization.mk_eq_mk_iff ℂ p.rep v (Projectivization.rep_nonzero p) hv] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have h_eval := congr_fun hc i
  change (c : ℂ) • v i = p.rep i at h_eval
  rw [smul_eq_mul] at h_eval
  rw [← h_eval]
  exact mul_ne_zero c.ne_zero h_vi

theorem mem_U_of_rep_ne_zero (p : Projectivization ℂ (Fin 3 → ℂ)) (i : Fin 3)
    (hp : p.rep i ≠ 0) : p ∈ Projectivization.U i := by
  refine ⟨p.rep, Projectivization.rep_nonzero p, Projectivization.mk_rep p, hp⟩

def PlaneCurve.U (H : PlaneCurveData) (i : Fin 3) : Set (PlaneCurve H) :=
  { p | (p.val : Projectivization ℂ (Fin 3 → ℂ)) ∈ Projectivization.U i }

theorem compl_infinityPoints_eq_U (H : PlaneCurveData) :
    (infinityPoints H)ᶜ = PlaneCurve.U H 2 := by
  ext p
  simp only [Set.mem_compl_iff, infinityPoints, Set.mem_setOf_eq, PlaneCurve.U]
  have h_iff : p.1 ∈ Projectivization.U 2 ↔ p.1.rep 2 ≠ 0 := by
    constructor
    · exact rep_ne_zero_of_mem_U p.1 2
    · exact mem_U_of_rep_ne_zero p.1 2
  constructor
  · intro h
    rw [h_iff]
    intro hz
    apply h
    refine ⟨p.1.rep, Projectivization.rep_nonzero p.1, Projectivization.mk_rep p.1, hz⟩
  · rintro hp ⟨v, hv, h_mk, hz⟩
    have h_rep := rep_ne_zero_of_mem_U p.1 2 hp
    have h_eq : Projectivization.mk ℂ p.1.rep (Projectivization.rep_nonzero p.1) =
                Projectivization.mk ℂ v hv := by
      rw [Projectivization.mk_rep, h_mk]
    rw [Projectivization.mk_eq_mk_iff ℂ p.1.rep v (Projectivization.rep_nonzero p.1) hv] at h_eq
    rcases h_eq with ⟨c, hc⟩
    have h_eval := congr_fun hc 2
    change (c : ℂ) • v 2 = p.1.rep 2 at h_eval
    rw [smul_eq_mul, hz, mul_zero] at h_eval
    exact h_rep h_eval.symm

theorem isOpen_U_PC (H : PlaneCurveData) (i : Fin 3) : IsOpen (PlaneCurve.U H i) :=
  IsOpen.preimage continuous_subtype_val (isOpen_U i)

private lemma homogeneous_eval_smul {p : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) (c : ℂ) (v : Fin 3 → ℂ) :
    p.eval (fun i => c * v i) = c ^ d * p.eval v := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  calc
    (∑ x ∈ p.support, p.coeff x * ∏ i, (c * v i) ^ x i)
        = ∑ x ∈ p.support, p.coeff x * (c ^ d * ∏ i, v i ^ x i) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hdeg : d = ∑ i ∈ x.support, x i :=
            hp.degree_eq_sum_deg_support hx
          have hprod : ∏ i : Fin 3, (c * v i) ^ x i =
              c ^ d * ∏ i : Fin 3, v i ^ x i := by
            rw [hdeg]
            simp_rw [mul_pow]
            rw [Finset.prod_mul_distrib]
            congr 1
            rw [Finset.prod_pow_eq_pow_sum]
            have hsum : x.sum (fun _ n => n) = ∑ i : Fin 3, x i :=
              Finsupp.sum_fintype x (fun _ n => n) (by simp)
            change c ^ (∑ i : Fin 3, x i) = c ^ (∑ i ∈ x.support, x i)
            rw [← hsum]
            rfl
          rw [hprod]
    _ = c ^ d * ∑ x ∈ p.support, p.coeff x * ∏ i, v i ^ x i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring

theorem check_rep (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    ∃ c : ℂˣ, (Projectivization.rep (Projectivization.mk ℂ v hv)) = c • v := by
  have h := Projectivization.mk_eq_mk_iff ℂ
    (Projectivization.rep (Projectivization.mk ℂ v hv)) v
    (Projectivization.rep_nonzero _) hv
  rw [Projectivization.mk_rep] at h
  rcases h.mp rfl with ⟨c, hc⟩
  exact ⟨c, hc.symm⟩

noncomputable def projZ (p : Projectivization ℂ (Fin 3 → ℂ)) : ℂ × ℂ :=
  (p.rep 0 / p.rep 2, p.rep 1 / p.rep 2)

noncomputable def projY (p : Projectivization ℂ (Fin 3 → ℂ)) : ℂ × ℂ :=
  (p.rep 0 / p.rep 1, p.rep 2 / p.rep 1)

noncomputable def projX (p : Projectivization ℂ (Fin 3 → ℂ)) : ℂ × ℂ :=
  (p.rep 1 / p.rep 0, p.rep 2 / p.rep 0)

lemma projZ_mk_eq (v : Fin 3 → ℂ) (hv : v ≠ 0) (_h2 : v 2 ≠ 0) :
    projZ (Projectivization.mk ℂ v hv) = (v 0 / v 2, v 1 / v 2) := by
  dsimp [projZ]
  obtain ⟨c, hc⟩ := check_rep v hv
  have hc0 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 0 = (c : ℂ) * v 0 := congr_fun hc 0
  have hc1 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 1 = (c : ℂ) * v 1 := congr_fun hc 1
  have hc2 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 2 = (c : ℂ) * v 2 := congr_fun hc 2
  rw [hc0, hc1, hc2]
  rw [mul_div_mul_left (v 0) (v 2) c.ne_zero]
  rw [mul_div_mul_left (v 1) (v 2) c.ne_zero]

lemma projY_mk_eq (v : Fin 3 → ℂ) (hv : v ≠ 0) (_h1 : v 1 ≠ 0) :
    projY (Projectivization.mk ℂ v hv) = (v 0 / v 1, v 2 / v 1) := by
  dsimp [projY]
  obtain ⟨c, hc⟩ := check_rep v hv
  have hc0 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 0 = (c : ℂ) * v 0 := congr_fun hc 0
  have hc1 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 1 = (c : ℂ) * v 1 := congr_fun hc 1
  have hc2 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 2 = (c : ℂ) * v 2 := congr_fun hc 2
  rw [hc0, hc1, hc2]
  rw [mul_div_mul_left (v 0) (v 1) c.ne_zero]
  rw [mul_div_mul_left (v 2) (v 1) c.ne_zero]

lemma projX_mk_eq (v : Fin 3 → ℂ) (hv : v ≠ 0) (_h0 : v 0 ≠ 0) :
    projX (Projectivization.mk ℂ v hv) = (v 1 / v 0, v 2 / v 0) := by
  dsimp [projX]
  obtain ⟨c, hc⟩ := check_rep v hv
  have hc0 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 0 = (c : ℂ) * v 0 := congr_fun hc 0
  have hc1 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 1 = (c : ℂ) * v 1 := congr_fun hc 1
  have hc2 : (Projectivization.rep (Projectivization.mk ℂ v hv)) 2 = (c : ℂ) * v 2 := congr_fun hc 2
  rw [hc0, hc1, hc2]
  rw [mul_div_mul_left (v 1) (v 0) c.ne_zero]
  rw [mul_div_mul_left (v 2) (v 0) c.ne_zero]

theorem continuous_projZ_comp :
    ContinuousOn (projZ ∘ Quotient.mk') { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 2 ≠ 0 } := by
  have h_eq : ∀ x ∈ { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 2 ≠ 0 },
      (projZ ∘ Quotient.mk') x = (x.val 0 / x.val 2, x.val 1 / x.val 2) := by
    rintro x (hx : x.val 2 ≠ 0)
    exact projZ_mk_eq x.val x.property hx
  refine ContinuousOn.congr ?_ h_eq
  have hc0 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 0)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 2 ≠ 0 } :=
    (continuous_apply 0).comp continuous_subtype_val |>.continuousOn
  have hc1 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 1)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 2 ≠ 0 } :=
    (continuous_apply 1).comp continuous_subtype_val |>.continuousOn
  have hc2 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 2)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 2 ≠ 0 } :=
    (continuous_apply 2).comp continuous_subtype_val |>.continuousOn
  have hc2_nz : ∀ x ∈ { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 2 ≠ 0 }, x.val 2 ≠ 0 :=
    fun _ hx => hx
  have h_div0 := hc0.div hc2 hc2_nz
  have h_div1 := hc1.div hc2 hc2_nz
  exact h_div0.prodMk h_div1

theorem continuous_projY_comp :
    ContinuousOn (projY ∘ Quotient.mk') { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 1 ≠ 0 } := by
  have h_eq : ∀ x ∈ { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 1 ≠ 0 },
      (projY ∘ Quotient.mk') x = (x.val 0 / x.val 1, x.val 2 / x.val 1) := by
    rintro x (hx : x.val 1 ≠ 0)
    exact projY_mk_eq x.val x.property hx
  refine ContinuousOn.congr ?_ h_eq
  have hc0 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 0)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 1 ≠ 0 } :=
    (continuous_apply 0).comp continuous_subtype_val |>.continuousOn
  have hc2 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 2)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 1 ≠ 0 } :=
    (continuous_apply 2).comp continuous_subtype_val |>.continuousOn
  have hc1 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 1)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 1 ≠ 0 } :=
    (continuous_apply 1).comp continuous_subtype_val |>.continuousOn
  have hc1_nz : ∀ x ∈ { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 1 ≠ 0 }, x.val 1 ≠ 0 :=
    fun _ hx => hx
  have h_div0 := hc0.div hc1 hc1_nz
  have h_div2 := hc2.div hc1 hc1_nz
  exact h_div0.prodMk h_div2

theorem continuous_projX_comp :
    ContinuousOn (projX ∘ Quotient.mk') { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 0 ≠ 0 } := by
  have h_eq : ∀ x ∈ { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 0 ≠ 0 },
      (projX ∘ Quotient.mk') x = (x.val 1 / x.val 0, x.val 2 / x.val 0) := by
    rintro x (hx : x.val 0 ≠ 0)
    exact projX_mk_eq x.val x.property hx
  refine ContinuousOn.congr ?_ h_eq
  have hc1 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 1)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 0 ≠ 0 } :=
    (continuous_apply 1).comp continuous_subtype_val |>.continuousOn
  have hc2 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 2)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 0 ≠ 0 } :=
    (continuous_apply 2).comp continuous_subtype_val |>.continuousOn
  have hc0 : ContinuousOn (fun x : { v : Fin 3 → ℂ // v ≠ 0 } => x.val 0)
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 0 ≠ 0 } :=
    (continuous_apply 0).comp continuous_subtype_val |>.continuousOn
  have hc0_nz : ∀ x ∈ { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 0 ≠ 0 }, x.val 0 ≠ 0 :=
    fun _ hx => hx
  have h_div1 := hc1.div hc0 hc0_nz
  have h_div2 := hc2.div hc0 hc0_nz
  exact h_div1.prodMk h_div2

theorem continuousOn_of_isOpenQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {f : X → Y} (hf : IsOpenQuotientMap f)
    {g : Y → Z} {U : Set Y} (hU : IsOpen U) (hc : ContinuousOn (g ∘ f) (f ⁻¹' U)) :
    ContinuousOn g U := by
  have h_open_pre : IsOpen (f ⁻¹' U) := hU.preimage hf.continuous
  rw [continuousOn_open_iff hU]
  intro V hV
  have hc' := (continuousOn_open_iff h_open_pre).mp hc V hV
  rw [Set.inter_comm] at hc'
  have h_pre : (g ∘ f) ⁻¹' V ∩ f ⁻¹' U = f ⁻¹' (g ⁻¹' V ∩ U) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply]
  rw [h_pre] at hc'
  have h_img := hf.isOpenMap _ hc'
  have h_surj : f '' (f ⁻¹' (g ⁻¹' V ∩ U)) = g ⁻¹' V ∩ U := by
    exact Set.image_preimage_eq _ hf.surjective
  rw [h_surj] at h_img
  rw [Set.inter_comm]
  exact h_img

theorem isOpenMap_of_continuous_inverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (_hf : Continuous f) {g : Set.range f → X}
    (hg : Continuous g) (h_left : ∀ x, g ⟨f x, ⟨x, rfl⟩⟩ = x)
    (h_range : IsOpen (Set.range f)) : IsOpenMap f := by
  intro U hU
  have h_pre : IsOpen (g ⁻¹' U) := hU.preimage hg
  rcases isOpen_induced_iff.mp h_pre with ⟨W, hW, h_eq⟩
  have h_img : f '' U = W ∩ Set.range f := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_mem : ⟨f x, ⟨x, rfl⟩⟩ ∈ g ⁻¹' U := by
        simp only [Set.mem_preimage]
        rw [h_left]
        exact hx
      have hyW_change : (⟨f x, ⟨x, rfl⟩⟩ : Subtype (Set.range f)) ∈ Subtype.val ⁻¹' W :=
        h_eq.symm ▸ h_mem
      exact ⟨hyW_change, ⟨x, rfl⟩⟩
    · intro h_hyp
      simp only [Set.mem_inter_iff, Set.mem_range] at h_hyp
      rcases h_hyp with ⟨hyW, ⟨x, hx⟩⟩
      subst hx
      have hyW' : ⟨f x, ⟨x, rfl⟩⟩ ∈ g ⁻¹' U := by
        have hyW_change : (⟨f x, ⟨x, rfl⟩⟩ : Subtype (Set.range f)) ∈
            Subtype.val ⁻¹' W := hyW
        exact h_eq ▸ hyW_change
      simp only [Set.mem_preimage] at hyW'
      rw [h_left] at hyW'
      exact ⟨x, hyW', rfl⟩
  rw [h_img]
  exact IsOpen.inter hW h_range

lemma preimage_U_eq (i : Fin 3) :
    Quotient.mk' ⁻¹' Projectivization.U i = { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val i ≠ 0 } := by
  ext x
  simp only [Set.mem_preimage, Projectivization.U, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, hv, h_mk, h_vi⟩
    have h_mk' : Projectivization.mk ℂ v hv =
        Projectivization.mk ℂ x.val x.property := h_mk
    rw [Projectivization.mk_eq_mk_iff ℂ v x.val hv x.property] at h_mk'
    rcases h_mk' with ⟨c, hc⟩
    intro h_zero
    apply h_vi
    have h_eval := congr_fun hc i
    change (c : ℂ) • x.val i = v i at h_eval
    rw [smul_eq_mul] at h_eval
    rw [h_zero, mul_zero] at h_eval
    exact h_eval.symm
  · intro h_xi
    refine ⟨x.val, x.property, ?_, h_xi⟩
    rfl

theorem continuousOn_projZ : ContinuousOn projZ (Projectivization.U 2) := by
  have h_eq : Quotient.mk' ⁻¹' Projectivization.U 2 =
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 2 ≠ 0 } := preimage_U_eq 2
  have hc_comp := continuous_projZ_comp
  rw [← h_eq] at hc_comp
  exact continuousOn_of_isOpenQuotientMap projectivization_isOpenQuotientMap_mk' (isOpen_U 2)
    hc_comp

theorem continuousOn_projY : ContinuousOn projY (Projectivization.U 1) := by
  have h_eq : Quotient.mk' ⁻¹' Projectivization.U 1 =
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 1 ≠ 0 } := preimage_U_eq 1
  have hc_comp := continuous_projY_comp
  rw [← h_eq] at hc_comp
  exact continuousOn_of_isOpenQuotientMap projectivization_isOpenQuotientMap_mk' (isOpen_U 1)
    hc_comp

theorem continuousOn_projX : ContinuousOn projX (Projectivization.U 0) := by
  have h_eq : Quotient.mk' ⁻¹' Projectivization.U 0 =
      { x : { v : Fin 3 → ℂ // v ≠ 0 } | x.val 0 ≠ 0 } := preimage_U_eq 0
  have hc_comp := continuous_projX_comp
  rw [← h_eq] at hc_comp
  exact continuousOn_of_isOpenQuotientMap projectivization_isOpenQuotientMap_mk' (isOpen_U 0)
    hc_comp

noncomputable def PlaneCurveAffineY.toPlaneCurve (H : PlaneCurveData)
    (p : PlaneCurveAffineY H) : PlaneCurve H :=
  ⟨Projectivization.mk ℂ ![p.val.1, 1, p.val.2] (by
    intro h
    have h1 : ![p.val.1, 1, p.val.2] 1 = 0 := congrFun h 1
    exact one_ne_zero h1),
   ![p.val.1, 1, p.val.2],
   (by
    intro h
    have h1 : ![p.val.1, 1, p.val.2] 1 = 0 := congrFun h 1
    exact one_ne_zero h1),
   rfl,
   p.property⟩

theorem continuous_toPlaneCurveY (H : PlaneCurveData) :
    Continuous (PlaneCurveAffineY.toPlaneCurve H) := by
  letI : Setoid { v : Fin 3 → ℂ // v ≠ 0 } := projectivizationSetoid ℂ (Fin 3 → ℂ)
  letI : TopologicalSpace (Projectivization ℂ (Fin 3 → ℂ)) :=
    inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ _)))
  apply Continuous.subtype_mk
  refine continuous_quotient_mk'.comp ?_
  apply Continuous.subtype_mk
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · exact continuous_subtype_val.fst
  · exact continuous_const
  · exact continuous_subtype_val.snd

noncomputable def PlaneCurveAffineX.toPlaneCurve (H : PlaneCurveData)
    (p : PlaneCurveAffineX H) : PlaneCurve H :=
  ⟨Projectivization.mk ℂ ![1, p.val.1, p.val.2] (by
    intro h
    have h0 : ![1, p.val.1, p.val.2] 0 = 0 := congrFun h 0
    exact one_ne_zero h0),
   ![1, p.val.1, p.val.2],
   (by
    intro h
    have h0 : ![1, p.val.1, p.val.2] 0 = 0 := congrFun h 0
    exact one_ne_zero h0),
   rfl,
   p.property⟩

theorem continuous_toPlaneCurveX (H : PlaneCurveData) :
    Continuous (PlaneCurveAffineX.toPlaneCurve H) := by
  letI : Setoid { v : Fin 3 → ℂ // v ≠ 0 } := projectivizationSetoid ℂ (Fin 3 → ℂ)
  letI : TopologicalSpace (Projectivization ℂ (Fin 3 → ℂ)) :=
    inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ _)))
  apply Continuous.subtype_mk
  refine continuous_quotient_mk'.comp ?_
  apply Continuous.subtype_mk
  refine continuous_pi (fun i => ?_)
  fin_cases i
  · exact continuous_const
  · exact continuous_subtype_val.fst
  · exact continuous_subtype_val.snd

theorem toPlaneCurve_injective (H : PlaneCurveData) :
    Function.Injective (PlaneCurveAffine.toPlaneCurve H) := by
  intro p1 p2 h
  have h_eq : (PlaneCurveAffine.toPlaneCurve H p1).val =
              (PlaneCurveAffine.toPlaneCurve H p2).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffine.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have h2 := congr_fun hc 2
  have hc1 : (c : ℂ) = 1 := by
    change (c : ℂ) * 1 = 1 at h2
    rw [mul_one] at h2
    exact h2
  apply Subtype.ext
  ext
  · have h0 := congr_fun hc 0
    change (c : ℂ) * p2.val.1 = p1.val.1 at h0
    rw [hc1, one_mul] at h0
    exact h0.symm
  · have h1 := congr_fun hc 1
    change (c : ℂ) * p2.val.2 = p1.val.2 at h1
    rw [hc1, one_mul] at h1
    exact h1.symm

theorem toPlaneCurveY_injective (H : PlaneCurveData) :
    Function.Injective (PlaneCurveAffineY.toPlaneCurve H) := by
  intro p1 p2 h
  have h_eq : (PlaneCurveAffineY.toPlaneCurve H p1).val =
              (PlaneCurveAffineY.toPlaneCurve H p2).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffineY.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have h1 := congr_fun hc 1
  have hc1 : (c : ℂ) = 1 := by
    change (c : ℂ) * 1 = 1 at h1
    rw [mul_one] at h1
    exact h1
  apply Subtype.ext
  ext
  · have h0 := congr_fun hc 0
    change (c : ℂ) * p2.val.1 = p1.val.1 at h0
    rw [hc1, one_mul] at h0
    exact h0.symm
  · have h2 := congr_fun hc 2
    change (c : ℂ) * p2.val.2 = p1.val.2 at h2
    rw [hc1, one_mul] at h2
    exact h2.symm

theorem toPlaneCurveX_injective (H : PlaneCurveData) :
    Function.Injective (PlaneCurveAffineX.toPlaneCurve H) := by
  intro p1 p2 h
  have h_eq : (PlaneCurveAffineX.toPlaneCurve H p1).val =
              (PlaneCurveAffineX.toPlaneCurve H p2).val := congrArg Subtype.val h
  dsimp [PlaneCurveAffineX.toPlaneCurve] at h_eq
  rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have h0 := congr_fun hc 0
  have hc1 : (c : ℂ) = 1 := by
    change (c : ℂ) * 1 = 1 at h0
    rw [mul_one] at h0
    exact h0
  apply Subtype.ext
  ext
  · have h1 := congr_fun hc 1
    change (c : ℂ) * p2.val.1 = p1.val.1 at h1
    rw [hc1, one_mul] at h1
    exact h1.symm
  · have h2 := congr_fun hc 2
    change (c : ℂ) * p2.val.2 = p1.val.2 at h2
    rw [hc1, one_mul] at h2
    exact h2.symm

noncomputable def PlaneCurveAffine.projZ_inv (H : PlaneCurveData)
    (p : Set.range (PlaneCurveAffine.toPlaneCurve H)) : PlaneCurveAffine H := by
  let pt := projZ p.val.val
  have h_range : p.val ∈ PlaneCurve.U H 2 := by
    rcases p.property with ⟨q, hq⟩
    rw [← hq]
    dsimp [PlaneCurveAffine.toPlaneCurve, PlaneCurve.U, Projectivization.U]
    refine ⟨![q.val.1, q.val.2, 1], ?_, ?_⟩
    · intro h
      have h2 : ![q.val.1, q.val.2, 1] 2 = 0 := congrFun h 2
      exact one_ne_zero h2
    · refine ⟨rfl, ?_⟩
      exact one_ne_zero
  have h_vec : ![pt.1, pt.2, 1] = (p.val.val.rep 2)⁻¹ • p.val.val.rep := by
    ext i
    fin_cases i
    · dsimp [pt, projZ]
      rw [div_eq_mul_inv, mul_comm]
    · dsimp [pt, projZ]
      rw [div_eq_mul_inv, mul_comm]
    · dsimp
      rw [inv_mul_cancel₀ (rep_ne_zero_of_mem_U p.val.val 2 h_range)]
  have h_eval : H.F.val.eval ![pt.1, pt.2, 1] = 0 := by
    rw [h_vec]
    change H.F.val.eval (fun i => (p.val.val.rep 2)⁻¹ * p.val.val.rep i) = 0
    rw [homogeneous_eval_smul H.F.homogeneous]
    have heval_rep : H.F.val.eval p.val.val.rep = 0 := by
      obtain ⟨v, hv, h_mk, heval⟩ := p.val.property
      have h_eq : Projectivization.mk ℂ p.val.val.rep (Projectivization.rep_nonzero p.val.val) =
                  Projectivization.mk ℂ v hv := by
        rw [Projectivization.mk_rep, h_mk]
      rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
      rcases h_eq with ⟨c, hc⟩
      have h_comp : p.val.val.rep = (c : ℂ) • v := hc.symm
      rw [h_comp]
      change H.F.val.eval (fun i => (c : ℂ) * v i) = 0
      rw [homogeneous_eval_smul H.F.homogeneous]
      rw [heval, mul_zero]
    rw [heval_rep, mul_zero]
  exact ⟨pt, h_eval⟩

noncomputable def PlaneCurveAffineY.projY_inv (H : PlaneCurveData)
    (p : Set.range (PlaneCurveAffineY.toPlaneCurve H)) : PlaneCurveAffineY H := by
  let pt := projY p.val.val
  have h_range : p.val ∈ PlaneCurve.U H 1 := by
    rcases p.property with ⟨q, hq⟩
    rw [← hq]
    exact ⟨![q.val.1, 1, q.val.2], (by
      intro h
      exact one_ne_zero (congrFun h 1)),
      rfl,
      one_ne_zero⟩
  have h_vec : ![pt.1, 1, pt.2] = (p.val.val.rep 1)⁻¹ • p.val.val.rep := by
    ext i
    fin_cases i
    · dsimp [pt, projY]
      rw [div_eq_mul_inv, mul_comm]
    · dsimp
      rw [inv_mul_cancel₀ (rep_ne_zero_of_mem_U p.val.val 1 h_range)]
    · dsimp [pt, projY]
      rw [div_eq_mul_inv, mul_comm]
  have h_eval : H.F.val.eval ![pt.1, 1, pt.2] = 0 := by
    rw [h_vec]
    change H.F.val.eval (fun i => (p.val.val.rep 1)⁻¹ * p.val.val.rep i) = 0
    rw [homogeneous_eval_smul H.F.homogeneous]
    have heval_rep : H.F.val.eval p.val.val.rep = 0 := by
      obtain ⟨v, hv, h_mk, heval⟩ := p.val.property
      have h_eq : Projectivization.mk ℂ p.val.val.rep
                    (Projectivization.rep_nonzero p.val.val) =
                  Projectivization.mk ℂ v hv := by
        rw [Projectivization.mk_rep, h_mk]
      rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
      rcases h_eq with ⟨c, hc⟩
      have h_comp : p.val.val.rep = (c : ℂ) • v := hc.symm
      rw [h_comp]
      change H.F.val.eval (fun i => (c : ℂ) * v i) = 0
      rw [homogeneous_eval_smul H.F.homogeneous]
      rw [heval, mul_zero]
    rw [heval_rep, mul_zero]
  exact ⟨pt, h_eval⟩

noncomputable def PlaneCurveAffineX.projX_inv (H : PlaneCurveData)
    (p : Set.range (PlaneCurveAffineX.toPlaneCurve H)) : PlaneCurveAffineX H := by
  let pt := projX p.val.val
  have h_range : p.val ∈ PlaneCurve.U H 0 := by
    rcases p.property with ⟨q, hq⟩
    rw [← hq]
    exact ⟨![1, q.val.1, q.val.2], (by
      intro h
      exact one_ne_zero (congrFun h 0)),
      rfl,
      one_ne_zero⟩
  have h_vec : ![1, pt.1, pt.2] = (p.val.val.rep 0)⁻¹ • p.val.val.rep := by
    ext i
    fin_cases i
    · dsimp
      rw [inv_mul_cancel₀ (rep_ne_zero_of_mem_U p.val.val 0 h_range)]
    · dsimp [pt, projX]
      rw [div_eq_mul_inv, mul_comm]
    · dsimp [pt, projX]
      rw [div_eq_mul_inv, mul_comm]
  have h_eval : H.F.val.eval ![1, pt.1, pt.2] = 0 := by
    rw [h_vec]
    change H.F.val.eval (fun i => (p.val.val.rep 0)⁻¹ * p.val.val.rep i) = 0
    rw [homogeneous_eval_smul H.F.homogeneous]
    have heval_rep : H.F.val.eval p.val.val.rep = 0 := by
      obtain ⟨v, hv, h_mk, heval⟩ := p.val.property
      have h_eq : Projectivization.mk ℂ p.val.val.rep
                    (Projectivization.rep_nonzero p.val.val) =
                  Projectivization.mk ℂ v hv := by
        rw [Projectivization.mk_rep, h_mk]
      rw [Projectivization.mk_eq_mk_iff ℂ] at h_eq
      rcases h_eq with ⟨c, hc⟩
      have h_comp : p.val.val.rep = (c : ℂ) • v := hc.symm
      rw [h_comp]
      change H.F.val.eval (fun i => (c : ℂ) * v i) = 0
      rw [homogeneous_eval_smul H.F.homogeneous]
      rw [heval, mul_zero]
    rw [heval_rep, mul_zero]
  exact ⟨pt, h_eval⟩

theorem continuous_projZ_inv (H : PlaneCurveData) :
    Continuous (PlaneCurveAffine.projZ_inv H) := by
  apply Continuous.subtype_mk
  have h_comp : (fun p : Set.range (PlaneCurveAffine.toPlaneCurve H) => projZ p.val.val) =
      projZ ∘ (fun p : Set.range (PlaneCurveAffine.toPlaneCurve H) => p.val.val) := rfl
  rw [h_comp]
  refine ContinuousOn.comp_continuous continuousOn_projZ ?_ ?_
  · exact continuous_subtype_val.comp continuous_subtype_val
  · rintro ⟨p, ⟨q, hq⟩⟩
    subst hq
    dsimp [PlaneCurveAffine.toPlaneCurve, PlaneCurve.U, Projectivization.U]
    refine ⟨![q.val.1, q.val.2, 1], ?_, ?_⟩
    · intro h
      have h2 : ![q.val.1, q.val.2, 1] 2 = 0 := congrFun h 2
      exact one_ne_zero h2
    · refine ⟨rfl, ?_⟩
      exact one_ne_zero

theorem continuous_projY_inv (H : PlaneCurveData) :
    Continuous (PlaneCurveAffineY.projY_inv H) := by
  apply Continuous.subtype_mk
  have h_comp : (fun p : Set.range (PlaneCurveAffineY.toPlaneCurve H) => projY p.val.val) =
      projY ∘ (fun p : Set.range (PlaneCurveAffineY.toPlaneCurve H) => p.val.val) := rfl
  rw [h_comp]
  refine ContinuousOn.comp_continuous continuousOn_projY ?_ ?_
  · exact continuous_subtype_val.comp continuous_subtype_val
  · rintro ⟨p, ⟨q, hq⟩⟩
    subst hq
    dsimp [PlaneCurveAffineY.toPlaneCurve, PlaneCurve.U, Projectivization.U]
    refine ⟨![q.val.1, 1, q.val.2], ?_, ?_⟩
    · intro h
      have h1 : ![q.val.1, 1, q.val.2] 1 = 0 := congrFun h 1
      exact one_ne_zero h1
    · refine ⟨rfl, ?_⟩
      exact one_ne_zero

theorem continuous_projX_inv (H : PlaneCurveData) :
    Continuous (PlaneCurveAffineX.projX_inv H) := by
  apply Continuous.subtype_mk
  have h_comp : (fun p : Set.range (PlaneCurveAffineX.toPlaneCurve H) => projX p.val.val) =
      projX ∘ (fun p : Set.range (PlaneCurveAffineX.toPlaneCurve H) => p.val.val) := rfl
  rw [h_comp]
  refine ContinuousOn.comp_continuous continuousOn_projX ?_ ?_
  · exact continuous_subtype_val.comp continuous_subtype_val
  · rintro ⟨p, ⟨q, hq⟩⟩
    subst hq
    dsimp [PlaneCurveAffineX.toPlaneCurve, PlaneCurve.U, Projectivization.U]
    refine ⟨![1, q.val.1, q.val.2], ?_, ?_⟩
    · intro h
      have h0 : ![1, q.val.1, q.val.2] 0 = 0 := congrFun h 0
      exact one_ne_zero h0
    · refine ⟨rfl, ?_⟩
      exact one_ne_zero

theorem left_inverse_projZ_inv (H : PlaneCurveData) (x : PlaneCurveAffine H) :
    PlaneCurveAffine.projZ_inv H ⟨PlaneCurveAffine.toPlaneCurve H x, ⟨x, rfl⟩⟩ = x := by
  apply Subtype.ext
  dsimp [PlaneCurveAffine.projZ_inv, PlaneCurveAffine.toPlaneCurve, projZ]
  obtain ⟨c, hc⟩ := check_rep ![x.val.1, x.val.2, 1] (by
    intro h
    have h2 : ![x.val.1, x.val.2, 1] 2 = 0 := congrFun h 2
    exact one_ne_zero h2)
  have hc0 : (Projectivization.rep (Projectivization.mk ℂ ![x.val.1, x.val.2, 1] _)) 0 =
    (c : ℂ) * x.val.1 := congr_fun hc 0
  have hc1 : (Projectivization.rep (Projectivization.mk ℂ ![x.val.1, x.val.2, 1] _)) 1 =
    (c : ℂ) * x.val.2 := congr_fun hc 1
  have hc2 : (Projectivization.rep (Projectivization.mk ℂ ![x.val.1, x.val.2, 1] _)) 2 =
    (c : ℂ) * 1 := congr_fun hc 2
  rw [hc0, hc1, hc2]
  rw [mul_one]
  rw [mul_div_cancel_left₀ x.val.1 c.ne_zero]
  rw [mul_div_cancel_left₀ x.val.2 c.ne_zero]

theorem left_inverse_projY_inv (H : PlaneCurveData) (x : PlaneCurveAffineY H) :
    PlaneCurveAffineY.projY_inv H ⟨PlaneCurveAffineY.toPlaneCurve H x, ⟨x, rfl⟩⟩ = x := by
  apply Subtype.ext
  dsimp [PlaneCurveAffineY.projY_inv, PlaneCurveAffineY.toPlaneCurve, projY]
  obtain ⟨c, hc⟩ := check_rep ![x.val.1, 1, x.val.2] (by
    intro h
    have h1 : ![x.val.1, 1, x.val.2] 1 = 0 := congrFun h 1
    exact one_ne_zero h1)
  have hc0 : (Projectivization.rep (Projectivization.mk ℂ ![x.val.1, 1, x.val.2] _)) 0 =
    (c : ℂ) * x.val.1 := congr_fun hc 0
  have hc1 : (Projectivization.rep (Projectivization.mk ℂ ![x.val.1, 1, x.val.2] _)) 1 =
    (c : ℂ) * 1 := congr_fun hc 1
  have hc2 : (Projectivization.rep (Projectivization.mk ℂ ![x.val.1, 1, x.val.2] _)) 2 =
    (c : ℂ) * x.val.2 := congr_fun hc 2
  rw [hc0, hc1, hc2]
  rw [mul_one]
  rw [mul_div_cancel_left₀ x.val.1 c.ne_zero]
  rw [mul_div_cancel_left₀ x.val.2 c.ne_zero]

theorem left_inverse_projX_inv (H : PlaneCurveData) (x : PlaneCurveAffineX H) :
    PlaneCurveAffineX.projX_inv H ⟨PlaneCurveAffineX.toPlaneCurve H x, ⟨x, rfl⟩⟩ = x := by
  apply Subtype.ext
  dsimp [PlaneCurveAffineX.projX_inv, PlaneCurveAffineX.toPlaneCurve, projX]
  obtain ⟨c, hc⟩ := check_rep ![1, x.val.1, x.val.2] (by
    intro h
    have h0 : ![1, x.val.1, x.val.2] 0 = 0 := congrFun h 0
    exact one_ne_zero h0)
  have hc0 : (Projectivization.rep (Projectivization.mk ℂ ![1, x.val.1, x.val.2] _)) 0 =
    (c : ℂ) * 1 := congr_fun hc 0
  have hc1 : (Projectivization.rep (Projectivization.mk ℂ ![1, x.val.1, x.val.2] _)) 1 =
    (c : ℂ) * x.val.1 := congr_fun hc 1
  have hc2 : (Projectivization.rep (Projectivization.mk ℂ ![1, x.val.1, x.val.2] _)) 2 =
    (c : ℂ) * x.val.2 := congr_fun hc 2
  rw [hc0, hc1, hc2]
  rw [mul_one]
  rw [mul_div_cancel_left₀ x.val.1 c.ne_zero]
  rw [mul_div_cancel_left₀ x.val.2 c.ne_zero]

theorem toPlaneCurve_projZ_inv (H : PlaneCurveData)
    (p : Set.range (PlaneCurveAffine.toPlaneCurve H)) :
    PlaneCurveAffine.toPlaneCurve H (PlaneCurveAffine.projZ_inv H p) = p.val := by
  rcases p with ⟨q, ⟨x, rfl⟩⟩
  rw [left_inverse_projZ_inv H x]

theorem toPlaneCurveY_projY_inv (H : PlaneCurveData)
    (p : Set.range (PlaneCurveAffineY.toPlaneCurve H)) :
    PlaneCurveAffineY.toPlaneCurve H (PlaneCurveAffineY.projY_inv H p) = p.val := by
  rcases p with ⟨q, ⟨x, rfl⟩⟩
  rw [left_inverse_projY_inv H x]

theorem toPlaneCurveX_projX_inv (H : PlaneCurveData)
    (p : Set.range (PlaneCurveAffineX.toPlaneCurve H)) :
    PlaneCurveAffineX.toPlaneCurve H (PlaneCurveAffineX.projX_inv H p) = p.val := by
  rcases p with ⟨q, ⟨x, rfl⟩⟩
  rw [left_inverse_projX_inv H x]

theorem range_toPlaneCurve_eq_U2 (H : PlaneCurveData) :
    Set.range (PlaneCurveAffine.toPlaneCurve H) = PlaneCurve.U H 2 := by
  ext p
  simp only [Set.mem_range, PlaneCurve.U, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, rfl⟩
    dsimp [PlaneCurveAffine.toPlaneCurve, Projectivization.U]
    refine ⟨![q.val.1, q.val.2, 1], ?_, ?_⟩
    · intro h
      have h2 : ![q.val.1, q.val.2, 1] 2 = 0 := congrFun h 2
      exact one_ne_zero h2
    · refine ⟨rfl, ?_⟩
      exact one_ne_zero
  · intro hp
    obtain ⟨v, hv, h_mk, heval⟩ := p.2
    have h_v2 : v 2 ≠ 0 := mem_U_iff_representative_ne_zero v hv 2 |>.mp (h_mk ▸ hp)
    let c := (v 2)⁻¹
    let w := c • v
    have hw2 : w 2 = 1 := by
      change c * v 2 = 1
      exact inv_mul_cancel₀ h_v2
    have heval_w : H.F.val.eval w = 0 := by
      change H.F.val.eval (fun i => c * v i) = 0
      rw [homogeneous_eval_smul H.F.homogeneous]
      rw [heval, mul_zero]
    have h_w_eq : w = ![w 0, w 1, 1] := by
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact hw2
    have h_q_eval : H.F.val.eval ![w 0, w 1, (1 : ℂ)] = 0 := by
      rw [← h_w_eq]
      exact heval_w
    let q : PlaneCurveAffine H := ⟨(w 0, w 1), h_q_eval⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    change Projectivization.mk ℂ ![w 0, w 1, 1] _ = p.val
    have hw_nonzero : w ≠ 0 := by
      intro h
      have h2 : w 2 = 0 := congrFun h 2
      rw [hw2] at h2
      exact one_ne_zero h2
    have h_mk_eq : Projectivization.mk ℂ ![w 0, w 1, 1] (h_w_eq ▸ hw_nonzero) =
        Projectivization.mk ℂ w hw_nonzero := by
      congr 1
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact hw2.symm
    rw [h_mk_eq]
    rw [← h_mk]
    rw [Projectivization.mk_eq_mk_iff ℂ w v hw_nonzero hv]
    refine ⟨Units.mk0 c (inv_ne_zero h_v2), rfl⟩

theorem range_toPlaneCurveY_eq_U1 (H : PlaneCurveData) :
    Set.range (PlaneCurveAffineY.toPlaneCurve H) = PlaneCurve.U H 1 := by
  ext p
  simp only [Set.mem_range, PlaneCurve.U, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, rfl⟩
    dsimp [PlaneCurveAffineY.toPlaneCurve, Projectivization.U]
    refine ⟨![q.val.1, 1, q.val.2], ?_, ?_⟩
    · intro h
      have h1 : ![q.val.1, 1, q.val.2] 1 = 0 := congrFun h 1
      exact one_ne_zero h1
    · refine ⟨rfl, ?_⟩
      exact one_ne_zero
  · intro hp
    obtain ⟨v, hv, h_mk, heval⟩ := p.2
    have h_v1 : v 1 ≠ 0 := mem_U_iff_representative_ne_zero v hv 1 |>.mp (h_mk ▸ hp)
    let c := (v 1)⁻¹
    let w := c • v
    have hw1 : w 1 = 1 := by
      change c * v 1 = 1
      exact inv_mul_cancel₀ h_v1
    have heval_w : H.F.val.eval w = 0 := by
      change H.F.val.eval (fun i => c * v i) = 0
      rw [homogeneous_eval_smul H.F.homogeneous]
      rw [heval, mul_zero]
    have h_w_eq : w = ![w 0, 1, w 2] := by
      ext i
      fin_cases i
      · rfl
      · exact hw1
      · rfl
    have h_q_eval : H.F.val.eval ![w 0, (1 : ℂ), w 2] = 0 := by
      rw [← h_w_eq]
      exact heval_w
    let q : PlaneCurveAffineY H := ⟨(w 0, w 2), h_q_eval⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    have hw_nonzero : w ≠ 0 := by
      intro h
      have h1 : w 1 = 0 := congrFun h 1
      rw [hw1] at h1
      exact one_ne_zero h1
    have h_mk_eq : (PlaneCurveAffineY.toPlaneCurve H q).val =
        Projectivization.mk ℂ w hw_nonzero := by
      dsimp [PlaneCurveAffineY.toPlaneCurve]
      congr 1
      ext i
      fin_cases i
      · rfl
      · exact hw1.symm
      · rfl
    rw [h_mk_eq]
    rw [← h_mk]
    rw [Projectivization.mk_eq_mk_iff ℂ w v hw_nonzero hv]
    refine ⟨Units.mk0 c (inv_ne_zero h_v1), rfl⟩

theorem range_toPlaneCurveX_eq_U0 (H : PlaneCurveData) :
    Set.range (PlaneCurveAffineX.toPlaneCurve H) = PlaneCurve.U H 0 := by
  ext p
  simp only [Set.mem_range, PlaneCurve.U, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, rfl⟩
    dsimp [PlaneCurveAffineX.toPlaneCurve, Projectivization.U]
    refine ⟨![1, q.val.1, q.val.2], ?_, ?_⟩
    · intro h
      have h0 : ![1, q.val.1, q.val.2] 0 = 0 := congrFun h 0
      exact one_ne_zero h0
    · refine ⟨rfl, ?_⟩
      exact one_ne_zero
  · intro hp
    obtain ⟨v, hv, h_mk, heval⟩ := p.2
    have h_v0 : v 0 ≠ 0 := mem_U_iff_representative_ne_zero v hv 0 |>.mp (h_mk ▸ hp)
    let c := (v 0)⁻¹
    let w := c • v
    have hw0 : w 0 = 1 := by
      change c * v 0 = 1
      exact inv_mul_cancel₀ h_v0
    have heval_w : H.F.val.eval w = 0 := by
      change H.F.val.eval (fun i => c * v i) = 0
      rw [homogeneous_eval_smul H.F.homogeneous]
      rw [heval, mul_zero]
    have h_w_eq : w = ![1, w 1, w 2] := by
      ext i
      fin_cases i
      · exact hw0
      · rfl
      · rfl
    have h_q_eval : H.F.val.eval ![(1 : ℂ), w 1, w 2] = 0 := by
      rw [← h_w_eq]
      exact heval_w
    let q : PlaneCurveAffineX H := ⟨(w 1, w 2), h_q_eval⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    have hw_nonzero : w ≠ 0 := by
      intro h
      have h0 : w 0 = 0 := congrFun h 0
      rw [hw0] at h0
      exact one_ne_zero h0
    have h_mk_eq : (PlaneCurveAffineX.toPlaneCurve H q).val =
        Projectivization.mk ℂ w hw_nonzero := by
      dsimp [PlaneCurveAffineX.toPlaneCurve]
      congr 1
      ext i
      fin_cases i
      · exact hw0.symm
      · rfl
      · rfl
    rw [h_mk_eq]
    rw [← h_mk]
    rw [Projectivization.mk_eq_mk_iff ℂ w v hw_nonzero hv]
    refine ⟨Units.mk0 c (inv_ne_zero h_v0), rfl⟩

theorem isOpenEmbedding_toPlaneCurve (H : PlaneCurveData) :
    Topology.IsOpenEmbedding (PlaneCurveAffine.toPlaneCurve H) := by
  have h_range_open : IsOpen (Set.range (PlaneCurveAffine.toPlaneCurve H)) := by
    rw [range_toPlaneCurve_eq_U2 H]
    exact isOpen_U_PC H 2
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_toPlaneCurve H) (toPlaneCurve_injective H) ?_
  exact isOpenMap_of_continuous_inverse (continuous_toPlaneCurve H)
    (continuous_projZ_inv H) (left_inverse_projZ_inv H) h_range_open

theorem isOpenEmbedding_toPlaneCurveY (H : PlaneCurveData) :
    Topology.IsOpenEmbedding (PlaneCurveAffineY.toPlaneCurve H) := by
  have h_range_open : IsOpen (Set.range (PlaneCurveAffineY.toPlaneCurve H)) := by
    rw [range_toPlaneCurveY_eq_U1 H]
    exact isOpen_U_PC H 1
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_toPlaneCurveY H) (toPlaneCurveY_injective H) ?_
  exact isOpenMap_of_continuous_inverse (continuous_toPlaneCurveY H)
    (continuous_projY_inv H) (left_inverse_projY_inv H) h_range_open

theorem isOpenEmbedding_toPlaneCurveX (H : PlaneCurveData) :
    Topology.IsOpenEmbedding (PlaneCurveAffineX.toPlaneCurve H) := by
  have h_range_open : IsOpen (Set.range (PlaneCurveAffineX.toPlaneCurve H)) := by
    rw [range_toPlaneCurveX_eq_U0 H]
    exact isOpen_U_PC H 0
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_toPlaneCurveX H) (toPlaneCurveX_injective H) ?_
  exact isOpenMap_of_continuous_inverse (continuous_toPlaneCurveX H)
    (continuous_projX_inv H) (left_inverse_projX_inv H) h_range_open

noncomputable def PlaneCurveAffine.prefChart (H : PlaneCurveData) (p : PlaneCurveAffine H) :
    OpenPartialHomeomorph (PlaneCurveAffine H) ℂ :=
  open Classical in
  if hp : p ∈ PlaneCurveAffine.smoothLocusX H then
    affineChartProjY H p hp
  else
    have hpY : p ∈ PlaneCurveAffine.smoothLocusY H := by
      rcases smooth_locus_cover p with h1 | h2
      · contradiction
      · exact h2
    affineChartProjX H p hpY

noncomputable def PlaneCurveAffineY.prefChart (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    [Nonempty (PlaneCurveAffineY H)] :
    OpenPartialHomeomorph (PlaneCurveAffineY H) ℂ :=
  open Classical in
  if hp : p ∈ PlaneCurveAffineY.smoothLocusX H then
    affineChartProjZ_Y H p hp
  else
    have hpZ : p ∈ PlaneCurveAffineY.smoothLocusZ H := by
      rcases smooth_locus_coverY p with h1 | h2
      · contradiction
      · exact h2
    affineChartProjX_Y H p hpZ

noncomputable def PlaneCurveAffineX.prefChart (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    [Nonempty (PlaneCurveAffineX H)] :
    OpenPartialHomeomorph (PlaneCurveAffineX H) ℂ :=
  open Classical in
  if hp : p ∈ PlaneCurveAffineX.smoothLocusY H then
    affineChartProjZ_X H p hp
  else
    have hpZ : p ∈ PlaneCurveAffineX.smoothLocusZ H := by
      rcases smooth_locus_coverX p with h1 | h2
      · contradiction
      · exact h2
    affineChartProjY_X H p hpZ

noncomputable def centralLiftChart (H : PlaneCurveData) (p : PlaneCurveAffine H) :
    OpenPartialHomeomorph (PlaneCurve H) ℂ :=
  (PlaneCurveAffine.prefChart H p).lift_openEmbedding (isOpenEmbedding_toPlaneCurve H)

noncomputable def yLiftChart (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    [Nonempty (PlaneCurveAffineY H)] :
    OpenPartialHomeomorph (PlaneCurve H) ℂ :=
  (PlaneCurveAffineY.prefChart H p).lift_openEmbedding (isOpenEmbedding_toPlaneCurveY H)

noncomputable def xLiftChart (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    [Nonempty (PlaneCurveAffineX H)] :
    OpenPartialHomeomorph (PlaneCurve H) ℂ :=
  (PlaneCurveAffineX.prefChart H p).lift_openEmbedding (isOpenEmbedding_toPlaneCurveX H)

theorem affineChartProjY_mem_source (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusX H) :
    p ∈ (affineChartProjY H p hp).source := by
  dsimp [affineChartProjY]
  exact phiLocalHomeomorph_mem_source H p hp

theorem affineChartProjX_mem_source (H : PlaneCurveData) (p : PlaneCurveAffine H)
    (hp : p ∈ PlaneCurveAffine.smoothLocusY H) :
    p ∈ (affineChartProjX H p hp).source := by
  dsimp [affineChartProjX]
  exact psiLocalHomeomorph_mem_source H p hp

theorem affineChartProjZ_Y_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusX H) [Nonempty (PlaneCurveAffineY H)] :
    p ∈ (affineChartProjZ_Y H p hp).source := by
  dsimp [affineChartProjZ_Y]
  exact phiYLocalHomeomorph_mem_source H p hp

theorem affineChartProjX_Y_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    (hp : p ∈ PlaneCurveAffineY.smoothLocusZ H) [Nonempty (PlaneCurveAffineY H)] :
    p ∈ (affineChartProjX_Y H p hp).source := by
  dsimp [affineChartProjX_Y]
  exact psiYLocalHomeomorph_mem_source H p hp

theorem affineChartProjZ_X_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusY H) [Nonempty (PlaneCurveAffineX H)] :
    p ∈ (affineChartProjZ_X H p hp).source := by
  dsimp [affineChartProjZ_X]
  exact phiXLocalHomeomorph_mem_source H p hp

theorem affineChartProjY_X_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    (hp : p ∈ PlaneCurveAffineX.smoothLocusZ H) [Nonempty (PlaneCurveAffineX H)] :
    p ∈ (affineChartProjY_X H p hp).source := by
  dsimp [affineChartProjY_X]
  exact psiXLocalHomeomorph_mem_source H p hp

theorem PlaneCurveAffine.prefChart_mem_source (H : PlaneCurveData) (p : PlaneCurveAffine H) :
    p ∈ (prefChart H p).source := by
  unfold prefChart
  split_ifs with hp
  · exact affineChartProjY_mem_source H p hp
  · exact affineChartProjX_mem_source H p _

theorem PlaneCurveAffineY.prefChart_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineY H)
    [Nonempty (PlaneCurveAffineY H)] :
    p ∈ (prefChart H p).source := by
  unfold prefChart
  split_ifs with hp
  · exact affineChartProjZ_Y_mem_source H p hp
  · exact affineChartProjX_Y_mem_source H p _

theorem PlaneCurveAffineX.prefChart_mem_source (H : PlaneCurveData) (p : PlaneCurveAffineX H)
    [Nonempty (PlaneCurveAffineX H)] :
    p ∈ (prefChart H p).source := by
  unfold prefChart
  split_ifs with hp
  · exact affineChartProjZ_X_mem_source H p hp
  · exact affineChartProjY_X_mem_source H p _

noncomputable def chartAt (H : PlaneCurveData) (q : PlaneCurve H) :
    OpenPartialHomeomorph (PlaneCurve H) ℂ :=
  open Classical in
  if h2 : q.val.rep 2 ≠ 0 then
    have hq : q ∈ PlaneCurve.U H 2 := mem_U_of_rep_ne_zero q.val 2 h2
    let p : PlaneCurveAffine H := PlaneCurveAffine.projZ_inv H ⟨q, by
      rw [range_toPlaneCurve_eq_U2 H]
      exact hq⟩
    centralLiftChart H p
  else if h1 : q.val.rep 1 ≠ 0 then
    have hq : q ∈ PlaneCurve.U H 1 := mem_U_of_rep_ne_zero q.val 1 h1
    let p : PlaneCurveAffineY H := PlaneCurveAffineY.projY_inv H ⟨q, by
      rw [range_toPlaneCurveY_eq_U1 H]
      exact hq⟩
    haveI : Nonempty (PlaneCurveAffineY H) := ⟨p⟩
    yLiftChart H p
  else
    have h0 : q.val.rep 0 ≠ 0 := by
      have h_nz := Projectivization.rep_nonzero q.val
      intro h_zero
      apply h_nz
      ext i
      fin_cases i
      · exact h_zero
      · exact not_not.mp h1
      · exact not_not.mp h2
    have hq : q ∈ PlaneCurve.U H 0 := mem_U_of_rep_ne_zero q.val 0 h0
    let p : PlaneCurveAffineX H := PlaneCurveAffineX.projX_inv H ⟨q, by
      rw [range_toPlaneCurveX_eq_U0 H]
      exact hq⟩
    haveI : Nonempty (PlaneCurveAffineX H) := ⟨p⟩
    xLiftChart H p

theorem mem_chartAt_source (H : PlaneCurveData) (q : PlaneCurve H) :
    q ∈ (chartAt H q).source := by
  dsimp [chartAt]
  split
  · rename_i h2
    unfold centralLiftChart
    simp only [OpenPartialHomeomorph.lift_openEmbedding_source]
    refine ⟨_, PlaneCurveAffine.prefChart_mem_source H _, ?_⟩
    exact toPlaneCurve_projZ_inv H ⟨q, by
      rw [range_toPlaneCurve_eq_U2 H]
      exact mem_U_of_rep_ne_zero q.val 2 h2⟩
  · split
    · rename_i _h2_neg h1
      have hq : q ∈ PlaneCurve.U H 1 := mem_U_of_rep_ne_zero q.val 1 h1
      haveI : Nonempty (PlaneCurveAffineY H) := ⟨PlaneCurveAffineY.projY_inv H ⟨q, by
        rw [range_toPlaneCurveY_eq_U1 H]
        exact hq⟩⟩
      unfold yLiftChart
      simp only [OpenPartialHomeomorph.lift_openEmbedding_source]
      refine ⟨_, PlaneCurveAffineY.prefChart_mem_source H _, ?_⟩
      exact toPlaneCurveY_projY_inv H ⟨q, by
        rw [range_toPlaneCurveY_eq_U1 H]
        exact hq⟩
    · rename_i _h2_neg h1_neg
      have h0 : q.val.rep 0 ≠ 0 := by
        have h_nz := Projectivization.rep_nonzero q.val
        intro h_zero
        apply h_nz
        ext i
        fin_cases i
        · exact h_zero
        · exact not_not.mp h1_neg
        · exact not_not.mp _h2_neg
      have hq : q ∈ PlaneCurve.U H 0 := mem_U_of_rep_ne_zero q.val 0 h0
      haveI : Nonempty (PlaneCurveAffineX H) := ⟨PlaneCurveAffineX.projX_inv H ⟨q, by
        rw [range_toPlaneCurveX_eq_U0 H]
        exact hq⟩⟩
      unfold xLiftChart
      simp only [OpenPartialHomeomorph.lift_openEmbedding_source]
      refine ⟨_, PlaneCurveAffineX.prefChart_mem_source H _, ?_⟩
      exact toPlaneCurveX_projX_inv H ⟨q, by
        rw [range_toPlaneCurveX_eq_U0 H]
        exact hq⟩

noncomputable instance PlaneCurve.instChartedSpace (H : PlaneCurveData) :
    ChartedSpace ℂ (PlaneCurve H) where
  atlas := Set.range (chartAt H)
  chartAt := chartAt H
  mem_chart_source q := mem_chartAt_source H q
  chart_mem_atlas q := ⟨q, rfl⟩

end Jacobians.ProjectiveCurve
