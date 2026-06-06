import Jacobians.RiemannSurface.CanonicalArcIntegral

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open intervalIntegral MeasureTheory

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

namespace AnalyticArc

/-- Reverse an analytic arc by the affine reparametrization `r ↦ 1 - r`. -/
noncomputable def reverse (γ : AnalyticArc X) : AnalyticArc X where
  extend r := γ.extend (1 - r)
  continuous' := γ.continuous'.comp (continuous_const.sub continuous_id)
  partition := γ.partition.image (fun p : ℝ => 1 - p)
  partition_subset := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
    have hp01 := γ.partition_subset hp
    constructor <;> linarith [hp01.1, hp01.2]
  zero_mem := by
    exact Finset.mem_image.mpr ⟨1, γ.one_mem, by norm_num⟩
  one_mem := by
    exact Finset.mem_image.mpr ⟨0, γ.zero_mem, by norm_num⟩
  is_analytic := by
    intro u hu hupart
    have h₁u : 1 - u ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hu.1, hu.2]
    have h₁u_part : 1 - u ∉ (γ.partition : Set ℝ) := by
      intro hmem
      apply hupart
      refine Finset.mem_image.mpr ⟨1 - u, hmem, ?_⟩
      ring
    have han := γ.is_analytic (1 - u) h₁u h₁u_part
    simpa [sub_sub_cancel] using
      han.comp' (analyticAt_const.sub analyticAt_id)

/-- Concatenate two analytic arcs with matching endpoint and start point. -/
noncomputable def trans (γ₁ γ₂ : AnalyticArc X)
    (h : γ₁.extend 1 = γ₂.extend 0) : AnalyticArc X where
  extend r :=
    if r ≤ (1 / 2 : ℝ) then γ₁.extend (2 * r) else γ₂.extend (2 * r - 1)
  continuous' := by
    classical
    let f : ℝ → X := fun r => γ₁.extend (2 * r)
    let g : ℝ → X := fun r => γ₂.extend (2 * r - 1)
    have hf : Continuous f :=
      γ₁.continuous'.comp (continuous_const.mul continuous_id)
    have hg : Continuous g :=
      γ₂.continuous'.comp ((continuous_const.mul continuous_id).sub continuous_const)
    have hfrontier :
        ∀ r ∈ frontier {r : ℝ | r ≤ (1 / 2 : ℝ)}, f r = g r := by
      intro r hr
      have hrIic : r ∈ frontier (Set.Iic (1 / 2 : ℝ)) := by
        simpa [Set.Iic] using hr
      have hr_eq : r = (1 / 2 : ℝ) :=
        Set.mem_singleton_iff.mp ((frontier_Iic_subset (1 / 2 : ℝ)) hrIic)
      subst r
      simpa [f, g] using h
    simpa [f, g] using
      (hf.if (p := fun r : ℝ => r ≤ (1 / 2 : ℝ)) hfrontier hg)
  partition :=
    γ₁.partition.image (fun p : ℝ => p / 2) ∪
      γ₂.partition.image (fun p : ℝ => (p + 1) / 2)
  partition_subset := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
      have hp01 := γ₁.partition_subset hp
      constructor <;> linarith [hp01.1, hp01.2]
    · rcases Finset.mem_image.mp hr with ⟨p, hp, rfl⟩
      have hp01 := γ₂.partition_subset hp
      constructor <;> linarith [hp01.1, hp01.2]
  zero_mem := by
    exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_image.mpr ⟨0, γ₁.zero_mem, by norm_num⟩))
  one_mem := by
    exact Finset.mem_union.mpr
      (Or.inr (Finset.mem_image.mpr ⟨1, γ₂.one_mem, by norm_num⟩))
  is_analytic := by
    classical
    intro u hu hupart
    have hhalf_mem :
        (1 / 2 : ℝ) ∈
          ((γ₁.partition.image (fun p : ℝ => p / 2) ∪
            γ₂.partition.image (fun p : ℝ => (p + 1) / 2)) : Finset ℝ) := by
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨1, γ₁.one_mem, by norm_num⟩))
    have hu_ne_half : u ≠ (1 / 2 : ℝ) := by
      intro hu_eq
      apply hupart
      simpa [hu_eq] using hhalf_mem
    rcases lt_or_gt_of_ne hu_ne_half with hu_lt | hu_gt
    · have h2u : 2 * u ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hu.1, hu_lt]
      have h2u_part : 2 * u ∉ (γ₁.partition : Set ℝ) := by
        intro hmem
        apply hupart
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_image.mpr ⟨2 * u, hmem, by ring⟩))
      have han := γ₁.is_analytic (2 * u) h2u h2u_part
      have haff : AnalyticAt ℝ (fun r : ℝ => 2 * r) u :=
        analyticAt_const.mul analyticAt_id
      have hcomp :
          AnalyticAt ℝ
            (fun r : ℝ =>
              (extChartAt 𝓘(ℂ) (γ₁.extend (2 * u))) (γ₁.extend (2 * r))) u := by
        simpa [Function.comp_def] using han.comp' haff
      refine hcomp.congr ?_
      filter_upwards [(isOpen_Iio.mem_nhds hu_lt)] with r hr
      have hu_le : u ≤ (1 / 2 : ℝ) := le_of_lt hu_lt
      have hr_le : r ≤ (1 / 2 : ℝ) := le_of_lt hr
      have hu_le' : u ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hu_le
      have hr_le' : r ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hr_le
      simp [hu_le', hr_le']
    · have h2u : 2 * u - 1 ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [hu.2, hu_gt]
      have h2u_part : 2 * u - 1 ∉ (γ₂.partition : Set ℝ) := by
        intro hmem
        apply hupart
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨2 * u - 1, hmem, by ring⟩))
      have han := γ₂.is_analytic (2 * u - 1) h2u h2u_part
      have haff : AnalyticAt ℝ (fun r : ℝ => 2 * r - 1) u :=
        (analyticAt_const.mul analyticAt_id).sub analyticAt_const
      have hcomp :
          AnalyticAt ℝ
            (fun r : ℝ =>
              (extChartAt 𝓘(ℂ) (γ₂.extend (2 * u - 1)))
                (γ₂.extend (2 * r - 1))) u := by
        have hinner : (fun r : ℝ => 2 * r - 1) u = 2 * u - 1 := by
          ring
        simpa [Function.comp_def] using
          han.comp_of_eq' haff hinner
      refine hcomp.congr ?_
      filter_upwards [(isOpen_Ioi.mem_nhds hu_gt)] with r hr
      have hu_not_le : ¬u ≤ (1 / 2 : ℝ) := not_le.mpr hu_gt
      have hr_not_le : ¬r ≤ (1 / 2 : ℝ) := not_le.mpr hr
      have hu_not_le' : ¬u ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hu_not_le
      have hr_not_le' : ¬r ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hr_not_le
      simp [hu_not_le', hr_not_le']

end AnalyticArc

/-- Reversal negates the canonical moving-chart integrand after the
substitution `r ↦ 1 - r`. -/
theorem canonicalIntegrand_reverse (γ : AnalyticArc X)
    (form : HolomorphicOneForm X) (r : ℝ) :
    canonicalIntegrand γ.reverse form r =
      -canonicalIntegrand γ form (1 - r) := by
  have hderiv :
      deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ.extend (1 - r))) (γ.extend (1 - u))) r =
        -deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ.extend (1 - r))) (γ.extend u)) (1 - r) := by
    simpa using
      (deriv_comp_const_sub
        (f := fun u : ℝ =>
          (chartAt ℂ (γ.extend (1 - r))) (γ.extend u))
        (a := (1 : ℝ)) (x := r))
  let c : ℂ :=
    form.coeff (γ.extend (1 - r))
      ((chartAt ℂ (γ.extend (1 - r))) (γ.extend (1 - r)))
  let d : ℂ :=
    deriv
      (fun u : ℝ =>
        (chartAt ℂ (γ.extend (1 - r))) (γ.extend u)) (1 - r)
  change
    c *
        deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ.extend (1 - r))) (γ.extend (1 - u))) r =
      -(c * d)
  calc
    c *
        deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ.extend (1 - r))) (γ.extend (1 - u))) r =
        c * (-d) := by
      simpa [d] using congrArg (fun z : ℂ => c * z) hderiv
    _ = -(c * d) := by ring

/-- Reversing an analytic arc changes the sign of its canonical integral. -/
theorem canonicalArcIntegral_reverse (γ : AnalyticArc X)
    (form : HolomorphicOneForm X) :
    canonicalArcIntegral γ.reverse form = -canonicalArcIntegral γ form := by
  unfold canonicalArcIntegral
  calc
    (∫ r in (0 : ℝ)..1, canonicalIntegrand γ.reverse form r) =
        ∫ r in (0 : ℝ)..1, -canonicalIntegrand γ form (1 - r) := by
      refine intervalIntegral.integral_congr_ae ?_
      exact Filter.Eventually.of_forall fun r _ => canonicalIntegrand_reverse γ form r
    _ = -∫ r in (0 : ℝ)..1, canonicalIntegrand γ form (1 - r) := by
      simp
    _ = -∫ r in (0 : ℝ)..1, canonicalIntegrand γ form r := by
      rw [intervalIntegral.integral_comp_sub_left (canonicalIntegrand γ form) (1 : ℝ)]
      norm_num

private theorem canonicalIntegrand_trans_left (γ₁ γ₂ : AnalyticArc X)
    (h : γ₁.extend 1 = γ₂.extend 0) (form : HolomorphicOneForm X)
    {r : ℝ} (hr : r < (1 / 2 : ℝ)) :
    canonicalIntegrand (γ₁.trans γ₂ h) form r =
      (2 : ℂ) * canonicalIntegrand γ₁ form (2 * r) := by
  have hr_lt' : r < (2 : ℝ)⁻¹ := by simpa [one_div] using hr
  have hr_le' : r ≤ (2 : ℝ)⁻¹ := le_of_lt hr_lt'
  have hderiv_if :
      deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ₁.extend (2 * r)))
              (if u ≤ (2 : ℝ)⁻¹ then
                γ₁.extend (2 * u)
              else
                γ₂.extend (2 * u - 1))) r =
        deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ₁.extend (2 * r))) (γ₁.extend (2 * u))) r := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [(isOpen_Iio.mem_nhds hr_lt')] with u hu
    have hu_le : u ≤ (2 : ℝ)⁻¹ := le_of_lt hu
    simp [hu_le]
  have hderiv_mul :
      deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ₁.extend (2 * r))) (γ₁.extend (2 * u))) r =
        (2 : ℝ) •
          deriv
            (fun u : ℝ =>
              (chartAt ℂ (γ₁.extend (2 * r))) (γ₁.extend u)) (2 * r) := by
    simpa [Function.comp_def] using
      (deriv_comp_mul_left
        (f := fun u : ℝ =>
          (chartAt ℂ (γ₁.extend (2 * r))) (γ₁.extend u))
        (c := (2 : ℝ)) (x := r))
  simp [canonicalIntegrand, AnalyticArc.trans, hr_le', hderiv_if, hderiv_mul]
  ring

private theorem canonicalIntegrand_trans_right (γ₁ γ₂ : AnalyticArc X)
    (h : γ₁.extend 1 = γ₂.extend 0) (form : HolomorphicOneForm X)
    {r : ℝ} (hr : (1 / 2 : ℝ) < r) :
    canonicalIntegrand (γ₁.trans γ₂ h) form r =
      (2 : ℂ) * canonicalIntegrand γ₂ form (2 * r - 1) := by
  have hr_lt' : (2 : ℝ)⁻¹ < r := by simpa [one_div] using hr
  have hr_not_le' : ¬r ≤ (2 : ℝ)⁻¹ := not_le.mpr hr_lt'
  have hderiv_if :
      deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ₂.extend (2 * r - 1)))
              (if u ≤ (2 : ℝ)⁻¹ then
                γ₁.extend (2 * u)
              else
                γ₂.extend (2 * u - 1))) r =
        deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ₂.extend (2 * r - 1)))
              (γ₂.extend (2 * u - 1))) r := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [(isOpen_Ioi.mem_nhds hr_lt')] with u hu
    have hu_not_le : ¬u ≤ (2 : ℝ)⁻¹ := not_le.mpr hu
    simp [hu_not_le]
  let F : ℝ → ℂ := fun u =>
    (chartAt ℂ (γ₂.extend (2 * r - 1))) (γ₂.extend u)
  have hderiv_affine :
      deriv (fun u : ℝ => F (2 * u - 1)) r =
        (2 : ℝ) • deriv F (2 * r - 1) := by
    calc
      deriv (fun u : ℝ => F (2 * u - 1)) r =
          (2 : ℝ) • deriv (fun x : ℝ => F (x - 1)) (2 * r) := by
        simpa [Function.comp_def] using
          (deriv_comp_mul_left (f := fun x : ℝ => F (x - 1))
            (c := (2 : ℝ)) (x := r))
      _ = (2 : ℝ) • deriv F (2 * r - 1) := by
        rw [deriv_comp_sub_const (f := F) (a := (1 : ℝ)) (x := 2 * r)]
  have hderiv_mul :
      deriv
          (fun u : ℝ =>
            (chartAt ℂ (γ₂.extend (2 * r - 1)))
              (γ₂.extend (2 * u - 1))) r =
        (2 : ℝ) •
          deriv
            (fun u : ℝ =>
              (chartAt ℂ (γ₂.extend (2 * r - 1))) (γ₂.extend u))
            (2 * r - 1) := by
    simpa [F] using hderiv_affine
  simp [canonicalIntegrand, AnalyticArc.trans, hr_not_le', hderiv_if, hderiv_mul]
  ring

/-- Concatenating analytic arcs adds their canonical integrals. -/
theorem canonicalArcIntegral_trans (γ₁ γ₂ : AnalyticArc X)
    (h : γ₁.extend 1 = γ₂.extend 0) (form : HolomorphicOneForm X)
    (hint₁ : IntervalIntegrable (canonicalIntegrand γ₁ form) volume 0 1)
    (hint₂ : IntervalIntegrable (canonicalIntegrand γ₂ form) volume 0 1) :
    canonicalArcIntegral (γ₁.trans γ₂ h) form =
      canonicalArcIntegral γ₁ form + canonicalArcIntegral γ₂ form := by
  have hleft_comp :
      IntervalIntegrable
        (fun r : ℝ => canonicalIntegrand γ₁ form (2 * r))
        volume (0 : ℝ) (1 / 2 : ℝ) := by
    simpa [one_div] using (hint₁.comp_mul_left (c := (2 : ℝ)))
  have hleft_target :
      IntervalIntegrable
        (fun r : ℝ => (2 : ℂ) * canonicalIntegrand γ₁ form (2 * r))
        volume (0 : ℝ) (1 / 2 : ℝ) :=
    hleft_comp.const_mul (2 : ℂ)
  have hleft_ae :
      (fun r : ℝ => (2 : ℂ) * canonicalIntegrand γ₁ form (2 * r)) =ᵐ[
        volume.restrict (Set.uIoc (0 : ℝ) (1 / 2 : ℝ))]
        canonicalIntegrand (γ₁.trans γ₂ h) form := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards
      [Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
        (μ := volume)] with r hr_eq
    intro hrmem
    have hr_ioc : r ∈ Set.Ioc (0 : ℝ) (1 / 2 : ℝ) := by
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hrmem
    have hr_ioo : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := by
      change Set.Ioo (0 : ℝ) (1 / 2 : ℝ) r
      rw [hr_eq]
      exact hr_ioc
    exact (canonicalIntegrand_trans_left γ₁ γ₂ h form hr_ioo.2).symm
  have hleft_trans :
      IntervalIntegrable (canonicalIntegrand (γ₁.trans γ₂ h) form)
        volume (0 : ℝ) (1 / 2 : ℝ) :=
    hleft_target.congr_ae hleft_ae
  have hright_shift :
      IntervalIntegrable
        (fun r : ℝ => canonicalIntegrand γ₂ form (r - 1))
        volume (1 : ℝ) 2 := by
    convert (hint₂.comp_sub_right (c := (1 : ℝ))) using 1 <;> norm_num
  have hright_comp :
      IntervalIntegrable
        (fun r : ℝ => canonicalIntegrand γ₂ form (2 * r - 1))
        volume (1 / 2 : ℝ) 1 := by
    simpa [one_div] using (hright_shift.comp_mul_left (c := (2 : ℝ)))
  have hright_target :
      IntervalIntegrable
        (fun r : ℝ => (2 : ℂ) * canonicalIntegrand γ₂ form (2 * r - 1))
        volume (1 / 2 : ℝ) 1 :=
    hright_comp.const_mul (2 : ℂ)
  have hright_ae :
      (fun r : ℝ => (2 : ℂ) * canonicalIntegrand γ₂ form (2 * r - 1)) =ᵐ[
        volume.restrict (Set.uIoc (1 / 2 : ℝ) 1)]
        canonicalIntegrand (γ₁.trans γ₂ h) form := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards
      [Ioo_ae_eq_Ioc (a := (1 / 2 : ℝ)) (b := (1 : ℝ))
        (μ := volume)] with r hr_eq
    intro hrmem
    have hr_ioc : r ∈ Set.Ioc (1 / 2 : ℝ) 1 := by
      have hr_ioc' : r ∈ Set.Ioc ((2 : ℝ)⁻¹) 1 := by
        simpa [Set.uIoc_of_le (by norm_num : ((2 : ℝ)⁻¹) ≤ 1)] using hrmem
      simpa [one_div] using hr_ioc'
    have hr_ioo : r ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
      change Set.Ioo (1 / 2 : ℝ) 1 r
      rw [hr_eq]
      exact hr_ioc
    exact (canonicalIntegrand_trans_right γ₁ γ₂ h form hr_ioo.1).symm
  have hright_trans :
      IntervalIntegrable (canonicalIntegrand (γ₁.trans γ₂ h) form)
        volume (1 / 2 : ℝ) 1 :=
    hright_target.congr_ae hright_ae
  have hleft_integral :
      (∫ r in (0 : ℝ)..(1 / 2 : ℝ),
          canonicalIntegrand (γ₁.trans γ₂ h) form r) =
        ∫ r in (0 : ℝ)..(1 / 2 : ℝ),
          (2 : ℂ) * canonicalIntegrand γ₁ form (2 * r) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_uIoc_iff]
    constructor
    · filter_upwards
        [Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
          (μ := volume)] with r hr_eq hr
      have hr_ioo : r ∈ Set.Ioo (0 : ℝ) (1 / 2 : ℝ) := by
        change Set.Ioo (0 : ℝ) (1 / 2 : ℝ) r
        rw [hr_eq]
        exact hr
      exact canonicalIntegrand_trans_left γ₁ γ₂ h form hr_ioo.2
    · filter_upwards with r hr
      have h_empty : Set.Ioc (1 / 2 : ℝ) 0 = (∅ : Set ℝ) :=
        Set.Ioc_eq_empty (not_lt_of_ge (by norm_num : (0 : ℝ) ≤ 1 / 2))
      rw [h_empty] at hr
      exact False.elim hr
  have hright_integral :
      (∫ r in (1 / 2 : ℝ)..1,
          canonicalIntegrand (γ₁.trans γ₂ h) form r) =
        ∫ r in (1 / 2 : ℝ)..1,
          (2 : ℂ) * canonicalIntegrand γ₂ form (2 * r - 1) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_uIoc_iff]
    constructor
    · filter_upwards
        [Ioo_ae_eq_Ioc (a := (1 / 2 : ℝ)) (b := (1 : ℝ))
          (μ := volume)] with r hr_eq hr
      have hr_ioo : r ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
        change Set.Ioo (1 / 2 : ℝ) 1 r
        rw [hr_eq]
        exact hr
      exact canonicalIntegrand_trans_right γ₁ γ₂ h form hr_ioo.1
    · filter_upwards with r hr
      have h_empty : Set.Ioc (1 : ℝ) (1 / 2 : ℝ) = (∅ : Set ℝ) :=
        Set.Ioc_eq_empty (not_lt_of_ge (by norm_num : (1 / 2 : ℝ) ≤ 1))
      rw [h_empty] at hr
      exact False.elim hr
  have hleft_value :
      (∫ r in (0 : ℝ)..(1 / 2 : ℝ),
          canonicalIntegrand (γ₁.trans γ₂ h) form r) =
        ∫ r in (0 : ℝ)..1, canonicalIntegrand γ₁ form r := by
    calc
      (∫ r in (0 : ℝ)..(1 / 2 : ℝ),
          canonicalIntegrand (γ₁.trans γ₂ h) form r) =
          ∫ r in (0 : ℝ)..(1 / 2 : ℝ),
            (2 : ℂ) * canonicalIntegrand γ₁ form (2 * r) := hleft_integral
      _ = (2 : ℝ) •
          (∫ r in (0 : ℝ)..(1 / 2 : ℝ),
            canonicalIntegrand γ₁ form (2 * r)) := by
        simp
      _ = ∫ r in (0 : ℝ)..1, canonicalIntegrand γ₁ form r := by
        simp
  have hright_value :
      (∫ r in (1 / 2 : ℝ)..1,
          canonicalIntegrand (γ₁.trans γ₂ h) form r) =
        ∫ r in (0 : ℝ)..1, canonicalIntegrand γ₂ form r := by
    calc
      (∫ r in (1 / 2 : ℝ)..1,
          canonicalIntegrand (γ₁.trans γ₂ h) form r) =
          ∫ r in (1 / 2 : ℝ)..1,
            (2 : ℂ) * canonicalIntegrand γ₂ form (2 * r - 1) := hright_integral
      _ = (2 : ℝ) •
          (∫ r in (1 / 2 : ℝ)..1,
            canonicalIntegrand γ₂ form (2 * r - 1)) := by
        simp
      _ = ∫ r in (0 : ℝ)..1, canonicalIntegrand γ₂ form r := by
        calc
          (2 : ℝ) •
              (∫ r in (1 / 2 : ℝ)..1,
                canonicalIntegrand γ₂ form (2 * r - 1)) =
              ∫ r in (2 : ℝ) * (1 / 2 : ℝ) - 1..(2 : ℝ) * 1 - 1,
                canonicalIntegrand γ₂ form r :=
            intervalIntegral.smul_integral_comp_mul_sub
              (canonicalIntegrand γ₂ form) (2 : ℝ) (1 : ℝ)
          _ = ∫ r in (0 : ℝ)..1, canonicalIntegrand γ₂ form r := by
            norm_num
  unfold canonicalArcIntegral
  calc
    (∫ r in (0 : ℝ)..1, canonicalIntegrand (γ₁.trans γ₂ h) form r) =
        (∫ r in (0 : ℝ)..(1 / 2 : ℝ),
          canonicalIntegrand (γ₁.trans γ₂ h) form r) +
          ∫ r in (1 / 2 : ℝ)..1,
            canonicalIntegrand (γ₁.trans γ₂ h) form r := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        hleft_trans hright_trans).symm
    _ = (∫ r in (0 : ℝ)..1, canonicalIntegrand γ₁ form r) +
        ∫ r in (0 : ℝ)..1, canonicalIntegrand γ₂ form r := by
      rw [hleft_value, hright_value]

end Jacobians.RiemannSurface
