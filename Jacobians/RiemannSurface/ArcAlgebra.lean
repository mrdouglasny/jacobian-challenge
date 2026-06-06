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
  is_analytic_strong := by
    intro s hs t ht hst hcons
    rcases Finset.mem_image.mp hs with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp ht with ⟨b, hb, rfl⟩
    have hba : b < a := by linarith
    have hcons' : ∀ r ∈ γ.partition, r ∉ Set.Ioo b a := by
      intro r hr hri
      exact hcons (1 - r) (Finset.mem_image.mpr ⟨r, hr, rfl⟩) (by
        constructor <;> linarith [hri.1, hri.2])
    obtain ⟨p, U₀, f₀, hU₀open, hIccU₀, hf₀, hsource₀, hcoinc₀⟩ :=
      γ.is_analytic_strong b hb a ha hba hcons'
    refine ⟨p, (fun r : ℝ => 1 - r) ⁻¹' U₀, fun r : ℝ => f₀ (1 - r), ?_, ?_, ?_, ?_, ?_⟩
    · exact hU₀open.preimage (continuous_const.sub continuous_id)
    · intro r hr
      exact hIccU₀ ⟨by linarith [hr.2], by linarith [hr.1]⟩
    · intro r hr
      have hbase : AnalyticAt ℝ f₀ (1 - r) := hf₀ (1 - r) hr
      simpa [Function.comp_def] using
        hbase.comp' (analyticAt_const.sub analyticAt_id : AnalyticAt ℝ (fun x : ℝ => 1 - x) r)
    · intro r hr
      exact hsource₀ (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
    · intro r hr
      exact hcoinc₀ (1 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩

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
  is_analytic_strong := by
    classical
    intro s hs t ht hst hcons
    have hhalf_mem :
        (1 / 2 : ℝ) ∈
          ((γ₁.partition.image (fun p : ℝ => p / 2) ∪
            γ₂.partition.image (fun p : ℝ => (p + 1) / 2)) : Finset ℝ) := by
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_image.mpr ⟨1, γ₁.one_mem, by norm_num⟩))
    have left_mem_of_le {x : ℝ}
        (hx : x ∈ γ₁.partition.image (fun p : ℝ => p / 2) ∪
          γ₂.partition.image (fun p : ℝ => (p + 1) / 2))
        (hxle : x ≤ (1 / 2 : ℝ)) :
        x ∈ γ₁.partition.image (fun p : ℝ => p / 2) := by
      rcases Finset.mem_union.mp hx with hx₁ | hx₂
      · exact hx₁
      rcases Finset.mem_image.mp hx₂ with ⟨p, hp, rfl⟩
      have hp01 := γ₂.partition_subset hp
      have hp0 : p = 0 := by linarith [hp01.1, hxle]
      subst p
      exact Finset.mem_image.mpr ⟨1, γ₁.one_mem, by norm_num⟩
    have right_mem_of_ge {x : ℝ}
        (hx : x ∈ γ₁.partition.image (fun p : ℝ => p / 2) ∪
          γ₂.partition.image (fun p : ℝ => (p + 1) / 2))
        (hxge : (1 / 2 : ℝ) ≤ x) :
        x ∈ γ₂.partition.image (fun p : ℝ => (p + 1) / 2) := by
      rcases Finset.mem_union.mp hx with hx₁ | hx₂
      · rcases Finset.mem_image.mp hx₁ with ⟨p, hp, rfl⟩
        have hp01 := γ₁.partition_subset hp
        have hp1 : p = 1 := by linarith [hp01.2, hxge]
        subst p
        exact Finset.mem_image.mpr ⟨0, γ₂.zero_mem, by norm_num⟩
      · exact hx₂
    rcases le_or_gt t (1 / 2 : ℝ) with ht_le_half | hhalf_lt_t
    · have hs_le_half : s ≤ (1 / 2 : ℝ) := le_trans (le_of_lt hst) ht_le_half
      rcases Finset.mem_image.mp (left_mem_of_le hs hs_le_half) with ⟨a, ha, hs_eq⟩
      rcases Finset.mem_image.mp (left_mem_of_le ht ht_le_half) with ⟨b, hb, ht_eq⟩
      subst s
      subst t
      have hab : a < b := by linarith
      have hcons₁ : ∀ r ∈ γ₁.partition, r ∉ Set.Ioo a b := by
        intro r hr hri
        exact hcons (r / 2)
          (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨r, hr, rfl⟩))) (by
            constructor <;> linarith [hri.1, hri.2])
      obtain ⟨p, U₀, f₀, hU₀open, hIccU₀, hf₀, hsource₀, hcoinc₀⟩ :=
        γ₁.is_analytic_strong a ha b hb hab hcons₁
      refine ⟨p, (fun r : ℝ => 2 * r) ⁻¹' U₀, fun r : ℝ => f₀ (2 * r), ?_, ?_, ?_, ?_, ?_⟩
      · exact hU₀open.preimage (continuous_const.mul continuous_id)
      · intro r hr
        exact hIccU₀ ⟨by linarith [hr.1], by linarith [hr.2]⟩
      · intro r hr
        have hbase : AnalyticAt ℝ f₀ (2 * r) := hf₀ (2 * r) hr
        simpa [Function.comp_def] using
          hbase.comp' (analyticAt_const.mul analyticAt_id :
            AnalyticAt ℝ (fun x : ℝ => 2 * x) r)
      · intro r hr
        have hr_le : r ≤ (1 / 2 : ℝ) := by linarith [hr.2, ht_le_half]
        have hr_le' : r ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hr_le
        simpa [hr_le'] using hsource₀ (2 * r) ⟨by linarith [hr.1], by linarith [hr.2]⟩
      · intro r hr
        have hr_le : r ≤ (1 / 2 : ℝ) := by linarith [hr.2, ht_le_half]
        have hr_le' : r ≤ (2 : ℝ)⁻¹ := by simpa [one_div] using hr_le
        simpa [hr_le'] using hcoinc₀ (2 * r) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    · have hhalf_le_s : (1 / 2 : ℝ) ≤ s := by
        by_contra hs_not
        have hs_lt_half : s < (1 / 2 : ℝ) := lt_of_not_ge hs_not
        exact hcons (1 / 2) hhalf_mem ⟨hs_lt_half, hhalf_lt_t⟩
      rcases Finset.mem_image.mp (right_mem_of_ge hs hhalf_le_s) with ⟨a, ha, hs_eq⟩
      rcases Finset.mem_image.mp (right_mem_of_ge ht (le_trans hhalf_le_s (le_of_lt hst))) with
        ⟨b, hb, ht_eq⟩
      subst s
      subst t
      have hab : a < b := by linarith
      have hcons₂ : ∀ r ∈ γ₂.partition, r ∉ Set.Ioo a b := by
        intro r hr hri
        exact hcons ((r + 1) / 2)
          (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨r, hr, rfl⟩))) (by
            constructor <;> linarith [hri.1, hri.2])
      obtain ⟨p, U₀, f₀, hU₀open, hIccU₀, hf₀, hsource₀, hcoinc₀⟩ :=
        γ₂.is_analytic_strong a ha b hb hab hcons₂
      refine ⟨p, (fun r : ℝ => 2 * r - 1) ⁻¹' U₀, fun r : ℝ => f₀ (2 * r - 1), ?_, ?_, ?_, ?_, ?_⟩
      · exact hU₀open.preimage ((continuous_const.mul continuous_id).sub continuous_const)
      · intro r hr
        exact hIccU₀ ⟨by linarith [hr.1], by linarith [hr.2]⟩
      · intro r hr
        have hbase : AnalyticAt ℝ f₀ (2 * r - 1) := hf₀ (2 * r - 1) hr
        have haff : AnalyticAt ℝ (fun x : ℝ => 2 * x - 1) r := by
          fun_prop
        have hinner : (fun x : ℝ => 2 * x - 1) r = 2 * r - 1 := by
          ring
        simpa [Function.comp_def] using hbase.comp_of_eq' haff hinner
      · intro r hr
        have hext :
            (if r ≤ (2 : ℝ)⁻¹ then γ₁.extend (2 * r) else γ₂.extend (2 * r - 1)) =
              γ₂.extend (2 * r - 1) := by
          by_cases hrle : r ≤ (2 : ℝ)⁻¹
          · have hr_eq : r = (1 / 2 : ℝ) := by
              have hhalf_le_r : (1 / 2 : ℝ) ≤ r := by linarith [hr.1]
              have hrle_half : r ≤ (1 / 2 : ℝ) := by simpa [one_div] using hrle
              exact le_antisymm hrle_half hhalf_le_r
            subst r
            simp [h]
          · simp [hrle]
        simpa [hext] using hsource₀ (2 * r - 1) ⟨by linarith [hr.1], by linarith [hr.2]⟩
      · intro r hr
        have hext :
            (if r ≤ (2 : ℝ)⁻¹ then γ₁.extend (2 * r) else γ₂.extend (2 * r - 1)) =
              γ₂.extend (2 * r - 1) := by
          by_cases hrle : r ≤ (2 : ℝ)⁻¹
          · have hr_eq : r = (1 / 2 : ℝ) := by
              have hhalf_le_r : (1 / 2 : ℝ) ≤ r := by linarith [hr.1]
              have hrle_half : r ≤ (1 / 2 : ℝ) := by simpa [one_div] using hrle
              exact le_antisymm hrle_half hhalf_le_r
            subst r
            simp [h]
          · simp [hrle]
        simpa [hext] using hcoinc₀ (2 * r - 1) ⟨by linarith [hr.1], by linarith [hr.2]⟩

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
