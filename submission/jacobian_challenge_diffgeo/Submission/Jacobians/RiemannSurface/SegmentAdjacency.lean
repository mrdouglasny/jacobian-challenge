/-
Adjacency additivity for chart-local segment integrals.
-/
import Submission.Jacobians.RiemannSurface.MultiChartIntegral
import Submission.Jacobians.RiemannSurface.ArcChartDifferentiable

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

private lemma chartSeg_derivWithin_eq_deriv (γ : AnalyticArc X) (p : X)
    {a b s t r : ℝ} (hs : s ∈ γ.partition) (ht : t ∈ γ.partition)
    (hst : s < t) (hgap : Set.Ioo a b ⊆ Set.Ioo s t)
    (hgap_no : ∀ u ∈ γ.partition, u ∉ Set.Ioo s t)
    (hp : ∀ u ∈ Set.Ioo a b, γ.extend u ∈ (extChartAt 𝓘(ℂ) p).source)
    (hr : r ∈ Set.Ioo a b) :
    derivWithin (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u))
        (Set.Ioo a b) r =
      deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r := by
  have _hst : s < t := hst
  have hrst : r ∈ Set.Ioo s t := hgap hr
  have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
    have hs01 := γ.partition_subset hs
    have ht01 := γ.partition_subset ht
    exact ⟨hs01.1.trans_lt hrst.1, hrst.2.trans_le ht01.2⟩
  have hr_notmem : r ∉ (γ.partition : Set ℝ) := by
    intro hrmem
    have hrmem' : r ∈ γ.partition := by
      simpa using hrmem
    exact (hgap_no r hrmem') hrst
  have _ : DifferentiableWithinAt ℝ
      (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) (Set.Ioo a b) r :=
    arc_chart_differentiableWithinAt γ p hr01 hr_notmem (hp r hr) (Set.Ioo a b)
  exact derivWithin_of_isOpen isOpen_Ioo hr

/-- On a forward-oriented subinterval lying in one analytic partition gap and
one chart source, the chart-local segment integrand can be written using the
ordinary derivative. -/
theorem pathIntegralOnChartSeg_eq_deriv (γ : AnalyticArc X) (p : X)
    (a b : ℝ) (form : HolomorphicOneForm X) (hab : a ≤ b)
    {s t : ℝ} (hs : s ∈ γ.partition) (ht : t ∈ γ.partition) (hst : s < t)
    (hgap : Set.Ioo a b ⊆ Set.Ioo s t)
    (hgap_no : ∀ u ∈ γ.partition, u ∉ Set.Ioo s t)
    (hp : ∀ r ∈ Set.Ioo a b, γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source) :
    pathIntegralOnChartSeg γ p a b form =
      ∫ r in a..b,
        form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r := by
  unfold pathIntegralOnChartSeg
  have h_pointwise : ∀ r ∈ Set.Ioo a b,
      form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
          derivWithin (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u))
            (Set.Ioo a b) r =
        form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r := by
    intro r hr
    rw [chartSeg_derivWithin_eq_deriv γ p hs ht hst hgap hgap_no hp hr]
  refine intervalIntegral.integral_congr_ae ?_
  rw [MeasureTheory.ae_uIoc_iff]
  constructor
  · filter_upwards
      [Ioo_ae_eq_Ioc (a := a) (b := b) (μ := MeasureTheory.volume)]
      with r hr_eq hr
    exact h_pointwise r (by
      change Set.Ioo a b r
      rw [hr_eq]
      exact hr)
  · filter_upwards with r hr
    have h_empty : Set.Ioc b a = (∅ : Set ℝ) :=
      Set.Ioc_eq_empty (not_lt_of_ge hab)
    rw [h_empty] at hr
    exact False.elim hr

/-- Adjacent chart-local segment integrals with the same chart center add to the
integral over their union. -/
theorem pathIntegralOnChartSeg_split (γ : AnalyticArc X) (p : X)
    {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (form : HolomorphicOneForm X)
    {s t : ℝ} (hs : s ∈ γ.partition) (ht : t ∈ γ.partition) (hst : s < t)
    (hgap : Set.Ioo a b ⊆ Set.Ioo s t)
    (hgap_no : ∀ u ∈ γ.partition, u ∉ Set.Ioo s t)
    (hp : ∀ r ∈ Set.Ioo a b, γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source)
    (hint : IntervalIntegrable
      (fun r : ℝ =>
        form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r)
      MeasureTheory.volume a b) :
    pathIntegralOnChartSeg γ p a b form =
      pathIntegralOnChartSeg γ p a c form +
        pathIntegralOnChartSeg γ p c b form := by
  let F : ℝ → ℂ := fun r =>
    form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
      deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r
  have hab : a ≤ b := hac.trans hcb
  have hcab : c ∈ Set.uIcc a b := Set.mem_uIcc_of_le hac hcb
  have hgap_ac : Set.Ioo a c ⊆ Set.Ioo s t := by
    intro r hr
    exact hgap ⟨hr.1, hr.2.trans_le hcb⟩
  have hp_ac : ∀ r ∈ Set.Ioo a c, γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source := by
    intro r hr
    exact hp r ⟨hr.1, hr.2.trans_le hcb⟩
  have hgap_cb : Set.Ioo c b ⊆ Set.Ioo s t := by
    intro r hr
    exact hgap ⟨hac.trans_lt hr.1, hr.2⟩
  have hp_cb : ∀ r ∈ Set.Ioo c b, γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source := by
    intro r hr
    exact hp r ⟨hac.trans_lt hr.1, hr.2⟩
  have hint_ac : IntervalIntegrable F MeasureTheory.volume a c :=
    hint.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hcab)
  have hint_cb : IntervalIntegrable F MeasureTheory.volume c b :=
    hint.mono_set (Set.uIcc_subset_uIcc hcab Set.right_mem_uIcc)
  have h_ab :
      pathIntegralOnChartSeg γ p a b form = ∫ r in a..b, F r := by
    simpa [F] using
      pathIntegralOnChartSeg_eq_deriv γ p a b form hab hs ht hst hgap hgap_no hp
  have h_ac :
      pathIntegralOnChartSeg γ p a c form = ∫ r in a..c, F r := by
    simpa [F] using
      pathIntegralOnChartSeg_eq_deriv γ p a c form hac hs ht hst hgap_ac hgap_no hp_ac
  have h_cb :
      pathIntegralOnChartSeg γ p c b form = ∫ r in c..b, F r := by
    simpa [F] using
      pathIntegralOnChartSeg_eq_deriv γ p c b form hcb hs ht hst hgap_cb hgap_no hp_cb
  calc
    pathIntegralOnChartSeg γ p a b form = ∫ r in a..b, F r := h_ab
    _ = (∫ r in a..c, F r) + ∫ r in c..b, F r :=
      (intervalIntegral.integral_add_adjacent_intervals hint_ac hint_cb).symm
    _ = pathIntegralOnChartSeg γ p a c form +
        pathIntegralOnChartSeg γ p c b form := by
      rw [← h_ac, ← h_cb]

end Jacobians.RiemannSurface
