/-
Good-partition independence for the multi-chart integral along an analytic arc.
-/
import Submission.Jacobians.RiemannSurface.SegmentAdjacency
import Submission.Jacobians.RiemannSurface.SegmentCenterIndependence

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open intervalIntegral MeasureTheory
open Set Filter

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- A chart-subordinate partition whose open cells lie in analytic partition
gaps of the arc. -/
structure GoodPartition (γ : AnalyticArc X) extends ChartSubordinatePartition γ where
  gap : ∀ i : Fin n, ∃ s ∈ γ.partition, ∃ u ∈ γ.partition,
    s < u ∧ Set.Ioo (t i.castSucc) (t i.succ) ⊆ Set.Ioo s u ∧
      (∀ r ∈ γ.partition, r ∉ Set.Ioo s u)

namespace GoodPartition

/-- Good partitions exist by refining a chart-subordinate partition with the
analytic partition of the arc. -/
instance instNonempty (γ : AnalyticArc X) : Nonempty (GoodPartition γ) := by
  obtain ⟨n, tau, p, ht_zero, ht_last, ht_mono, hmem, hgap⟩ :=
    exists_good_partition γ
  exact ⟨
    { n := n
      t := tau
      p := p
      t_zero := ht_zero
      t_last := ht_last
      t_mono := ht_mono
      mem_source := hmem
      gap := hgap }⟩

end GoodPartition

/-- The ordinary-derivative integrand using the moving chart centered at
`γ.extend r`. -/
noncomputable def canonicalIntegrand (γ : AnalyticArc X)
    (form : HolomorphicOneForm X) : ℝ → ℂ :=
  fun r : ℝ =>
    form.coeff (γ.extend r)
        ((extChartAt 𝓘(ℂ) (γ.extend r)) (γ.extend r)) *
      deriv
        (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ.extend r)) (γ.extend u)) r

private lemma no_mem_between_orderEmb_succ (Pset : Finset ℝ) {m : ℕ}
    (hcard : Pset.card = m + 1) (i : Fin m) {x : ℝ}
    (hx : x ∈ Pset)
    (hbetween : Pset.orderEmbOfFin hcard i.castSucc < x ∧
      x < Pset.orderEmbOfFin hcard i.succ) : False := by
  have hxrange : x ∈ Set.range (Pset.orderEmbOfFin hcard) := by
    simpa [Finset.range_orderEmbOfFin Pset hcard] using hx
  rcases hxrange with ⟨j, rfl⟩
  have hleft : i.castSucc < j :=
    ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hbetween.1
  have hright : j < i.succ :=
    ((Pset.orderEmbOfFin hcard).lt_iff_lt).mp hbetween.2
  have hleft_nat : i.val < j.val := by
    simpa [Fin.lt_def, Fin.val_castSucc] using hleft
  have hright_nat : j.val < i.val + 1 := by
    simpa [Fin.lt_def, Fin.val_succ] using hright
  omega

private lemma analyticArc_canonicalIntegrand_refined_cell_intervalIntegrable
    (γ : AnalyticArc X) (form : HolomorphicOneForm X)
    {a b s t : ℝ} (ha : a ∈ γ.partition) (hb : b ∈ γ.partition) (_hab : a < b)
    (hbase_cons : ∀ r ∈ γ.partition, r ∉ Set.Ioo a b)
    (hst : s < t) (hcell_base : Set.Icc s t ⊆ Set.Icc a b)
    {p : X} {U : Set ℝ} {f : ℝ → ℂ}
    (hUopen : IsOpen U) (hIccU : Set.Icc s t ⊆ U) (hfU : AnalyticOnNhd ℝ f U)
    (hsource : ∀ r ∈ U ∩ Set.Icc a b, γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source)
    (hcoinc : ∀ r ∈ U ∩ Set.Icc a b, (extChartAt 𝓘(ℂ) p) (γ.extend r) = f r) :
    IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume s t := by
  let G : ℝ → ℂ := fun r => form.coeff p (f r) * deriv f r
  have hf_cont : ContinuousOn f (Set.Icc s t) :=
    hfU.continuousOn.mono hIccU
  have htarget : Set.MapsTo f (Set.Icc s t) (extChartAt 𝓘(ℂ) p).target := by
    intro r hr
    have hrU : r ∈ U ∩ Set.Icc a b := ⟨hIccU hr, hcell_base hr⟩
    rw [← hcoinc r hrU]
    exact (extChartAt 𝓘(ℂ) p).map_source (hsource r hrU)
  have hcoeff_cont : ContinuousOn (fun r : ℝ => form.coeff p (f r)) (Set.Icc s t) :=
    (form.2.1 p).continuousOn.comp hf_cont htarget
  have hf_contDiff : ContDiffOn ℝ ∞ f U :=
    hfU.analyticOn.contDiffOn hUopen.uniqueDiffOn
  have hderiv_cont : ContinuousOn (deriv f) (Set.Icc s t) :=
    (hf_contDiff.continuousOn_deriv_of_isOpen hUopen (by simp)).mono hIccU
  have hG_cont : ContinuousOn G (Set.Icc s t) :=
    hcoeff_cont.mul hderiv_cont
  have hG_int : IntervalIntegrable G MeasureTheory.volume s t :=
    hG_cont.intervalIntegrable_of_Icc hst.le
  refine hG_int.congr_ae ?_
  rw [Filter.EventuallyEq, Set.uIoc_of_le hst.le]
  refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Filter.Eventually.of_forall fun r hrst => by
    have hricc : r ∈ Set.Icc s t := Set.Ioo_subset_Icc_self hrst
    have hrbase : r ∈ Set.Icc a b := hcell_base hricc
    have hsbase : a ≤ s := (hcell_base ⟨le_rfl, le_of_lt hst⟩).1
    have htbase : t ≤ b := (hcell_base ⟨le_of_lt hst, le_rfl⟩).2
    have hrU : r ∈ U ∩ Set.Icc a b := ⟨hIccU hricc, hrbase⟩
    have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
      have ha01 := γ.partition_subset ha
      have hb01 := γ.partition_subset hb
      exact ⟨ha01.1.trans_lt (lt_of_le_of_lt hsbase hrst.1),
        (lt_of_lt_of_le hrst.2 htbase).trans_le hb01.2⟩
    have hr_notmem : r ∉ (γ.partition : Set ℝ) := by
      intro hrmem
      exact hbase_cons r (by simpa using hrmem)
        ⟨lt_of_le_of_lt hsbase hrst.1, lt_of_lt_of_le hrst.2 htbase⟩
    have hdp : DifferentiableWithinAt ℝ
        (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) (Set.Ioo s t) r :=
      arc_chart_differentiableWithinAt γ p hr01 hr_notmem (hsource r hrU) (Set.Ioo s t)
    have hcenter := integrand_center_independent form γ p (γ.extend r) s t r
      (hsource r hrU) (mem_extChartAt_source (I := 𝓘(ℂ)) (γ.extend r)) hdp hrst
    have hcoord_eq : (chartAt ℂ p) (γ.extend r) = f r := by
      simpa [extChartAt_coe, modelWithCornersSelf_coe] using hcoinc r hrU
    have hfixed_eq :
        (fun u : ℝ => (chartAt ℂ p) (γ.extend u)) =ᶠ[𝓝 r] f := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hrst] with u hu
      have huicc : u ∈ Set.Icc s t := Set.Ioo_subset_Icc_self hu
      simpa [extChartAt_coe, modelWithCornersSelf_coe] using
        hcoinc u ⟨hIccU huicc, hcell_base huicc⟩
    have hderiv_eq :
        deriv (fun u : ℝ => (chartAt ℂ p) (γ.extend u)) r = deriv f r :=
      hfixed_eq.deriv_eq
    have hpoint :
        form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r =
          canonicalIntegrand γ form r := by
      simpa [canonicalIntegrand, derivWithin_of_isOpen isOpen_Ioo hrst] using hcenter
    simpa [G, hcoord_eq, hderiv_eq] using hpoint

private lemma analyticArc_canonicalIntegrand_cell_intervalIntegrable
    (γ : AnalyticArc X) (form : HolomorphicOneForm X)
    {s t : ℝ} (hs : s ∈ γ.partition) (ht : t ∈ γ.partition) (hst : s < t)
    (hcons : ∀ r ∈ γ.partition, r ∉ Set.Ioo s t) :
    IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume s t := by
  classical
  obtain ⟨τ, hsτ, htτ, hτsub, hτ⟩ := γ.is_analytic_strong s hs t ht hst hcons
  let Pset : Finset ℝ := τ
  have hPsubset : ↑Pset ⊆ Set.Icc s t := by
    simpa [Pset] using hτsub
  have hzeroP : s ∈ Pset := by
    simpa [Pset] using hsτ
  have honeP : t ∈ Pset := by
    simpa [Pset] using htτ
  have hP_nonempty : Pset.Nonempty := ⟨s, hzeroP⟩
  have hcard_pos : 0 < Pset.card := Finset.card_pos.mpr hP_nonempty
  let n : Nat := Pset.card - 1
  have hcard : Pset.card = n + 1 := by
    have hsucc := Nat.succ_pred_eq_of_pos hcard_pos
    simpa [n, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using hsucc.symm
  let a : ℕ → ℝ :=
    fun k => if h : k < n + 1 then Pset.orderEmbOfFin hcard ⟨k, h⟩ else s
  have ha0 : a 0 = s := by
    have hz : 0 < n + 1 := Nat.succ_pos n
    change Pset.orderEmbOfFin hcard ⟨0, hz⟩ = s
    calc
      Pset.orderEmbOfFin hcard ⟨0, hz⟩ =
          Pset.min' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
        simpa using Finset.orderEmbOfFin_zero (s := Pset) hcard hz
      _ = s := by
        exact (Finset.min'_eq_iff Pset _ s).2
          ⟨hzeroP, fun x hx => (hPsubset hx).1⟩
  have haN : a n = t := by
    have hn : n < n + 1 := Nat.lt_succ_self n
    dsimp [a]
    rw [dif_pos hn]
    have hfin :
        (⟨n, hn⟩ : Fin (n + 1)) = Fin.last n := by
      ext
      simp [Fin.last]
    calc
      Pset.orderEmbOfFin hcard ⟨n, hn⟩ =
          Pset.orderEmbOfFin hcard (Fin.last n) := by rw [hfin]
      _ = Pset.max' (Finset.card_pos.mp (hcard.symm ▸ Nat.succ_pos n)) := by
        simpa [Fin.last, Nat.succ_eq_add_one] using
          Finset.orderEmbOfFin_last (s := Pset) hcard (Nat.succ_pos n)
      _ = t := by
        exact (Finset.max'_eq_iff Pset _ t).2
          ⟨honeP, fun x hx => (hPsubset hx).2⟩
  have hcells : ∀ k < n,
      IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
        (a k) (a (k + 1)) := by
    intro k hk
    let i : Fin n := ⟨k, hk⟩
    have hk0 : k < n + 1 := Nat.lt_trans hk (Nat.lt_succ_self n)
    have hk1 : k + 1 < n + 1 := Nat.succ_lt_succ hk
    have hak : a k = Pset.orderEmbOfFin hcard i.castSucc := by
      dsimp [a]
      rw [dif_pos hk0]
      rfl
    have hak1 : a (k + 1) = Pset.orderEmbOfFin hcard i.succ := by
      dsimp [a]
      rw [dif_pos hk1]
      rfl
    have hs_mem : a k ∈ τ := by
      rw [hak]
      simpa [Pset]
    have ht_mem : a (k + 1) ∈ τ := by
      rw [hak1]
      simpa [Pset]
    have hst_cell : a k < a (k + 1) := by
      rw [hak, hak1]
      exact (Pset.orderEmbOfFin hcard).strictMono (by
        simp [i, Fin.lt_def, Fin.val_castSucc, Fin.val_succ])
    have hτcons : ∀ r ∈ τ, r ∉ Set.Ioo (a k) (a (k + 1)) := by
      intro r hr hrt
      rw [hak, hak1] at hrt
      exact no_mem_between_orderEmb_succ Pset hcard i (by simpa [Pset] using hr) hrt
    have hcell_base : Set.Icc (a k) (a (k + 1)) ⊆ Set.Icc s t := by
      intro r hr
      have hs_base := hτsub hs_mem
      have ht_base := hτsub ht_mem
      exact ⟨hs_base.1.trans hr.1, hr.2.trans ht_base.2⟩
    obtain ⟨p, U, f, hUopen, hIccU, hfU, hsource, hcoinc⟩ :=
      hτ (a k) hs_mem (a (k + 1)) ht_mem hst_cell hτcons
    exact analyticArc_canonicalIntegrand_refined_cell_intervalIntegrable γ form
      hs ht hst hcons hst_cell hcell_base hUopen hIccU hfU hsource hcoinc
  have hchain : IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume (a 0) (a n) :=
    IntervalIntegrable.trans_iterate hcells
  simpa [ha0, haN] using hchain

/-- Strong analytic arcs have interval-integrable canonical moving-chart
integrands on `[0, 1]`. -/
theorem analyticArc_canonicalIntegrand_intervalIntegrable
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) :
    IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume 0 1 := by
  classical
  let Pset : Finset ℝ := γ.partition
  have hPsubset : ↑Pset ⊆ Set.Icc (0 : ℝ) 1 := by
    simpa [Pset] using γ.partition_subset
  have hzeroP : (0 : ℝ) ∈ Pset := by
    simpa [Pset] using γ.zero_mem
  have honeP : (1 : ℝ) ∈ Pset := by
    simpa [Pset] using γ.one_mem
  have hP_nonempty : Pset.Nonempty := ⟨0, hzeroP⟩
  have hcard_pos : 0 < Pset.card := Finset.card_pos.mpr hP_nonempty
  let n : Nat := Pset.card - 1
  have hcard : Pset.card = n + 1 := by
    have hsucc := Nat.succ_pred_eq_of_pos hcard_pos
    simpa [n, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using hsucc.symm
  let a : ℕ → ℝ :=
    fun k => if h : k < n + 1 then Pset.orderEmbOfFin hcard ⟨k, h⟩ else 0
  have ha0 : a 0 = 0 := by
    have hz : 0 < n + 1 := Nat.succ_pos n
    change Pset.orderEmbOfFin hcard ⟨0, hz⟩ = 0
    calc
      Pset.orderEmbOfFin hcard ⟨0, hz⟩ =
          Pset.min' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
        simpa using Finset.orderEmbOfFin_zero (s := Pset) hcard hz
      _ = 0 := by
        exact (Finset.min'_eq_iff Pset _ 0).2
          ⟨hzeroP, fun x hx => (hPsubset hx).1⟩
  have haN : a n = 1 := by
    have hn : n < n + 1 := Nat.lt_succ_self n
    dsimp [a]
    rw [dif_pos hn]
    have hfin :
        (⟨n, hn⟩ : Fin (n + 1)) = Fin.last n := by
      ext
      simp [Fin.last]
    calc
      Pset.orderEmbOfFin hcard ⟨n, hn⟩ =
          Pset.orderEmbOfFin hcard (Fin.last n) := by rw [hfin]
      _ = Pset.max' (Finset.card_pos.mp (hcard.symm ▸ Nat.succ_pos n)) := by
        simpa [Fin.last, Nat.succ_eq_add_one] using
          Finset.orderEmbOfFin_last (s := Pset) hcard (Nat.succ_pos n)
      _ = 1 := by
        exact (Finset.max'_eq_iff Pset _ 1).2
          ⟨honeP, fun x hx => (hPsubset hx).2⟩
  have hcells : ∀ k < n,
      IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
        (a k) (a (k + 1)) := by
    intro k hk
    let i : Fin n := ⟨k, hk⟩
    have hk0 : k < n + 1 := Nat.lt_trans hk (Nat.lt_succ_self n)
    have hk1 : k + 1 < n + 1 := Nat.succ_lt_succ hk
    have hak : a k = Pset.orderEmbOfFin hcard i.castSucc := by
      dsimp [a]
      rw [dif_pos hk0]
      rfl
    have hak1 : a (k + 1) = Pset.orderEmbOfFin hcard i.succ := by
      dsimp [a]
      rw [dif_pos hk1]
      rfl
    have hs_mem : a k ∈ γ.partition := by
      rw [hak]
      simpa [Pset]
    have ht_mem : a (k + 1) ∈ γ.partition := by
      rw [hak1]
      simpa [Pset]
    have hst_cell : a k < a (k + 1) := by
      rw [hak, hak1]
      exact (Pset.orderEmbOfFin hcard).strictMono (by
        simp [i, Fin.lt_def, Fin.val_castSucc, Fin.val_succ])
    have hcons : ∀ r ∈ γ.partition, r ∉ Set.Ioo (a k) (a (k + 1)) := by
      intro r hr hrt
      rw [hak, hak1] at hrt
      exact no_mem_between_orderEmb_succ Pset hcard i (by simpa [Pset] using hr) hrt
    exact analyticArc_canonicalIntegrand_cell_intervalIntegrable γ form
      hs_mem ht_mem hst_cell hcons
  have hchain : IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume (a 0) (a n) :=
    IntervalIntegrable.trans_iterate hcells
  simpa [ha0, haN] using hchain

private lemma analyticArc_fixedChartIntegrand_refined_cell_intervalIntegrable
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) (q : X)
    {a b s t : ℝ} (ha : a ∈ γ.partition) (hb : b ∈ γ.partition) (_hab : a < b)
    (hbase_cons : ∀ r ∈ γ.partition, r ∉ Set.Ioo a b)
    (hst : s < t) (hcell_base : Set.Icc s t ⊆ Set.Icc a b)
    (hqsource : ∀ r ∈ Set.Icc a b, γ.extend r ∈ (extChartAt 𝓘(ℂ) q).source)
    {p : X} {U : Set ℝ} {f : ℝ → ℂ}
    (hUopen : IsOpen U) (hIccU : Set.Icc s t ⊆ U) (hfU : AnalyticOnNhd ℝ f U)
    (hsource : ∀ r ∈ U ∩ Set.Icc a b, γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source)
    (hcoinc : ∀ r ∈ U ∩ Set.Icc a b, (extChartAt 𝓘(ℂ) p) (γ.extend r) = f r) :
    IntervalIntegrable
      (fun r : ℝ =>
        form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u)) r)
      MeasureTheory.volume s t := by
  let G : ℝ → ℂ := fun r => form.coeff p (f r) * deriv f r
  have hf_cont : ContinuousOn f (Set.Icc s t) :=
    hfU.continuousOn.mono hIccU
  have htarget : Set.MapsTo f (Set.Icc s t) (extChartAt 𝓘(ℂ) p).target := by
    intro r hr
    have hrU : r ∈ U ∩ Set.Icc a b := ⟨hIccU hr, hcell_base hr⟩
    rw [← hcoinc r hrU]
    exact (extChartAt 𝓘(ℂ) p).map_source (hsource r hrU)
  have hcoeff_cont : ContinuousOn (fun r : ℝ => form.coeff p (f r)) (Set.Icc s t) :=
    (form.2.1 p).continuousOn.comp hf_cont htarget
  have hf_contDiff : ContDiffOn ℝ ∞ f U :=
    hfU.analyticOn.contDiffOn hUopen.uniqueDiffOn
  have hderiv_cont : ContinuousOn (deriv f) (Set.Icc s t) :=
    (hf_contDiff.continuousOn_deriv_of_isOpen hUopen (by simp)).mono hIccU
  have hG_cont : ContinuousOn G (Set.Icc s t) :=
    hcoeff_cont.mul hderiv_cont
  have hG_int : IntervalIntegrable G MeasureTheory.volume s t :=
    hG_cont.intervalIntegrable_of_Icc hst.le
  refine hG_int.congr_ae ?_
  rw [Filter.EventuallyEq, Set.uIoc_of_le hst.le]
  refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Filter.Eventually.of_forall fun r hrst => by
    have hricc : r ∈ Set.Icc s t := Set.Ioo_subset_Icc_self hrst
    have hrbase : r ∈ Set.Icc a b := hcell_base hricc
    have hsbase : a ≤ s := (hcell_base ⟨le_rfl, le_of_lt hst⟩).1
    have htbase : t ≤ b := (hcell_base ⟨le_of_lt hst, le_rfl⟩).2
    have hrU : r ∈ U ∩ Set.Icc a b := ⟨hIccU hricc, hrbase⟩
    have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
      have ha01 := γ.partition_subset ha
      have hb01 := γ.partition_subset hb
      exact ⟨ha01.1.trans_lt (lt_of_le_of_lt hsbase hrst.1),
        (lt_of_lt_of_le hrst.2 htbase).trans_le hb01.2⟩
    have hr_notmem : r ∉ (γ.partition : Set ℝ) := by
      intro hrmem
      exact hbase_cons r (by simpa using hrmem)
        ⟨lt_of_le_of_lt hsbase hrst.1, lt_of_lt_of_le hrst.2 htbase⟩
    have hdp : DifferentiableWithinAt ℝ
        (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) (Set.Ioo s t) r :=
      arc_chart_differentiableWithinAt γ p hr01 hr_notmem (hsource r hrU) (Set.Ioo s t)
    have hcenter := integrand_center_independent form γ p q s t r
      (hsource r hrU) (hqsource r hrbase) hdp hrst
    have hcoord_eq : (chartAt ℂ p) (γ.extend r) = f r := by
      simpa [extChartAt_coe, modelWithCornersSelf_coe] using hcoinc r hrU
    have hfixed_eq :
        (fun u : ℝ => (chartAt ℂ p) (γ.extend u)) =ᶠ[𝓝 r] f := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioo hrst] with u hu
      have huicc : u ∈ Set.Icc s t := Set.Ioo_subset_Icc_self hu
      simpa [extChartAt_coe, modelWithCornersSelf_coe] using
        hcoinc u ⟨hIccU huicc, hcell_base huicc⟩
    have hderiv_eq :
        deriv (fun u : ℝ => (chartAt ℂ p) (γ.extend u)) r = deriv f r :=
      hfixed_eq.deriv_eq
    have hpoint :
        form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r =
          form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u)) r := by
      simpa [derivWithin_of_isOpen isOpen_Ioo hrst] using hcenter
    simpa [G, hcoord_eq, hderiv_eq] using hpoint

private lemma analyticArc_fixedChartIntegrand_cell_intervalIntegrable
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) (q : X)
    {s t : ℝ} (hs : s ∈ γ.partition) (ht : t ∈ γ.partition) (hst : s < t)
    (hcons : ∀ r ∈ γ.partition, r ∉ Set.Ioo s t)
    (hqsource : ∀ r ∈ Set.Icc s t, γ.extend r ∈ (extChartAt 𝓘(ℂ) q).source) :
    IntervalIntegrable
      (fun r : ℝ =>
        form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u)) r)
      MeasureTheory.volume s t := by
  classical
  obtain ⟨τ, hsτ, htτ, hτsub, hτ⟩ := γ.is_analytic_strong s hs t ht hst hcons
  let Pset : Finset ℝ := τ
  have hPsubset : ↑Pset ⊆ Set.Icc s t := by
    simpa [Pset] using hτsub
  have hzeroP : s ∈ Pset := by
    simpa [Pset] using hsτ
  have honeP : t ∈ Pset := by
    simpa [Pset] using htτ
  have hP_nonempty : Pset.Nonempty := ⟨s, hzeroP⟩
  have hcard_pos : 0 < Pset.card := Finset.card_pos.mpr hP_nonempty
  let n : Nat := Pset.card - 1
  have hcard : Pset.card = n + 1 := by
    have hsucc := Nat.succ_pred_eq_of_pos hcard_pos
    simpa [n, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using hsucc.symm
  let a : ℕ → ℝ :=
    fun k => if h : k < n + 1 then Pset.orderEmbOfFin hcard ⟨k, h⟩ else s
  have ha0 : a 0 = s := by
    have hz : 0 < n + 1 := Nat.succ_pos n
    change Pset.orderEmbOfFin hcard ⟨0, hz⟩ = s
    calc
      Pset.orderEmbOfFin hcard ⟨0, hz⟩ =
          Pset.min' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
        simpa using Finset.orderEmbOfFin_zero (s := Pset) hcard hz
      _ = s := by
        exact (Finset.min'_eq_iff Pset _ s).2
          ⟨hzeroP, fun x hx => (hPsubset hx).1⟩
  have haN : a n = t := by
    have hn : n < n + 1 := Nat.lt_succ_self n
    dsimp [a]
    rw [dif_pos hn]
    have hfin :
        (⟨n, hn⟩ : Fin (n + 1)) = Fin.last n := by
      ext
      simp [Fin.last]
    calc
      Pset.orderEmbOfFin hcard ⟨n, hn⟩ =
          Pset.orderEmbOfFin hcard (Fin.last n) := by rw [hfin]
      _ = Pset.max' (Finset.card_pos.mp (hcard.symm ▸ Nat.succ_pos n)) := by
        simpa [Fin.last, Nat.succ_eq_add_one] using
          Finset.orderEmbOfFin_last (s := Pset) hcard (Nat.succ_pos n)
      _ = t := by
        exact (Finset.max'_eq_iff Pset _ t).2
          ⟨honeP, fun x hx => (hPsubset hx).2⟩
  have hcells : ∀ k < n,
      IntervalIntegrable
        (fun r : ℝ =>
          form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u)) r)
        MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    let i : Fin n := ⟨k, hk⟩
    have hk0 : k < n + 1 := Nat.lt_trans hk (Nat.lt_succ_self n)
    have hk1 : k + 1 < n + 1 := Nat.succ_lt_succ hk
    have hak : a k = Pset.orderEmbOfFin hcard i.castSucc := by
      dsimp [a]
      rw [dif_pos hk0]
      rfl
    have hak1 : a (k + 1) = Pset.orderEmbOfFin hcard i.succ := by
      dsimp [a]
      rw [dif_pos hk1]
      rfl
    have hs_mem : a k ∈ τ := by
      rw [hak]
      simpa [Pset]
    have ht_mem : a (k + 1) ∈ τ := by
      rw [hak1]
      simpa [Pset]
    have hst_cell : a k < a (k + 1) := by
      rw [hak, hak1]
      exact (Pset.orderEmbOfFin hcard).strictMono (by
        simp [i, Fin.lt_def, Fin.val_castSucc, Fin.val_succ])
    have hτcons : ∀ r ∈ τ, r ∉ Set.Ioo (a k) (a (k + 1)) := by
      intro r hr hrt
      rw [hak, hak1] at hrt
      exact no_mem_between_orderEmb_succ Pset hcard i (by simpa [Pset] using hr) hrt
    have hcell_base : Set.Icc (a k) (a (k + 1)) ⊆ Set.Icc s t := by
      intro r hr
      have hs_base := hτsub hs_mem
      have ht_base := hτsub ht_mem
      exact ⟨hs_base.1.trans hr.1, hr.2.trans ht_base.2⟩
    obtain ⟨p, U, f, hUopen, hIccU, hfU, hsource, hcoinc⟩ :=
      hτ (a k) hs_mem (a (k + 1)) ht_mem hst_cell hτcons
    exact analyticArc_fixedChartIntegrand_refined_cell_intervalIntegrable γ form q
      hs ht hst hcons hst_cell hcell_base hqsource hUopen hIccU hfU hsource hcoinc
  have hchain :
      IntervalIntegrable
        (fun r : ℝ =>
          form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u)) r)
        MeasureTheory.volume (a 0) (a n) :=
    IntervalIntegrable.trans_iterate hcells
  simpa [ha0, haN] using hchain

/-- Strong analytic arcs have interval-integrable fixed-chart integrands on
`[0, 1]`, provided the arc lies in the fixed chart source on `[0, 1]`. -/
theorem analyticArc_fixedChartIntegrand_intervalIntegrable
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) (q : X)
    (hqsource : ∀ r ∈ Set.Icc (0 : ℝ) 1,
      γ.extend r ∈ (extChartAt 𝓘(ℂ) q).source) :
    IntervalIntegrable
      (fun r : ℝ =>
        form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
          deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u)) r)
      MeasureTheory.volume 0 1 := by
  classical
  let Pset : Finset ℝ := γ.partition
  have hPsubset : ↑Pset ⊆ Set.Icc (0 : ℝ) 1 := by
    simpa [Pset] using γ.partition_subset
  have hzeroP : (0 : ℝ) ∈ Pset := by
    simpa [Pset] using γ.zero_mem
  have honeP : (1 : ℝ) ∈ Pset := by
    simpa [Pset] using γ.one_mem
  have hP_nonempty : Pset.Nonempty := ⟨0, hzeroP⟩
  have hcard_pos : 0 < Pset.card := Finset.card_pos.mpr hP_nonempty
  let n : Nat := Pset.card - 1
  have hcard : Pset.card = n + 1 := by
    have hsucc := Nat.succ_pred_eq_of_pos hcard_pos
    simpa [n, Nat.pred_eq_sub_one, Nat.succ_eq_add_one] using hsucc.symm
  let a : ℕ → ℝ :=
    fun k => if h : k < n + 1 then Pset.orderEmbOfFin hcard ⟨k, h⟩ else 0
  have ha0 : a 0 = 0 := by
    have hz : 0 < n + 1 := Nat.succ_pos n
    change Pset.orderEmbOfFin hcard ⟨0, hz⟩ = 0
    calc
      Pset.orderEmbOfFin hcard ⟨0, hz⟩ =
          Pset.min' (Finset.card_pos.mp (hcard.symm ▸ hz)) := by
        simpa using Finset.orderEmbOfFin_zero (s := Pset) hcard hz
      _ = 0 := by
        exact (Finset.min'_eq_iff Pset _ 0).2
          ⟨hzeroP, fun x hx => (hPsubset hx).1⟩
  have haN : a n = 1 := by
    have hn : n < n + 1 := Nat.lt_succ_self n
    dsimp [a]
    rw [dif_pos hn]
    have hfin :
        (⟨n, hn⟩ : Fin (n + 1)) = Fin.last n := by
      ext
      simp [Fin.last]
    calc
      Pset.orderEmbOfFin hcard ⟨n, hn⟩ =
          Pset.orderEmbOfFin hcard (Fin.last n) := by rw [hfin]
      _ = Pset.max' (Finset.card_pos.mp (hcard.symm ▸ Nat.succ_pos n)) := by
        simpa [Fin.last, Nat.succ_eq_add_one] using
          Finset.orderEmbOfFin_last (s := Pset) hcard (Nat.succ_pos n)
      _ = 1 := by
        exact (Finset.max'_eq_iff Pset _ 1).2
          ⟨honeP, fun x hx => (hPsubset hx).2⟩
  have hcells : ∀ k < n,
      IntervalIntegrable
        (fun r : ℝ =>
          form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u)) r)
        MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    let i : Fin n := ⟨k, hk⟩
    have hk0 : k < n + 1 := Nat.lt_trans hk (Nat.lt_succ_self n)
    have hk1 : k + 1 < n + 1 := Nat.succ_lt_succ hk
    have hak : a k = Pset.orderEmbOfFin hcard i.castSucc := by
      dsimp [a]
      rw [dif_pos hk0]
      rfl
    have hak1 : a (k + 1) = Pset.orderEmbOfFin hcard i.succ := by
      dsimp [a]
      rw [dif_pos hk1]
      rfl
    have hs_mem : a k ∈ γ.partition := by
      rw [hak]
      simpa [Pset]
    have ht_mem : a (k + 1) ∈ γ.partition := by
      rw [hak1]
      simpa [Pset]
    have hst_cell : a k < a (k + 1) := by
      rw [hak, hak1]
      exact (Pset.orderEmbOfFin hcard).strictMono (by
        simp [i, Fin.lt_def, Fin.val_castSucc, Fin.val_succ])
    have hcons : ∀ r ∈ γ.partition, r ∉ Set.Ioo (a k) (a (k + 1)) := by
      intro r hr hrt
      rw [hak, hak1] at hrt
      exact no_mem_between_orderEmb_succ Pset hcard i (by simpa [Pset] using hr) hrt
    have hqsource_cell : ∀ r ∈ Set.Icc (a k) (a (k + 1)),
        γ.extend r ∈ (extChartAt 𝓘(ℂ) q).source := by
      intro r hr
      have hs01 := γ.partition_subset hs_mem
      have ht01 := γ.partition_subset ht_mem
      exact hqsource r ⟨hs01.1.trans hr.1, hr.2.trans ht01.2⟩
    exact analyticArc_fixedChartIntegrand_cell_intervalIntegrable γ form q
      hs_mem ht_mem hst_cell hcons hqsource_cell
  have hchain :
      IntervalIntegrable
        (fun r : ℝ =>
          form.coeff q ((extChartAt 𝓘(ℂ) q) (γ.extend r)) *
            deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) q) (γ.extend u)) r)
        MeasureTheory.volume (a 0) (a n) :=
    IntervalIntegrable.trans_iterate hcells
  simpa [ha0, haN] using hchain

private lemma chartSubordinatePartition_t_mem_uIcc (γ : AnalyticArc X)
    (P : ChartSubordinatePartition γ) (j : Fin (P.n + 1)) :
    P.t j ∈ Set.uIcc (0 : ℝ) 1 := by
  refine Set.mem_uIcc_of_le ?_ ?_
  · have h0j : (0 : Fin (P.n + 1)) ≤ j := Fin.zero_le j
    have := P.t_mono h0j
    simpa [P.t_zero] using this
  · have hjlast : j ≤ Fin.last P.n := Fin.le_last j
    have := P.t_mono hjlast
    simpa [P.t_last] using this

private lemma chartSubordinatePartition_cell_intervalIntegrable
    (γ : AnalyticArc X) (P : ChartSubordinatePartition γ)
    (form : HolomorphicOneForm X)
    (hint : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume 0 1)
    (i : Fin P.n) :
    IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
      (P.t i.castSucc) (P.t i.succ) := by
  exact hint.mono_set (Set.uIcc_subset_uIcc
    (chartSubordinatePartition_t_mem_uIcc γ P i.castSucc)
    (chartSubordinatePartition_t_mem_uIcc γ P i.succ))

private lemma pathIntegralOnChartSeg_eq_canonicalIntegrand
    (γ : AnalyticArc X) (p : X) (a b : ℝ)
    (form : HolomorphicOneForm X) (hab : a ≤ b)
    {s t : ℝ} (hs : s ∈ γ.partition) (ht : t ∈ γ.partition)
    (hst : s < t) (hgap : Set.Ioo a b ⊆ Set.Ioo s t)
    (hgap_no : ∀ r ∈ γ.partition, r ∉ Set.Ioo s t)
    (hp : ∀ r ∈ Set.Ioo a b,
      γ.extend r ∈ (extChartAt 𝓘(ℂ) p).source) :
    pathIntegralOnChartSeg γ p a b form =
      ∫ r in a..b, canonicalIntegrand γ form r := by
  let Fp : ℝ → ℂ := fun r =>
    form.coeff p ((extChartAt 𝓘(ℂ) p) (γ.extend r)) *
      deriv (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u)) r
  have h_deriv :
      pathIntegralOnChartSeg γ p a b form = ∫ r in a..b, Fp r := by
    simpa [Fp] using
      pathIntegralOnChartSeg_eq_deriv γ p a b form hab hs ht hst hgap hgap_no hp
  have h_congr :
      (∫ r in a..b, Fp r) =
        ∫ r in a..b, canonicalIntegrand γ form r := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_uIoc_iff]
    constructor
    · filter_upwards
        [Ioo_ae_eq_Ioc (a := a) (b := b) (μ := MeasureTheory.volume)]
        with r hr_eq hr
      have hro : r ∈ Set.Ioo a b := by
        change Set.Ioo a b r
        rw [hr_eq]
        exact hr
      have hdp : DifferentiableWithinAt ℝ
          (fun u : ℝ => (extChartAt 𝓘(ℂ) p) (γ.extend u))
          (Set.Ioo a b) r :=
        have hrst : r ∈ Set.Ioo s t := hgap hro
        have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := by
          have hs01 := γ.partition_subset hs
          have ht01 := γ.partition_subset ht
          exact ⟨hs01.1.trans_lt hrst.1, hrst.2.trans_le ht01.2⟩
        have hr_notmem : r ∉ (γ.partition : Set ℝ) := by
          intro hrmem
          have hrmem' : r ∈ γ.partition := by
            simpa using hrmem
          exact (hgap_no r hrmem') hrst
        arc_chart_differentiableWithinAt γ p hr01 hr_notmem
          (hp r hro) (Set.Ioo a b)
      have hcenter := integrand_center_independent form γ p (γ.extend r)
        a b r (hp r hro) (mem_extChartAt_source (I := 𝓘(ℂ)) (γ.extend r))
        hdp hro
      simpa [Fp, canonicalIntegrand, derivWithin_of_isOpen isOpen_Ioo hro]
        using hcenter
    · filter_upwards with r hr
      have h_empty : Set.Ioc b a = (∅ : Set ℝ) :=
        Set.Ioc_eq_empty (not_lt_of_ge hab)
      rw [h_empty] at hr
      exact False.elim hr
  exact h_deriv.trans h_congr

private lemma pathIntegralOverGoodPartition_eq_canonicalIntegrand
    (γ : AnalyticArc X) (P : GoodPartition γ)
    (form : HolomorphicOneForm X)
    (hint : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume 0 1) :
    pathIntegralOverPartition γ P.toChartSubordinatePartition form =
      ∫ r in 0..1, canonicalIntegrand γ form r := by
  let Q : ChartSubordinatePartition γ := P.toChartSubordinatePartition
  have hcells : ∀ i : Fin Q.n,
      pathIntegralOnChartSeg γ (Q.p i) (Q.t i.castSucc) (Q.t i.succ) form =
        ∫ r in (Q.t i.castSucc)..(Q.t i.succ),
          canonicalIntegrand γ form r := by
    intro i
    rcases P.gap i with ⟨s, hs, t, ht, hst, hgap, hgap_no⟩
    have hab : Q.t i.castSucc ≤ Q.t i.succ :=
      Q.t_mono (Fin.castSucc_le_succ i)
    have hp : ∀ r ∈ Set.Ioo (Q.t i.castSucc) (Q.t i.succ),
        γ.extend r ∈ (extChartAt 𝓘(ℂ) (Q.p i)).source := by
      intro r hr
      have hrcc : r ∈ Set.Icc (Q.t i.castSucc) (Q.t i.succ) :=
        ⟨le_of_lt hr.1, le_of_lt hr.2⟩
      simpa [extChartAt_source] using Q.mem_source i r hrcc
    exact pathIntegralOnChartSeg_eq_canonicalIntegrand γ (Q.p i)
      (Q.t i.castSucc) (Q.t i.succ) form hab hs ht hst hgap hgap_no hp
  have hsum_cells :
      (∑ i : Fin Q.n,
          ∫ r in (Q.t i.castSucc)..(Q.t i.succ),
            canonicalIntegrand γ form r) =
        ∫ r in 0..1, canonicalIntegrand γ form r := by
    let a : ℕ → ℝ :=
      fun k => if h : k < Q.n + 1 then Q.t ⟨k, h⟩ else 0
    have hcell_hint : ∀ i : Fin Q.n,
        IntervalIntegrable (canonicalIntegrand γ form) MeasureTheory.volume
          (Q.t i.castSucc) (Q.t i.succ) :=
      chartSubordinatePartition_cell_intervalIntegrable γ Q form hint
    have hsum :
        ∑ k ∈ Finset.range Q.n,
            ∫ r in (a k)..(a (k + 1)), canonicalIntegrand γ form r =
          ∫ r in (a 0)..(a Q.n), canonicalIntegrand γ form r := by
      refine intervalIntegral.sum_integral_adjacent_intervals
        (a := a) (n := Q.n) ?_
      intro k hk
      have hk0 : k ≤ Q.n := Nat.le_of_lt hk
      have hk1 : k < Q.n := hk
      simpa [a, hk0, hk1] using hcell_hint ⟨k, hk⟩
    have ha0 : a 0 = 0 := by
      simp [a, Q.t_zero]
    have haN : a Q.n = 1 := by
      have hfin :
          (⟨Q.n, Nat.lt_succ_self Q.n⟩ : Fin (Q.n + 1)) =
            Fin.last Q.n := by
        ext
        simp [Fin.last]
      calc
        a Q.n = Q.t ⟨Q.n, Nat.lt_succ_self Q.n⟩ := by simp [a]
        _ = Q.t (Fin.last Q.n) := by rw [hfin]
        _ = 1 := Q.t_last
    calc
      (∑ i : Fin Q.n,
          ∫ r in (Q.t i.castSucc)..(Q.t i.succ),
            canonicalIntegrand γ form r) =
          ∑ k ∈ Finset.range Q.n,
            ∫ r in (a k)..(a (k + 1)), canonicalIntegrand γ form r := by
        rw [Finset.sum_fin_eq_sum_range]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hklt : k < Q.n := by simpa using hk
        have hk0 : k ≤ Q.n := Nat.le_of_lt hklt
        have hk1 : k < Q.n := hklt
        simp [a, hk0, hk1]
      _ = ∫ r in 0..1, canonicalIntegrand γ form r := by
        simpa [ha0, haN] using hsum
  unfold pathIntegralOverPartition
  calc
    (∑ i : Fin Q.n,
        pathIntegralOnChartSeg γ (Q.p i)
          (Q.t i.castSucc) (Q.t i.succ) form) =
        ∑ i : Fin Q.n,
          ∫ r in (Q.t i.castSucc)..(Q.t i.succ),
            canonicalIntegrand γ form r := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hcells i
    _ = ∫ r in 0..1, canonicalIntegrand γ form r := hsum_cells

/-- The fixed-partition integral over a good partition is independent of the
chosen good partition.  The only analytic input retained as a hypothesis is
interval integrability of the moving-center ordinary-derivative integrand on
`[0, 1]`. -/
theorem pathIntegralOverPartition_good_indep (γ : AnalyticArc X)
    (P₁ P₂ : GoodPartition γ) (form : HolomorphicOneForm X)
    (hint : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume 0 1) :
    pathIntegralOverPartition γ P₁.toChartSubordinatePartition form =
    pathIntegralOverPartition γ P₂.toChartSubordinatePartition form := by
  rw [pathIntegralOverGoodPartition_eq_canonicalIntegrand γ P₁ form hint,
    pathIntegralOverGoodPartition_eq_canonicalIntegrand γ P₂ form hint]

/-- The fixed-partition integral over any good partition agrees with the
raw moving-chart integral. -/
theorem pathIntegralOverGoodPartition_eq_canonicalIntegrand_integral
    (γ : AnalyticArc X) (P : GoodPartition γ)
    (form : HolomorphicOneForm X)
    (hint : IntervalIntegrable (canonicalIntegrand γ form)
      MeasureTheory.volume 0 1) :
    pathIntegralOverPartition γ P.toChartSubordinatePartition form =
      ∫ r in (0 : ℝ)..1, canonicalIntegrand γ form r :=
  pathIntegralOverGoodPartition_eq_canonicalIntegrand γ P form hint

end Jacobians.RiemannSurface
