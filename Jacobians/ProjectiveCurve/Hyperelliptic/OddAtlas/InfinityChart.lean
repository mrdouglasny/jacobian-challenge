/-
# Phase OA2 — Chart at infinity on `HyperellipticOdd H h`

In the odd-degree case `deg f = 2g + 1`, the smooth model
`HyperellipticOdd H h := OnePoint (HyperellipticAffine H)` has a single
point at infinity, which is also a **branch point** of the
hyperelliptic projection `(x, y) ↦ x`.

The standard chart at infinity uses the uniformizer `t := y / x^{g+1}`.
Near `t = 0`, on the curve `y² = f(x)` with `deg f = 2g + 1`:
* `x = 1 / (lc(f) · t²) · (1 + O(t))` (where `lc(f)` is the leading
  coefficient);
* `y = 1 / (lc(f)^{(2g+1)/2} · t^{2g+1}) · (1 + O(t))`.

So the inverse `t ↦ (x(t), y(t))` is an analytic bijection from a
punctured disk `0 < |t| < ε` onto a punctured neighborhood of `∞`,
extending continuously by `t = 0 ↦ OnePoint.infty`.

## Mathlib API

* `OnePoint.openEmbedding_coe : OpenEmbedding ((↑) : X → OnePoint X)` —
  affine charts pull back to `OnePoint X` for points coming from `X`.
* `OnePoint.continuous_iff_continuousAt_infty` — for verifying
  continuity at `∞`.
* No general "chart at the added point" lemma in Mathlib; we construct
  the `PartialHomeomorph` by hand.

See `docs/hyperelliptic-odd-atlas-plan.md` §OA2.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.InfinityInverse
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Monoid
import Jacobians.GeneralResults.InverseFunctionTheorem
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff Topology
open OnePoint Polynomial Complex Filter Set

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

lemma continuousOn_S_sq (H : HyperellipticData) :
    ContinuousOn (fun w => InfinityInverse.S H (w ^ 2))
      (InfinityInverse.tLocalHomeomorph H).source := by
  intro w hw
  by_cases hw0 : w = 0
  · rw [hw0]
    have h_S_cont : ContinuousAt (InfinityInverse.S H) 0 :=
      (InfinityInverse.S_analyticAt H).continuousAt
    have h_zero_pow : (0 : ℂ) ^ 2 = 0 := by simp
    have h_S_cont' : ContinuousAt (InfinityInverse.S H) ((fun w : ℂ => w ^ 2) 0) := by
      rwa [show (fun w : ℂ => w ^ 2) 0 = (0 : ℂ) ^ 2 by rfl, h_zero_pow]
    have h_sq_cont : ContinuousAt (fun w : ℂ => w ^ 2) 0 := by fun_prop
    have h_comp : ContinuousAt (InfinityInverse.S H ∘ (fun w : ℂ => w ^ 2)) 0 :=
      ContinuousAt.comp h_S_cont' h_sq_cont
    exact h_comp.continuousWithinAt
  · have h_t_cont : ContinuousWithinAt (InfinityInverse.t H)
        (InfinityInverse.tLocalHomeomorph H).source w := by
      have h_chart_cont := (InfinityInverse.tLocalHomeomorph H).continuousOn w hw
      have h_coe := InfinityInverse.tLocalHomeomorph_coe H
      have h_app : (↑(InfinityInverse.tLocalHomeomorph H) : ℂ → ℂ) =
        (InfinityInverse.tLocalHomeomorph H) := rfl
      rw [h_app] at h_coe
      rw [h_coe] at h_chart_cont
      exact h_chart_cont
    have h_w_cont : ContinuousWithinAt (fun w => w) (InfinityInverse.tLocalHomeomorph H).source w :=
      continuous_id.continuousWithinAt
    have h_div := ContinuousWithinAt.div h_t_cont h_w_cont hw0
    have h_inter : (InfinityInverse.tLocalHomeomorph H).source ∩ {0}ᶜ ∈ 𝓝 w := by
      apply Filter.inter_mem
      · exact (InfinityInverse.tLocalHomeomorph H).open_source.mem_nhds hw
      · exact isOpen_ne.mem_nhds hw0
    have h_eq : InfinityInverse.t H / (fun w => w) =ᶠ[(𝓝[
        (InfinityInverse.tLocalHomeomorph H).source ] w)]
          (fun w => InfinityInverse.S H (w ^ 2)) := by
      refine Filter.eventually_of_mem
        (U := (InfinityInverse.tLocalHomeomorph H).source ∩ {0}ᶜ) ?_ ?_
      · exact mem_nhdsWithin_of_mem_nhds h_inter
      · intro x hx
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff] at hx
        have h_t_eval : InfinityInverse.t H x = x * InfinityInverse.S H (x ^ 2) := rfl
        change InfinityInverse.t H x / x = InfinityInverse.S H (x ^ 2)
        rw [h_t_eval]
        rw [mul_div_cancel_left₀ _ hx.2]
    rw [h_eq.congr_continuousWithinAt_of_mem hw] at h_div
    exact h_div

def V (H : HyperellipticData) : Set (HyperellipticAffine H) :=
  { q : HyperellipticAffine H | q.val.1 ≠ 0 ∧ q.val.2 ≠ 0 ∧
    (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹) ∈
      (InfinityInverse.tLocalHomeomorph H).source }

-- Topological axioms to bridge the analytic gaps

def D_S (H : HyperellipticData) : Set ℂ :=
  { z : ℂ | H.f.leadingCoeff⁻¹ * H.f.reverse.eval z ∈ InfinityInverse.slitPlane }

lemma isOpen_D_S (H : HyperellipticData) : IsOpen (D_S H) := by
  have h_cont : Continuous (fun z : ℂ => H.f.leadingCoeff⁻¹ * H.f.reverse.eval z) :=
    continuous_const.mul H.f.reverse.continuous
  exact IsOpen.preimage h_cont InfinityInverse.isOpen_slitPlane

lemma S_analyticAt_of_mem_D_S (H : HyperellipticData) {z : ℂ} (hz : z ∈ D_S H) :
    AnalyticAt ℂ (InfinityInverse.S H) z := by
  have hz' : H.f.leadingCoeff⁻¹ * H.f.reverse.eval z ∈ Complex.slitPlane := hz
  have h_rev : AnalyticAt ℂ (fun z => H.f.reverse.eval z) z :=
    H.f.reverse.differentiable.analyticAt z
  have h_scaled : AnalyticAt ℂ (fun z => H.f.leadingCoeff⁻¹ * H.f.reverse.eval z) z :=
    analyticAt_const.mul h_rev
  have h_two : AnalyticAt ℂ (fun _ : ℂ => (2⁻¹ : ℂ)) z :=
    analyticAt_const
  have h_pow : AnalyticAt ℂ (fun z =>
      (H.f.leadingCoeff⁻¹ * H.f.reverse.eval z) ^ (2⁻¹ : ℂ)) z := by
    exact AnalyticAt.cpow h_scaled h_two hz'
  exact analyticAt_const.mul h_pow

lemma S_ne_zero_of_mem_D_S (H : HyperellipticData) {z : ℂ} (hz : z ∈ D_S H) :
    InfinityInverse.S H z ≠ 0 := by
  intro hc
  have hc' : InfinityInverse.S H z = 0 := hc
  unfold InfinityInverse.S at hc'
  have h_lc_ne := InfinityInverse.leadingCoeff_ne_zero H
  have h_sqrt : Complex.sqrt H.f.leadingCoeff ≠ 0 := InfinityInverse.sqrt_ne_zero_of_ne_zero h_lc_ne
  rw [smul_eq_mul, smul_eq_mul] at hc'
  have h_pow_zero : (H.f.leadingCoeff⁻¹ * H.f.reverse.eval z) ^ (2⁻¹ : ℂ) = 0 := by
    exact mul_eq_zero.mp hc' |>.resolve_left h_sqrt
  rw [Complex.cpow_eq_zero_iff] at h_pow_zero
  have h_prod_zero := h_pow_zero.1
  have hz' : H.f.leadingCoeff⁻¹ * H.f.reverse.eval z ∈ InfinityInverse.slitPlane := hz
  rw [h_prod_zero] at hz'
  change 0 < (0 : ℂ).re ∨ (0 : ℂ).im ≠ 0 at hz'
  simp at hz'

lemma isOpen_Ω (H : HyperellipticData) :
    IsOpen { q : HyperellipticAffine H | q.val.1 ≠ 0 ∧ q.val.1⁻¹ ∈ D_S H } := by
  have h_open1 : IsOpen { q : HyperellipticAffine H | q.val.1 ≠ 0 } :=
    isOpen_ne_fun continuous_subtype_val.fst continuous_const
  have h_cont : ContinuousOn (fun q : HyperellipticAffine H => q.val.1⁻¹) { q | q.val.1 ≠ 0 } := by
    have h_fst : ContinuousOn (fun q : HyperellipticAffine H => q.val.1) { q | q.val.1 ≠ 0 } :=
      continuous_subtype_val.fst.continuousOn
    exact ContinuousOn.inv₀ h_fst (fun q hq => hq)
  have h_open2 : IsOpen (D_S H) := isOpen_D_S H
  exact h_cont.isOpen_inter_preimage h_open1 h_open2

lemma isBounded_image_val_of_bounded_components (H : HyperellipticData)
    {s : Set (HyperellipticAffine H)}
    (h1 : ∃ R1 : ℝ, ∀ q ∈ s, ‖q.val.1‖ ≤ R1)
    (h2 : ∃ R2 : ℝ, ∀ q ∈ s, ‖q.val.2‖ ≤ R2) :
    Bornology.IsBounded (Subtype.val '' s) := by
  rcases h1 with ⟨R1, hR1⟩
  rcases h2 with ⟨R2, hR2⟩
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ × ℂ)]
  use max R1 R2
  intro p hp
  rcases hp with ⟨q, hq_mem, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Prod.norm_def]
  have hq1_le : ‖q.val.1‖ ≤ R1 := hR1 q hq_mem
  have hq2_le : ‖q.val.2‖ ≤ R2 := hR2 q hq_mem
  exact max_le_max hq1_le hq2_le

lemma isCompact_of_isClosed_bounded_fst (H : HyperellipticData)
    {s : Set (HyperellipticAffine H)} (hs : IsClosed s)
    (h_bound : ∃ R : ℝ, ∀ q ∈ s, ‖q.val.1‖ ≤ R) :
    IsCompact s := by
  change @IsCompact { p : ℂ × ℂ // p.2 ^ 2 = H.f.eval p.1 } instTopologicalSpaceSubtype s
  rw [Topology.IsEmbedding.isCompact_iff Topology.IsEmbedding.subtypeVal]
  have h_closed_emb : Topology.IsClosedEmbedding (Subtype.val : HyperellipticAffine H → ℂ × ℂ) :=
    IsClosed.isClosedEmbedding_subtypeVal (HyperellipticAffine.isClosed_carrier H)
  have h_closed_img : IsClosed (Subtype.val '' s) :=
    h_closed_emb.isClosedMap s hs
  refine Metric.isCompact_of_isClosed_isBounded h_closed_img ?_
  rcases h_bound with ⟨R1, hR1⟩
  have h_comp_ball : IsCompact (Metric.closedBall (0 : ℂ) R1) :=
    ProperSpace.isCompact_closedBall 0 R1
  have h_cont_f : Continuous (fun x : ℂ => ‖H.f.eval x‖) :=
    continuous_norm.comp (Polynomial.continuous H.f)
  have h_comp_img : IsCompact ((fun x : ℂ => ‖H.f.eval x‖) '' Metric.closedBall (0 : ℂ) R1) :=
    IsCompact.image h_comp_ball h_cont_f
  have h_bounded_img : Bornology.IsBounded
    ((fun x : ℂ => ‖H.f.eval x‖) '' Metric.closedBall (0 : ℂ) R1) :=
    h_comp_img.isBounded
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ)] at h_bounded_img
  rcases h_bounded_img with ⟨R2, hR2⟩
  have h_bound_y : ∀ q ∈ s, ‖q.val.2‖ ≤ Real.sqrt R2 := by
    intro q hq
    have hq1_in : q.val.1 ∈ Metric.closedBall (0 : ℂ) R1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hR1 q hq
    have h_eval_in : ‖H.f.eval q.val.1‖ ∈
      (fun x : ℂ => ‖H.f.eval x‖) '' Metric.closedBall (0 : ℂ) R1 :=
      ⟨q.val.1, hq1_in, rfl⟩
    have h_le := hR2 h_eval_in
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)] at h_le
    have h_y_sq : q.val.2 ^ 2 = H.f.eval q.val.1 := q.property
    have h_abs_sq : ‖q.val.2 ^ 2‖ = ‖H.f.eval q.val.1‖ := by
      rw [h_y_sq]
    rw [norm_pow] at h_abs_sq
    have h_le_R2 : ‖q.val.2‖ ^ 2 ≤ R2 := by
      rw [h_abs_sq]
      exact h_le
    have h_R2_nonneg : 0 ≤ R2 := (sq_nonneg ‖q.val.2‖).trans h_le_R2
    exact Real.le_sqrt_of_sq_le h_le_R2
  exact isBounded_image_val_of_bounded_components H ⟨R1, hR1⟩ ⟨Real.sqrt R2, h_bound_y⟩

lemma mem_source_imp_sq_mem_D_S {w : ℂ} (hw : w ∈ (InfinityInverse.tLocalHomeomorph H).source) :
    w ^ 2 ∈ D_S H :=
  hw.2

lemma w_q_mem_source_imp_x_inv_mem_D_S (h : Odd H.f.natDegree) (q : HyperellipticAffine H)
    (hq1 : q.val.1 ≠ 0) (hq2 : q.val.2 ≠ 0)
    (hw : (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹) ∈
      (InfinityInverse.tLocalHomeomorph H).source) :
    q.val.1⁻¹ ∈ D_S H := by
  have h_sq := mem_source_imp_sq_mem_D_S hw
  have h_eq := InfinityInverse.w_q_sq_eq_inv h q hq1 hq2
  rwa [h_eq] at h_sq

def Ω (H : HyperellipticData) : Set (HyperellipticAffine H) :=
  { q : HyperellipticAffine H | q.val.1 ≠ 0 ∧ q.val.1⁻¹ ∈ D_S H }

noncomputable def f_w (H : HyperellipticData) (q : HyperellipticAffine H) : ℂ :=
  q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹

lemma continuousOn_x_inv (H : HyperellipticData) :
    ContinuousOn (fun q : HyperellipticAffine H => q.val.1⁻¹) (Ω H) := by
  have h_cont : ContinuousOn (fun q : HyperellipticAffine H => q.val.1⁻¹) { q | q.val.1 ≠ 0 } := by
    have h_fst : ContinuousOn (fun q : HyperellipticAffine H => q.val.1) { q | q.val.1 ≠ 0 } :=
      continuous_subtype_val.fst.continuousOn
    exact ContinuousOn.inv₀ h_fst (fun q hq => hq)
  refine h_cont.mono ?_
  intro q hq
  exact hq.1

lemma continuousOn_S_inv (H : HyperellipticData) :
    ContinuousOn (fun z : ℂ => (InfinityInverse.S H z)⁻¹) (D_S H) := by
  have h_cont : ContinuousOn (InfinityInverse.S H) (D_S H) := by
    intro z hz
    exact (S_analyticAt_of_mem_D_S H hz).continuousAt.continuousWithinAt
  have h_ne : ∀ z ∈ D_S H, InfinityInverse.S H z ≠ 0 := by
    intro z hz
    exact S_ne_zero_of_mem_D_S H hz
  exact h_cont.inv₀ h_ne

lemma continuousOn_S_inv_x_inv (H : HyperellipticData) :
    ContinuousOn (fun q : HyperellipticAffine H => (InfinityInverse.S H q.val.1⁻¹)⁻¹) (Ω H) := by
  have h1 : ContinuousOn (fun q : HyperellipticAffine H => q.val.1⁻¹) (Ω H) :=
    continuousOn_x_inv H
  have h2 : ContinuousOn (fun z : ℂ => (InfinityInverse.S H z)⁻¹) (D_S H) :=
    continuousOn_S_inv H
  have h_maps : Set.MapsTo (fun q : HyperellipticAffine H => q.val.1⁻¹) (Ω H) (D_S H) := by
    intro q hq
    exact hq.2
  exact h2.comp h1 h_maps

lemma continuousOn_f_w (H : HyperellipticData) :
    ContinuousOn (f_w H) (Ω H) := by
  have h_y : ContinuousOn (fun q : HyperellipticAffine H => q.val.2) (Ω H) :=
    continuous_subtype_val.snd.continuousOn.mono (Set.subset_univ _)
  have h_x_inv : ContinuousOn (fun q : HyperellipticAffine H => q.val.1⁻¹) (Ω H) :=
    continuousOn_x_inv H
  have h_x_inv_pow : ContinuousOn
    (fun q : HyperellipticAffine H => q.val.1⁻¹ ^ (H.genus + 1)) (Ω H) :=
    h_x_inv.pow (H.genus + 1)
  have h_y_mul_pow : ContinuousOn
    (fun q : HyperellipticAffine H => q.val.2 * q.val.1⁻¹ ^ (H.genus + 1)) (Ω H) :=
    h_y.mul h_x_inv_pow
  have h_S_inv : ContinuousOn
    (fun q : HyperellipticAffine H => (InfinityInverse.S H q.val.1⁻¹)⁻¹) (Ω H) :=
    continuousOn_S_inv_x_inv H
  exact h_y_mul_pow.mul h_S_inv

lemma V_eq_inter (h : Odd H.f.natDegree) :
    V H = { q | q.val.2 ≠ 0 } ∩ (f_w H ⁻¹' (InfinityInverse.tLocalHomeomorph H).source ∩ Ω H) := by
  ext q
  constructor
  · intro hq
    have hq1 := hq.1
    have hq2 := hq.2.1
    have hqw := hq.2.2
    have h_mem : q.val.1⁻¹ ∈ D_S H :=
      w_q_mem_source_imp_x_inv_mem_D_S h q hq1 hq2 hqw
    refine ⟨hq2, ⟨hqw, ⟨hq1, h_mem⟩⟩⟩
  · rintro ⟨hq2, ⟨hqw, ⟨hq1, h_mem⟩⟩⟩
    exact ⟨hq1, hq2, hqw⟩

theorem V_open (H : HyperellipticData) (h_odd : Odd H.f.natDegree) : IsOpen (V H) := by
  rw [V_eq_inter h_odd]
  have h_open_y : IsOpen { q : HyperellipticAffine H | q.val.2 ≠ 0 } :=
    isOpen_ne_fun continuous_subtype_val.snd continuous_const
  have h_open_Ω : IsOpen (Ω H) := isOpen_Ω H
  have h_cont : ContinuousOn (f_w H) (Ω H) := continuousOn_f_w H
  have h_open_source : IsOpen (InfinityInverse.tLocalHomeomorph H).source :=
    (InfinityInverse.tLocalHomeomorph H).open_source
  have h_open_pre : IsOpen (f_w H ⁻¹' (InfinityInverse.tLocalHomeomorph H).source ∩ Ω H) := by
    rw [Set.inter_comm]
    exact h_cont.isOpen_inter_preimage h_open_Ω h_open_source
  exact h_open_y.inter h_open_pre

lemma mem_V_compl_iff (q : HyperellipticAffine H) :
    q ∈ (V H)ᶜ ↔
      q.val.1 = 0 ∨ q.val.2 = 0 ∨
      (q.val.1 ≠ 0 ∧ q.val.2 ≠ 0 ∧ f_w H q ∉ (InfinityInverse.tLocalHomeomorph H).source) := by
  constructor
  · intro hq
    by_cases h1 : q.val.1 = 0
    · left; exact h1
    · by_cases h2 : q.val.2 = 0
      · right; left; exact h2
      · right; right
        refine ⟨h1, h2, ?_⟩
        intro hc
        exact hq ⟨h1, h2, hc⟩
  · rintro (h1 | h2 | ⟨h1, h2, h3⟩)
    · intro hc
      exact hc.1 h1
    · intro hc
      exact hc.2.1 h2
    · intro hc
      exact h3 hc.2.2

lemma bounded_roots (H : HyperellipticData) :
    ∃ R : ℝ, ∀ z ∈ H.f.roots.toFinset, ‖z‖ ≤ R := by
  set s := H.f.roots.toFinset.image norm
  by_cases hs : s.Nonempty
  · obtain ⟨M, hM⟩ := s.max_of_nonempty hs
    use M
    intro z hz
    have h_mem : ‖z‖ ∈ s := Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have h_le := Finset.le_max h_mem
    rw [hM] at h_le
    exact WithBot.coe_le_coe.mp h_le
  · use 0
    intro z hz
    exfalso
    have : s.Nonempty := ⟨‖z‖, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    exact hs this

lemma mem_roots_of_eval_zero {z : ℂ} (hz : H.f.eval z = 0) : z ∈ H.f.roots.toFinset := by
  have h_ne : H.f ≠ 0 := by
    intro hc
    have := InfinityInverse.leadingCoeff_ne_zero H
    rw [hc, Polynomial.leadingCoeff_zero] at this
    exact this rfl
  rw [Multiset.mem_toFinset, Polynomial.mem_roots h_ne]
  exact hz

lemma ball_subset_source (H : HyperellipticData) :
    ∃ ε > 0, Metric.ball 0 ε ⊆ (InfinityInverse.tLocalHomeomorph H).source := by
  have h_open : IsOpen (InfinityInverse.tLocalHomeomorph H).source :=
    (InfinityInverse.tLocalHomeomorph H).open_source
  have h_zero : 0 ∈ (InfinityInverse.tLocalHomeomorph H).source :=
    InfinityInverse.tLocalHomeomorph_source H
  rw [Metric.isOpen_iff] at h_open
  rcases h_open 0 h_zero with ⟨ε, hε, h_sub⟩
  exact ⟨ε, hε, h_sub⟩

lemma norm_x_le_of_w_not_mem_source (h : Odd H.f.natDegree) (q : HyperellipticAffine H)
    (hq1 : q.val.1 ≠ 0) (hq2 : q.val.2 ≠ 0)
    {ε : ℝ} (hε : ε > 0) (h_sub : Metric.ball 0 ε ⊆ (InfinityInverse.tLocalHomeomorph H).source)
    (hw : f_w H q ∉ (InfinityInverse.tLocalHomeomorph H).source) :
    ‖q.val.1‖ ≤ ε⁻¹ ^ 2 := by
  have h_not_ball : f_w H q ∉ Metric.ball (0 : ℂ) ε := by
    intro hc
    exact hw (h_sub hc)
  rw [Metric.mem_ball, dist_zero_right] at h_not_ball
  have h_ge : ε ≤ ‖f_w H q‖ := not_lt.mp h_not_ball
  have h_sq := InfinityInverse.w_q_sq_eq_inv h q hq1 hq2
  have h_eq : q.val.1 = (f_w H q)⁻¹ ^ 2 := by
    unfold f_w
    rw [inv_pow]
    rw [h_sq]
    rw [inv_inv]
  rw [h_eq]
  rw [norm_pow, norm_inv]
  have h_norm_ge : ε ^ 2 ≤ ‖f_w H q‖ ^ 2 := by
    nlinarith
  have h_eps_sq_pos : 0 < ε ^ 2 := pow_pos hε 2
  have h_fw_sq_pos : 0 < ‖f_w H q‖ ^ 2 := lt_of_lt_of_le h_eps_sq_pos h_norm_ge
  have h_inv_le : (‖f_w H q‖ ^ 2)⁻¹ ≤ (ε ^ 2)⁻¹ := by
    exact (inv_le_inv₀ h_fw_sq_pos h_eps_sq_pos).mpr h_norm_ge
  rw [inv_pow, inv_pow]
  exact h_inv_le

theorem V_compl_compact (H : HyperellipticData) (h_odd : Odd H.f.natDegree) : IsCompact (V H)ᶜ := by
  refine isCompact_of_isClosed_bounded_fst H (V_open H h_odd).isClosed_compl ?_
  obtain ⟨R_roots, h_roots⟩ := bounded_roots H
  obtain ⟨ε, hε, h_ball⟩ := ball_subset_source H
  use max 0 (max R_roots (ε⁻¹ ^ 2))
  intro q hq
  rw [mem_V_compl_iff] at hq
  rcases hq with (hq1 | hq2 | ⟨hq1, hq2, hqw⟩)
  · rw [hq1, norm_zero]
    exact le_max_left 0 _
  · have h_eval : H.f.eval q.val.1 = 0 := by
      have h_prop := q.property
      rw [hq2, zero_pow (by decide)] at h_prop
      exact h_prop.symm
    have h_mem := mem_roots_of_eval_zero h_eval
    have h_le := h_roots q.val.1 h_mem
    refine h_le.trans ?_
    exact le_max_left R_roots (ε⁻¹ ^ 2) |>.trans (le_max_right 0 _)
  · have h_le := norm_x_le_of_w_not_mem_source h_odd q hq1 hq2 hε h_ball hqw
    refine h_le.trans ?_
    exact le_max_right R_roots (ε⁻¹ ^ 2) |>.trans (le_max_right 0 _)

noncomputable def infinityInverseMap (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ℂ → HyperellipticAffine H :=
  InfinityInverse.infinityInverseMap H h

noncomputable def infinityForward (H : HyperellipticData) (h : Odd H.f.natDegree)
    (p : HyperellipticOdd H h) : ℂ :=
  p.elim 0 (fun q => q.val.2 / q.val.1 ^ (H.genus + 1))

noncomputable def infinityBackward (H : HyperellipticData) (h : Odd H.f.natDegree)
    (t : ℂ) : HyperellipticOdd H h :=
  if t = 0 then ∞ else coe (InfinityInverse.infinityInverseMap H h t)

lemma infinityInverseMap_val_of_ne_zero (z : ℂ)
    (hz : z ∈ (InfinityInverse.tLocalHomeomorph H).target) (hz0 : z ≠ 0) :
    InfinityInverse.infinityInverseMap H h z =
      let W := (InfinityInverse.tLocalHomeomorph H).symm z
      let x := W⁻¹ ^ 2
      let y := z * x ^ (H.genus + 1)
      ⟨(x, y), InfinityInverse.y_sq_eq_eval_x h z hz hz0⟩ := by
  unfold InfinityInverse.infinityInverseMap
  have hz_cond : z ∈ (InfinityInverse.tLocalHomeomorph H).target ∧ z ≠ 0 := ⟨hz, hz0⟩
  rw [dif_pos hz_cond]

lemma infinityForward_infinityInverseMap_eq_self (z : ℂ)
    (hz : z ∈ (InfinityInverse.tLocalHomeomorph H).target) (hz0 : z ≠ 0) :
    infinityForward H h (coe (InfinityInverse.infinityInverseMap H h z)) = z := by
  rw [infinityInverseMap_val_of_ne_zero z hz hz0]
  dsimp [infinityForward]
  have hw : (InfinityInverse.tLocalHomeomorph H).symm z ≠ 0 := by
    intro hw0
    have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H hz
    rw [hw0] at h_tz
    have h_zero : InfinityInverse.t H 0 = 0 := by
      unfold InfinityInverse.t
      simp
    rw [h_zero] at h_tz
    exact hz0 h_tz.symm
  have hx : ((InfinityInverse.tLocalHomeomorph H).symm z)⁻¹ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (inv_ne_zero hw)
  have hpow : (((InfinityInverse.tLocalHomeomorph H).symm z)⁻¹ ^ 2) ^ (H.genus + 1) ≠ 0 :=
    pow_ne_zero _ hx
  exact mul_div_cancel_right₀ z hpow

lemma w_infinityInverseMap (t : ℂ) (ht : t ∈ (InfinityInverse.tLocalHomeomorph H).target)
    (ht0 : t ≠ 0) :
    let q := InfinityInverse.infinityInverseMap H h t
    q.val.1 ≠ 0 ∧ q.val.2 ≠ 0 ∧
    q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹ =
      (InfinityInverse.tLocalHomeomorph H).symm t := by
  intro q
  have hq_eq : q = InfinityInverse.infinityInverseMap H h t := rfl
  rw [infinityInverseMap_val_of_ne_zero t ht ht0] at hq_eq
  rw [hq_eq]
  dsimp
  have hw_nz : (InfinityInverse.tLocalHomeomorph H).symm t ≠ 0 := by
    intro hw0
    have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H ht
    rw [hw0] at h_tz
    have h_zero : InfinityInverse.t H 0 = 0 := by
      unfold InfinityInverse.t
      simp
    rw [h_zero] at h_tz
    exact ht0 h_tz.symm
  have hx_nz : ((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (inv_ne_zero hw_nz)
  have hy_nz : t * (((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2) ^ (H.genus + 1) ≠ 0 := by
    refine mul_ne_zero ht0 (pow_ne_zero _ hx_nz)
  refine ⟨hx_nz, hy_nz, ?_⟩
  have h_x_inv : (((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2)⁻¹ =
    ((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2 := by
    rw [inv_pow, inv_inv]
  rw [h_x_inv]
  have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H ht
  nth_rw 1 [← h_tz]
  unfold InfinityInverse.t
  have h_S_nz : InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) ≠ 0 := by
    intro hc
    have ht_eq : t = ((InfinityInverse.tLocalHomeomorph H).symm t) *
      InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) := h_tz.symm
    have ht0' : t = 0 := by
      rw [ht_eq, hc, mul_zero]
    exact ht0 ht0'
  have h_S_inv : InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) *
    (InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2))⁻¹ = 1 :=
      mul_inv_cancel₀ h_S_nz
  have h_W_pow : (((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2) ^ (H.genus + 1) *
    (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) ^ (H.genus + 1) = 1 := by
    rw [← mul_pow]
    have : ((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2 *
      ((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hw_nz, one_pow]
    rw [this, one_pow]
  calc ((InfinityInverse.tLocalHomeomorph H).symm t) *
      InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) *
      (((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2) ^ (H.genus + 1) *
      (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) ^ (H.genus + 1) *
      (InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2))⁻¹
    _ = ((InfinityInverse.tLocalHomeomorph H).symm t) *
      InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) *
      ((((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2) ^ (H.genus + 1) *
      (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) ^ (H.genus + 1)) *
      (InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2))⁻¹ := by ring
    _ = ((InfinityInverse.tLocalHomeomorph H).symm t) *
      InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) * 1 *
      (InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2))⁻¹ := by rw [h_W_pow]
    _ = ((InfinityInverse.tLocalHomeomorph H).symm t) *
      (InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2) *
      (InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm t) ^ 2))⁻¹) := by ring
    _ = ((InfinityInverse.tLocalHomeomorph H).symm t) * 1 := by rw [h_S_inv]
    _ = ((InfinityInverse.tLocalHomeomorph H).symm t) := mul_one _

lemma t_w_q (h : Odd H.f.natDegree) (q : HyperellipticAffine H)
    (hq1 : q.val.1 ≠ 0) (hq2 : q.val.2 ≠ 0) :
    let w_q := q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹
    InfinityInverse.t H w_q = q.val.2 / q.val.1 ^ (H.genus + 1) := by
  intro w_q
  unfold InfinityInverse.t
  have h_rev := reverse_eval_inv_eq (H := H) q.val.1 hq1
  have h_S_sq := InfinityInverse.S_sq_eq_eval_rev H q.val.1⁻¹
  have h_y_sq : q.val.2 ^ 2 = H.f.eval q.val.1 := q.property
  have h_f_eval_nz : H.f.eval q.val.1 ≠ 0 := by
    intro hc
    have hc2 : q.val.2 ^ 2 = 0 := by rw [h_y_sq, hc]
    exact hq2 (sq_eq_zero_iff.mp hc2)
  have h_rev_nz : (H.f.reverse).eval q.val.1⁻¹ ≠ 0 := by
    rw [h_rev]
    exact mul_ne_zero h_f_eval_nz (pow_ne_zero _ (inv_ne_zero hq1))
  have h_S_nz : InfinityInverse.S H q.val.1⁻¹ ≠ 0 := by
    intro hc
    have hc2 : (InfinityInverse.S H q.val.1⁻¹) ^ 2 = 0 := by rw [hc, zero_pow (by decide)]
    rw [h_S_sq] at hc2
    exact h_rev_nz hc2
  have hw_sq := InfinityInverse.w_q_sq_eq_inv h q hq1 hq2
  rw [hw_sq]
  have h_S_cancel : InfinityInverse.S H q.val.1⁻¹ * (InfinityInverse.S H q.val.1⁻¹)⁻¹ = 1 :=
    mul_inv_cancel₀ h_S_nz
  calc w_q * InfinityInverse.S H q.val.1⁻¹
    _ = q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹ *
      InfinityInverse.S H q.val.1⁻¹ := rfl
    _ = q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) *
      ((InfinityInverse.S H q.val.1⁻¹)⁻¹ * InfinityInverse.S H q.val.1⁻¹) := by ring
    _ = q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * 1 := by
      rw [mul_comm (InfinityInverse.S H q.val.1⁻¹)⁻¹, h_S_cancel]
    _ = q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) := mul_one _
    _ = q.val.2 / q.val.1 ^ (H.genus + 1) := by rw [div_eq_mul_inv, inv_pow]

lemma tendsto_norm_sq_nhdsWithin :
    Tendsto (fun w : ℂ => ‖w‖ ^ 2) (𝓝[≠] 0) (𝓝[Set.Ioi 0] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h_cont : ContinuousAt (fun w : ℂ => ‖w‖ ^ 2) 0 := by fun_prop
    have h_eq : ‖(0 : ℂ)‖ ^ 2 = 0 := by simp
    have h_tend := h_cont.tendsto
    rw [h_eq] at h_tend
    exact h_tend.mono_left nhdsWithin_le_nhds
  · refine Filter.eventually_of_mem (self_mem_nhdsWithin (a := (0 : ℂ))) ?_
    intro w hw
    have h_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    exact pow_pos h_pos 2

lemma tendsto_inv_sq_norm_zero :
    Tendsto (fun w : ℂ => (‖w‖ ^ 2)⁻¹) (𝓝[≠] 0) atTop :=
  tendsto_norm_sq_nhdsWithin.inv_tendsto_nhdsGT_zero

lemma tendsto_inv_sq_norm_zero_eq :
    Tendsto (fun w : ℂ => ‖w⁻¹ ^ 2‖) (𝓝[≠] 0) atTop := by
  have h_eq : (fun w : ℂ => ‖w⁻¹ ^ 2‖) = (fun w : ℂ => (‖w‖ ^ 2)⁻¹) := by
    ext w
    rw [norm_pow, norm_inv, inv_pow]
  rw [h_eq]
  exact tendsto_inv_sq_norm_zero

lemma tendsto_symm_nhdsWithin {H : HyperellipticData} :
    Tendsto (InfinityInverse.tLocalHomeomorph H).symm (𝓝[≠] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have h_cont : ContinuousAt (InfinityInverse.tLocalHomeomorph H).symm 0 :=
      (InfinityInverse.tLocalHomeomorph H).continuousAt_symm
        (InfinityInverse.tLocalHomeomorph_target_zero H)
    have h_zero : (InfinityInverse.tLocalHomeomorph H).symm 0 = 0 := by
      have h_linv := (InfinityInverse.tLocalHomeomorph H).left_inv
        (InfinityInverse.tLocalHomeomorph_source H)
      have h_app : (InfinityInverse.tLocalHomeomorph H) 0 = 0 :=
        InfinityInverse.tLocalHomeomorph_apply_zero H
      rwa [h_app] at h_linv
    have h_tend : Tendsto (InfinityInverse.tLocalHomeomorph H).symm (𝓝 0) (𝓝 0) := by
      have h_tend_eq := h_cont.tendsto
      rwa [h_zero] at h_tend_eq
    exact h_tend.mono_left nhdsWithin_le_nhds
  · have h_target : (InfinityInverse.tLocalHomeomorph H).target ∈ 𝓝 (0 : ℂ) :=
      (InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds
        (InfinityInverse.tLocalHomeomorph_target_zero H)
    have h_ev_target : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ (InfinityInverse.tLocalHomeomorph H).target :=
      nhdsWithin_le_nhds h_target
    have h_ev_ne : ∀ᶠ w : ℂ in 𝓝[≠] 0, w ≠ 0 := self_mem_nhdsWithin
    filter_upwards [h_ev_target, h_ev_ne]
    intro w hw_target hw_ne hc
    have h_eq : w = InfinityInverse.tLocalHomeomorph H
      ((InfinityInverse.tLocalHomeomorph H).symm w) :=
      ((InfinityInverse.tLocalHomeomorph H).right_inv hw_target).symm
    rw [hc, InfinityInverse.tLocalHomeomorph_apply_zero] at h_eq
    exact hw_ne h_eq

lemma tendsto_cocompact_of_tendsto_norm_atTop {α : Type*} {l : Filter α} {f : α → ℂ}
    (h : Tendsto (fun x => ‖f x‖) l atTop) :
    Tendsto f l (cocompact ℂ) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have h_ev := h (eventually_gt_atTop R)
  filter_upwards [h_ev]
  intro x hx h_in
  have h_ball := hR h_in
  rw [Metric.mem_closedBall, dist_zero_right] at h_ball
  exact not_lt.mpr h_ball hx

lemma tendsto_cocompact_of_fst {H : HyperellipticData} {α : Type*} {l : Filter α}
    (g : α → HyperellipticAffine H)
    (hg : Tendsto (fun t => (g t).val.1) l (cocompact ℂ)) :
    Tendsto g l (cocompact (HyperellipticAffine H)) := by
  rw [hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  have hK_x : IsCompact ((fun q : HyperellipticAffine H => q.val.1) '' K) :=
    hK.image continuous_subtype_val.fst
  have h_ev := (hasBasis_cocompact.tendsto_right_iff.mp hg) _ hK_x
  filter_upwards [h_ev]
  intro x hx h_in
  exact hx ⟨g x, h_in, rfl⟩

theorem tendsto_infinityBackward_zero (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Tendsto (fun t => @coe H h (InfinityInverse.infinityInverseMap H h t)) (𝓝[≠] 0)
      (𝓝 (∞ : HyperellipticOdd H h)) := by
  have h_coe := OnePoint.tendsto_coe_infty (X := HyperellipticAffine H)
  rw [coclosedCompact_eq_cocompact] at h_coe
  refine Tendsto.comp h_coe ?_
  refine tendsto_cocompact_of_fst _ ?_
  have h_comp_comp : Tendsto ((fun w : ℂ => ‖w⁻¹ ^ 2‖) ∘
    (InfinityInverse.tLocalHomeomorph H).symm) (𝓝[≠] 0) atTop :=
      Tendsto.comp tendsto_inv_sq_norm_zero_eq (tendsto_symm_nhdsWithin (H := H))
  have h_comp : Tendsto (fun t => ‖((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2‖)
    (𝓝[≠] 0) atTop := h_comp_comp
  have h_comp_cocompact := tendsto_cocompact_of_tendsto_norm_atTop
    (f := fun t => ((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2) h_comp
  have h_eq : (fun t => (InfinityInverse.infinityInverseMap H h t).val.1) =ᶠ[𝓝[≠] 0]
      (fun t => ((InfinityInverse.tLocalHomeomorph H).symm t)⁻¹ ^ 2) := by
    have h_target : (InfinityInverse.tLocalHomeomorph H).target ∈ 𝓝 (0 : ℂ) :=
      (InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds
        (InfinityInverse.tLocalHomeomorph_target_zero H)
    refine eventually_nhdsWithin_iff.mpr (eventually_of_mem h_target ?_)
    intro t ht ht0
    dsimp
    rw [infinityInverseMap_val_of_ne_zero t ht ht0]
  exact (tendsto_congr' h_eq).mpr h_comp_cocompact

lemma tendsto_pow_div_pow_cocompact (i : ℕ) (n : ℕ) (h_lt : i < n) :
    Tendsto (fun x : ℂ => x ^ i / x ^ n) (cocompact ℂ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_eq : (fun x : ℂ => ‖x ^ i / x ^ n‖) = (fun x => ‖x‖ ^ i / ‖x‖ ^ n) := by
    ext x
    simp [norm_pow]
  rw [h_eq]
  change Tendsto ((fun y : ℝ => y ^ i / y ^ n) ∘ norm) (cocompact ℂ) (𝓝 0)
  refine Tendsto.comp ?_ (tendsto_norm_cocompact_atTop : Tendsto norm (cocompact ℂ) atTop)
  have h_eq' : (fun y : ℝ => y ^ i / y ^ n) =ᶠ[atTop] (fun y => (y ^ (n - i))⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)]
    intro y hy
    have hy0 : y ≠ 0 := by linarith
    rw [show n = i + (n - i) by omega, pow_add]
    rw [← div_div, div_self (pow_ne_zero i hy0), one_div, show i + (n - i) - i = n - i by omega]
  rw [tendsto_congr' h_eq']
  refine tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega))

lemma tendsto_eval_div_pow_cocompact (p : Polynomial ℂ) (n : ℕ) (hn : p.natDegree < n) :
    Tendsto (fun x : ℂ => p.eval x / x ^ n) (cocompact ℂ) (𝓝 0) := by
  have h_eq : (fun x : ℂ => p.eval x / x ^ n) =
    (fun x => (Finset.range (p.natDegree + 1)).sum
      (fun i => p.coeff i * (x ^ i / x ^ n))) := by
    ext x
    rw [Polynomial.eval_eq_sum_range, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_div_assoc]
  rw [h_eq]
  have h_zero : (Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i * (0 : ℂ)) = 0 := by
    have : (fun i => p.coeff i * (0 : ℂ)) = (fun _ => 0) := by ext; ring
    rw [this, Finset.sum_const_zero]
  rw [← h_zero]
  refine tendsto_finsetSum _ ?_
  intro i hi
  have h_lt : i < n := by
    rw [Finset.mem_range] at hi
    omega
  have h_lim := tendsto_pow_div_pow_cocompact i n h_lt
  exact Tendsto.const_mul (p.coeff i) h_lim

lemma tendsto_zero_of_tendsto_sq_zero {α : Type*} {l : Filter α} {f : α → ℂ}
    (h : Tendsto (fun x => ‖f x‖ ^ 2) l (𝓝 0)) :
    Tendsto f l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_sqrt := Real.continuous_sqrt.continuousAt.tendsto.comp h
  rw [Real.sqrt_zero] at h_sqrt
  have h_eq : (fun x => Real.sqrt (‖f x‖ ^ 2)) = (fun x => ‖f x‖) := by
    ext x
    exact Real.sqrt_sq (norm_nonneg _)
  change Tendsto (fun x => Real.sqrt (‖f x‖ ^ 2)) l (𝓝 0) at h_sqrt
  rwa [h_eq] at h_sqrt

lemma eventually_ne_zero_cocompact (H : HyperellipticData) :
    ∀ᶠ q : HyperellipticAffine H in cocompact (HyperellipticAffine H), q.val.1 ≠ 0 := by
  have h_compact : IsCompact {q : HyperellipticAffine H | q.val.1 = 0} := by
    refine isCompact_of_isClosed_bounded_fst H ?_ ⟨0, ?_⟩
    · exact isClosed_eq continuous_subtype_val.fst continuous_const
    · intro q hq
      rw [Set.mem_setOf_eq] at hq
      rw [hq, norm_zero]
  have h_compl := h_compact.compl_mem_cocompact
  filter_upwards [h_compl]
  intro q hq
  exact hq

lemma tendsto_fst_cocompact (H : HyperellipticData) :
    Tendsto (fun q : HyperellipticAffine H => q.val.1)
      (cocompact (HyperellipticAffine H)) (cocompact ℂ) := by
  rw [hasBasis_cocompact.tendsto_iff hasBasis_cocompact]
  intro K hK
  use (fun q => q.val.1) ⁻¹' K
  refine ⟨?_, Set.Subset.rfl⟩
  have h_closed : IsClosed ((fun q : HyperellipticAffine H => q.val.1) ⁻¹' K) :=
    hK.isClosed.preimage (continuous_subtype_val.fst)
  have h_bound : ∃ R, ∀ q ∈ ((fun q : HyperellipticAffine H => q.val.1) ⁻¹' K), ‖q.val.1‖ ≤ R := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    use R
    intro q hq
    have h_in : q.val.1 ∈ K := hq
    have h_ball := hR h_in
    rw [Metric.mem_closedBall, dist_zero_right] at h_ball
    exact h_ball
  exact isCompact_of_isClosed_bounded_fst H h_closed h_bound

lemma sq_norm_div_eq_eval_div (H : HyperellipticData) (q : HyperellipticAffine H)
    (_hq : q.val.1 ≠ 0) :
    ‖q.val.2 / q.val.1 ^ (H.genus + 1)‖ ^ 2 = ‖H.f.eval q.val.1 / q.val.1 ^ (2 * H.genus + 2)‖ := by
  rw [← norm_pow]
  congr 1
  rw [div_pow, q.property]
  congr 1
  rw [show 2 * H.genus + 2 = (H.genus + 1) * 2 by ring, pow_mul]

theorem tendsto_infinityForward_infty (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Tendsto (fun q : HyperellipticAffine H => q.val.2 / q.val.1 ^ (H.genus + 1))
      (coclosedCompact (HyperellipticAffine H)) (𝓝 0) := by
  rw [coclosedCompact_eq_cocompact]
  refine tendsto_zero_of_tendsto_sq_zero ?_
  have h_ev_ne := eventually_ne_zero_cocompact H
  have h_eq : (fun q : HyperellipticAffine H => ‖q.val.2 / q.val.1 ^ (H.genus + 1)‖ ^ 2)
    =ᶠ[cocompact (HyperellipticAffine H)]
      (fun q => ‖H.f.eval q.val.1 / q.val.1 ^ (2 * H.genus + 2)‖) := by
    filter_upwards [h_ev_ne]
    intro q hq
    exact sq_norm_div_eq_eval_div H q hq
  rw [tendsto_congr' h_eq]
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  have h_deg : H.f.natDegree < 2 * H.genus + 2 := by
    rcases h with ⟨k, hk⟩
    dsimp [HyperellipticData.genus]
    rw [hk]
    simp
  have h_lim := tendsto_eval_div_pow_cocompact H.f (2 * H.genus + 2) h_deg
  have h_comp := Tendsto.comp h_lim (tendsto_fst_cocompact H)
  exact h_comp

theorem continuousAt_infinityInverseMap (H : HyperellipticData) (h : Odd H.f.natDegree) (t : ℂ)
    (ht : t ∈ (InfinityInverse.tLocalHomeomorph H).target) (ht0 : t ≠ 0) :
    ContinuousAt (InfinityInverse.infinityInverseMap H h) t := by
  refine (Topology.IsInducing.continuousAt_iff Topology.IsInducing.subtypeVal).mpr ?_
  have h_open : IsOpen ((InfinityInverse.tLocalHomeomorph H).target ∩ {0}ᶜ) :=
    IsOpen.inter (InfinityInverse.tLocalHomeomorph H).open_target isOpen_ne
  have h_mem : t ∈ (InfinityInverse.tLocalHomeomorph H).target ∩ {0}ᶜ := ⟨ht, ht0⟩
  have h_eq : (Subtype.val ∘ InfinityInverse.infinityInverseMap H h) =ᶠ[𝓝 t] (fun w =>
      let W := (InfinityInverse.tLocalHomeomorph H).symm w
      let x := W⁻¹ ^ 2
      let y := w * x ^ (H.genus + 1)
      (x, y)) := by
    refine Filter.eventually_of_mem (U := (InfinityInverse.tLocalHomeomorph H).target ∩ {0}ᶜ) ?_ ?_
    · exact h_open.mem_nhds h_mem
    · intro w hw
      dsimp [InfinityInverse.infinityInverseMap]
      have hw' : w ∈ (InfinityInverse.tLocalHomeomorph H).target ∧ w ≠ 0 := by
        rcases hw with ⟨h1, h2⟩
        exact ⟨h1, h2⟩
      rw [dif_pos hw']
  refine (continuousAt_congr h_eq).mpr ?_
  have h_symm_cont : ContinuousAt (InfinityInverse.tLocalHomeomorph H).symm t :=
    OpenPartialHomeomorph.continuousAt_symm (InfinityInverse.tLocalHomeomorph H) ht
  have h_symm_ne : (InfinityInverse.tLocalHomeomorph H).symm t ≠ 0 := by
    intro hc
    have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H ht
    rw [hc] at h_tz
    have h_zero : InfinityInverse.t H 0 = 0 := by
      unfold InfinityInverse.t
      simp
    rw [h_zero] at h_tz
    exact ht0 h_tz.symm
  have h_inv_cont : ContinuousAt (fun w => ((InfinityInverse.tLocalHomeomorph H).symm w)⁻¹) t :=
    h_symm_cont.inv₀ h_symm_ne
  have h_x_cont : ContinuousAt (fun w => ((InfinityInverse.tLocalHomeomorph H).symm w)⁻¹ ^ 2) t :=
    h_inv_cont.pow 2
  have h_y_cont : ContinuousAt (fun w => w *
    (((InfinityInverse.tLocalHomeomorph H).symm w)⁻¹ ^ 2) ^ (H.genus + 1)) t := by
    have h1 : ContinuousAt (fun w => w) t := continuousAt_id
    have h2 : ContinuousAt (fun w =>
      (((InfinityInverse.tLocalHomeomorph H).symm w)⁻¹ ^ 2) ^ (H.genus + 1)) t :=
      h_x_cont.pow (H.genus + 1)
    exact h1.mul h2
  exact h_x_cont.prodMk h_y_cont

lemma open_source : IsOpen ({ (∞ : HyperellipticOdd H h) } ∪ @coe H h '' V H) := by
  change IsOpen ({ (∞ : OnePoint (HyperellipticAffine H)) } ∪ OnePoint.some '' V H)
  have h_eq : ({ (∞ : OnePoint (HyperellipticAffine H)) } ∪ OnePoint.some '' V H) =
    (OnePoint.some '' (V H)ᶜ)ᶜ := by
    ext x
    induction x using OnePoint.rec with
    | infty =>
      simp [OnePoint.coe_ne_infty]
    | coe q =>
      simp [OnePoint.coe_ne_infty]
  rw [h_eq]
  rw [isOpen_compl_iff]
  rw [OnePoint.isClosed_image_coe]
  refine ⟨?_, V_compl_compact H h⟩
  rw [isClosed_compl_iff]
  exact V_open H h

lemma continuousAt_infinityForward_coe (q : HyperellipticAffine H) (hq1 : q.val.1 ≠ 0) :
    ContinuousAt (fun q : HyperellipticAffine H => q.val.2 / q.val.1 ^ (H.genus + 1)) q := by
  have h1 : ContinuousAt (fun q : HyperellipticAffine H => q.val.2) q :=
    continuous_subtype_val.snd.continuousAt
  have h2 : ContinuousAt (fun q : HyperellipticAffine H => q.val.1 ^ (H.genus + 1)) q := by
    exact (continuous_subtype_val.fst.pow (H.genus + 1)).continuousAt
  have h3 : q.val.1 ^ (H.genus + 1) ≠ 0 := pow_ne_zero _ hq1
  exact ContinuousAt.div h1 h2 h3

lemma continuousAt_infinityForward_infty :
    ContinuousAt (infinityForward H h) ∞ := by
  exact OnePoint.continuousAt_infty'.mpr (tendsto_infinityForward_infty H h)

lemma continuousOn_infinityForward :
    ContinuousOn (infinityForward H h) ({ (∞ : HyperellipticOdd H h) } ∪ @coe H h '' V H) := by
  intro p hp
  have h_open : IsOpen ({ (∞ : HyperellipticOdd H h) } ∪ @coe H h '' V H) := open_source
  have h_nhds : 𝓝[({ (∞ : HyperellipticOdd H h) } ∪ @coe H h '' V H)] p = 𝓝 p := by
    exact h_open.nhdsWithin_eq hp
  rw [ContinuousWithinAt, h_nhds]
  induction p using OnePoint.rec with
  | infty =>
    exact continuousAt_infinityForward_infty
  | coe q =>
    rcases hp with (hp | hp)
    · exfalso
      exact OnePoint.coe_ne_infty q hp
    · have h_q_mem : q ∈ V H := by
        rcases hp with ⟨q', hq', h_eq⟩
        injection h_eq with h_eq'
        rw [← h_eq']
        exact hq'
      have hq1 : q.val.1 ≠ 0 := h_q_mem.1
      exact OnePoint.continuousAt_coe.mpr (continuousAt_infinityForward_coe q hq1)

lemma continuousAt_infinityBackward_of_ne_zero (t : ℂ)
    (ht : t ∈ (InfinityInverse.tLocalHomeomorph H).target) (ht0 : t ≠ 0) :
    ContinuousAt (infinityBackward H h) t := by
  have h_eq : infinityBackward H h =ᶠ[𝓝 t]
    (fun w => @coe H h (InfinityInverse.infinityInverseMap H h w)) := by
    have h_ne : {0}ᶜ ∈ 𝓝 t := isOpen_ne.mem_nhds ht0
    refine Filter.eventually_of_mem h_ne ?_
    intro w hw
    change w ≠ 0 at hw
    dsimp [infinityBackward]
    rw [if_neg hw]
  rw [continuousAt_congr h_eq]
  have h_cont : ContinuousAt (InfinityInverse.infinityInverseMap H h) t :=
    continuousAt_infinityInverseMap H h t ht ht0
  have h_coe_cont : Continuous (@coe H h) := OnePoint.continuous_coe
  exact h_coe_cont.continuousAt.comp h_cont

lemma continuousWithinAt_infinityBackward_zero :
    ContinuousWithinAt (infinityBackward H h) (InfinityInverse.tLocalHomeomorph H).target 0 := by
  rw [ContinuousWithinAt]
  have h_target : (InfinityInverse.tLocalHomeomorph H).target ∈ 𝓝 (0 : ℂ) :=
    (InfinityInverse.tLocalHomeomorph H).open_target.mem_nhds
      (InfinityInverse.tLocalHomeomorph_target_zero H)
  rw [nhdsWithin_eq_nhds.mpr h_target]
  have h_nhds : 𝓝 (0 : ℂ) = 𝓝[≠] (0 : ℂ) ⊔ pure 0 := (nhdsNE_sup_pure 0).symm
  have h_zero : infinityBackward H h 0 = (∞ : HyperellipticOdd H h) := by
    dsimp [infinityBackward]
    rw [if_pos rfl]
  rw [h_nhds, tendsto_sup]
  constructor
  · have h_eq : (infinityBackward H h) =ᶠ[𝓝[≠] 0]
      (fun t => @coe H h (InfinityInverse.infinityInverseMap H h t)) := by
      refine Filter.eventually_of_mem (self_mem_nhdsWithin) ?_
      intro t ht
      change t ≠ 0 at ht
      dsimp [infinityBackward]
      rw [if_neg ht]
    rw [tendsto_congr' h_eq]
    rw [h_zero]
    exact tendsto_infinityBackward_zero H h
  · exact tendsto_pure_nhds (infinityBackward H h) 0

lemma continuousOn_infinityBackward :
    ContinuousOn (infinityBackward H h) (InfinityInverse.tLocalHomeomorph H).target := by
  intro t ht
  by_cases ht0 : t = 0
  · rw [ht0]
    exact continuousWithinAt_infinityBackward_zero
  · exact (continuousAt_infinityBackward_of_ne_zero t ht ht0).continuousWithinAt

noncomputable def infinityChart (H : HyperellipticData) (h : Odd H.f.natDegree) :
    OpenPartialHomeomorph (HyperellipticOdd H h) ℂ where
  toFun := infinityForward H h
  invFun := infinityBackward H h
  source := { (∞ : HyperellipticOdd H h) } ∪ @coe H h '' V H
  target := (InfinityInverse.tLocalHomeomorph H).target
  map_source' := by
    intro p hp
    rcases hp with (hp | hp)
    · have hp_eq : p = (∞ : HyperellipticOdd H h) := Set.mem_singleton_iff.mp hp
      rw [hp_eq]
      dsimp [infinityForward]
      exact InfinityInverse.tLocalHomeomorph_target_zero H
    · rcases hp with ⟨q, ⟨hq1, hq2, hq_w⟩, rfl⟩
      change q.val.2 / q.val.1 ^ (H.genus + 1) ∈ (InfinityInverse.tLocalHomeomorph H).target
      have hw_in_source : (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) *
        (InfinityInverse.S H q.val.1⁻¹)⁻¹) ∈ (InfinityInverse.tLocalHomeomorph H).source := hq_w
      have hz_eq : q.val.2 / q.val.1 ^ (H.genus + 1) =
        InfinityInverse.tLocalHomeomorph H (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) *
          (InfinityInverse.S H q.val.1⁻¹)⁻¹) := by
        rw [InfinityInverse.tLocalHomeomorph_coe]
        exact (t_w_q h q hq1 hq2).symm
      rw [hz_eq]
      exact (InfinityInverse.tLocalHomeomorph H).map_source hw_in_source
  map_target' := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0]
      rw [infinityBackward, if_pos rfl]
      left
      exact Set.mem_singleton _
    · right
      set q := InfinityInverse.infinityInverseMap H h t
      use q
      have h_w := w_infinityInverseMap (h := h) t ht ht0
      refine ⟨⟨h_w.1, h_w.2.1, ?_⟩, ?_⟩
      · rw [h_w.2.2]
        exact (InfinityInverse.tLocalHomeomorph H).symm_mapsTo ht
      · dsimp [infinityBackward]
        rw [if_neg ht0]
  left_inv' := by
    intro p hp
    rcases hp with (hp | hp)
    · have hp_eq : p = (∞ : HyperellipticOdd H h) := Set.mem_singleton_iff.mp hp
      rw [hp_eq]
      simp [infinityForward, infinityBackward]
    · rcases hp with ⟨q, ⟨hq1, hq2, hq_w⟩, rfl⟩
      let z := infinityForward H h (coe q)
      have hz_eq : z = q.val.2 / q.val.1 ^ (H.genus + 1) := rfl
      have hz0 : z ≠ 0 := by
        intro hc
        have : q.val.2 = 0 := by
          have : q.val.2 / q.val.1 ^ (H.genus + 1) = 0 := hc
          exact div_eq_zero_iff.mp this |>.resolve_right (pow_ne_zero _ hq1)
        exact hq2 this
      have hz_in_target : z ∈ (InfinityInverse.tLocalHomeomorph H).target := by
        have hw_in_source : (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) *
          (InfinityInverse.S H q.val.1⁻¹)⁻¹) ∈ (InfinityInverse.tLocalHomeomorph H).source := hq_w
        have hz_eq' : z = InfinityInverse.tLocalHomeomorph H
          (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹) := by
          rw [InfinityInverse.tLocalHomeomorph_coe]
          exact (t_w_q h q hq1 hq2).symm
        rw [hz_eq']
        exact (InfinityInverse.tLocalHomeomorph H).map_source hw_in_source
      change infinityBackward H h z = coe q
      dsimp [infinityBackward]
      rw [if_neg hz0]
      congr 1
      rw [infinityInverseMap_val_of_ne_zero z hz_in_target hz0]
      apply Subtype.ext
      dsimp
      have h_symm : (InfinityInverse.tLocalHomeomorph H).symm z =
        (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹) := by
        have hz_eq' : z = InfinityInverse.tLocalHomeomorph H
          (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹) := by
          rw [InfinityInverse.tLocalHomeomorph_coe]
          exact (t_w_q h q hq1 hq2).symm
        rw [hz_eq']
        exact (InfinityInverse.tLocalHomeomorph H).left_inv hq_w
      have hW_sq : ((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2 = q.val.1⁻¹ := by
        rw [h_symm]
        exact InfinityInverse.w_q_sq_eq_inv h q hq1 hq2
      have h_x : ((InfinityInverse.tLocalHomeomorph H).symm z)⁻¹ ^ 2 = q.val.1 := by
        rw [inv_pow, hW_sq, inv_inv]
      refine Prod.ext h_x ?_
      dsimp
      rw [h_x]
      have hz_val : z = q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) := by
        have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H hz_in_target
        have hz_eq'' : z = (InfinityInverse.tLocalHomeomorph H).symm z *
          InfinityInverse.S H (((InfinityInverse.tLocalHomeomorph H).symm z) ^ 2) := h_tz.symm
        rw [h_symm] at hz_eq''
        rw [hz_eq'']
        have hw_sq := InfinityInverse.w_q_sq_eq_inv h q hq1 hq2
        rw [hw_sq]
        have h_S_nz : InfinityInverse.S H q.val.1⁻¹ ≠ 0 := by
          intro hc
          have h_S_sq := InfinityInverse.S_sq_eq_eval_rev H q.val.1⁻¹
          have hc2 : (InfinityInverse.S H q.val.1⁻¹) ^ 2 = 0 := by rw [hc, zero_pow (by decide)]
          rw [h_S_sq] at hc2
          have h_rev := reverse_eval_inv_eq (H := H) q.val.1 hq1
          rw [h_rev] at hc2
          have h_y_sq : q.val.2 ^ 2 = H.f.eval q.val.1 := q.property
          have h_f_eval_nz : H.f.eval q.val.1 ≠ 0 := by
            intro hc3
            have hc4 : q.val.2 ^ 2 = 0 := by rw [h_y_sq, hc3]
            exact hq2 (sq_eq_zero_iff.mp hc4)
          have h_source : (InfinityInverse.tLocalHomeomorph H).source =
            ((HasStrictFDerivAt.toOpenPartialHomeomorph (InfinityInverse.t H)
              (InfinityInverse.tLocalHomeomorph_hd H)).source ∩
                (fun x => -x) ⁻¹' (HasStrictFDerivAt.toOpenPartialHomeomorph (InfinityInverse.t H)
                  (InfinityInverse.tLocalHomeomorph_hd H)).source) ∩
            InfinityInverse.U_S H := by
              dsimp [InfinityInverse.tLocalHomeomorph]
              ext x
              simp only [Set.mem_inter_iff]
              tauto
          rw [h_source] at hq_w
          exact (mul_ne_zero h_f_eval_nz (pow_ne_zero _ (inv_ne_zero hq1))) hc2
        calc q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * (InfinityInverse.S H q.val.1⁻¹)⁻¹ *
            InfinityInverse.S H q.val.1⁻¹
          _ = q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) *
            ((InfinityInverse.S H q.val.1⁻¹)⁻¹ * InfinityInverse.S H q.val.1⁻¹) := by ring
          _ = q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) * 1 := by rw [inv_mul_cancel₀ h_S_nz]
          _ = q.val.2 * q.val.1⁻¹ ^ (H.genus + 1) := mul_one _
      calc z * q.val.1 ^ (H.genus + 1)
        _ = (q.val.2 * q.val.1⁻¹ ^ (H.genus + 1)) * q.val.1 ^ (H.genus + 1) := by rw [hz_val]
        _ = q.val.2 * (q.val.1⁻¹ ^ (H.genus + 1) * q.val.1 ^ (H.genus + 1)) := by ring
        _ = q.val.2 * 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hq1, one_pow]
        _ = q.val.2 := mul_one _
  right_inv' := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0]
      simp [infinityBackward, infinityForward]
    · rw [infinityBackward, if_neg ht0]
      exact infinityForward_infinityInverseMap_eq_self t ht ht0
  open_source := open_source
  open_target := (InfinityInverse.tLocalHomeomorph H).open_target
  continuousOn_toFun := continuousOn_infinityForward
  continuousOn_invFun := continuousOn_infinityBackward

/-- The infinity chart is defined at the point `∞`. -/
theorem infinityChart_mem_source (H : HyperellipticData) (h : Odd H.f.natDegree) :
    (∞ : HyperellipticOdd H h) ∈ (infinityChart H h).source := by
  left
  rfl

theorem tLocalHomeomorph_symm_contDiffOn (H : HyperellipticData) :
    ContDiffOn ℂ ω (InfinityInverse.tLocalHomeomorph H).symm
      (InfinityInverse.tLocalHomeomorph H).target := by
  intro y hy
  let e := HasStrictFDerivAt.toOpenPartialHomeomorph (InfinityInverse.t H)
    (InfinityInverse.tLocalHomeomorph_hd H)
  have h_eq : ∀ z ∈ (InfinityInverse.tLocalHomeomorph H).target,
      (InfinityInverse.tLocalHomeomorph H).symm z = e.symm z := by
    intro z hz
    rfl
  refine ContDiffWithinAt.congr ?_ h_eq (h_eq y hy)
  have hy_e : y ∈ e.target := by
    exact hy.1.1
  have h_sub : (InfinityInverse.tLocalHomeomorph H).target ⊆ e.target := by
    intro z hz
    exact hz.1.1
  refine ContDiffWithinAt.mono ?_ h_sub
  have h_mem_source : e.symm y ∈ (InfinityInverse.U_S H) := by
    exact hy.2
  have h_mem_nhds : InfinityInverse.U_S H ∈ 𝓝 (e.symm y) :=
    (InfinityInverse.isOpen_U_S H).mem_nhds h_mem_source
  let df_equiv_u := (ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 (deriv (InfinityInverse.t H) 0) (InfinityInverse.t_deriv_ne_zero H)) : ℂ ≃L[ℂ] ℂ)
  let df_inv := (df_equiv_u.symm : ℂ →L[ℂ] ℂ)
  have h_approx : ApproximatesLinearOn (InfinityInverse.t H) (df_equiv_u : ℂ →L[ℂ] ℂ)
    e.source (‖df_inv‖₊⁻¹ / 2) := by
    have h_hd := InfinityInverse.tLocalHomeomorph_hd H
    exact (Classical.choose_spec h_hd.approximates_deriv_on_open_nhds).2.2
  have h_cd_x : ContDiffAt ℂ ω (InfinityInverse.t H) (e.symm y) := by
    have h_ana := InfinityInverse.t_analyticAt_of_mem H h_mem_source
    exact h_ana.contDiffAt
  have h_deriv_x : HasFDerivAt (InfinityInverse.t H)
    (fderiv ℂ (InfinityInverse.t H) (e.symm y)) (e.symm y) :=
    h_cd_x.differentiableAt (by simp) |>.hasFDerivAt
  have h_pos : 0 < ‖df_inv‖₊ := by
    cases df_equiv_u.subsingleton_or_nnnorm_symm_pos with
    | inl h_sub =>
      have h_eq' : (0 : ℂ) = 1 := Subsingleton.elim 0 1
      norm_num at h_eq'
    | inr h_pos => exact h_pos
  have h_lt : ‖df_inv‖₊⁻¹ / 2 < ‖df_inv‖₊⁻¹ := by
    apply NNReal.half_lt_self
    exact inv_ne_zero (ne_of_gt h_pos)
  have h_open_source := e.open_source
  have hx_source : e.symm y ∈ e.source := e.map_target' hy_e
  let df_equiv := GeneralResults.equivOfApproxAt h_open_source h_approx hx_source h_deriv_x h_lt
  have h_deriv_e_x : HasFDerivAt (⇑e) (df_equiv : ℂ →L[ℂ] ℂ) (e.symm y) := h_deriv_x
  have h_cd_e_x : ContDiffAt ℂ ω (⇑e) (e.symm y) := h_cd_x
  rw [contDiffWithinAt_iff_contDiffAt (e.open_target.mem_nhds hy_e)]
  exact e.contDiffAt_symm hy_e h_deriv_e_x h_cd_e_x

lemma affineLiftProjX_trans_infinityChart_apply
    (p : HyperellipticAffine H) (hpY : p ∈ HyperellipticAffine.smoothLocusY H)
    {x : ℂ}
    (hx : x ∈ ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)).source)) :
    (((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) x =
      (HyperellipticAffine.squareLocalHomeomorph (H := H) p hpY).symm (H.f.eval x) /
        x ^ (H.genus + 1) := by
  have h_trans : (((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
      (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
      (infinityChart H h)) x =
      infinityForward H h (((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
      (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm x) := by
    rfl
  rw [h_trans]
  have h_symm : ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
      (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm x =
      (coe ((HyperellipticAffine.affineChartProjX (H := H) p hpY).symm x) :
        HyperellipticOdd H h) := by
    rfl
  rw [h_symm]
  dsimp [infinityForward, OnePoint.elim]
  have hx0 : x ∈ (HyperellipticAffine.affineChartProjX p hpY).target := by
    rcases hx with ⟨hx_lift, _⟩
    exact hx_lift
  have h_fst := HyperellipticAffine.affineChartProjX_symm_apply_fst (H := H) p hpY hx0
  have h_snd := HyperellipticAffine.affineChartProjX_symm_apply_snd (H := H) p hpY hx0
  change (((HyperellipticAffine.affineChartProjX (H := H) p hpY).symm x :
    HyperellipticAffine H).val.2) /
    (((HyperellipticAffine.affineChartProjX (H := H) p hpY).symm x :
      HyperellipticAffine H).val.1) ^ (H.genus + 1) = _
  rw [h_fst, h_snd]

lemma affineLiftProjY_trans_infinityChart_apply
    (p : HyperellipticAffine H) (hpX : p ∈ HyperellipticAffine.smoothLocusX H)
    {y : ℂ}
    (hy : y ∈ ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)).source)) :
    (((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) y =
      y / ((HyperellipticAffine.polynomialLocalHomeomorph (H := H) p hpX).symm (y ^ 2)) ^
        (H.genus + 1) := by
  have h_trans : (((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
      (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
      (infinityChart H h)) y =
      infinityForward H h (((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
      (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm y) := by
    rfl
  rw [h_trans]
  have h_symm : ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
      (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm y =
      (coe ((HyperellipticAffine.affineChartProjY (H := H) p hpX).symm y) :
        HyperellipticOdd H h) := by
    rfl
  rw [h_symm]
  dsimp [infinityForward, OnePoint.elim]
  have hy0 : y ∈ (HyperellipticAffine.affineChartProjY p hpX).target := by
    rcases hy with ⟨hy_lift, _⟩
    exact hy_lift
  have h_fst := HyperellipticAffine.affineChartProjY_symm_apply_fst (H := H) p hpX hy0
  have h_snd := HyperellipticAffine.affineChartProjY_symm_apply_snd (H := H) p hpX hy0
  change (((HyperellipticAffine.affineChartProjY (H := H) p hpX).symm y :
    HyperellipticAffine H).val.2) /
    (((HyperellipticAffine.affineChartProjY (H := H) p hpX).symm y :
      HyperellipticAffine H).val.1) ^ (H.genus + 1) = _
  rw [h_fst, h_snd]

lemma infinityChart_trans_affineLiftProjX_apply
    (p : HyperellipticAffine H) (hpY : p ∈ HyperellipticAffine.smoothLocusY H)
    {x : ℂ}
    (hx : x ∈ (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source)) :
    (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) x) =
      ((InfinityInverse.tLocalHomeomorph H).symm x)⁻¹ ^ 2 := by
  have h_trans : (((infinityChart H h).symm.trans
      ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) x) =
      ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))) (infinityBackward H h x) := by
    rfl
  rw [h_trans]
  have h_mem := hx.2
  have h_ne_infty : infinityBackward H h x ≠ (∞ : HyperellipticOdd H h) := by
    intro hc
    have h_mem' : (∞ : HyperellipticOdd H h) ∈
      ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).source := by
      rwa [← hc]
    rcases h_mem' with ⟨q, hq, h_eq⟩
    exact OnePoint.infty_notMem_range_coe ⟨q, h_eq⟩
  have hx0 : x ≠ 0 := by
    intro hc
    rw [hc] at h_ne_infty
    dsimp [infinityBackward] at h_ne_infty
    have h_inf_zero : infinityBackward H h 0 = (∞ : HyperellipticOdd H h) := by
      unfold infinityBackward; rw [if_pos rfl]
    exact h_ne_infty h_inf_zero
  have h_eq_coe : infinityBackward H h x = coe (InfinityInverse.infinityInverseMap H h x) := by
    dsimp [infinityBackward]
    rw [if_neg hx0]
  rw [h_eq_coe]
  have h_lift : ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
      (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))
      (coe (InfinityInverse.infinityInverseMap H h x) : HyperellipticOdd H h) =
      (InfinityInverse.infinityInverseMap H h x).val.1 := by
    erw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  rw [h_lift]
  have h_target : x ∈ (InfinityInverse.tLocalHomeomorph H).target := by
    have hx_t := hx.1
    exact hx_t
  rw [infinityInverseMap_val_of_ne_zero x h_target hx0]

lemma infinityChart_trans_affineLiftProjY_apply
    (p : HyperellipticAffine H) (hpX : p ∈ HyperellipticAffine.smoothLocusX H)
    {x : ℂ}
    (hx : x ∈ (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source)) :
    (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) x) =
      x * (((InfinityInverse.tLocalHomeomorph H).symm x)⁻¹ ^ 2) ^ (H.genus + 1) := by
  have h_trans : (((infinityChart H h).symm.trans
      ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) x) =
      ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))) (infinityBackward H h x) := by
    rfl
  rw [h_trans]
  have h_mem := hx.2
  have h_ne_infty : infinityBackward H h x ≠ (∞ : HyperellipticOdd H h) := by
    intro hc
    have h_mem' : (∞ : HyperellipticOdd H h) ∈
      ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).source := by
      rwa [← hc]
    rcases h_mem' with ⟨q, hq, h_eq⟩
    exact OnePoint.infty_notMem_range_coe ⟨q, h_eq⟩
  have hx0 : x ≠ 0 := by
    intro hc
    rw [hc] at h_ne_infty
    dsimp [infinityBackward] at h_ne_infty
    have h_inf_zero : infinityBackward H h 0 = (∞ : HyperellipticOdd H h) := by
      unfold infinityBackward; rw [if_pos rfl]
    exact h_ne_infty h_inf_zero
  have h_eq_coe : infinityBackward H h x = coe (InfinityInverse.infinityInverseMap H h x) := by
    dsimp [infinityBackward]
    rw [if_neg hx0]
  rw [h_eq_coe]
  have h_lift : ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
      (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))
      (coe (InfinityInverse.infinityInverseMap H h x) : HyperellipticOdd H h) =
      (InfinityInverse.infinityInverseMap H h x).val.2 := by
    erw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  rw [h_lift]
  have h_target : x ∈ (InfinityInverse.tLocalHomeomorph H).target := by
    have hx_t := hx.1
    exact hx_t
  rw [infinityInverseMap_val_of_ne_zero x h_target hx0]

/-- Remaining OA2 local boundary: infinity chart followed by the lifted affine `x`-chart. -/
theorem infinityChart_compat_affineLiftProjX
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) : ℂ → ℂ)
      ((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source := by
  have h_symm_smooth : ContDiffOn ℂ ω (InfinityInverse.tLocalHomeomorph H).symm
      (InfinityInverse.tLocalHomeomorph H).target :=
    tLocalHomeomorph_symm_contDiffOn H
  have h_sub : (((infinityChart H h).symm.trans
      ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source) ⊆
      (InfinityInverse.tLocalHomeomorph H).target := by
    intro x hx
    exact hx.1
  have h_symm_sub := h_symm_smooth.mono h_sub
  have h_nz : ∀ x ∈ (((infinityChart H h).symm.trans
      ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source),
      (InfinityInverse.tLocalHomeomorph H).symm x ≠ 0 := by
    intro x hx
    have h_mem := hx.2
    have hx0 : x ≠ 0 := by
      intro hc
      have h_ne_infty : infinityBackward H h x ≠ (∞ : HyperellipticOdd H h) := by
        intro hc'
        have h_mem' : (∞ : HyperellipticOdd H h) ∈
      ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).source := by
          rwa [← hc']
        rcases h_mem' with ⟨q, hq, h_eq⟩
        exact OnePoint.infty_notMem_range_coe ⟨q, h_eq⟩
      rw [hc] at h_ne_infty
      have h_inf_zero : infinityBackward H h 0 = (∞ : HyperellipticOdd H h) := by
        unfold infinityBackward; rw [if_pos rfl]
      exact h_ne_infty h_inf_zero
    have h_target : x ∈ (InfinityInverse.tLocalHomeomorph H).target := hx.1
    have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H h_target
    intro hc
    rw [hc] at h_tz
    have h_zero : InfinityInverse.t H 0 = 0 := by
      unfold InfinityInverse.t
      simp
    rw [h_zero] at h_tz
    exact hx0 h_tz.symm
  have h_inv : ContDiffOn ℂ ω (fun x => ((InfinityInverse.tLocalHomeomorph H).symm x)⁻¹)
      (((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source) :=
    h_symm_sub.inv h_nz
  have h_pow2 := h_inv.pow 2
  refine ContDiffOn.congr h_pow2 ?_
  intro x hx
  exact infinityChart_trans_affineLiftProjX_apply p hpY hx

/-- Remaining OA2 local boundary: the lifted affine `x`-chart followed by the infinity chart. -/
theorem affineLiftProjX_compat_infinityChart
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) : ℂ → ℂ)
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source := by
  set e := HyperellipticAffine.squareLocalHomeomorph (H := H) p hpY
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    HyperellipticAffine.squareLocalHomeomorph_contDiffOn_symm (H := H) p hpY
  have hpoly : ContDiffOn ℂ ω (fun x : ℂ => H.f.eval x)
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    (Polynomial.contDiff_aeval H.f ω).contDiffOn
  have hmaps : Set.MapsTo (fun x : ℂ => H.f.eval x)
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source e.target := by
    intro x hx
    have hx_lift := hx.1
    simp only [OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.lift_openEmbedding_target] at hx_lift
    exact hx_lift
  have h_num : ContDiffOn ℂ ω (fun x => e.symm (H.f.eval x))
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    hsymm.comp hpoly hmaps
  have h_den : ContDiffOn ℂ ω (fun x : ℂ => x ^ (H.genus + 1))
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    (contDiff_id.pow (H.genus + 1)).contDiffOn
  have h_den_nz : ∀ x ∈ ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source, x ^ (H.genus + 1) ≠ 0 := by
    intro x hx
    have h_symm : ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm x =
        (coe ((HyperellipticAffine.affineChartProjX (H := H) p hpY).symm x) :
        HyperellipticOdd H h) := by
      rfl
    have h_img : (((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm) x ∈
          (infinityChart H h).source := hx.2
    rw [h_symm] at h_img
    have h_mem_source :
      ((HyperellipticAffine.affineChartProjX p hpY).symm x : HyperellipticAffine H).val.1 ≠ 0 := by
      rcases h_img with h_inf | ⟨q, hq, h_eq_coe⟩
      · exfalso
        exact OnePoint.infty_notMem_range_coe
          ⟨((HyperellipticAffine.affineChartProjX p hpY).symm x : HyperellipticAffine H), h_inf⟩
      · have hq_eq : q = (HyperellipticAffine.affineChartProjX p hpY).symm x := by
          exact coe_injective h_eq_coe
        rw [← hq_eq]
        exact hq.1
    have hx0 : x ∈ (HyperellipticAffine.affineChartProjX p hpY).target := by
      have hx_lift := hx.1
      simp only [OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.lift_openEmbedding_target] at hx_lift
      exact hx_lift
    have h_fst := HyperellipticAffine.affineChartProjX_symm_apply_fst (H := H) p hpY hx0
    rw [h_fst] at h_mem_source
    exact pow_ne_zero _ h_mem_source
  have h_div : ContDiffOn ℂ ω (fun x => e.symm (H.f.eval x) / x ^ (H.genus + 1))
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    h_num.div h_den h_den_nz
  refine ContDiffOn.congr h_div ?_
  intro x hx
  exact affineLiftProjX_trans_infinityChart_apply p hpY hx

/-- Remaining OA2 local boundary: infinity chart followed by the lifted affine `y`-chart. -/
theorem infinityChart_compat_affineLiftProjY
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpX : p ∈ HyperellipticAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) : ℂ → ℂ)
      ((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source := by
  have h_symm_smooth : ContDiffOn ℂ ω (InfinityInverse.tLocalHomeomorph H).symm
      (InfinityInverse.tLocalHomeomorph H).target :=
    tLocalHomeomorph_symm_contDiffOn H
  have h_sub : (((infinityChart H h).symm.trans
      ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source) ⊆
      (InfinityInverse.tLocalHomeomorph H).target := by
    intro x hx
    exact hx.1
  have h_symm_sub := h_symm_smooth.mono h_sub
  have h_nz : ∀ x ∈ (((infinityChart H h).symm.trans
      ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source),
      (InfinityInverse.tLocalHomeomorph H).symm x ≠ 0 := by
    intro x hx
    have h_mem := hx.2
    have hx0 : x ≠ 0 := by
      intro hc
      have h_ne_infty : infinityBackward H h x ≠ (∞ : HyperellipticOdd H h) := by
        intro hc'
        have h_mem' : (∞ : HyperellipticOdd H h) ∈
      ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).source := by
          rwa [← hc']
        rcases h_mem' with ⟨q, hq, h_eq⟩
        exact OnePoint.infty_notMem_range_coe ⟨q, h_eq⟩
      rw [hc] at h_ne_infty
      have h_inf_zero : infinityBackward H h 0 = (∞ : HyperellipticOdd H h) := by
        unfold infinityBackward; rw [if_pos rfl]
      exact h_ne_infty h_inf_zero
    have h_target : x ∈ (InfinityInverse.tLocalHomeomorph H).target := hx.1
    have h_tz := InfinityInverse.tLocalHomeomorph_right_inv H h_target
    intro hc
    rw [hc] at h_tz
    have h_zero : InfinityInverse.t H 0 = 0 := by
      unfold InfinityInverse.t
      simp
    rw [h_zero] at h_tz
    exact hx0 h_tz.symm
  have h_inv : ContDiffOn ℂ ω (fun x => ((InfinityInverse.tLocalHomeomorph H).symm x)⁻¹)
      (((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source) :=
    h_symm_sub.inv h_nz
  have h_pow : ContDiffOn ℂ ω
    (fun x => (((InfinityInverse.tLocalHomeomorph H).symm x)⁻¹ ^ 2) ^ (H.genus + 1))
      (((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source) :=
    (h_inv.pow 2).pow (H.genus + 1)
  have h_id : ContDiffOn ℂ ω (fun x : ℂ => x)
      (((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source) :=
    contDiffOn_id
  have h_mul := h_id.mul h_pow
  refine ContDiffOn.congr h_mul ?_
  intro x hx
  exact infinityChart_trans_affineLiftProjY_apply p hpX hx

/-- Remaining OA2 local boundary: the lifted affine `y`-chart followed by the infinity chart. -/
theorem affineLiftProjY_compat_infinityChart
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpX : p ∈ HyperellipticAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) : ℂ → ℂ)
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source := by
  set e := HyperellipticAffine.polynomialLocalHomeomorph (H := H) p hpX
  have hsymm : ContDiffOn ℂ ω e.symm e.target :=
    HyperellipticAffine.polynomialLocalHomeomorph_contDiffOn_symm (H := H) p hpX
  have hsq : ContDiffOn ℂ ω (fun y : ℂ => y ^ 2)
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    (contDiff_id.pow 2).contDiffOn
  have hmaps : Set.MapsTo (fun y : ℂ => y ^ 2)
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source e.target := by
    intro y hy
    have hy_lift := hy.1
    simp only [OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.lift_openEmbedding_target] at hy_lift
    exact hy_lift
  have h_den_inner : ContDiffOn ℂ ω (fun y => e.symm (y ^ 2))
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    hsymm.comp hsq hmaps
  have h_den : ContDiffOn ℂ ω (fun y => (e.symm (y ^ 2)) ^ (H.genus + 1))
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    h_den_inner.pow (H.genus + 1)
  have h_num : ContDiffOn ℂ ω (fun y : ℂ => y)
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    contDiffOn_id
  have h_den_nz : ∀ y ∈ ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source, (e.symm (y ^ 2)) ^ (H.genus + 1) ≠ 0 := by
    intro y hy
    have h_symm : ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm y =
        (coe ((HyperellipticAffine.affineChartProjY (H := H) p hpX).symm y) :
        HyperellipticOdd H h) := by
      rfl
    have h_img : (((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
        (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm) y ∈
          (infinityChart H h).source := hy.2
    rw [h_symm] at h_img
    have h_mem_source :
      ((HyperellipticAffine.affineChartProjY p hpX).symm y : HyperellipticAffine H).val.1 ≠ 0 := by
      rcases h_img with h_inf | ⟨q, hq, h_eq_coe⟩
      · exfalso
        exact OnePoint.infty_notMem_range_coe
          ⟨((HyperellipticAffine.affineChartProjY p hpX).symm y : HyperellipticAffine H), h_inf⟩
      · have hq_eq : q = (HyperellipticAffine.affineChartProjY p hpX).symm y := by
          exact coe_injective h_eq_coe
        rw [← hq_eq]
        exact hq.1
    have hy0 : y ∈ (HyperellipticAffine.affineChartProjY p hpX).target := by
      have hy_lift := hy.1
      simp only [OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.lift_openEmbedding_target] at hy_lift
      exact hy_lift
    have h_fst := HyperellipticAffine.affineChartProjY_symm_apply_fst (H := H) p hpX hy0
    rw [h_fst] at h_mem_source
    exact pow_ne_zero _ h_mem_source
  have h_div : ContDiffOn ℂ ω (fun y => y / (e.symm (y ^ 2)) ^ (H.genus + 1))
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source :=
    h_num.div h_den h_den_nz
  refine ContDiffOn.congr h_div ?_
  intro y hy
  exact affineLiftProjY_trans_infinityChart_apply p hpX hy

end Jacobians.ProjectiveCurve.HyperellipticOdd
