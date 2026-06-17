/-
Copyright (c) 2026 Michal J Wallace. All rights reserved.
Released under the MIT license (the upstream repository LICENSE; © Michal J Wallace).
Original source: https://github.com/tangentstorm/JacobianChallenge
                 Jacobian/HolomorphicForms/AnalyticLocalMapping.lean (commit 82349bc8, 2026-06-01).
Note: the upstream repo LICENSE is MIT; on full adoption, vendor the upstream
LICENSE under `vendor/wallace-jacobian-challenge/`.

Vendored (trial) into this repository on 2026-06-02 by Michael R Douglas.
Modifications relative to upstream:
- Renamespaced under `Jacobians.Vendor.Wallace.HolomorphicForms.*`.
- Internal imports retargeted to the vendored module paths.
No mathematical content was altered.
-/

import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic

/-!
# Analytic Local Mapping Theorem (ℂ → ℂ)

The local mapping theorem for analytic functions: near a zero of order `k`,
the function has exactly `k` simple preimages of any nearby nonzero value.
-/

noncomputable section

open scoped Topology
open Set Filter

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.style.emptyLine false
set_option linter.unusedSectionVars false

namespace Jacobians.Vendor.Wallace.HolomorphicForms.AnalyticLocalMapping

/-! ### Power map root counting -/

theorem card_roots_pow_eq (k : ℕ) (hk : 0 < k) (w : ℂ) (hw : w ≠ 0) :
    ∃ S : Finset ℂ, S.card = k ∧
    (∀ t ∈ S, t ^ k = w) ∧
    (∀ t, t ^ k = w → t ∈ S) := by
  refine ⟨ ( Polynomial.map ( algebraMap ℂ ℂ ) ( Polynomial.X ^ k - Polynomial.C w ) |> Polynomial.roots |> Multiset.toFinset ), ?_, ?_, ?_ ⟩;
  · nontriviality;
    rw [ Multiset.toFinset_card_of_nodup ] <;> norm_num;
    · rw [ ← Polynomial.Splits.natDegree_eq_card_roots ];
      · rw [ Polynomial.natDegree_X_pow_sub_C ];
      · exact IsAlgClosed.splits (Polynomial.X ^ k - Polynomial.C w);
    · have := Polynomial.separable_X_pow_sub_C w ( Nat.cast_ne_zero.mpr hk.ne' ) hw;
      exact Polynomial.nodup_roots this;
  · intro t ht
    rw [Multiset.mem_toFinset] at ht
    have h_ne : Polynomial.map (algebraMap ℂ ℂ) (Polynomial.X ^ k - Polynomial.C w) ≠ 0 := by
      rw [Algebra.algebraMap_self, Polynomial.map_id]
      intro h
      have h_deg : (Polynomial.X ^ k - Polynomial.C w).natDegree = 0 := by
        rw [h, Polynomial.natDegree_zero]
      rw [Polynomial.natDegree_X_pow_sub_C] at h_deg
      omega
    rw [Polynomial.mem_roots h_ne] at ht
    rw [Polynomial.IsRoot.def, Algebra.algebraMap_self, Polynomial.map_id, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at ht
    exact sub_eq_zero.mp ht
  · intro t ht
    rw [Multiset.mem_toFinset]
    have h_ne : Polynomial.map (algebraMap ℂ ℂ) (Polynomial.X ^ k - Polynomial.C w) ≠ 0 := by
      rw [Algebra.algebraMap_self, Polynomial.map_id]
      intro h
      have h_deg : (Polynomial.X ^ k - Polynomial.C w).natDegree = 0 := by
        rw [h, Polynomial.natDegree_zero]
      rw [Polynomial.natDegree_X_pow_sub_C] at h_deg
      omega
    rw [Polynomial.mem_roots h_ne]
    rw [Polynomial.IsRoot.def, Algebra.algebraMap_self, Polynomial.map_id, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [ht, sub_self]

/-
All k-th roots of w lie in the ball of radius ‖w‖^(1/k) + 1.
-/
theorem pow_root_norm_bound (k : ℕ) (hk : 0 < k) (t w : ℂ) (ht : t ^ k = w) :
    ‖t‖ ≤ ‖w‖ ^ (1 / (k : ℝ)) + 1 := by
  exact le_add_of_le_of_nonneg ( by rw [ ← ht, norm_pow ] ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] ) zero_le_one

/-
If all k-th roots of w have norm < r, then w = t^k implies ‖t‖ < r.
More precisely: if ‖w‖ < r^k for r > 0, then any k-th root of w has norm < r.
-/
theorem pow_root_in_ball (k : ℕ) (_hk : 0 < k) (r : ℝ) (hr : 0 < r)
    (t w : ℂ) (ht : t ^ k = w) (hw : ‖w‖ < r ^ k) :
    ‖t‖ < r := by
  contrapose! hw;
  simpa [ ← ht ] using pow_le_pow_left₀ hr.le hw k

/-! ### k-th root of nonvanishing analytic function -/

theorem analyticAt_kthRoot (k : ℕ) (hk : 0 < k) (u : ℂ → ℂ) (z₀ : ℂ)
    (hu : AnalyticAt ℂ u z₀) (hu0 : u z₀ ≠ 0) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v z₀ ∧ v z₀ ≠ 0 ∧
    ∀ᶠ z in 𝓝 z₀, v z ^ k = u z := by
  by_cases hsl : u z₀ ∈ Complex.slitPlane;
  · refine ⟨fun z => u z ^ ( 1 / k : ℂ ), ?_, ?_, ?_⟩;
    · apply_rules [ AnalyticAt.cpow, hu ];
      exact analyticAt_const;
    · aesop;
    · filter_upwards [ hu.continuousAt.eventually_mem ( Complex.isOpen_slitPlane.mem_nhds hsl ) ] with z hz using by rw [ ← Complex.cpow_nat_mul, mul_comm ] ; norm_num [ hk.ne' ] ;
  · have h_neg_slit : -u z₀ ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hsl ⊢
      push Not at hsl
      simp only [Complex.neg_re, neg_pos]
      have : (u z₀).re ≠ 0 := by
        intro h
        apply hu0
        apply Complex.ext
        · exact h
        · exact hsl.2
      exact Or.inl (lt_of_le_of_ne hsl.1 this)
    obtain ⟨ω, hω⟩ : ∃ ω : ℂ, ω ^ k = -1 := by
      exact ⟨ ( -1 : ℂ ) ^ ( 1 / k : ℂ ), by rw [ ← Complex.cpow_nat_mul, mul_one_div_cancel ( Nat.cast_ne_zero.mpr hk.ne' ), Complex.cpow_one ] ⟩;
    refine ⟨ fun z => ω * ( -u z ) ^ ( 1 / k : ℂ ), ?_, ?_, ?_ ⟩
    · apply_rules [ AnalyticAt.mul, AnalyticAt.cpow, analyticAt_id, analyticAt_const ];
      exact hu.neg;
    · cases k <;> aesop;
    · filter_upwards [ hu.continuousAt.eventually ( Metric.ball_mem_nhds _ <| show 0 < ‖u z₀‖ by aesop ) ] with z hz ;
      simp only [mul_pow, ← Complex.cpow_nat_mul, hω, neg_mul, one_mul] ; norm_num [ hk.ne' ]

/-! ### Local normal form φ(z)^k -/

theorem exists_local_power_form (g : ℂ → ℂ) (z₀ : ℂ) (k : ℕ) (hk : 0 < k)
    (hg : AnalyticAt ℂ g z₀) (_hg0 : g z₀ = 0)
    (hord : analyticOrderNatAt g z₀ = k)
    (hord_ne_top : analyticOrderAt g z₀ ≠ ⊤) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ z₀ ∧ φ z₀ = 0 ∧ deriv φ z₀ ≠ 0 ∧
    ∀ᶠ z in 𝓝 z₀, g z = φ z ^ k := by
  obtain ⟨u, hu_analytic, hu_zero, hu_eq⟩ : ∃ u : ℂ → ℂ, AnalyticAt ℂ u z₀ ∧ u z₀ ≠ 0 ∧ ∀ᶠ z in nhds z₀, g z = (z - z₀)^k * u z := by
    convert AnalyticAt.analyticOrderNatAt_eq_iff hg hord_ne_top |>.1 hord;
  obtain ⟨ v, hv_analytic, hv_zero, hv_eq ⟩ := analyticAt_kthRoot k hk u z₀ hu_analytic hu_zero;
  refine ⟨ fun z => ( z - z₀ ) * v z, ?_, ?_, ?_, ?_ ⟩;
  · fun_prop;
  · grind +splitImp;
  · norm_num [ hv_analytic.differentiableAt, hv_zero ];
  · filter_upwards [ hu_eq, hv_eq ] with z hz₁ hz₂ using by rw [ hz₁, mul_pow, hz₂ ] ;

/-! ### Strengthened local biholomorphism -/

/-
An analytic function with nonzero derivative is a local biholomorphism
with nonzero derivative and analyticity everywhere on the domain.
-/
theorem exists_local_biholomorphism_strong (φ : ℂ → ℂ) (z₀ : ℂ)
    (hφ : AnalyticAt ℂ φ z₀) (hφ' : deriv φ z₀ ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧
    ∃ W : Set ℂ, IsOpen W ∧ φ z₀ ∈ W ∧
    InjOn φ U ∧
    W ⊆ φ '' U ∧
    (∀ z ∈ U, φ z ∈ W) ∧
    (∀ z ∈ U, AnalyticAt ℂ φ z) ∧
    (∀ z ∈ U, deriv φ z ≠ 0) := by
  -- By the inverse function theorem, there exists a neighborhood $U$ of $z_0$ such that $\varphi$ is a diffeomorphism from $U$ to $\varphi(U)$.
  obtain ⟨U, hU_open, hz₀_in_U, h_inj⟩ : ∃ U : (Set ℂ), IsOpen U ∧ z₀ ∈ U ∧ InjOn φ U ∧ (∀ z ∈ U, AnalyticAt ℂ φ z) ∧ (∀ z ∈ U, deriv φ z ≠ 0) := by
    obtain ⟨U, hU⟩ : ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ (∀ z ∈ U, AnalyticAt ℂ φ z) ∧ (∀ z ∈ U, deriv φ z ≠ 0) := by
      have h_cont : ContinuousAt (deriv φ) z₀ := by
        exact hφ.deriv.continuousAt;
      obtain ⟨U, hU⟩ : ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ (∀ z ∈ U, deriv φ z ≠ 0) := by
        exact Exists.imp ( by tauto ) ( mem_nhds_iff.mp ( h_cont.eventually_ne hφ' ) );
      exact ⟨ U ∩ { z | AnalyticAt ℂ φ z }, hU.1.inter ( isOpen_analyticAt ℂ φ ), ⟨ hU.2.1, hφ ⟩, fun z hz => hz.2, fun z hz => hU.2.2 z hz.1 ⟩;
    have h_inj : ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧ InjOn φ V := by
      have h_inv : HasStrictFDerivAt φ (fderiv ℂ φ z₀) z₀ := by
        exact hφ.hasStrictFDerivAt
      have := h_inv.isLittleO.tendsto_div_nhds_zero
      generalize_proofs at *;
      have := Metric.tendsto_nhds_nhds.1 this ( ‖deriv φ z₀‖ ) ( by simpa using hφ' );
      obtain ⟨ δ, δ_pos, H ⟩ := this; use Metric.ball z₀ δ ∩ U;
      simp only [Prod.forall, Prod.dist_eq, max_lt_iff, and_imp] at H
      refine ⟨ IsOpen.inter ( Metric.isOpen_ball ) hU.1, ⟨by simp [δ_pos], hU.2.1⟩, Set.inter_subset_right, fun x₁ hx₁ x₂ hx₂ h => Classical.not_not.1 fun hx => ?_ ⟩
      have h_ne : ‖x₁ - x₂‖ ≠ 0 := by
        rw [ne_eq, norm_eq_zero, sub_eq_zero]
        exact hx
      have h_lt : dist ((φ x₁ - φ x₂ - (fderiv ℂ φ z₀) (x₁ - x₂)) / (x₁ - x₂)) 0 = ‖deriv φ z₀‖ := by
        simp [h, h_ne]
      exact lt_irrefl _ (h_lt ▸ H x₁ x₂ hx₁.1 hx₂.1)
    generalize_proofs at *;
    exact ⟨ h_inj.choose, h_inj.choose_spec.1, h_inj.choose_spec.2.1, h_inj.choose_spec.2.2.2, fun z hz => hU.2.2.1 z ( h_inj.choose_spec.2.2.1 hz ), fun z hz => hU.2.2.2 z ( h_inj.choose_spec.2.2.1 hz ) ⟩;
  -- Since $\varphi$ is a diffeomorphism from $U$ to $\varphi(U)$, $\varphi(U)$ is open.
  have h_image_open : IsOpen (φ '' U) := by
    have h_image_open : ∀ z ∈ U, ∃ ε > 0, Metric.ball (φ z) ε ⊆ φ '' U := by
      intro z hz
      have h_image_open : AnalyticAt ℂ φ z ∧ deriv φ z ≠ 0 := by
        aesop;
      have := h_image_open.1.eventually_constant_or_nhds_le_map_nhds;
      rcases this with h | h;
      · exact False.elim <| h_image_open.2 <| HasDerivAt.deriv <| HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) h;
      · rw [ Filter.le_map_iff ] at h;
        exact Metric.mem_nhds_iff.mp ( h U ( hU_open.mem_nhds hz ) );
    exact Metric.isOpen_iff.mpr fun x hx => by rcases hx with ⟨ z, hz, rfl ⟩ ; obtain ⟨ ε, ε_pos, hε ⟩ := h_image_open z hz; exact ⟨ ε, ε_pos, hε ⟩ ;
  exact ⟨ U, hU_open, hz₀_in_U, φ '' U, h_image_open, Set.mem_image_of_mem _ hz₀_in_U, h_inj.1, Set.Subset.rfl, fun z hz => Set.mem_image_of_mem _ hz, h_inj.2.1, h_inj.2.2 ⟩

/-! ### Order of g(z)^k - c at a simple preimage -/

/-
If φ is analytic at z' with φ'(z') ≠ 0 and φ(z')^k = w ≠ 0,
then the function z ↦ φ(z)^k - w has order exactly 1 at z'.
-/

theorem analyticOrderNatAt_pow_sub_at_simple_root
    (φ : ℂ → ℂ) (z' : ℂ) (k : ℕ) (hk : 0 < k) (w : ℂ)
    (hφ : AnalyticAt ℂ φ z') (hφ' : deriv φ z' ≠ 0)
    (hroot : φ z' ^ k = w) (hw : w ≠ 0) :
    analyticOrderNatAt (fun z => φ z ^ k - w) z' = 1 := by
  have hg_nz : (fun z => ∑ i ∈ Finset.range k, φ z ^ i * φ z' ^ (k - 1 - i)) z' ≠ 0 := by
    dsimp
    have h_pow : ∀ i ∈ Finset.range k, φ z' ^ i * φ z' ^ (k - 1 - i) = φ z' ^ (k - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      exact add_tsub_cancel_of_le (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))
    rw [Finset.sum_congr rfl h_pow]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hk_ne : (k : ℂ) ≠ 0 := by exact Nat.cast_ne_zero.mpr (ne_of_gt hk)
    have hphi_ne : φ z' ≠ 0 := by
      intro h_zero
      rw [h_zero, zero_pow (ne_of_gt hk)] at hroot
      exact hw (hroot.symm)
    have hpow_ne : φ z' ^ (k - 1) ≠ 0 := by
      exact pow_ne_zero (k - 1) hphi_ne
    exact mul_ne_zero hk_ne hpow_ne

  have h_order : analyticOrderNatAt (fun z => (φ z - φ z') * (∑ i ∈ Finset.range k, φ z ^ i * φ z' ^ (k - 1 - i))) z' = analyticOrderNatAt (fun z => φ z - φ z') z' + analyticOrderNatAt (fun z => ∑ i ∈ Finset.range k, φ z ^ i * φ z' ^ (k - 1 - i)) z' := by
    apply_rules [ analyticOrderNatAt_mul ];
    · exact hφ.sub ( analyticAt_const );
    · fun_prop;
    · rw [hφ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hφ']; exact ENat.one_ne_top
    · have hg_eq : analyticOrderAt (fun z => ∑ i ∈ Finset.range k, φ z ^ i * φ z' ^ (k - 1 - i)) z' = 0 := by
        exact analyticOrderAt_eq_zero.mpr (Or.inr hg_nz)
      rw [hg_eq]
      exact ENat.zero_ne_top

  have h_order_zero : analyticOrderNatAt (fun z => ∑ i ∈ Finset.range k, φ z ^ i * φ z' ^ (k - 1 - i)) z' = 0 := by
    unfold analyticOrderNatAt
    have hg_eq : analyticOrderAt (fun z => ∑ i ∈ Finset.range k, φ z ^ i * φ z' ^ (k - 1 - i)) z' = 0 := by
      exact analyticOrderAt_eq_zero.mpr (Or.inr hg_nz)
    rw [hg_eq]
    rfl

  convert h_order using 1
  · congr! 2
    rw [← hroot, mul_comm, geom_sum₂_mul]
  · rw [h_order_zero, add_zero]
    unfold analyticOrderNatAt
    rw [hφ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hφ']
    rfl

/-! ### Assembly -/

/-
**Local mapping theorem for analytic functions ℂ → ℂ.**
If `g` is analytic at `z₀` with `g(z₀) = 0` and order `k ≥ 1`,
then nearby nonzero values have exactly `k` simple preimages near `z₀`.
-/

theorem analytic_local_mapping_theorem (g : ℂ → ℂ) (z₀ : ℂ) (k : ℕ) (hk : 0 < k)
    {N : Set ℂ} (hN_open : IsOpen N) (hz₀N : z₀ ∈ N)
    (hg : AnalyticAt ℂ g z₀) (hg0 : g z₀ = 0)
    (hord : analyticOrderNatAt g z₀ = k)
    (hord_ne_top : analyticOrderAt g z₀ ≠ ⊤) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧
    U ⊆ N ∧
    ∃ V : Set ℂ, IsOpen V ∧ (0 : ℂ) ∈ V ∧
    ∀ w ∈ V, w ≠ 0 →
    ∃ S : Finset ℂ, S.card = k ∧ ↑S ⊆ U ∧
      (∀ z' ∈ S, g z' = w ∧ analyticOrderNatAt (fun z => g z - w) z' = 1) ∧
      (∀ z' ∈ U, g z' = w → z' ∈ S) := by
  -- By exists_local_power_form, get φ analytic at z₀ with φ(z₀) = 0, φ'(z₀) ≠ 0, and g =ᶠ φ^k near z₀.
  obtain ⟨φ, hφ, hφ'⟩ : ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ z₀ ∧ φ z₀ = 0 ∧ deriv φ z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, g z = φ z ^ k := by
    exact exists_local_power_form g z₀ k hk hg hg0 hord hord_ne_top;
  obtain ⟨U, hU, hU'⟩ : ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ N ∧ InjOn φ U ∧ (∀ z ∈ U, AnalyticAt ℂ φ z) ∧ (∀ z ∈ U, deriv φ z ≠ 0) ∧ ∀ z ∈ U, g z = φ z ^ k := by
      have := exists_local_biholomorphism_strong φ z₀ hφ hφ'.2.1;
      obtain ⟨ U, hU₁, hU₂, W, hW₁, hW₂, hW₃, hW₄, hW₅, hW₆, hW₇ ⟩ := this; rcases Metric.mem_nhds_iff.mp hφ'.2.2 with ⟨ ε, ε_pos, hε ⟩ ; exact ⟨ (U ∩ Metric.ball z₀ ε) ∩ N, (hU₁.inter ( Metric.isOpen_ball )).inter hN_open, ⟨⟨ hU₂, Metric.mem_ball_self ε_pos ⟩, hz₀N⟩, Set.inter_subset_right, hW₃.mono <| (Set.inter_subset_left.trans Set.inter_subset_left), fun z hz => hW₆ z hz.1.1, fun z hz => hW₇ z hz.1.1, fun z hz => hε <| Metric.mem_ball.mpr <| by aesop ⟩ ;
  obtain ⟨V, hV, hV'⟩ : ∃ V : Set ℂ, IsOpen V ∧ φ z₀ ∈ V ∧ V ⊆ φ '' U ∧ (∀ w ∈ V, ∃ z ∈ U, φ z = w) := by
    have h_image : IsOpen (φ '' U) := by
      apply_rules [ isOpen_iff_mem_nhds.mpr ];
      rintro _ ⟨ x, hx, rfl ⟩;
      have h_image : AnalyticAt ℂ φ x := by
        exact hU'.2.2.2.1 x hx;
      have := h_image.eventually_constant_or_nhds_le_map_nhds;
      rcases this with h | h;
      · have h_const : ∀ᶠ z in 𝓝 x, deriv φ z = 0 := by
          rw [ eventually_nhds_iff ] at *;
          obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := h; exact ⟨ t, fun y hy => HasDerivAt.deriv ( by exact HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) ( Filter.eventuallyEq_of_mem ( IsOpen.mem_nhds ht₂ hy ) fun z hz => ht₁ z hz ) ), ht₂, ht₃ ⟩ ;
        exact absurd ( h_const.self_of_nhds ) ( hU'.2.2.2.2.1 x hx );
      · exact h ( Filter.mem_map.mpr <| Filter.mem_of_superset ( hU.mem_nhds hx ) <| Set.subset_preimage_image _ _ );
    exact ⟨ φ '' U, h_image, Set.mem_image_of_mem φ hU'.1, Set.Subset.refl _, fun w hw => hw ⟩;
  obtain ⟨ε, hε⟩ : ∃ ε > 0, Metric.ball 0 ε ⊆ V := by
    exact Metric.isOpen_iff.mp hV 0 ( by aesop );
  refine ⟨ U, hU, hU'.1, hU'.2.1, Metric.ball 0 ( ε ^ k ), Metric.isOpen_ball, ?_, ?_ ⟩
  · rw [ Metric.mem_ball, dist_self ]
    exact pow_pos hε.1 k
  · intro w hw hw'
    obtain ⟨S, hS⟩ : ∃ S : Finset ℂ, S.card = k ∧ (∀ t ∈ S, t ^ k = w) ∧ (∀ t, t ^ k = w → t ∈ S) := by
      exact card_roots_pow_eq k hk w hw'
    -- For each $t \in S$, there exists $z_t \in U$ such that $\varphi(z_t) = t$.
    obtain ⟨z, hz⟩ : ∃ z : ℂ → ℂ, (∀ t ∈ S, z t ∈ U ∧ φ (z t) = t) ∧ (∀ t₁ t₂, t₁ ∈ S → t₂ ∈ S → t₁ ≠ t₂ → z t₁ ≠ z t₂) := by
      have hz : ∀ t ∈ S, ∃ z ∈ U, φ z = t := by
        intros t ht
        have ht_norm : ‖t‖ < ε := by
          have := hS.2.1 t ht
          have hw'' : ‖w‖ < ε ^ k := by rwa [mem_ball_zero_iff] at hw
          exact pow_root_in_ball k hk ε hε.1 t w this hw''
        exact hV'.2.2 t ( hε.2 ( mem_ball_zero_iff.mpr ht_norm ) )
      choose! z hz using hz
      exact ⟨ z, hz, fun t₁ t₂ ht₁ ht₂ hne h => hne <| by have := hz t₁ ht₁; have := hz t₂ ht₂; aesop ⟩
    refine ⟨ Finset.image z S, ?_, ?_, ?_, ?_ ⟩
    · rw [ Finset.card_image_of_injOn fun t₁ ht₁ t₂ ht₂ h => by contrapose! h; exact hz.2 t₁ t₂ ht₁ ht₂ h, hS.1 ]
    · rw [ Finset.coe_image, Set.image_subset_iff ]
      exact fun t ht => (hz.1 t ht).1
    · intro x hx
      rw [ Finset.mem_image ] at hx
      obtain ⟨ t, ht, rfl ⟩ := hx
      have h_gt : g (z t) = w := by rw [ hU'.2.2.2.2.2 (z t) (hz.1 t ht).1, (hz.1 t ht).2, hS.2.1 t ht ]
      refine ⟨ h_gt, ?_ ⟩
      have h_congr : (fun z => g z - w) =ᶠ[𝓝 (z t)] (fun z => φ z ^ k - w) := by
        filter_upwards [ IsOpen.mem_nhds hU (hz.1 t ht).1 ] with y hy
        rw [ hU'.2.2.2.2.2 y hy ]
      unfold analyticOrderNatAt
      rw [ analyticOrderAt_congr h_congr ]
      exact analyticOrderNatAt_pow_sub_at_simple_root φ (z t) k hk w
        (hU'.2.2.2.1 (z t) (hz.1 t ht).1) (hU'.2.2.2.2.1 (z t) (hz.1 t ht).1)
        (by rw [ (hz.1 t ht).2, hS.2.1 t ht ]) hw'
    · intro z' hz' hz''
      rw [ Finset.mem_image ]
      have h_root : φ z' ^ k = w := by rw [ ← hU'.2.2.2.2.2 z' hz', hz'' ]
      have h_mem : φ z' ∈ S := hS.2.2 (φ z') h_root
      use φ z', h_mem
      exact hU'.2.2.1 (hz.1 (φ z') h_mem).1 hz' (hz.1 (φ z') h_mem).2

end Jacobians.Vendor.Wallace.HolomorphicForms.AnalyticLocalMapping
