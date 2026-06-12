/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.MeromorphicToP1
import Jacobians.RiemannSurface.GenusInvariance
import Jacobians.ProjectiveCurve.Line.Genus
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Degree-one meromorphic functions force genus zero

This file proves the genus obstruction used in the `ofCurve` injectivity
discharge: on a positive-genus compact Riemann surface, no nonzero
meromorphic function can have principal divisor `(Q₁) - (Q₂)` with
`Q₁ ≠ Q₂`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open scoped Manifold Topology ContDiff BigOperators
open Filter Function Set

open Jacobians.Axioms
open Jacobians.ProjectiveCurve
open Jacobians.Vendor.Wallace.HolomorphicForms

namespace Jacobians.RiemannSurface

namespace MeromorphicFunctionField

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

private theorem coeff_divisor (f : MeromorphicFunctionField X) (p : X) :
    FreeAbelianGroup.coeff p (divisor f : FreeAbelianGroup X) =
      (orderAtMF p f).untop₀ := by
  refine Quotient.inductionOn f ?_
  intro f
  simpa [divisor, orderAtMF] using Rep.divisor_coeff f p

private theorem orderAtMF_ne_top (f : MeromorphicFunctionField X) (p : X) :
    orderAtMF p f ≠ ⊤ := by
  refine Quotient.inductionOn f ?_
  intro f
  simpa [orderAtMF] using f.order_ne_top p

private theorem withTop_eq_coe_of_untop₀_eq {a : WithTop ℤ} {n : ℤ}
    (ha : a ≠ ⊤) (h : a.untop₀ = n) : a = (n : WithTop ℤ) := by
  rw [← WithTop.coe_untop₀_of_ne_top ha]
  exact congrArg (fun z : ℤ => (z : WithTop ℤ)) h

private theorem pointSub_coeff_left {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂) :
    FreeAbelianGroup.coeff Q₁
      ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X)) = 1 := by
  classical
  simp [FreeAbelianGroup.coeff, hne]

private theorem pointSub_coeff_right {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂) :
    FreeAbelianGroup.coeff Q₂
      ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X)) = -1 := by
  classical
  simp [FreeAbelianGroup.coeff, hne]

private theorem pointSub_coeff_of_ne {Q₁ Q₂ p : X} (hp₁ : p ≠ Q₁) (hp₂ : p ≠ Q₂) :
    FreeAbelianGroup.coeff p
      ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X)) = 0 := by
  classical
  simp [FreeAbelianGroup.coeff, hp₁, hp₂]

private theorem orderAtMF_eq_of_divisor_eq {f : MeromorphicFunctionField X}
    {D : Divisor X} (hdiv : divisor f = D) {p : X} {n : ℤ}
    (hcoeff : FreeAbelianGroup.coeff p (D : FreeAbelianGroup X) = n) :
    orderAtMF p f = (n : WithTop ℤ) := by
  apply withTop_eq_coe_of_untop₀_eq (orderAtMF_ne_top f p)
  rw [← coeff_divisor f p, hdiv, hcoeff]

private theorem divisor_eq_of_divHom_eq {f : MeromorphicFunctionField X} {D : Divisor X}
    (hdiv : divHom f = Multiplicative.ofAdd D) : divisor f = D :=
  Multiplicative.ofAdd.injective hdiv

private theorem orderAtMF_left_of_divHom_eq {f : MeromorphicFunctionField X} {Q₁ Q₂ : X}
    (hne : Q₁ ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    orderAtMF Q₁ f = (1 : WithTop ℤ) :=
  orderAtMF_eq_of_divisor_eq (divisor_eq_of_divHom_eq hdiv) (pointSub_coeff_left hne)

private theorem orderAtMF_right_of_divHom_eq {f : MeromorphicFunctionField X} {Q₁ Q₂ : X}
    (hne : Q₁ ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    orderAtMF Q₂ f = ((-1 : ℤ) : WithTop ℤ) :=
  orderAtMF_eq_of_divisor_eq (divisor_eq_of_divHom_eq hdiv) (pointSub_coeff_right hne)

private theorem orderAtMF_of_ne_of_divHom_eq {f : MeromorphicFunctionField X} {Q₁ Q₂ p : X}
    (hp₁ : p ≠ Q₁) (hp₂ : p ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    orderAtMF p f = (0 : WithTop ℤ) :=
  orderAtMF_eq_of_divisor_eq (divisor_eq_of_divHom_eq hdiv)
    (pointSub_coeff_of_ne hp₁ hp₂)

private theorem toP1_infty_fiber_eq_singleton {f : MeromorphicFunctionField X} {Q₁ Q₂ : X}
    (hne : Q₁ ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    (toP1 f ⁻¹' ({(OnePoint.infty : ProjectiveLine)} : Set ProjectiveLine)) =
      ({Q₂} : Set X) := by
  ext p
  constructor
  · intro hp
    have hpole : orderAtMF p f < 0 := (toP1_eq_infty_iff f p).1 (by simpa using hp)
    by_cases hp₂ : p = Q₂
    · exact hp₂
    by_cases hp₁ : p = Q₁
    · subst p
      exfalso
      have horder : orderAtMF Q₁ f = (1 : WithTop ℤ) :=
        orderAtMF_left_of_divHom_eq hne hdiv
      rw [horder] at hpole
      exact (not_lt_of_ge (show (0 : WithTop ℤ) ≤ (1 : WithTop ℤ) by norm_num)) hpole
    · exfalso
      have horder : orderAtMF p f = (0 : WithTop ℤ) :=
        orderAtMF_of_ne_of_divHom_eq hp₁ hp₂ hdiv
      rw [horder] at hpole
      exact (lt_irrefl (0 : WithTop ℤ)) hpole
  · intro hp
    have hpQ₂ : p = Q₂ := by simpa using hp
    subst p
    apply (toP1_eq_infty_iff f Q₂).2
    have horder : orderAtMF Q₂ f = ((-1 : ℤ) : WithTop ℤ) :=
      orderAtMF_right_of_divHom_eq hne hdiv
    rw [horder]
    exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)

private theorem toP1_infty_weightedFiberSum_eq_one {f : MeromorphicFunctionField X}
    {Q₁ Q₂ : X} (hne : Q₁ ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    (toP1_infty_fiber_finite f).toFinset.sum (mapAnalyticOrderAt (toP1 f)) = 1 := by
  have hfiber := toP1_infty_fiber_eq_singleton (f := f) hne hdiv
  have hfinset : (toP1_infty_fiber_finite f).toFinset = {Q₂} := by
    apply Finset.ext
    intro p
    simpa [Set.Finite.mem_toFinset, hfiber]
  rw [toP1_infty_weightedFiberSum, hfinset]
  rw [Finset.sum_singleton, orderAtMF_right_of_divHom_eq hne hdiv]
  change ((1 : ℤ).toNat = 1)
  norm_num

private theorem toP1_finite_fiber (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) :
    ∀ y : ProjectiveLine, (toP1 f ⁻¹' {y}).Finite := by
  have htop : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) (toP1 f) :=
    toP1_contMDiff f
  have hhol : IsHolomorphic (toP1 f) :=
    isHolomorphic_of_contMDiff htop (hasLocalKfoldRamification_of_contMDiff htop)
  intro y
  exact isHolomorphic_finite_fiber hhol (toP1_nonconst hf) y

private theorem weightedFiberSum_constant_toP1 (f : MeromorphicFunctionField X)
    (hf : Nonconstant f) :
    ∃ finite_fiber : ∀ y : ProjectiveLine, (toP1 f ⁻¹' {y}).Finite,
      ∀ y : ProjectiveLine,
        (finite_fiber y).toFinset.sum (mapAnalyticOrderAt (toP1 f)) =
          (finite_fiber (OnePoint.infty : ProjectiveLine)).toFinset.sum
            (mapAnalyticOrderAt (toP1 f)) := by
  classical
  let finite_fiber : ∀ y : ProjectiveLine, (toP1 f ⁻¹' {y}).Finite :=
    toP1_finite_fiber f hf
  refine ⟨finite_fiber, ?_⟩
  let Φ : ProjectiveLine → ℕ :=
    fun y => (finite_fiber y).toFinset.sum (mapAnalyticOrderAt (toP1 f))
  have htop : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) (toP1 f) :=
    toP1_contMDiff f
  have hloc : IsLocallyConstant Φ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro y₀
    have hev : ∀ᶠ y in 𝓝 y₀, Φ y = Φ y₀ := by
      simpa [Φ, finite_fiber] using
        weightedFiberConservation_of_contMDiff
          (f := toP1 f) htop (toP1_nonconst hf) finite_fiber y₀
    rcases mem_nhds_iff.mp (Filter.eventually_iff.mp hev) with
      ⟨U, hUsub, hUopen, hy₀U⟩
    exact ⟨U, hUopen, hy₀U, fun y hyU => hUsub hyU⟩
  intro y
  exact (LocallyConstant.apply_eq_of_preconnectedSpace
    (⟨Φ, hloc⟩ : LocallyConstant ProjectiveLine ℕ) y
    (OnePoint.infty : ProjectiveLine))

private theorem weightedFiberSum_one_toP1 {f : MeromorphicFunctionField X} {Q₁ Q₂ : X}
    (hf : Nonconstant f) (hne : Q₁ ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    ∃ finite_fiber : ∀ y : ProjectiveLine, (toP1 f ⁻¹' {y}).Finite,
      ∀ y : ProjectiveLine,
        (finite_fiber y).toFinset.sum (mapAnalyticOrderAt (toP1 f)) = 1 := by
  obtain ⟨finite_fiber, hconst⟩ := weightedFiberSum_constant_toP1 f hf
  refine ⟨finite_fiber, ?_⟩
  have hfinset_infty :
      (finite_fiber (OnePoint.infty : ProjectiveLine)).toFinset =
        (toP1_infty_fiber_finite f).toFinset := by
    apply Finset.ext
    intro p
    simp [Set.Finite.mem_toFinset]
  have hinfty :
      (finite_fiber (OnePoint.infty : ProjectiveLine)).toFinset.sum
        (mapAnalyticOrderAt (toP1 f)) = 1 := by
    rw [hfinset_infty]
    exact toP1_infty_weightedFiberSum_eq_one (f := f) hne hdiv
  intro y
  rw [hconst y, hinfty]

private theorem finset_sum_eq_one_singleton {α : Type*} {s : Finset α} {w : α → ℕ}
    (hpos : ∀ x ∈ s, 0 < w x) (hsum : s.sum w = 1) :
    ∃ x, s = {x} ∧ w x = 1 := by
  have hcard_le_sum : s.card ≤ s.sum w := by
    have hconst : s.card = s.sum (fun _ : α => (1 : ℕ)) := by simp
    rw [hconst]
    exact Finset.sum_le_sum fun x hx => hpos x hx
  rw [hsum] at hcard_le_sum
  have hne : s.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  have hcard : s.card = 1 := le_antisymm hcard_le_sum hne.card_pos
  rw [Finset.card_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  refine ⟨x, hx, ?_⟩
  rw [hx, Finset.sum_singleton] at hsum
  exact hsum

private theorem toP1_bijective_of_weightedFiberSum_one {f : MeromorphicFunctionField X}
    (hf : Nonconstant f)
    (finite_fiber : ∀ y : ProjectiveLine, (toP1 f ⁻¹' {y}).Finite)
    (hsum : ∀ y : ProjectiveLine,
      (finite_fiber y).toFinset.sum (mapAnalyticOrderAt (toP1 f)) = 1) :
    Function.Bijective (toP1 f) ∧ ∀ x : X, mapAnalyticOrderAt (toP1 f) x = 1 := by
  have htop : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) (toP1 f) :=
    toP1_contMDiff f
  have hpos : ∀ x : X, 0 < mapAnalyticOrderAt (toP1 f) x :=
    fun x => mapAnalyticOrderAt_pos_of_contMDiff htop (toP1_nonconst hf) x
  have hsingle : ∀ y : ProjectiveLine,
      ∃ x, (finite_fiber y).toFinset = {x} ∧ mapAnalyticOrderAt (toP1 f) x = 1 := by
    intro y
    exact finset_sum_eq_one_singleton
      (fun x _hx => hpos x) (hsum y)
  constructor
  · constructor
    · intro x₁ x₂ heq
      obtain ⟨x, hxfin, _hxord⟩ := hsingle (toP1 f x₁)
      have hx₁ : x₁ = x := by
        have hmem : x₁ ∈ (finite_fiber (toP1 f x₁)).toFinset := by
          rw [Set.Finite.mem_toFinset]
          rfl
        rw [hxfin, Finset.mem_singleton] at hmem
        exact hmem
      have hx₂ : x₂ = x := by
        have hmem : x₂ ∈ (finite_fiber (toP1 f x₁)).toFinset := by
          rw [Set.Finite.mem_toFinset]
          exact heq.symm
        rw [hxfin, Finset.mem_singleton] at hmem
        exact hmem
      rw [hx₁, hx₂]
    · intro y
      obtain ⟨x, hxfin, _hxord⟩ := hsingle y
      have hmem : x ∈ (finite_fiber y).toFinset := by
        rw [hxfin]
        exact Finset.mem_singleton_self x
      rw [Set.Finite.mem_toFinset] at hmem
      exact ⟨x, hmem⟩
  · intro x
    obtain ⟨x₀, hxfin, hxord⟩ := hsingle (toP1 f x)
    have hxmem : x ∈ (finite_fiber (toP1 f x)).toFinset := by
      rw [Set.Finite.mem_toFinset]
      rfl
    rw [hxfin, Finset.mem_singleton] at hxmem
    rwa [hxmem]

private theorem IsHolomorphicAt.localInverse_eventually_right_inverse
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {F : X → Y} {p : X} (hF : IsHolomorphicAt F p)
    (hcont : ContinuousAt F p)
    (hderiv : deriv (chartLocalAt F p) (chartAt ℂ p p) ≠ 0) :
    (fun y => F (hF.localInverse hderiv y)) =ᶠ[𝓝 (F p)] id := by
  let r : ℂ → ℂ :=
    hF.hasStrictDerivAt.localInverse (chartLocalAt F p)
      (deriv (chartLocalAt F p) (chartAt ℂ p p)) (chartAt ℂ p p) hderiv
  have hFp : chartLocalAt F p (chartAt ℂ p p) = chartAt ℂ (F p) (F p) := by
    simp [chartLocalAt]
  have hleft_r : r (chartAt ℂ (F p) (F p)) = chartAt ℂ p p := by
    dsimp [r]
    rw [← hFp]
    exact (HasStrictDerivAt.eventually_left_inverse
      (f := chartLocalAt F p)
      (f' := deriv (chartLocalAt F p) (chartAt ℂ p p))
      (a := chartAt ℂ p p) (hf := hF.hasStrictDerivAt)
      (hf' := hderiv)).self_of_nhds
  have hright_chart :
      ∀ᶠ z in 𝓝 (chartAt ℂ (F p) (F p)), chartLocalAt F p (r z) = z := by
    have h := HasStrictDerivAt.eventually_right_inverse
      (f := chartLocalAt F p)
      (f' := deriv (chartLocalAt F p) (chartAt ℂ p p))
      (a := chartAt ℂ p p) (hf := hF.hasStrictDerivAt)
      (hf' := hderiv)
    simpa [r, hFp] using h
  have hr_an : AnalyticAt ℂ r (chartAt ℂ (F p) (F p)) := by
    have h := hF.analyticAt_localInverse hderiv
    simpa [r, hFp] using h
  have hr_tendsto : Tendsto r (𝓝 (chartAt ℂ (F p) (F p))) (𝓝 (chartAt ℂ p p)) := by
    have hcont_r := hr_an.continuousAt
    change Tendsto r (𝓝 (chartAt ℂ (F p) (F p))) (𝓝 (r (chartAt ℂ (F p) (F p)))) at hcont_r
    simpa [hleft_r] using hcont_r
  have hchartY_tendsto :
      Tendsto (fun y : Y => chartAt ℂ (F p) y) (𝓝 (F p))
        (𝓝 (chartAt ℂ (F p) (F p))) :=
    (chartAt ℂ (F p)).continuousAt (mem_chart_source ℂ (F p))
  have htargetX :
      ∀ᶠ y in 𝓝 (F p), r (chartAt ℂ (F p) y) ∈ (chartAt ℂ p).target := by
    exact (hr_tendsto.comp hchartY_tendsto).eventually (chart_target_mem_nhds ℂ p)
  have hlinv_tendsto : Tendsto (hF.localInverse hderiv) (𝓝 (F p)) (𝓝 p) := by
    unfold IsHolomorphicAt.localInverse
    have hsymm_tendsto :
        Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p)) (𝓝 p) := by
      have hcont_symm := (chartAt ℂ p).continuousAt_symm
        ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
      change Tendsto (fun z => (chartAt ℂ p).symm z) (𝓝 (chartAt ℂ p p))
        (𝓝 ((chartAt ℂ p).symm (chartAt ℂ p p))) at hcont_symm
      simpa [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)] using hcont_symm
    exact hsymm_tendsto.comp (hr_tendsto.comp hchartY_tendsto)
  have hFy_source :
      ∀ᶠ y in 𝓝 (F p), F (hF.localInverse hderiv y) ∈ (chartAt ℂ (F p)).source := by
    exact (Tendsto.comp hcont hlinv_tendsto).eventually
      ((chartAt ℂ (F p)).open_source.mem_nhds (mem_chart_source ℂ (F p)))
  have hy_source : ∀ᶠ y in 𝓝 (F p), y ∈ (chartAt ℂ (F p)).source :=
    (chartAt ℂ (F p)).open_source.mem_nhds (mem_chart_source ℂ (F p))
  have hright_y :
      ∀ᶠ y in 𝓝 (F p), chartLocalAt F p (r (chartAt ℂ (F p) y)) =
        chartAt ℂ (F p) y :=
    hchartY_tendsto.eventually hright_chart
  filter_upwards [htargetX, hFy_source, hy_source, hright_y] with y hrt hFsrc hysrc hchart
  apply (chartAt ℂ (F p)).injOn hFsrc hysrc
  change chartAt ℂ (F p) (F ((chartAt ℂ p).symm (r (chartAt ℂ (F p) y)))) =
    chartAt ℂ (F p) y
  simpa [chartLocalAt, Function.comp_def, (chartAt ℂ p).right_inv hrt] using hchart

private theorem deriv_ne_zero_of_mapAnalyticOrderAt_eq_one
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {F : X → Y} {p : X} (hF : IsHolomorphicAt F p)
    (horder : mapAnalyticOrderAt F p = 1) :
    deriv (chartLocalAt F p) (chartAt ℂ p p) ≠ 0 := by
  let z₀ : ℂ := chartAt ℂ p p
  let G : ℂ → ℂ := fun z => chartLocalAt F p z - chartLocalAt F p z₀
  have hG_an : AnalyticAt ℂ G z₀ := hF.sub analyticAt_const
  have hG_order_nat : analyticOrderNatAt G z₀ = 1 := by
    simpa [mapAnalyticOrderAt, G, z₀] using horder
  have hG_ne_top : analyticOrderAt G z₀ ≠ ⊤ := by
    intro htop
    have hzero : analyticOrderNatAt G z₀ = 0 := by
      simp [analyticOrderNatAt, htop]
    omega
  have hG_order : analyticOrderAt G z₀ = (1 : ℕ∞) := by
    have hcast := Nat.cast_analyticOrderNatAt (f := G) (z₀ := z₀) hG_ne_top
    rw [hG_order_nat] at hcast
    simpa using hcast.symm
  have hder_order : analyticOrderAt (deriv G) z₀ = (0 : ℕ∞) := by
    simpa using (analyticOrderAt_deriv_of_pos (hf := hG_an) (n := 0) hG_order)
  have hderG_ne : deriv G z₀ ≠ 0 := by
    have hz := analyticOrderAt_eq_zero.mp hder_order
    rcases hz with hnot | hne
    · exact False.elim (hnot hG_an.deriv)
    · exact hne
  simpa [G] using hderG_ne

private theorem inverse_contMDiff_of_bijective_order_one
    {F : X → ProjectiveLine}
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) F)
    (hbij : Function.Bijective F)
    (horder : ∀ x : X, mapAnalyticOrderAt F x = 1) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) ((Equiv.ofBijective F hbij).symm) := by
  let e : X ≃ ProjectiveLine := Equiv.ofBijective F hbij
  let homeo : X ≃ₜ ProjectiveLine :=
    e.toHomeomorphOfContinuousClosed hF.continuous hF.continuous.isClosedMap
  have hcont_inv : Continuous (e.symm : ProjectiveLine → X) := by
    change Continuous homeo.symm
    exact homeo.symm.continuous
  have hholo_inv : ∀ y : ProjectiveLine, IsHolomorphicAt (e.symm : ProjectiveLine → X) y := by
    intro y
    let x : X := e.symm y
    have hy : y = F x := by
      change y = e x
      exact (e.apply_symm_apply y).symm
    have hFx : IsHolomorphicAt F x := IsHolomorphicAt.of_contMDiff hF x
    have hderiv : deriv (chartLocalAt F x) (chartAt ℂ x x) ≠ 0 :=
      deriv_ne_zero_of_mapAnalyticOrderAt_eq_one hFx (horder x)
    have hlocal_holo : IsHolomorphicAt (hFx.localInverse hderiv) (F x) :=
      hFx.localInverse_isHolomorphicAt hderiv
    have heq : hFx.localInverse hderiv =ᶠ[𝓝 (F x)] (e.symm : ProjectiveLine → X) := by
      have hright :=
        IsHolomorphicAt.localInverse_eventually_right_inverse
          hFx hF.continuous.continuousAt hderiv
      filter_upwards [hright] with y' hy'
      apply hbij.1
      calc
        F (hFx.localInverse hderiv y') = y' := hy'
        _ = F (e.symm y') := by
          change y' = e (e.symm y')
          exact (e.apply_symm_apply y').symm
    rw [hy]
    exact hlocal_holo.congr_of_eventuallyEq heq
  simpa [e] using
    ContMDiff.of_isHolomorphic_and_continuous hholo_inv hcont_inv

/-- A nonconstant meromorphic function with principal divisor `(Q₁) - (Q₂)`
for `Q₁ ≠ Q₂` gives a biholomorphism to `ℙ¹`: the underlying equivalence,
analytic in both directions. -/
theorem degreeOne_equiv_projectiveLine {f : MeromorphicFunctionField X} {Q₁ Q₂ : X}
    (hf : Nonconstant f) (hne : Q₁ ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    ∃ e : X ≃ ProjectiveLine,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) (e : X → ProjectiveLine) ∧
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) (e.symm : ProjectiveLine → X) := by
  obtain ⟨finite_fiber, hsum⟩ := weightedFiberSum_one_toP1 hf hne hdiv
  obtain ⟨hbij, horder⟩ := toP1_bijective_of_weightedFiberSum_one hf finite_fiber hsum
  refine ⟨Equiv.ofBijective (toP1 f) hbij, ?_, ?_⟩
  · simpa using (toP1_contMDiff f :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) (toP1 f))
  · simpa using
      inverse_contMDiff_of_bijective_order_one
        (F := toP1 f)
        (toP1_contMDiff f :
          ContMDiff 𝓘(ℂ) 𝓘(ℂ) (⊤ : WithTop ℕ∞) (toP1 f))
        hbij horder

/-- A nonconstant meromorphic function with principal divisor `(Q₁) - (Q₂)`
for `Q₁ ≠ Q₂` gives a biholomorphism to `ℙ¹`, hence the source has genus
zero. -/
theorem degreeOne_genus_zero {f : MeromorphicFunctionField X} {Q₁ Q₂ : X}
    (hf : Nonconstant f) (hne : Q₁ ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    genus X = 0 := by
  obtain ⟨e, he, he_symm⟩ := degreeOne_equiv_projectiveLine hf hne hdiv
  calc
    genus X = genus ProjectiveLine := genus_eq_of_biholo e he he_symm
    _ = 0 := ProjectiveCurve.genus_projectiveLine_eq_zero

private theorem nonconstant_of_divHom_eq_pointSub {f : MeromorphicFunctionField X} {Q₁ Q₂ : X}
    (hne : Q₁ ≠ Q₂)
    (hdiv : divHom f =
      Multiplicative.ofAdd
        ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X))) :
    Nonconstant f := by
  intro hconst
  obtain ⟨y₀, hy₀⟩ := hconst
  have hQ₂_infty : toP1 f Q₂ = (OnePoint.infty : ProjectiveLine) := by
    apply (toP1_eq_infty_iff f Q₂).2
    rw [orderAtMF_right_of_divHom_eq hne hdiv]
    exact_mod_cast (show (-1 : ℤ) < 0 by norm_num)
  have hQ₁_not_infty : toP1 f Q₁ ≠ (OnePoint.infty : ProjectiveLine) := by
    intro hQ₁
    have hpole : orderAtMF Q₁ f < 0 := (toP1_eq_infty_iff f Q₁).1 hQ₁
    rw [orderAtMF_left_of_divHom_eq hne hdiv] at hpole
    exact (not_lt_of_ge (show (0 : WithTop ℤ) ≤ (1 : WithTop ℤ) by norm_num)) hpole
  have hsame : toP1 f Q₁ = toP1 f Q₂ := by
    rw [hy₀ Q₁, hy₀ Q₂]
  exact hQ₁_not_infty (hsame.trans hQ₂_infty)

end MeromorphicFunctionField

open MeromorphicFunctionField

/-- Positive genus forbids a principal divisor of the form `(Q₁) - (Q₂)` unless
the two points coincide. -/
theorem principal_imp_eq_of_genus_pos
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]
    (hgenus : 0 < genus X) (Q₁ Q₂ : X)
    (hprincipal :
      ((FreeAbelianGroup.of Q₁ - FreeAbelianGroup.of Q₂ : FreeAbelianGroup X) : Divisor X)
        ∈ PrincipalDivisors X) :
    Q₁ = Q₂ := by
  by_contra hne
  rw [PrincipalDivisors] at hprincipal
  rcases hprincipal with ⟨f, hdiv⟩
  have hnonconst : MeromorphicFunctionField.Nonconstant f :=
    MeromorphicFunctionField.nonconstant_of_divHom_eq_pointSub hne hdiv
  have hzero : genus X = 0 :=
    MeromorphicFunctionField.degreeOne_genus_zero hnonconst hne hdiv
  omega

end Jacobians.RiemannSurface
