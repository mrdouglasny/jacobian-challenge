/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.MeromorphicFunctionField

/-!
# The Riemann-Roch space `L(D)`

This file anchors the textbook Riemann-Roch space attached to a divisor.  For
Forster, *Lectures on Riemann Surfaces*, §16, this is
`L(D) = H^0(X, O(D))`: meromorphic functions `f` satisfying `div(f) + D ≥ 0`.

The bridge to the `H0` API lives downstream in `LineBundle.lean`, where `H0`
is definitionally identified with this space.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

open scoped Manifold Topology ContDiff

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- An effective divisor is a formal integer combination of points whose
coefficients are all nonnegative.  This is the coefficientwise positivity
predicate on `Divisor X = FreeAbelianGroup X`, the positivity condition used in
Forster, *Lectures on Riemann Surfaces*, §16 for `L(D) = H^0(X, O(D))`. -/
def Effective (D : Divisor X) : Prop :=
  ∀ p : X, 0 ≤ FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)

@[simp]
theorem effective_zero : Effective (0 : Divisor X) := by
  intro p
  simp

@[simp]
theorem effective_of (p : X) : Effective (FreeAbelianGroup.of p : Divisor X) := by
  classical
  intro q
  change 0 ≤ FreeAbelianGroup.toFinsupp (FreeAbelianGroup.of p) q
  by_cases h : q = p
  · subst q
    simp
  · simp [h]

theorem Effective.add {D E : Divisor X} (hD : Effective D) (hE : Effective E) :
    Effective (D + E) := by
  intro p
  simpa using add_nonneg (hD p) (hE p)

@[simp]
theorem meromorphicAtX_zero (p : X) :
    MeromorphicAtX (0 : X → ℂ) p := by
  simpa [MeromorphicAtX, Function.comp_def] using
    (MeromorphicAt.const (0 : ℂ) ((extChartAt 𝓘(ℂ) p) p))

@[simp]
theorem orderAt_zero (p : X) :
    orderAt p (0 : X → ℂ) = ⊤ := by
  rw [orderAt]
  simpa [Function.comp_def] using
    (meromorphicOrderAt_const ((extChartAt 𝓘(ℂ) p) p) (0 : ℂ))

theorem MeromorphicAtX.add {f g : X → ℂ} {p : X}
    (hf : MeromorphicAtX f p) (hg : MeromorphicAtX g p) :
    MeromorphicAtX (f + g) p := by
  simpa [MeromorphicAtX, Function.comp_def, Pi.add_apply] using hf.add hg

theorem min_le_orderAt_add {f g : X → ℂ} {p : X}
    (hf : MeromorphicAtX f p) (hg : MeromorphicAtX g p) :
    min (orderAt p f) (orderAt p g) ≤ orderAt p (f + g) := by
  simpa [orderAt, Function.comp_def, Pi.add_apply] using
    (meromorphicOrderAt_add hf hg)

theorem MeromorphicAtX.const_smul (c : ℂ) {f : X → ℂ} {p : X}
    (hf : MeromorphicAtX f p) :
    MeromorphicAtX (c • f) p := by
  have hc : MeromorphicAt (fun _ : ℂ => c) ((extChartAt 𝓘(ℂ) p) p) :=
    MeromorphicAt.const c ((extChartAt 𝓘(ℂ) p) p)
  simpa [MeromorphicAtX, Function.comp_def, Pi.smul_apply, smul_eq_mul] using
    hc.smul hf

theorem orderAt_const_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (p : X) (f : X → ℂ) :
    orderAt p (c • f) = orderAt p f := by
  have hconst : AnalyticAt ℂ (fun _ : ℂ => c) ((extChartAt 𝓘(ℂ) p) p) :=
    analyticAt_const
  simpa [orderAt, Function.comp_def, Pi.smul_apply, smul_eq_mul] using
    (meromorphicOrderAt_smul_of_ne_zero
      (x := (extChartAt 𝓘(ℂ) p) p)
      (g := fun _ : ℂ => c)
      (f := f ∘ (extChartAt 𝓘(ℂ) p).symm) hconst hc)

/-- Adding a function whose germ is zero at `p` does not change the Wallace order at `p`. -/
theorem orderAt_add_of_orderAt_eq_top {f g : X → ℂ} {p : X}
    (hg : orderAt p g = ⊤) :
    orderAt p (f + g) = orderAt p f := by
  unfold orderAt at hg ⊢
  simpa [Function.comp_def, Pi.add_apply] using
    (meromorphicOrderAt_add_of_top_right
      (f₁ := f ∘ (extChartAt 𝓘(ℂ) p).symm)
      (f₂ := g ∘ (extChartAt 𝓘(ℂ) p).symm)
      (x := (extChartAt 𝓘(ℂ) p) p) hg)

/-- Raw functions that are meromorphic at every point of `X`. -/
def MeroFunctions (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X] :
    Submodule ℂ (X → ℂ) where
  carrier :=
    { f : X → ℂ | ∀ p : X, MeromorphicAtX f p }
  zero_mem' := by
    exact meromorphicAtX_zero
  add_mem' := by
    intro f g hf hg p
    exact (hf p).add (hg p)
  smul_mem' := by
    intro c f hf p
    exact MeromorphicAtX.const_smul c (hf p)

/-- Germ-zero global meromorphic functions: representatives whose order is `⊤` everywhere. -/
def GermZero (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X] :
    Submodule ℂ (MeroFunctions X) where
  carrier :=
    { f : MeroFunctions X | ∀ p : X, orderAt p (f : X → ℂ) = ⊤ }
  zero_mem' := by
    intro p
    simpa using (orderAt_zero (X := X) p)
  add_mem' := by
    intro f g hf hg p
    have hle :
        (⊤ : WithTop ℤ) ≤ orderAt p ((f + g : MeroFunctions X) : X → ℂ) := by
      simpa [hf p, hg p] using
        (min_le_orderAt_add (f.property p) (g.property p))
    exact top_le_iff.mp hle
  smul_mem' := by
    intro c f hf p
    by_cases hc : c = 0
    · subst c
      simpa using (orderAt_zero (X := X) p)
    · simpa [orderAt_const_smul_of_ne_zero hc p (f : X → ℂ)] using hf p

/-- The additive vector space of meromorphic functions modulo germ-zero representatives. -/
abbrev MeroField (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X] : Type u :=
  MeroFunctions X ⧸ GermZero X

theorem orderAt_eq_of_sub_mem_germZero {f g : MeroFunctions X}
    (hfg : f - g ∈ GermZero X) (p : X) :
    orderAt p (f : X → ℂ) = orderAt p (g : X → ℂ) := by
  have htop : orderAt p ((f - g : MeroFunctions X) : X → ℂ) = ⊤ := hfg p
  have horder :
      orderAt p ((g : X → ℂ) + ((f - g : MeroFunctions X) : X → ℂ)) =
        orderAt p (g : X → ℂ) :=
    orderAt_add_of_orderAt_eq_top (f := (g : X → ℂ))
      (g := ((f - g : MeroFunctions X) : X → ℂ)) htop
  have hfun :
      (g : X → ℂ) + ((f - g : MeroFunctions X) : X → ℂ) = (f : X → ℂ) := by
    ext x
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  simpa [hfun] using horder

/-- Wallace order on the germ quotient. -/
def orderAtField (p : X) : MeroField X → WithTop ℤ :=
  Quotient.lift
    (fun f : MeroFunctions X => orderAt p (f : X → ℂ))
    (by
      intro f g hfg
      exact orderAt_eq_of_sub_mem_germZero
        ((Submodule.quotientRel_def (p := GermZero X)).mp hfg) p)

@[simp]
theorem orderAtField_mk (p : X) (f : MeroFunctions X) :
    orderAtField p (Submodule.Quotient.mk f : MeroField X) =
      orderAt p (f : X → ℂ) :=
  rfl

theorem min_le_orderAtField_add (p : X) (F G : MeroField X) :
    min (orderAtField p F) (orderAtField p G) ≤ orderAtField p (F + G) := by
  refine Submodule.Quotient.induction_on (GermZero X) F ?_
  intro f
  refine Submodule.Quotient.induction_on (GermZero X) G ?_
  intro g
  simpa using (min_le_orderAt_add (f.property p) (g.property p))

theorem orderAtField_const_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (p : X)
    (F : MeroField X) :
    orderAtField p (c • F) = orderAtField p F := by
  refine Submodule.Quotient.induction_on (GermZero X) F ?_
  intro f
  simpa using (orderAt_const_smul_of_ne_zero hc p (f : X → ℂ))

/-- A raw point-spike function. It is nonzero as a function, but zero as a meromorphic germ. -/
def pointSpike (p : X) : X → ℂ :=
  by
    classical
    exact fun x => if x = p then 1 else 0

theorem pointSpike_eventuallyEq_zero_chart (p q : X) :
    (pointSpike p ∘ (chartAt ℂ q).symm) =ᶠ[𝓝[≠] (chartAt ℂ q q)] 0 := by
  by_cases hq : q = p
  · subst q
    let e := chartAt ℂ p
    have htarget : e.target ∈ 𝓝 (e p) := chart_target_mem_nhds ℂ p
    filter_upwards [Filter.mem_inf_of_left htarget, self_mem_nhdsWithin] with z hz_target hz_ne
    change pointSpike p (e.symm z) = 0
    have hne : e.symm z ≠ p := by
      intro hsymm
      have hz_eq : z = e p := by
        calc
          z = e (e.symm z) := (e.right_inv hz_target).symm
          _ = e p := by rw [hsymm]
      exact hz_ne hz_eq
    classical
    simp [pointSpike, hne]
  · have hcompl : ({p} : Set X)ᶜ ∈ 𝓝 q := compl_singleton_mem_nhds hq
    have hzeroX : ∀ᶠ x in 𝓝 q, pointSpike p x = 0 :=
      Filter.mem_of_superset hcompl (by
        intro x hx
        classical
        have hxne : x ≠ p := by
          simpa using hx
        change (if x = p then (1 : ℂ) else 0) = 0
        rw [if_neg hxne])
    have hzeroChart :
        ∀ᶠ z in 𝓝 (chartAt ℂ q q), pointSpike p ((chartAt ℂ q).symm z) = 0 := by
      simpa using
        (((chartAt ℂ q).eventually_nhds' (fun x => pointSpike p x = 0)
          (mem_chart_source ℂ q)).2 hzeroX)
    exact eventually_nhdsWithin_of_eventually_nhds hzeroChart

theorem orderAt_pointSpike (p q : X) :
    orderAt q (pointSpike p) = ⊤ := by
  rw [orderAt_eq_chartAt]
  exact meromorphicOrderAt_eq_top_iff.mpr (pointSpike_eventuallyEq_zero_chart p q)

theorem meromorphicAtX_pointSpike (p q : X) :
    MeromorphicAtX (pointSpike p) q := by
  exact meromorphicAt_of_meromorphicOrderAt_ne_zero (by
    change orderAt q (pointSpike p) ≠ 0
    rw [orderAt_pointSpike]
    simp)

/-- The point-spike lies in the germ-zero submodule. -/
theorem pointSpike_mem_germZero (p : X) :
    (⟨pointSpike p, meromorphicAtX_pointSpike p⟩ : MeroFunctions X) ∈ GermZero X := by
  intro q
  exact orderAt_pointSpike p q

/-- The point-spike is killed by the germ quotient. -/
theorem pointSpike_mk_eq_zero (p : X) :
    (Submodule.Quotient.mk
      (⟨pointSpike p, meromorphicAtX_pointSpike p⟩ : MeroFunctions X) : MeroField X) = 0 :=
  (Submodule.Quotient.mk_eq_zero (GermZero X)).2 (pointSpike_mem_germZero p)

/-- The point-spike is not the zero raw function. -/
theorem pointSpike_ne_zero (p : X) :
    pointSpike p ≠ (0 : X → ℂ) := by
  intro h
  have hp := congr_fun h p
  classical
  simpa [pointSpike] using hp

/-- `GermZero` is nontrivial as a submodule of raw meromorphic functions; this is why
`MeroField` quotients by it before defining `L(D)`. -/
theorem germZero_ne_bot (p : X) :
    GermZero X ≠ (⊥ : Submodule ℂ (MeroFunctions X)) := by
  intro hbot
  have hmem : (⟨pointSpike p, meromorphicAtX_pointSpike p⟩ : MeroFunctions X) ∈
      (⊥ : Submodule ℂ (MeroFunctions X)) := by
    simpa [hbot] using pointSpike_mem_germZero (X := X) p
  have hzero :
      (⟨pointSpike p, meromorphicAtX_pointSpike p⟩ : MeroFunctions X) = 0 := by
    simpa using hmem
  apply pointSpike_ne_zero (X := X) p
  exact congr_arg Subtype.val hzero

/-- The Riemann-Roch space `L(D)` on the germ quotient:
`L(D) = { f meromorphic on X | div(f) + D ≥ 0 } = H^0(X, O(D))` in the
textbook notation of Forster, *Lectures on Riemann Surfaces*, §16.  With the
Wallace convention, the condition is `ord_p(f) ≥ -coeff_p(D)` for every point,
and the zero germ is included because its order is `⊤`. -/
def riemannRochSpace (D : Divisor X) : Submodule ℂ (MeroField X) where
  carrier :=
    { F : MeroField X |
      ∀ p : X,
        ((-(FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)) : ℤ) : WithTop ℤ) ≤
          orderAtField p F }
  zero_mem' := by
    intro p
    rw [show (0 : MeroField X) =
        Submodule.Quotient.mk (0 : MeroFunctions X) from rfl, orderAtField_mk]
    change
      ((-(FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)) : ℤ) : WithTop ℤ) ≤
        orderAt p (0 : X → ℂ)
    rw [orderAt_zero]
    exact le_top
  add_mem' := by
    intro F G hF hG p
    exact (le_min (hF p) (hG p)).trans (min_le_orderAtField_add p F G)
  smul_mem' := by
    intro c F hF
    by_cases hc : c = 0
    · subst c
      intro p
      rw [zero_smul]
      rw [show (0 : MeroField X) =
          Submodule.Quotient.mk (0 : MeroFunctions X) from rfl, orderAtField_mk]
      change
        ((-(FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)) : ℤ) : WithTop ℤ) ≤
          orderAt p (0 : X → ℂ)
      rw [orderAt_zero]
      exact le_top
    · intro p
      rw [orderAtField_const_smul_of_ne_zero hc p F]
      exact hF p

end Jacobians.RiemannSurface
