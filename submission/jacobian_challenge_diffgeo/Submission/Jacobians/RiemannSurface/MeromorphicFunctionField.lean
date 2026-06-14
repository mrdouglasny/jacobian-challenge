/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Submission.Jacobians.RiemannSurface.Divisor
import Submission.Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# Global meromorphic functions and their divisors

This file gives the first real meromorphic-function layer for compact connected
Riemann surfaces.  A global meromorphic function is represented by an ordinary
function `X → ℂ` together with pointwise Wallace meromorphy and finite
Wallace order everywhere.  The actual field carrier quotients these
representatives by equality on every punctured chart neighborhood; this is the
standard way to avoid depending on arbitrary values at zeros and poles.

The divisor homomorphism records the finite formal sum of Wallace orders.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

open scoped Manifold Topology ContDiff
open Filter Function Set Topology

namespace Jacobians.RiemannSurface

open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- A bundled representative of a nonzero global meromorphic function.

The field `order_ne_top` is the germ-level nonzero condition.  It rules out the
zero meromorphic function and also makes the inverse law true after quotienting
by punctured-chart equality.
-/
structure MeromorphicFunctionField.Rep (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X] where
  toFun : X → ℂ
  meromorphicAt : ∀ p : X, MeromorphicAtX toFun p
  order_ne_top : ∀ p : X, orderAt p toFun ≠ ⊤

namespace MeromorphicFunctionField

namespace Rep

instance : CoeFun (Rep X) (fun _ => X → ℂ) := ⟨Rep.toFun⟩

@[ext]
theorem ext {f g : Rep X} (h : (f : X → ℂ) = g) : f = g := by
  cases f
  cases g
  simp_all

/-- Representatives are equivalent when they agree in every punctured
coordinate neighborhood. -/
def Rel (f g : Rep X) : Prop :=
  ∀ p : X,
    (f : X → ℂ) ∘ (chartAt ℂ p).symm =ᶠ[𝓝[≠] (chartAt ℂ p p)]
      (g : X → ℂ) ∘ (chartAt ℂ p).symm

theorem rel_refl (f : Rep X) : Rel f f := fun _ => EventuallyEq.rfl

theorem rel_symm {f g : Rep X} (h : Rel f g) : Rel g f := fun p => (h p).symm

theorem rel_trans {f g h : Rep X} (hfg : Rel f g) (hgh : Rel g h) :
    Rel f h := fun p => (hfg p).trans (hgh p)

instance setoid : Setoid (Rep X) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

theorem rel_orderAt {f g : Rep X} (h : Rel f g) (p : X) :
    orderAt p (f : X → ℂ) = orderAt p (g : X → ℂ) :=
  by
    rw [orderAt_eq_chartAt p (f : X → ℂ), orderAt_eq_chartAt p (g : X → ℂ)]
    exact meromorphicOrderAt_congr (h p)

theorem meromorphicAt_mul (f g : Rep X) (p : X) :
    MeromorphicAtX (fun x => f x * g x) p := by
  simpa [MeromorphicAtX, Function.comp_def] using
    (f.meromorphicAt p).mul (g.meromorphicAt p)

theorem meromorphicAt_inv (f : Rep X) (p : X) :
    MeromorphicAtX (fun x => (f x)⁻¹) p := by
  simpa [MeromorphicAtX, Function.comp_def] using (f.meromorphicAt p).fun_inv

theorem meromorphicAt_one (p : X) :
    MeromorphicAtX (fun _ : X => (1 : ℂ)) p := by
  simpa [MeromorphicAtX, Function.comp_def] using
    (MeromorphicAt.const (1 : ℂ) ((extChartAt 𝓘(ℂ) p) p))

theorem orderAt_mul (f g : Rep X) (p : X) :
    orderAt p (fun x => f x * g x) =
      orderAt p (f : X → ℂ) + orderAt p (g : X → ℂ) := by
  simpa [orderAt, Function.comp_def] using
    meromorphicOrderAt_mul (f.meromorphicAt p) (g.meromorphicAt p)

theorem orderAt_inv (f : Rep X) (p : X) :
    orderAt p (fun x => (f x)⁻¹) = -orderAt p (f : X → ℂ) := by
  simpa [orderAt, Function.comp_def] using
    (meromorphicOrderAt_inv (f := (f : X → ℂ) ∘ (extChartAt 𝓘(ℂ) p).symm)
      (x := (extChartAt 𝓘(ℂ) p) p))

theorem orderAt_one (p : X) :
    orderAt p (fun _ : X => (1 : ℂ)) = 0 := by
  rw [orderAt]
  simpa [Function.comp_def] using
    (meromorphicOrderAt_const ((extChartAt 𝓘(ℂ) p) p) (1 : ℂ))

private theorem add_ne_top_of_ne_top {a b : WithTop ℤ} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a + b ≠ ⊤ := by
  cases a <;> cases b <;> simp_all

private theorem neg_ne_top_of_ne_top {a : WithTop ℤ} (ha : a ≠ ⊤) : -a ≠ ⊤ := by
  cases a <;> simp_all

theorem orderAt_mul_ne_top (f g : Rep X) (p : X) :
    orderAt p (fun x => f x * g x) ≠ ⊤ := by
  rw [orderAt_mul f g p]
  exact add_ne_top_of_ne_top (f.order_ne_top p) (g.order_ne_top p)

theorem orderAt_inv_ne_top (f : Rep X) (p : X) :
    orderAt p (fun x => (f x)⁻¹) ≠ ⊤ := by
  rw [orderAt_inv f p]
  exact neg_ne_top_of_ne_top (f.order_ne_top p)

theorem orderAt_one_ne_top (p : X) :
    orderAt p (fun _ : X => (1 : ℂ)) ≠ ⊤ := by
  rw [orderAt_one p]
  simp

/-- The constant-one representative. -/
def one : Rep X where
  toFun := fun _ => 1
  meromorphicAt := meromorphicAt_one
  order_ne_top := orderAt_one_ne_top

/-- Pointwise product of representatives. -/
def mul (f g : Rep X) : Rep X where
  toFun := fun x => f x * g x
  meromorphicAt := meromorphicAt_mul f g
  order_ne_top := orderAt_mul_ne_top f g

/-- Pointwise reciprocal of a representative. -/
def inv (f : Rep X) : Rep X where
  toFun := fun x => (f x)⁻¹
  meromorphicAt := meromorphicAt_inv f
  order_ne_top := orderAt_inv_ne_top f

theorem rel_mul {f₁ f₂ g₁ g₂ : Rep X} (hf : Rel f₁ f₂) (hg : Rel g₁ g₂) :
    Rel (mul f₁ g₁) (mul f₂ g₂) := by
  intro p
  filter_upwards [hf p, hg p] with z hfz hgz
  change ((f₁ : X → ℂ) ∘ (chartAt ℂ p).symm) z *
      ((g₁ : X → ℂ) ∘ (chartAt ℂ p).symm) z =
    ((f₂ : X → ℂ) ∘ (chartAt ℂ p).symm) z *
      ((g₂ : X → ℂ) ∘ (chartAt ℂ p).symm) z
  rw [hfz, hgz]

theorem rel_inv {f g : Rep X} (h : Rel f g) : Rel (inv f) (inv g) := by
  intro p
  filter_upwards [h p] with z hz
  change (((f : X → ℂ) ∘ (chartAt ℂ p).symm) z)⁻¹ =
    (((g : X → ℂ) ∘ (chartAt ℂ p).symm) z)⁻¹
  rw [hz]

theorem rel_one_mul (f : Rep X) : Rel (mul one f) f := by
  intro p
  filter_upwards [] with z
  simp [one, mul, Function.comp_def]

theorem rel_mul_one (f : Rep X) : Rel (mul f one) f := by
  intro p
  filter_upwards [] with z
  simp [one, mul, Function.comp_def]

theorem rel_mul_assoc (f g h : Rep X) :
    Rel (mul (mul f g) h) (mul f (mul g h)) := by
  intro p
  filter_upwards [] with z
  simp [mul, Function.comp_def, mul_assoc]

theorem rel_mul_comm (f g : Rep X) : Rel (mul f g) (mul g f) := by
  intro p
  filter_upwards [] with z
  simp [mul, Function.comp_def, mul_comm]

theorem eventually_ne_zero_chart (f : Rep X) (p : X) :
    ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p),
      ((f : X → ℂ) ∘ (chartAt ℂ p).symm) z ≠ 0 := by
  have h :
      ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ) p p),
        ((f : X → ℂ) ∘ (extChartAt 𝓘(ℂ) p).symm) z ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (f.meromorphicAt p)).1
      (f.order_ne_top p)
  rwa [extChartAt_eq_chartAt p, extChartAt_symm_eq_chartAt_symm p] at h

theorem rel_inv_mul (f : Rep X) : Rel (mul (inv f) f) one := by
  intro p
  filter_upwards [eventually_ne_zero_chart f p] with z hz
  change (((f : X → ℂ) ∘ (chartAt ℂ p).symm) z)⁻¹ *
      (((f : X → ℂ) ∘ (chartAt ℂ p).symm) z) = 1
  exact inv_mul_cancel₀ hz

/-- The other inverse law, useful for readability even though commutativity
would also imply it. -/
theorem rel_mul_inv (f : Rep X) : Rel (mul f (inv f)) one := by
  intro p
  filter_upwards [eventually_ne_zero_chart f p] with z hz
  change (((f : X → ℂ) ∘ (chartAt ℂ p).symm) z) *
      (((f : X → ℂ) ∘ (chartAt ℂ p).symm) z)⁻¹ = 1
  exact mul_inv_cancel₀ hz

theorem rel_orderCoeff {f g : Rep X} (h : Rel f g) :
    (fun p : X => (orderAt p (f : X → ℂ)).untop₀) =
      fun p : X => (orderAt p (g : X → ℂ)).untop₀ := by
  funext p
  rw [rel_orderAt h p]

/-- Local finiteness of the nonzero order function for a representative. -/
theorem orderCoeff_locallyFiniteSupport (f : Rep X) :
    LocallyFiniteSupport
      (fun p : X => (orderAt p (f : X → ℂ)).untop₀) := by
  intro x
  let e := chartAt ℂ x
  let F : ℂ → ℂ := (f : X → ℂ) ∘ e.symm
  let D := MeromorphicOn.divisor F e.target
  have hF : MeromorphicOn F e.target :=
    meromorphicOn_chart_pullback_of_meromorphicAtX f.meromorphicAt x
  have hx_source : x ∈ e.source := mem_chart_source ℂ x
  have hx_target : e x ∈ e.target := e.map_source hx_source
  obtain ⟨u, hu_mem, hu_fin⟩ := D.supportLocallyFiniteWithinDomain (e x) hx_target
  refine ⟨e.source ∩ e ⁻¹' u, ?_, ?_⟩
  · have hu_pre : e ⁻¹' u ∈ 𝓝 x := by
      simpa [Filter.mem_map] using e.continuousAt hx_source hu_mem
    exact Filter.inter_mem (e.open_source.mem_nhds hx_source) hu_pre
  · let S : Set X :=
      (e.source ∩ e ⁻¹' u) ∩ Function.support
        (fun p : X => (orderAt p (f : X → ℂ)).untop₀)
    have h_image_subset : e '' S ⊆ u ∩ D.support := by
      rintro y ⟨p, hpS, rfl⟩
      rcases hpS with ⟨⟨hp_source, hp_u⟩, hp_support⟩
      constructor
      · exact hp_u
      · have hp_target : e p ∈ e.target := e.map_source hp_source
        have h_order :
            orderAt p (f : X → ℂ) = meromorphicOrderAt F (e p) := by
          simpa [e, F] using
            orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas (p := p)
              (f : X → ℂ) e (IsManifold.chart_mem_maximalAtlas x) hp_source
        have h_ne_zero : meromorphicOrderAt F (e p) ≠ 0 := by
          have h_support :
              meromorphicOrderAt F (e p) ≠ 0 ∧ meromorphicOrderAt F (e p) ≠ ⊤ := by
            simpa [h_order, Function.mem_support, WithTop.untop₀_eq_zero] using hp_support
          exact h_support.1
        have h_ne_top : meromorphicOrderAt F (e p) ≠ ⊤ := by
          simpa [h_order] using f.order_ne_top p
        have h_coeff_ne : (meromorphicOrderAt F (e p)).untop₀ ≠ 0 := by
          intro hzero
          apply h_ne_zero
          rw [← WithTop.coe_untop₀_of_ne_top h_ne_top, hzero]
          rfl
        simpa [D, MeromorphicOn.divisor_apply hF hp_target, Function.mem_support] using
          h_coeff_ne
    have h_image_fin : (e '' S).Finite := hu_fin.subset h_image_subset
    have h_inj : InjOn e S := by
      intro a ha b hb hab
      calc
        a = e.symm (e a) := (e.left_inv ha.1.1).symm
        _ = e.symm (e b) := by rw [hab]
        _ = b := e.left_inv hb.1.1
    · exact h_image_fin.of_finite_image h_inj

theorem orderCoeff_support_finite (f : Rep X) :
    (Function.support fun p : X => (orderAt p (f : X → ℂ)).untop₀).Finite := by
  have h := (orderCoeff_locallyFiniteSupport f).finite_inter_support_of_isCompact
    (W := (Set.univ : Set X)) isCompact_univ
  simpa using h

/-- A nonzero global meromorphic representative has finitely many nonzero
Wallace orders. -/
theorem orderSupport_finite (f : Rep X) :
    {p : X | orderAt p (f : X → ℂ) ≠ 0}.Finite := by
  have h_eq :
      Function.support (fun p : X => (orderAt p (f : X → ℂ)).untop₀) =
        {p : X | orderAt p (f : X → ℂ) ≠ 0} := by
    ext p
    constructor
    · intro hp hzero
      exact hp (by simp [hzero])
    · intro hp hcoeff
      apply hp
      rw [← WithTop.coe_untop₀_of_ne_top (f.order_ne_top p)]
      exact_mod_cast hcoeff
  simpa [h_eq] using orderCoeff_support_finite f

/-- The finite-order coefficient function as a `Finsupp`. -/
def orderFinsupp (f : Rep X) : X →₀ ℤ :=
  Finsupp.ofSupportFinite
    (fun p : X => (orderAt p (f : X → ℂ)).untop₀)
    (orderCoeff_support_finite f)

@[simp]
theorem orderFinsupp_apply (f : Rep X) (p : X) :
    orderFinsupp f p = (orderAt p (f : X → ℂ)).untop₀ := by
  rw [orderFinsupp, Finsupp.ofSupportFinite_coe]

/-- The divisor of a representative as a formal integer sum of points. -/
def divisor (f : Rep X) : Divisor X :=
  Finsupp.toFreeAbelianGroup (orderFinsupp f)

@[simp]
theorem divisor_coeff (f : Rep X) (p : X) :
    FreeAbelianGroup.coeff p (divisor f : FreeAbelianGroup X) =
      (orderAt p (f : X → ℂ)).untop₀ := by
  simp [divisor, FreeAbelianGroup.coeff]

theorem divisor_congr {f g : Rep X} (h : Rel f g) : divisor f = divisor g := by
  apply (FreeAbelianGroup.equivFinsupp X).injective
  ext p
  simp [divisor, orderFinsupp, Finsupp.ofSupportFinite_coe, rel_orderAt h p]

theorem orderAt_mul_untop₀ (f g : Rep X) (p : X) :
    (orderAt p (mul f g : X → ℂ)).untop₀ =
      (orderAt p (f : X → ℂ)).untop₀ + (orderAt p (g : X → ℂ)).untop₀ := by
  change (orderAt p (fun x => f x * g x)).untop₀ =
    (orderAt p (f : X → ℂ)).untop₀ + (orderAt p (g : X → ℂ)).untop₀
  rw [orderAt_mul f g p]
  have hf_ne_top := f.order_ne_top p
  have hg_ne_top := g.order_ne_top p
  cases hf : orderAt p (f : X → ℂ) <;> cases hg : orderAt p (g : X → ℂ) <;> simp_all

theorem divisor_mul (f g : Rep X) : divisor (mul f g) = divisor f + divisor g := by
  apply (FreeAbelianGroup.equivFinsupp X).injective
  ext p
  simp [divisor, orderFinsupp, Finsupp.ofSupportFinite_coe, orderAt_mul_untop₀ f g p]

theorem divisor_one : divisor (one : Rep X) = 0 := by
  apply (FreeAbelianGroup.equivFinsupp X).injective
  ext p
  simp [divisor, orderFinsupp, Finsupp.ofSupportFinite_coe, one, orderAt_one]

end Rep

end MeromorphicFunctionField

/-- The group of nonzero global meromorphic functions on `X`.

Elements are represented by `Rep X` but quotiented by equality in every
punctured coordinate neighborhood, so arbitrary values at zeros and poles do
not affect equality.
-/
def MeromorphicFunctionField (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ⊤ X] : Type _ :=
  Quotient (MeromorphicFunctionField.Rep.setoid (X := X))

namespace MeromorphicFunctionField

instance : One (MeromorphicFunctionField X) :=
  ⟨Quotient.mk (Rep.setoid (X := X)) Rep.one⟩

instance : Mul (MeromorphicFunctionField X) where
  mul :=
    Quotient.lift₂
      (fun f g : Rep X => Quotient.mk (Rep.setoid (X := X)) (Rep.mul f g))
      (by
        intro f₁ f₂ g₁ g₂ hf hg
        exact Quotient.sound (Rep.rel_mul hf hg))

instance : Inv (MeromorphicFunctionField X) where
  inv :=
    Quotient.lift
      (fun f : Rep X => Quotient.mk (Rep.setoid (X := X)) (Rep.inv f))
      (by
        intro f g h
        exact Quotient.sound (Rep.rel_inv h))

instance : CommGroup (MeromorphicFunctionField X) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  mul_assoc := by
    intro a b c
    refine Quotient.inductionOn₃ a b c ?_
    intro f g h
    exact Quotient.sound (Rep.rel_mul_assoc f g h)
  one_mul := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    exact Quotient.sound (Rep.rel_one_mul f)
  mul_one := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    exact Quotient.sound (Rep.rel_mul_one f)
  inv_mul_cancel := by
    intro a
    refine Quotient.inductionOn a ?_
    intro f
    exact Quotient.sound (Rep.rel_inv_mul f)
  mul_comm := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro f g
    exact Quotient.sound (Rep.rel_mul_comm f g)

/-- Wallace order of a meromorphic-function-field element at a point. -/
def orderAtMF (p : X) : MeromorphicFunctionField X → WithTop ℤ :=
  Quotient.lift
    (fun f : Rep X => orderAt p (f : X → ℂ))
    (by
      intro f g h
      exact Rep.rel_orderAt h p)

/-- A nonzero global meromorphic function has finite zero/pole support. -/
theorem orderSupport_finite (f : MeromorphicFunctionField X) :
    {p : X | orderAtMF p f ≠ 0}.Finite := by
  refine Quotient.inductionOn f ?_
  intro f
  simpa [orderAtMF] using Rep.orderSupport_finite f

/-- Divisor of a meromorphic-function-field element. -/
def divisor : MeromorphicFunctionField X → Divisor X :=
  Quotient.lift Rep.divisor (by
    intro f g h
    exact Rep.divisor_congr h)

@[simp]
theorem divisor_one : divisor (X := X) 1 = 0 := by
  exact Rep.divisor_one

theorem divisor_mul (f g : MeromorphicFunctionField X) :
    divisor (f * g) = divisor f + divisor g := by
  refine Quotient.inductionOn₂ f g ?_
  intro f g
  exact Rep.divisor_mul f g

/-- The principal-divisor homomorphism from nonzero meromorphic functions to
the additive divisor group, viewed multiplicatively in the codomain. -/
def divHom : MeromorphicFunctionField X →* Multiplicative (Divisor X) where
  toFun f := Multiplicative.ofAdd (divisor f)
  map_one' := by
    simp [divisor_one]
  map_mul' f g := by
    simp [divisor_mul f g]

end MeromorphicFunctionField

end Jacobians.RiemannSurface

namespace Jacobians.Axioms

open scoped Manifold Topology ContDiff
open Jacobians.RiemannSurface

/-- The subgroup of principal divisors: divisors of nonzero global
meromorphic functions. Kernel of the divisor-to-Jacobian map (Abel's theorem).

This is the additive subgroup corresponding to the multiplicative range of
`MeromorphicFunctionField.divHom`. -/
def PrincipalDivisors (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : AddSubgroup (Divisor X) :=
  Subgroup.toAddSubgroup'
    (MonoidHom.range (MeromorphicFunctionField.divHom (X := X)))

end Jacobians.Axioms
