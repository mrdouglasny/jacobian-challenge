/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace
import Mathlib.Data.Set.Finite.Basic

/-!
# Weil repartitions on a compact Riemann surface

This file introduces the algebraic adele/repartition layer used by Weil and
Serre on curves.  A repartition is a choice of a meromorphic germ-quotient
element at every point whose entries are integral at all but finitely many
places.
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

/-- The coefficient of a divisor at a point, in the `FreeAbelianGroup`
encoding used by `Divisor`. -/
def divisorCoeff (D : Divisor X) (p : X) : ℤ :=
  FreeAbelianGroup.coeff p (D : FreeAbelianGroup X)

/-- A Weil repartition: all but finitely many entries have nonnegative
valuation/order. -/
def IsRepartition (r : X → MeroField X) : Prop :=
  {p : X | ¬ (0 : WithTop ℤ) ≤ orderAtField p (r p)}.Finite

@[simp]
theorem orderAtField_zero (p : X) :
    orderAtField p (0 : MeroField X) = ⊤ := by
  rw [show (0 : MeroField X) =
      Submodule.Quotient.mk (0 : MeroFunctions X) from rfl, orderAtField_mk]
  exact orderAt_zero (X := X) p

@[simp]
theorem isRepartition_zero :
    IsRepartition (0 : X → MeroField X) := by
  simp [IsRepartition]

theorem isRepartition_add {r s : X → MeroField X}
    (hr : IsRepartition r) (hs : IsRepartition s) :
    IsRepartition (r + s) := by
  classical
  refine (hr.union hs).subset ?_
  intro p hp
  by_contra hp_union
  have hrp : (0 : WithTop ℤ) ≤ orderAtField p (r p) := by
    by_contra hbad
    exact hp_union (Or.inl hbad)
  have hsp : (0 : WithTop ℤ) ≤ orderAtField p (s p) := by
    by_contra hbad
    exact hp_union (Or.inr hbad)
  have hadd : (0 : WithTop ℤ) ≤ orderAtField p ((r + s) p) := by
    exact (le_min hrp hsp).trans
      (by
        simpa [Pi.add_apply] using min_le_orderAtField_add p (r p) (s p))
  exact hp hadd

theorem isRepartition_smul (c : ℂ) {r : X → MeroField X}
    (hr : IsRepartition r) :
    IsRepartition (c • r) := by
  classical
  by_cases hc : c = 0
  · subst c
    simpa using (isRepartition_zero (X := X))
  · refine hr.subset ?_
    intro p hp
    simpa [Pi.smul_apply, orderAtField_const_smul_of_ne_zero hc p (r p)] using hp

/-- The `ℂ`-submodule of Weil repartitions. -/
def repartitions (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X] :
    Submodule ℂ (X → MeroField X) where
  carrier := {r : X → MeroField X | IsRepartition r}
  zero_mem' := by
    exact isRepartition_zero (X := X)
  add_mem' := by
    intro r s hr hs
    exact isRepartition_add hr hs
  smul_mem' := by
    intro c r hr
    exact isRepartition_smul c hr

/-- Repartitions bounded by a divisor `D`, i.e. the algebraic adeles
`𝔸_X(D) = {r | ord_p(r_p) >= -D(p)}`. -/
def repartitionsBounded (D : Divisor X) : Submodule ℂ (X → MeroField X) where
  carrier :=
    {r : X → MeroField X |
      IsRepartition r ∧
        ∀ p : X,
          ((-(divisorCoeff D p) : ℤ) : WithTop ℤ) ≤ orderAtField p (r p)}
  zero_mem' := by
    constructor
    · exact isRepartition_zero (X := X)
    · intro p
      rw [Pi.zero_apply, orderAtField_zero]
      exact le_top
  add_mem' := by
    intro r s hr hs
    constructor
    · exact isRepartition_add hr.1 hs.1
    · intro p
      exact (le_min (hr.2 p) (hs.2 p)).trans
        (by
          simpa [Pi.add_apply] using min_le_orderAtField_add p (r p) (s p))
  smul_mem' := by
    intro c r hr
    constructor
    · exact isRepartition_smul c hr.1
    · by_cases hc : c = 0
      · subst c
        intro p
        rw [Pi.smul_apply, zero_smul, orderAtField_zero]
        exact le_top
      · intro p
        rw [Pi.smul_apply, orderAtField_const_smul_of_ne_zero hc p (r p)]
        exact hr.2 p

/-- The diagonal embedding of the meromorphic function field into the ambient
space of pointwise repartitions, `f ↦ (p ↦ f)`. -/
def diagonalRepartition : MeroField X →ₗ[ℂ] (X → MeroField X) where
  toFun f := fun _ => f
  map_add' := by
    intro f g
    ext p
    rfl
  map_smul' := by
    intro c f
    ext p
    rfl

/-- A raw globally meromorphic function has finitely many nonzero Wallace
order coefficients on a compact Riemann surface. -/
private theorem meroFun_orderCoeff_support_finite (g : X → ℂ)
    (hg : ∀ p : X, MeromorphicAtX g p) :
    (Function.support fun p : X => (orderAt p g).untop₀).Finite := by
  have hlocal :
      LocallyFiniteSupport (fun p : X => (orderAt p g).untop₀) := by
    intro x
    let e := chartAt ℂ x
    let F : ℂ → ℂ := g ∘ e.symm
    let D := MeromorphicOn.divisor F e.target
    have hF : MeromorphicOn F e.target :=
      meromorphicOn_chart_pullback_of_meromorphicAtX hg x
    have hx_source : x ∈ e.source := mem_chart_source ℂ x
    have hx_target : e x ∈ e.target := e.map_source hx_source
    obtain ⟨u, hu_mem, hu_fin⟩ := D.supportLocallyFiniteWithinDomain (e x) hx_target
    refine ⟨e.source ∩ e ⁻¹' u, ?_, ?_⟩
    · have hu_pre : e ⁻¹' u ∈ 𝓝 x := by
        simpa [Filter.mem_map] using e.continuousAt hx_source hu_mem
      exact Filter.inter_mem (e.open_source.mem_nhds hx_source) hu_pre
    · let S : Set X :=
        (e.source ∩ e ⁻¹' u) ∩ Function.support
          (fun p : X => (orderAt p g).untop₀)
      have h_image_subset : e '' S ⊆ u ∩ D.support := by
        rintro y ⟨p, hpS, rfl⟩
        rcases hpS with ⟨⟨hp_source, hp_u⟩, hp_support⟩
        constructor
        · exact hp_u
        · have hp_target : e p ∈ e.target := e.map_source hp_source
          have h_order :
              orderAt p g = meromorphicOrderAt F (e p) := by
            simpa [e, F] using
              orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas (p := p)
                g e (IsManifold.chart_mem_maximalAtlas x) hp_source
          have h_support :
              meromorphicOrderAt F (e p) ≠ 0 ∧
                meromorphicOrderAt F (e p) ≠ ⊤ := by
            simpa [h_order, Function.mem_support, WithTop.untop₀_eq_zero] using
              hp_support
          have h_coeff_ne : (meromorphicOrderAt F (e p)).untop₀ ≠ 0 := by
            intro hzero
            apply h_support.1
            rw [← WithTop.coe_untop₀_of_ne_top h_support.2, hzero]
            rfl
          simpa [D, MeromorphicOn.divisor_apply hF hp_target, Function.mem_support] using
            h_coeff_ne
      have h_image_fin : (e '' S).Finite := hu_fin.subset h_image_subset
      have h_inj : Set.InjOn e S := by
        intro a ha b hb hab
        calc
          a = e.symm (e a) := (e.left_inv ha.1.1).symm
          _ = e.symm (e b) := by rw [hab]
          _ = b := e.left_inv hb.1.1
      exact h_image_fin.of_finite_image h_inj
  have h := hlocal.finite_inter_support_of_isCompact
    (W := (Set.univ : Set X)) isCompact_univ
  simpa using h

/-- A principal repartition has only finitely many poles.  This is the compact
Riemann-surface finite-pole theorem for the additive germ quotient `MeroField`. -/
theorem diagonal_isRepartition (f : MeroField X) :
    IsRepartition (fun _ : X => f) := by
  refine Submodule.Quotient.induction_on (GermZero X) f ?_
  intro g
  have hfin :
      (Function.support fun p : X => (orderAt p (g : X → ℂ)).untop₀).Finite :=
    meroFun_orderCoeff_support_finite (g : X → ℂ) g.property
  unfold IsRepartition
  refine hfin.subset ?_
  intro p hp
  change (orderAt p (g : X → ℂ)).untop₀ ≠ 0
  intro hzero
  apply hp
  rw [orderAtField_mk]
  have hcases :
      orderAt p (g : X → ℂ) = 0 ∨ orderAt p (g : X → ℂ) = ⊤ := by
    simpa [WithTop.untop₀_eq_zero] using hzero
  rcases hcases with horder | horder <;> simp [horder]

end Jacobians.RiemannSurface
