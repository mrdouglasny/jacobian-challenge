/-
# The degree theorem `deg(div f) = 0` — shared infrastructure (issue #120)

Toward `deg(div f) = ∑_p ord_p(f) = 0` (degree of a principal divisor is zero),
which gates Serre vanishing (`deg D < 0 ⇒ L(D) = 0`) and feeds `AX_SerreDuality` /
`AX_AbelTheorem`. Build order (`docs/planning/deg_divisor_eq_zero.md`): the shared
bridge first — this file starts with the elementary degree/effective facts.
-/

import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace

namespace Jacobians.RiemannSurface

open scoped Manifold ContDiff Classical
open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- The degree of a divisor is the total of its `Finsupp` coefficients. -/
theorem deg_eq_sum_toFinsupp (D : Divisor X) :
    Divisor.deg X D = (FreeAbelianGroup.toFinsupp D).sum (fun _ n => n) := by
  induction D using FreeAbelianGroup.induction_on with
  | zero => simp
  | of x => simp [Divisor.deg, FreeAbelianGroup.toFinsupp_of, Finsupp.sum_single_index]
  | neg x ih =>
      simp only [map_neg, ih, FreeAbelianGroup.toFinsupp_of]
      rw [show (-(Finsupp.single x (1 : ℤ))) = Finsupp.single x (-1) by
        ext a; simp [Finsupp.single_apply]]
      rw [Finsupp.sum_single_index, Finsupp.sum_single_index] <;> simp
  | add x y hx hy =>
      rw [map_add, hx, hy, map_add, Finsupp.sum_add_index'] <;> simp

/-- **Effective ⇒ degree ≥ 0.** An effective divisor is a sum of nonnegative
coefficients, so its degree is nonnegative. -/
theorem deg_nonneg_of_effective {D : Divisor X} (hD : Effective D) :
    0 ≤ Divisor.deg X D := by
  rw [deg_eq_sum_toFinsupp]
  refine Finset.sum_nonneg (fun x _ => ?_)
  exact hD x

/-! ### Bridge to the principal-divisor layer

A *non-zero* `MeroField` element is non-zero **everywhere** (identity principle on
connected `X`), so it has a representative usable as a `MeromorphicFunctionField`
element with a principal divisor. This is the entry point to the bridge. -/

/-- **Identity principle (field form).** A non-zero `F : MeroField X` has finite
order at every point: vanishing on a non-empty open set would force vanishing
everywhere (clopen + connected), contradicting `F ≠ 0`. -/
theorem orderAtField_ne_top_of_ne_zero {F : MeroField X} (hF : F ≠ 0) (p : X) :
    orderAtField p F ≠ ⊤ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (GermZero X) F
  rw [orderAtField_mk]
  have hf_notmem : f ∉ GermZero X := fun hmem =>
    hF ((Submodule.Quotient.mk_eq_zero (GermZero X)).mpr hmem)
  have hex : ∃ q, orderAt q (f : X → ℂ) ≠ ⊤ := by
    by_contra h
    push_neg at h
    exact hf_notmem h
  exact orderAt_ne_top_of_exists (fun q => f.property q) hex p

end Jacobians.RiemannSurface
