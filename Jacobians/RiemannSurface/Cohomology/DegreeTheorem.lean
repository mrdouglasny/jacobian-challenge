/-
# The degree theorem `deg(div f) = 0` — shared infrastructure (issue #120)

Toward `deg(div f) = ∑_p ord_p(f) = 0` (degree of a principal divisor is zero),
which gates Serre vanishing (`deg D < 0 ⇒ L(D) = 0`) and feeds `AX_SerreDuality` /
`AX_AbelTheorem`. Build order (`docs/planning/deg_divisor_eq_zero.md`): the shared
bridge first — this file starts with the elementary degree/effective facts.
-/

import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace
import Jacobians.RiemannSurface.MeromorphicFunctionField

namespace Jacobians.RiemannSurface

open scoped Manifold ContDiff Classical
open Jacobians.Axioms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder
open MeromorphicFunctionField

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

/-- A chosen `MeroFunctions` representative of a `MeroField` element. -/
private noncomputable def rep (F : MeroField X) : MeroFunctions X := Quotient.out F

private theorem rep_mk (F : MeroField X) :
    (Submodule.Quotient.mk (rep F) : MeroField X) = F := Quotient.out_eq F

private theorem orderAt_rep (F : MeroField X) (p : X) :
    orderAt p ((rep F : MeroFunctions X) : X → ℂ) = orderAtField p F := by
  conv_rhs => rw [← rep_mk F, orderAtField_mk]

/-- **The bridge.** A non-zero `MeroField` element as an element of the
principal-divisor layer `MeromorphicFunctionField` (where `div`/`deg` live). -/
noncomputable def toMF {F : MeroField X} (hF : F ≠ 0) : MeromorphicFunctionField X :=
  Quotient.mk Rep.setoid
    { toFun := ((rep F : MeroFunctions X) : X → ℂ)
      meromorphicAt := fun p => (rep F).property p
      order_ne_top := fun p => by
        rw [orderAt_rep]; exact orderAtField_ne_top_of_ne_zero hF p }

/-- The bridge preserves order: `ord_p (toMF F) = ord_p F`. -/
theorem orderAtMF_toMF {F : MeroField X} (hF : F ≠ 0) (p : X) :
    orderAtMF p (toMF hF) = orderAtField p F :=
  orderAt_rep F p

/-- The principal divisor of a non-zero `MeroField` element. -/
noncomputable def divisorOf {F : MeroField X} (hF : F ≠ 0) : Divisor X :=
  MeromorphicFunctionField.divisor (toMF hF)

/-- Its coefficients are the (finite) orders of `F`. -/
theorem coeff_divisorOf {F : MeroField X} (hF : F ≠ 0) (p : X) :
    FreeAbelianGroup.coeff p (divisorOf hF : FreeAbelianGroup X)
      = (orderAtField p F).untop₀ := by
  rw [show (divisorOf hF) = Rep.divisor _ from rfl, Rep.divisor_coeff, orderAt_rep]

/-- **Bridge to membership.** If `F ∈ L(D)` (and `F ≠ 0`) then `div(F) + D` is
effective — exactly the textbook `div f + D ≥ 0` characterizing `L(D)`. -/
theorem effective_divisorOf_add {F : MeroField X} (hF : F ≠ 0) {D : Divisor X}
    (hFD : F ∈ riemannRochSpace D) : Effective (divisorOf hF + D) := by
  intro p
  rw [map_add, coeff_divisorOf]
  have hord := hFD p
  have hfin := orderAtField_ne_top_of_ne_zero hF p
  rw [← WithTop.coe_untop₀_of_ne_top hfin, WithTop.coe_le_coe] at hord
  omega

/-- **Negative-degree vanishing** (modulo the degree theorem). If every principal
divisor has degree zero, then a divisor of negative degree has no global sections:
a non-zero `F ∈ L(D)` would give `0 ≤ deg(div F + D) = deg(div F) + deg D = deg D`,
contradicting `deg D < 0`. This is the Serre-vanishing ingredient. -/
theorem riemannRochSpace_eq_bot_of_deg_neg
    (hdeg0 : ∀ f : MeromorphicFunctionField X,
      Divisor.deg X (MeromorphicFunctionField.divisor f) = 0)
    {D : Divisor X} (hD : Divisor.deg X D < 0) :
    riemannRochSpace D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  by_contra hFne
  have heff := effective_divisorOf_add hFne hF
  have h0 := deg_nonneg_of_effective heff
  have hd0 : Divisor.deg X (divisorOf hFne) = 0 := hdeg0 (toMF hFne)
  rw [map_add, hd0, zero_add] at h0
  omega

end Jacobians.RiemannSurface
