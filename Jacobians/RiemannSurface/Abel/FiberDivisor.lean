/-
Algebraic fiber divisors for the Abel `⊇` workstream.

This file contains only the divisor-level algebra: the weighted fiber divisor
of a non-constant meromorphic function, and the reduction of
`abelJacobiDiv (div f)` to the difference between the fibers over `0` and
`∞`. Holomorphicity of the induced pencil map is deferred to later chunks.
-/

import Jacobians.RiemannSurface.DegreeViaP1
import Jacobians.Axioms.AbelTheorem

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff BigOperators
open Jacobians.Axioms
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.ProjectiveLine
open Jacobians.Vendor.Wallace.HolomorphicForms
open Jacobians.Vendor.Wallace.HolomorphicForms.VanishingOrder
open Filter OnePoint

namespace MeromorphicFunctionField

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

private theorem coeff_divisor_local (f : MeromorphicFunctionField X) (p : X) :
    FreeAbelianGroup.coeff p (divisor f : FreeAbelianGroup X) =
      (orderAtMF p f).untop₀ := by
  refine Quotient.inductionOn f ?_
  intro f
  change FreeAbelianGroup.coeff p
      (Rep.divisor f : FreeAbelianGroup X) =
      (orderAt p (f : X → ℂ)).untop₀
  exact Rep.divisor_coeff f p

private theorem orderAtMF_ne_top_local (f : MeromorphicFunctionField X) (p : X) :
    orderAtMF p f ≠ ⊤ := by
  refine Quotient.inductionOn f ?_
  intro f
  simpa [orderAtMF] using f.order_ne_top p

/-- The weighted divisor of the fiber of `toP1 f` over `y`, with ramification
multiplicity `mapAnalyticOrderAt`. -/
noncomputable def fiberDivisor (f : MeromorphicFunctionField X) (hf : Nonconstant f)
    (y : ProjectiveLine) : Divisor X :=
  ∑ x ∈ (toP1_fiber_finite hf y).toFinset,
    mapAnalyticOrderAt (toP1 f) x • FreeAbelianGroup.of x

open Classical in
/-- Coefficients of the weighted fiber divisor. -/
theorem coeff_fiberDivisor (f : MeromorphicFunctionField X) (hf : Nonconstant f)
    (y : ProjectiveLine) (p : X) :
    FreeAbelianGroup.coeff p (fiberDivisor f hf y : FreeAbelianGroup X) =
      if toP1 f p = y then (mapAnalyticOrderAt (toP1 f) p : ℤ) else 0 := by
  classical
  simp [fiberDivisor, FreeAbelianGroup.coeff, FreeAbelianGroup.toFinsupp_of,
    Finsupp.single_apply, Set.Finite.mem_toFinset]

private theorem toP1_eq_zero_iff_untop₀ (f : MeromorphicFunctionField X) (p : X) :
    toP1 f p = (((0 : ℂ) : ProjectiveLine)) ↔
      0 < (orderAtMF p f).untop₀ := by
  constructor
  · intro hp
    have hpos : 0 < orderAtMF p f := (toP1_eq_zero_iff f p).1 hp
    rw [← WithTop.coe_untop₀_of_ne_top (orderAtMF_ne_top_local f p)] at hpos
    exact_mod_cast hpos
  · intro hp
    apply (toP1_eq_zero_iff f p).2
    rw [← WithTop.coe_untop₀_of_ne_top (orderAtMF_ne_top_local f p)]
    exact_mod_cast hp

private theorem toP1_eq_infty_iff_untop₀ (f : MeromorphicFunctionField X) (p : X) :
    toP1 f p = (∞ : ProjectiveLine) ↔
      (orderAtMF p f).untop₀ < 0 := by
  constructor
  · intro hp
    have hneg : orderAtMF p f < 0 := (toP1_eq_infty_iff f p).1 hp
    rw [← WithTop.coe_untop₀_of_ne_top (orderAtMF_ne_top_local f p)] at hneg
    exact_mod_cast hneg
  · intro hp
    apply (toP1_eq_infty_iff f p).2
    rw [← WithTop.coe_untop₀_of_ne_top (orderAtMF_ne_top_local f p)]
    exact_mod_cast hp

/-- The difference between the weighted fibers over `0` and `∞` is the
principal divisor of `f`. -/
theorem fiberDivisor_zero_sub_infty (f : MeromorphicFunctionField X) (hf : Nonconstant f) :
    fiberDivisor f hf (((0 : ℂ) : ProjectiveLine)) -
        fiberDivisor f hf (∞ : ProjectiveLine) =
      divisor f := by
  classical
  apply (FreeAbelianGroup.equivFinsupp X).injective
  ext p
  change
    FreeAbelianGroup.coeff p
        ((fiberDivisor f hf (((0 : ℂ) : ProjectiveLine)) -
            fiberDivisor f hf (∞ : ProjectiveLine)) : FreeAbelianGroup X) =
      FreeAbelianGroup.coeff p (divisor f : FreeAbelianGroup X)
  simp only [map_sub, coeff_fiberDivisor, coeff_divisor_local]
  let n : ℤ := (orderAtMF p f).untop₀
  by_cases hzero : toP1 f p = (((0 : ℂ) : ProjectiveLine))
  · have hnot_infty : ¬ toP1 f p = (∞ : ProjectiveLine) := by
      intro hinfty
      have hbad : (((0 : ℂ) : ProjectiveLine)) = (∞ : ProjectiveLine) :=
        hzero.symm.trans hinfty
      exact OnePoint.coe_ne_infty (0 : ℂ) hbad
    rw [if_pos hzero, if_neg hnot_infty, sub_zero,
      mapAnalyticOrderAt_toP1_zero f hzero]
    exact Int.toNat_of_nonneg ((toP1_eq_zero_iff_untop₀ f p).1 hzero).le
  · by_cases hinfty : toP1 f p = (∞ : ProjectiveLine)
    · have hn_neg : n < 0 := by
        simpa [n] using (toP1_eq_infty_iff_untop₀ f p).1 hinfty
      rw [if_neg hzero, if_pos hinfty, zero_sub, mapAnalyticOrderAt_toP1 f hinfty]
      have hnonneg : 0 ≤ -((orderAtMF p f).untop₀) := by
        omega
      rw [Int.toNat_of_nonneg hnonneg]
      omega
    · have hn_not_pos : ¬ 0 < n := by
        intro hn_pos
        exact hzero ((toP1_eq_zero_iff_untop₀ f p).2 (by simpa [n] using hn_pos))
      have hn_not_neg : ¬ n < 0 := by
        intro hn_neg
        exact hinfty ((toP1_eq_infty_iff_untop₀ f p).2 (by simpa [n] using hn_neg))
      rw [if_neg hzero, if_neg hinfty, sub_zero]
      change 0 = n
      omega

/-- The Abel-Jacobi value of a weighted fiber, i.e. the algebraic map `Φ`. -/
noncomputable def fiberAJ (f : MeromorphicFunctionField X) (hf : Nonconstant f)
    (y : ProjectiveLine) : Jacobian X :=
  abelJacobiDiv X (fiberDivisor f hf y)

/-- Algebraic reduction of `abelJacobiDiv (div f)` to the difference between
the Abel-Jacobi values of the fibers over `0` and `∞`. -/
theorem fiberAJ_zero_sub_infty (f : MeromorphicFunctionField X) (hf : Nonconstant f) :
    fiberAJ f hf (((0 : ℂ) : ProjectiveLine)) - fiberAJ f hf (∞ : ProjectiveLine) =
      abelJacobiDiv X (divisor f) := by
  rw [fiberAJ, fiberAJ, ← (abelJacobiDiv X).map_sub, fiberDivisor_zero_sub_infty f hf]

end MeromorphicFunctionField

end Jacobians.RiemannSurface
