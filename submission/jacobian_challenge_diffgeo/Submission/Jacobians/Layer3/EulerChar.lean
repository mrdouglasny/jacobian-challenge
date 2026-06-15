import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

universe u v w

/-!
# Euler characteristic for a six-term exact sequence

This file records the finite-dimensional linear-algebra step needed by the
Riemann--Roch skyscraper-sequence reduction: a six-term exact sequence has zero
alternating dimension sum, hence the two-term Euler characteristic is additive.
-/

namespace Jacobians.Layer3

open Module


section SixTerm

variable {K : Type u} [DivisionRing K]
variable {A0 B0 C0 A1 B1 C1 : Type v}
variable [AddCommGroup A0] [Module K A0] [FiniteDimensional K A0]
variable [AddCommGroup B0] [Module K B0] [FiniteDimensional K B0]
variable [AddCommGroup C0] [Module K C0] [FiniteDimensional K C0]
variable [AddCommGroup A1] [Module K A1] [FiniteDimensional K A1]
variable [AddCommGroup B1] [Module K B1] [FiniteDimensional K B1]
variable [AddCommGroup C1] [Module K C1]

/-- Euler-characteristic additivity for a six-term exact sequence of
finite-dimensional vector spaces
`0 -> A0 -> B0 -> C0 -> A1 -> B1 -> C1 -> 0`.

The endpoint hypotheses use exactness against zero maps, which is equivalent to
injectivity of the first map and surjectivity of the last map. -/
theorem eulerChar_additive_of_exact_six
    [FiniteDimensional K C1]
    (f0 : A0 →ₗ[K] B0) (g0 : B0 →ₗ[K] C0) (d : C0 →ₗ[K] A1)
    (f1 : A1 →ₗ[K] B1) (g1 : B1 →ₗ[K] C1)
    (hA0 : Function.Exact (0 : A0 →ₗ[K] A0) f0)
    (hB0 : Function.Exact f0 g0)
    (hC0 : Function.Exact g0 d)
    (hA1 : Function.Exact d f1)
    (hB1 : Function.Exact f1 g1)
    (hC1 : Function.Exact g1 (0 : C1 →ₗ[K] C1)) :
    (finrank K B0 : ℤ) - (finrank K B1 : ℤ) =
      ((finrank K A0 : ℤ) - (finrank K A1 : ℤ)) +
        ((finrank K C0 : ℤ) - (finrank K C1 : ℤ)) := by
  let r0 := finrank K (LinearMap.range f0)
  let r1 := finrank K (LinearMap.range g0)
  let r2 := finrank K (LinearMap.range d)
  let r3 := finrank K (LinearMap.range f1)
  have hf0_range : r0 = finrank K A0 := by
    have hinj : Function.Injective f0 :=
      (LinearMap.exact_zero_iff_injective A0 f0).mp hA0
    have hker : finrank K (LinearMap.ker f0) = 0 := by
      rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot]
    have h := LinearMap.finrank_range_add_finrank_ker f0
    rw [hker, add_zero] at h
    exact h
  have hg0_rank : r1 + r0 = finrank K B0 := by
    have hker : finrank K (LinearMap.ker g0) = r0 := by
      rw [Function.Exact.linearMap_ker_eq hB0]
    have h := LinearMap.finrank_range_add_finrank_ker g0
    rwa [hker] at h
  have hd_rank : r2 + r1 = finrank K C0 := by
    have hker : finrank K (LinearMap.ker d) = r1 := by
      rw [Function.Exact.linearMap_ker_eq hC0]
    have h := LinearMap.finrank_range_add_finrank_ker d
    rwa [hker] at h
  have hf1_rank : r3 + r2 = finrank K A1 := by
    have hker : finrank K (LinearMap.ker f1) = r2 := by
      rw [Function.Exact.linearMap_ker_eq hA1]
    have h := LinearMap.finrank_range_add_finrank_ker f1
    rwa [hker] at h
  have hg1_rank : finrank K C1 + r3 = finrank K B1 := by
    have hsurj : Function.Surjective g1 :=
      (LinearMap.exact_zero_iff_surjective C1 g1).mp hC1
    have hrange : LinearMap.range g1 = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hker : finrank K (LinearMap.ker g1) = r3 := by
      rw [Function.Exact.linearMap_ker_eq hB1]
    have h := LinearMap.finrank_range_add_finrank_ker g1
    rwa [hrange, finrank_top, hker] at h
  omega

/-- The skyscraper-specialized form of
`eulerChar_additive_of_exact_six`: if the right-hand cohomology term has
dimensions `(1, 0)`, then the Euler characteristic increases by one. -/
theorem eulerChar_additive_of_exact_six_skyscraper
    [FiniteDimensional K C1]
    (f0 : A0 →ₗ[K] B0) (g0 : B0 →ₗ[K] C0) (d : C0 →ₗ[K] A1)
    (f1 : A1 →ₗ[K] B1) (g1 : B1 →ₗ[K] C1)
    (hA0 : Function.Exact (0 : A0 →ₗ[K] A0) f0)
    (hB0 : Function.Exact f0 g0)
    (hC0 : Function.Exact g0 d)
    (hA1 : Function.Exact d f1)
    (hB1 : Function.Exact f1 g1)
    (hC1 : Function.Exact g1 (0 : C1 →ₗ[K] C1))
    (hC0_dim : finrank K C0 = 1)
    (hC1_dim : finrank K C1 = 0) :
    (finrank K B0 : ℤ) - (finrank K B1 : ℤ) =
      ((finrank K A0 : ℤ) - (finrank K A1 : ℤ)) + 1 := by
  simpa [hC0_dim, hC1_dim] using
    eulerChar_additive_of_exact_six f0 g0 d f1 g1 hA0 hB0 hC0 hA1 hB1 hC1

end SixTerm

end Jacobians.Layer3
