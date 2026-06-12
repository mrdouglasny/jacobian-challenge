/-
# P9 — the g=1 boundary-word witness, stage 1: the two explicit integrals

Handover UPDATE 4 P9 (`docs/planning/P9_ELLIPTIC_WITNESS_PLAN.md`).  With
the constant/linear field choices `h := c`, `F := c·z`, the two boundary
words of `ArcBoundaryWordData` reduce to:

* `rectBoundaryIntegral (fun z => (c·z)·c) = 0` — Cauchy on the box for an
  entire function (`word_R1`'s right side);
* `boundaryForm (fun _ => c) (fun z => c·z) = normSq c · 2i` — the classic
  area integral `∮_{∂[0,1]²} conj z dz = 2i` (`word_R2`'s right side).

Stage 2 assembles the `ArcBoundaryWordData` structure over the elliptic
`aLoop`/`bLoop` with the orientation-normalized constant
`c := √(±Im (ω₂ · conj ω₁))`.
-/
import Jacobians.RiemannSurface.BilinearRelationsBoundaryWord

namespace Jacobians.RiemannSurface
namespace BoundaryWordElliptic

open Complex intervalIntegral

/-- Cauchy on the box for the `word_R1` integrand: `∮ (c·z)·c dz = 0`. -/
theorem rectBoundary_linear_mul_const (c : ℂ) :
    Jacobians.rectBoundaryIntegral (fun z => (c * z) * c) = 0 := by
  refine Jacobians.rectBoundaryIntegral_eq_zero_of_differentiableOn ?_
  exact (differentiable_id.const_mul c |>.mul_const c).differentiableOn

/-- `∫₀¹ (t : ℂ) dt = 1/2`. -/
theorem integral_coe_id : (∫ t in (0:ℝ)..1, (t : ℂ)) = 1 / 2 := by
  have h : (∫ t in (0:ℝ)..1, (t : ℝ)) = 1 / 2 := by
    rw [integral_id]
    norm_num
  rw [show (∫ t in (0:ℝ)..1, (t : ℂ))
      = ((∫ t in (0:ℝ)..1, (t : ℝ) : ℝ) : ℂ) from
    intervalIntegral.integral_ofReal, h]
  norm_num

/-- The conjugate of an affine path integrates to the conjugate affine
midpoint value: `∫₀¹ conj (p + t·q) dt = conj p + conj q / 2`. -/
theorem integral_conj_affine (p q : ℂ) :
    (∫ t in (0:ℝ)..1, (starRingEnd ℂ) (p + (t : ℂ) * q))
      = (starRingEnd ℂ) p + (starRingEnd ℂ) q / 2 := by
  have hfun : ∀ t : ℝ, (starRingEnd ℂ) (p + (t : ℂ) * q)
      = (starRingEnd ℂ) p + (t : ℂ) * (starRingEnd ℂ) q := by
    intro t
    rw [map_add, map_mul, Complex.conj_ofReal]
  rw [intervalIntegral.integral_congr fun t _ => hfun t]
  have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) * (starRingEnd ℂ) q)
      MeasureTheory.volume 0 1 :=
    (Complex.continuous_ofReal.mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add
    (f := fun _ : ℝ => (starRingEnd ℂ) p)
    (g := fun t : ℝ => (t : ℂ) * (starRingEnd ℂ) q)
    (continuous_const.intervalIntegrable _ _) hint,
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
    integral_coe_id]
  simp
  ring

/-- **The area integral** for the `word_R2` integrand:
`boundaryForm (const c) (c·z) = normSq c · 2i`. -/
theorem boundaryForm_const_linear (c : ℂ) :
    Jacobians.boundaryForm (fun _ => c) (fun z => c * z)
      = (Complex.normSq c : ℂ) * (2 * Complex.I) := by
  have hker : ∀ w : ℂ,
      (starRingEnd ℂ) (c * w) * c
      = (Complex.normSq c : ℂ) * (starRingEnd ℂ) w := by
    intro w
    rw [map_mul]
    calc (starRingEnd ℂ) c * (starRingEnd ℂ) w * c
        = ((starRingEnd ℂ) c * c) * (starRingEnd ℂ) w := by ring
      _ = (Complex.normSq c : ℂ) * (starRingEnd ℂ) w := by
          rw [← Complex.normSq_eq_conj_mul_self]
  have hw : ∀ x y : ℝ, (Jacobians.wCLM (x, y) : ℂ)
      = (x : ℂ) + (y : ℂ) * Complex.I := by
    intro x y
    show Complex.equivRealProdCLM.symm (x, y) = _
    apply Complex.ext <;>
      simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  unfold Jacobians.boundaryForm
  -- rewrite each of the four edges into the affine form and integrate
  have e₁ : (∫ x in (0:ℝ)..1,
      (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (x, 0))) *
        (fun _ => c) (Jacobians.wCLM (x, 0)))
      = (Complex.normSq c : ℂ) * (1 / 2) := by
    have : ∀ x : ℝ, (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (x, 0))) *
        (fun _ => c) (Jacobians.wCLM (x, 0))
        = (Complex.normSq c : ℂ) * (starRingEnd ℂ) ((0 : ℂ) + (x : ℂ) * 1) := by
      intro x
      rw [hker, hw]
      push_cast
      ring_nf
    rw [intervalIntegral.integral_congr fun x _ => this x,
      intervalIntegral.integral_const_mul, integral_conj_affine]
    congr 1
    norm_num
  have e₂ : (∫ y in (0:ℝ)..1,
      (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (1, y))) *
        (fun _ => c) (Jacobians.wCLM (1, y)))
      = (Complex.normSq c : ℂ) * (1 - Complex.I / 2) := by
    have : ∀ y : ℝ, (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (1, y))) *
        (fun _ => c) (Jacobians.wCLM (1, y))
        = (Complex.normSq c : ℂ) *
            (starRingEnd ℂ) ((1 : ℂ) + (y : ℂ) * Complex.I) := by
      intro y
      rw [hker, hw]
      push_cast
      ring_nf
    rw [intervalIntegral.integral_congr fun y _ => this y,
      intervalIntegral.integral_const_mul, integral_conj_affine]
    congr 1
    simp [Complex.conj_I]
    ring
  have e₃ : (∫ x in (0:ℝ)..1,
      (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (x, 1))) *
        (fun _ => c) (Jacobians.wCLM (x, 1)))
      = (Complex.normSq c : ℂ) * (1 / 2 - Complex.I) := by
    have : ∀ x : ℝ, (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (x, 1))) *
        (fun _ => c) (Jacobians.wCLM (x, 1))
        = (Complex.normSq c : ℂ) *
            (starRingEnd ℂ) ((Complex.I : ℂ) + (x : ℂ) * 1) := by
      intro x
      rw [hker, hw]
      push_cast
      ring_nf
    rw [intervalIntegral.integral_congr fun x _ => this x,
      intervalIntegral.integral_const_mul, integral_conj_affine]
    congr 1
    simp [Complex.conj_I]
    ring
  have e₄ : (∫ y in (0:ℝ)..1,
      (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (0, y))) *
        (fun _ => c) (Jacobians.wCLM (0, y)))
      = (Complex.normSq c : ℂ) * (-Complex.I / 2) := by
    have : ∀ y : ℝ, (starRingEnd ℂ) ((fun z => c * z) (Jacobians.wCLM (0, y))) *
        (fun _ => c) (Jacobians.wCLM (0, y))
        = (Complex.normSq c : ℂ) *
            (starRingEnd ℂ) ((0 : ℂ) + (y : ℂ) * Complex.I) := by
      intro y
      rw [hker, hw]
      push_cast
      ring_nf
    rw [intervalIntegral.integral_congr fun y _ => this y,
      intervalIntegral.integral_const_mul, integral_conj_affine]
    congr 1
    simp [Complex.conj_I]
  rw [e₁, e₂, e₃, e₄]
  ring_nf

end BoundaryWordElliptic
end Jacobians.RiemannSurface
