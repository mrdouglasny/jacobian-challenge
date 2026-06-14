/-
# Riemann bilinear reductions for normalized period matrices

This module is the axiom-free linear-algebra bridge from Riemann's bilinear
relations, supplied as hypotheses, to the normalized period matrix conditions
needed by the Layer 3 period lattice engine.
-/

import Submission.Jacobians.Layer3.PeriodLattice

namespace Jacobians.Layer3

open Matrix
open scoped BigOperators

noncomputable section

/-- A period vector: A-periods and B-periods. -/
abbrev PeriodVector (g : ℕ) : Type :=
  ComplexVec g × ComplexVec g

/-- The symplectic dual form on period vectors. -/
def Q {g : ℕ} (φ ψ : PeriodVector g) : ℂ :=
  Finset.univ.sum fun k : Fin g =>
    φ.fst k * ψ.snd k - φ.snd k * ψ.fst k

/-- The period vector of the `j`-th normalized differential. -/
def col {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) : PeriodVector g :=
  (Pi.single j (1 : ℂ), fun k => τ k j)

/--
Expansion of the first Riemann bilinear relation on normalized columns:
`∑ k (δ_ki τ_kj - τ_ki δ_kj) = τ_ij - τ_ji`.
-/
theorem Q_normalized_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    Q (col τ i) (col τ j) = τ i j - τ j i := by
  classical
  rw [Q, col, Finset.sum_sub_distrib]
  have hleft :
      (∑ x : Fin g, Pi.single (M := fun _ : Fin g => ℂ) i (1 : ℂ) x * τ x j) =
        τ i j := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro x _ hx
      simp [Pi.single_eq_of_ne hx]
    · intro hi
      simp at hi
  have hright :
      (∑ x : Fin g, τ x i * Pi.single (M := fun _ : Fin g => ℂ) j (1 : ℂ) x) =
        τ j i := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro x _ hx
      simp [Pi.single_eq_of_ne hx]
    · intro hj
      simp at hj
  simp [col, hleft, hright]

/-- RBR1 isotropy of normalized columns forces the period matrix to be symmetric. -/
theorem tau_symmetric_of_rbr1 {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hRBR1 : ∀ i j : Fin g, Q (col τ i) (col τ j) = 0) :
    τ.IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  have h := hRBR1 j i
  rw [Q_normalized_eq] at h
  exact sub_eq_zero.mp h

/-- The period vector of `∑ c_j ω_j` in normalized coordinates. -/
def omegaCol {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (c : ComplexVec g) :
    PeriodVector g :=
  (c, τ *ᵥ c)

/-- The period vector of the conjugate differential. -/
def conjCol {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (c : ComplexVec g) :
    PeriodVector g :=
  (star c, star (τ *ᵥ c))

/--
Expansion of the second Riemann bilinear expression on an arbitrary coefficient
vector. The first term contains the conjugated B-periods, i.e. `star (τ *ᵥ c)`.
-/
theorem Q_omega_conj_eq {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (c : ComplexVec g) :
    Q (omegaCol τ c) (conjCol τ c) =
      c ⬝ᵥ star (τ *ᵥ c) - (τ *ᵥ c) ⬝ᵥ star c := by
  simp [Q, omegaCol, conjCol, dotProduct]

private theorem re_I_mul_conj_sub_ofReal (x : ℝ) (z : ℂ) :
    (Complex.I * ((x : ℂ) * star z - z * star (x : ℂ))).re = 2 * x * z.im := by
  simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_comm, mul_left_comm]
  ring

/--
For real coefficient vectors, RBR2 computes exactly twice the quadratic form
attached to `Im τ`.
-/
theorem re_I_Q_omega_real {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : RealVec g) :
    (Complex.I *
        Q (omegaCol τ (fun i => (x i : ℂ)))
          (conjCol τ (fun i => (x i : ℂ)))).re =
      2 * (x ⬝ᵥ ((τ.map Complex.im) *ᵥ x)) := by
  classical
  rw [Q, omegaCol, conjCol]
  simp only
  rw [Finset.mul_sum, Complex.re_sum]
  simp only [Pi.star_apply]
  calc
    ∑ k : Fin g,
        (Complex.I *
          ((x k : ℂ) * star ((τ *ᵥ fun i => (x i : ℂ)) k) -
            (τ *ᵥ fun i => (x i : ℂ)) k * star (x k : ℂ))).re =
        ∑ k : Fin g, 2 * x k * ((τ *ᵥ fun i => (x i : ℂ)) k).im := by
      apply Finset.sum_congr rfl
      intro k _
      exact re_I_mul_conj_sub_ofReal (x k) ((τ *ᵥ fun i => (x i : ℂ)) k)
    _ = 2 * (x ⬝ᵥ ((τ.map Complex.im) *ᵥ x)) := by
      have him :
          ∀ k : Fin g,
            ((τ *ᵥ fun i => (x i : ℂ)) k).im = ((τ.map Complex.im) *ᵥ x) k := by
        intro k
        exact congr_fun (im_mulVec_ofReal τ x) k
      simp_rw [him]
      simp [dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/--
RBR2, together with RBR1 for the Hermitian/symmetry part, makes the imaginary
part of the normalized period matrix positive definite.
-/
theorem tau_posDef_of_rbr2 {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hRBR1 : ∀ i j : Fin g, Q (col τ i) (col τ j) = 0)
    (hRBR2 : ∀ c : ComplexVec g, c ≠ 0 →
      0 < (Complex.I * Q (omegaCol τ c) (conjCol τ c)).re) :
    (τ.map Complex.im).PosDef := by
  classical
  have hτsymm : τ.IsSymm := tau_symmetric_of_rbr1 hRBR1
  have hHerm : (τ.map Complex.im).IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    simpa using (hτsymm.map Complex.im).apply i j
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm ?_
  intro x hx
  have hxC : (fun i : Fin g => (x i : ℂ)) ≠ 0 := by
    intro hxC_zero
    apply hx
    ext i
    exact Complex.ofReal_eq_zero.mp (congr_fun hxC_zero i)
  have hQ := hRBR2 (fun i : Fin g => (x i : ℂ)) hxC
  have htwice :
      0 < 2 * (x ⬝ᵥ ((τ.map Complex.im) *ᵥ x)) := by
    simpa [re_I_Q_omega_real τ x] using hQ
  have hdot : 0 < x ⬝ᵥ ((τ.map Complex.im) *ᵥ x) :=
    by nlinarith
  simpa using hdot

/--
End-to-end Riemann-bilinear bridge to the normalized period lattice: RBR1 and
RBR2 imply that the lattice generated by `[I | τ]` is a full `ℤ`-lattice.
-/
theorem riemannBilinear_isZLattice {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hRBR1 : ∀ i j : Fin g, Q (col τ i) (col τ j) = 0)
    (hRBR2 : ∀ c : ComplexVec g, c ≠ 0 →
      0 < (Complex.I * Q (omegaCol τ c) (conjCol τ c)).re) :
    IsZLattice ℝ (periodLattice τ (tau_posDef_of_rbr2 hRBR1 hRBR2)) := by
  infer_instance

end

end Jacobians.Layer3
