/-
# Cholesky-type factorization of a positive definite complex matrix

`S = C * Cᴴ` with `C` invertible, from Mathlib's LDL decomposition
(`LDL.lower_conj_diag`) by taking entrywise real square roots of the
diagonal factor.  This is the finite-dimensional engine for the R2
Gram-word reduction of the hyperelliptic boundary-word walls
(`docs/planning/P10_BW_HYPERELLIPTIC_ROUTE.md`, follow-up 1): any
positive definite target Gram is realizable as a polynomial box-L²
Gram once it factors as `C * Cᴴ`.
-/
import Mathlib.Analysis.Matrix.LDL

namespace Jacobians.GeneralResults

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [LinearOrder n] [WellFoundedLT n]
  [LocallyFiniteOrderBot n]

/-- The diagonal entries of the LDL decomposition of a positive definite
complex matrix are positive (in the complex order, i.e. positive reals). -/
theorem ldl_diagEntries_pos {S : Matrix n n ℂ} (hS : S.PosDef) (i : n) :
    0 < LDL.diagEntries hS i := by
  have hrow : (fun k => LDL.lowerInv hS i k) ≠ 0 := by
    intro h0
    have hdet : (LDL.lowerInv hS).det = 0 :=
      Matrix.det_eq_zero_of_row_eq_zero i fun j => congrFun h0 j
    exact (Matrix.isUnit_det_of_invertible (LDL.lowerInv hS)).ne_zero hdet
  have hx : star (LDL.lowerInv hS i) ≠ 0 := by
    intro h0
    exact hrow (by simpa using congrArg star h0)
  have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hS).2 hx
  have hentry : LDL.diagEntries hS i
      = star (star (LDL.lowerInv hS i)) ⬝ᵥ (S *ᵥ star (LDL.lowerInv hS i)) := by
    simp [LDL.diagEntries, dotProduct, EuclideanSpace.inner_toLp_toLp, mul_comm]
  rw [hentry]
  simpa using hquad

/-- **Cholesky-type factorization.** Every positive definite complex matrix
factors as `C * Cᴴ` with `C` invertible (`C = L·√D` from the LDL
decomposition). -/
theorem PosDef.exists_isUnit_det_mul_conjTranspose_eq {S : Matrix n n ℂ}
    (hS : S.PosDef) :
    ∃ C : Matrix n n ℂ, IsUnit C.det ∧ C * Cᴴ = S := by
  set d : n → ℂ := LDL.diagEntries hS with hd
  have hdpos : ∀ i, 0 < d i := ldl_diagEntries_pos hS
  set s : n → ℂ := fun i => ((Real.sqrt (d i).re : ℝ) : ℂ) with hs
  have hdre : ∀ i, 0 < (d i).re := fun i => (Complex.pos_iff.mp (hdpos i)).1
  have hdim : ∀ i, (d i).im = 0 := fun i => ((Complex.pos_iff.mp (hdpos i)).2).symm
  have hssq : ∀ i, s i * s i = d i := by
    intro i
    have : (Real.sqrt (d i).re) * (Real.sqrt (d i).re) = (d i).re :=
      Real.mul_self_sqrt (hdre i).le
    rw [hs, ← Complex.ofReal_mul, this]
    exact Complex.ext (by simp) (by simp [hdim i])
  have hsne : ∀ i, s i ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hdre i)).ne'
  -- the diagonal factor splits as √D · (√D)ᴴ
  have hdiag : Matrix.diagonal s * (Matrix.diagonal s)ᴴ = LDL.diag hS := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    refine congrArg Matrix.diagonal (funext fun i => ?_)
    have hstar : star (s i) = s i := by simp [hs]
    show s i * (star s) i = _
    rw [Pi.star_apply, hstar, hssq i]
  refine ⟨LDL.lower hS * Matrix.diagonal s, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · exact Matrix.isUnit_nonsing_inv_det _
        (Matrix.isUnit_det_of_invertible (LDL.lowerInv hS))
    · rw [Matrix.det_diagonal]
      exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hsne i)
  · calc LDL.lower hS * Matrix.diagonal s * (LDL.lower hS * Matrix.diagonal s)ᴴ
        = LDL.lower hS * (Matrix.diagonal s * (Matrix.diagonal s)ᴴ)
            * (LDL.lower hS)ᴴ := by
          rw [Matrix.conjTranspose_mul]
          noncomm_ring
      _ = LDL.lower hS * LDL.diag hS * (LDL.lower hS)ᴴ := by rw [hdiag]
      _ = S := LDL.lower_conj_diag hS

end Jacobians.GeneralResults
