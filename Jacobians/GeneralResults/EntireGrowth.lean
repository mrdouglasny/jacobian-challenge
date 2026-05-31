/-
# Entire functions of polynomial growth are polynomials

A general complex-analysis lemma that Mathlib does not (yet) package:
an entire function `g : ℂ → ℂ` satisfying a polynomial growth bound
`‖g z‖ ≤ C · (1 + ‖z‖)^n` is a polynomial of degree `≤ n`.

This is **step 4** ("entire + polynomial growth ⇒ polynomial") of the
proof plan for `AX_HyperellipticForm_polynomial_decomposition` (Liouville
hierarchy Level 2) in `Jacobians/Axioms/HyperellipticLiouville.lean`, and
the analogous final step on the odd side. Discharged here as a reusable,
axiom-free lemma; the remaining (project-specific) Level-2 content is the
extension of the chart coefficient to an entire function with the right
growth exponent.

## Proof

Induction on `n`. The base case `n = 0` is Liouville's theorem (a bounded
entire function is constant). For the step, divide out the value at `0`
using the removable-singularity quotient `dslope g 0`: it is entire
(`Complex.differentiableOn_dslope`), satisfies `g z = z · (dslope g 0) z +
g 0` (`sub_smul_dslope`), and has growth exponent `n` (the `(1+‖z‖)`
factor is absorbed by dividing by `‖z‖` for `‖z‖ ≥ 1`; near `0` it is
bounded by compactness). The induction hypothesis turns it into a
polynomial `p`, and `g = X · p + C (g 0)`.
-/
import Mathlib

namespace Jacobians.GeneralResults

open Complex Set Metric Filter
open scoped Topology

/-- An entire function with polynomial growth `‖g z‖ ≤ C (1 + ‖z‖)^n` is a
polynomial of degree `≤ n`. -/
theorem differentiable_eq_polynomial_of_growth (n : ℕ) (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) (C : ℝ) (hC : ∀ z, ‖g z‖ ≤ C * (1 + ‖z‖) ^ n) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ n ∧ ∀ z, g z = p.eval z := by
  induction n generalizing g C with
  | zero =>
    -- bounded entire ⇒ constant (Liouville)
    have hbd : Bornology.IsBounded (range g) := by
      refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr ⟨C, ?_⟩
      rintro _ ⟨z, rfl⟩
      have := hC z
      simpa [mem_closedBall, dist_zero_right] using this
    obtain ⟨c, hc⟩ := hg.exists_const_forall_eq_of_bounded hbd
    exact ⟨Polynomial.C c, by simp, fun z => by rw [hc z]; simp⟩
  | succ n ih =>
    set h : ℂ → ℂ := dslope g 0 with hh
    have hh_diff : Differentiable ℂ h := by
      rw [hh, ← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr
        (differentiableOn_univ.mpr hg)
    have hid : ∀ z, g z = z * h z + g 0 := by
      intro z
      have hs := sub_smul_dslope g 0 z
      rw [sub_zero, smul_eq_mul, ← hh] at hs
      rw [hs]; ring
    have hC0 : 0 ≤ C := by have := hC 0; simpa using le_trans (norm_nonneg _) this
    -- bound on the unit ball by continuity
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ z ∈ closedBall (0 : ℂ) 1, ‖h z‖ ≤ M :=
      (isCompact_closedBall 0 1).exists_bound_of_continuousOn hh_diff.continuous.continuousOn
    -- growth bound on `h`, exponent `n`
    have hgrow : ∀ z, ‖h z‖ ≤ (max (2 * C + ‖g 0‖) M) * (1 + ‖z‖) ^ n := by
      intro z
      set C' := max (2 * C + ‖g 0‖) M with hC'
      have hP1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ n := one_le_pow₀ (by nlinarith [norm_nonneg z])
      have hPnn : (0 : ℝ) ≤ (1 + ‖z‖) ^ n := le_trans zero_le_one hP1
      by_cases hz : 1 ≤ ‖z‖
      · have hzpos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le one_pos hz
        have hzh : ‖z‖ * ‖h z‖ ≤ C * (1 + ‖z‖) ^ (n + 1) + ‖g 0‖ := by
          have hzx : z * h z = g z - g 0 := by
            have hs := sub_smul_dslope g 0 z
            rw [sub_zero, smul_eq_mul, ← hh] at hs; exact hs
          calc ‖z‖ * ‖h z‖ = ‖z * h z‖ := (norm_mul z (h z)).symm
            _ = ‖g z - g 0‖ := by rw [hzx]
            _ ≤ ‖g z‖ + ‖g 0‖ := norm_sub_le _ _
            _ ≤ C * (1 + ‖z‖) ^ (n + 1) + ‖g 0‖ := by linarith [hC z]
        have hA : 0 ≤ C * (1 + ‖z‖) ^ n * (‖z‖ - 1) :=
          mul_nonneg (mul_nonneg hC0 hPnn) (by linarith)
        have htP : 1 ≤ ‖z‖ * (1 + ‖z‖) ^ n :=
          le_trans hP1 (le_mul_of_one_le_left hPnn hz)
        have hB : 0 ≤ ‖g 0‖ * (‖z‖ * (1 + ‖z‖) ^ n - 1) :=
          mul_nonneg (norm_nonneg _) (by linarith)
        have hCmax : 2 * C + ‖g 0‖ ≤ C' := le_max_left _ _
        have hmul : (2 * C + ‖g 0‖) * (‖z‖ * (1 + ‖z‖) ^ n) ≤
            C' * (‖z‖ * (1 + ‖z‖) ^ n) :=
          mul_le_mul_of_nonneg_right hCmax (by linarith)
        have hkey : ‖z‖ * ‖h z‖ ≤ ‖z‖ * (C' * (1 + ‖z‖) ^ n) := by
          have hexpand : C * (1 + ‖z‖) ^ (n + 1) + ‖g 0‖ ≤
              ‖z‖ * (C' * (1 + ‖z‖) ^ n) := by
            rw [pow_succ]; nlinarith [hA, hB, hmul]
          exact le_trans hzh hexpand
        exact le_of_mul_le_mul_left hkey hzpos
      · have hz' : ‖z‖ < 1 := not_le.mp hz
        have hmem : z ∈ closedBall (0 : ℂ) 1 := by
          simp only [mem_closedBall, dist_zero_right]; linarith
        have hC'nn : 0 ≤ C' :=
          le_trans (le_trans (norm_nonneg (h z)) (hM z hmem)) (le_max_right _ _)
        calc ‖h z‖ ≤ M := hM z hmem
          _ ≤ C' := le_max_right _ _
          _ ≤ C' * (1 + ‖z‖) ^ n := by nlinarith [hP1, hC'nn]
    obtain ⟨p, hp_deg, hp⟩ := ih h hh_diff (max (2 * C + ‖g 0‖) M) hgrow
    -- assemble `g = X · p + C (g 0)`
    refine ⟨Polynomial.X * p + Polynomial.C (g 0), ?_, ?_⟩
    · refine le_trans (Polynomial.natDegree_add_le _ _) ?_
      simp only [Polynomial.natDegree_C, max_le_iff]
      refine ⟨le_trans (Polynomial.natDegree_mul_le) ?_, Nat.zero_le _⟩
      simp only [Polynomial.natDegree_X]
      omega
    · intro z
      rw [hid z, hp z]
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

end Jacobians.GeneralResults
