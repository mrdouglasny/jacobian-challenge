/-
# P10 — the g = 1 instantiation of the polynomial boundary-word engine

Satisfiability check for the engine's wall shape
(`docs/planning/P10_BW_HYPERELLIPTIC_ROUTE.md`): the merged g = 1
witness (`BoundaryWordElliptic.lean`, #225) factors through
`polyArcBoundaryWordData` with the one-element polynomial family
`P = C c · X`, `c = orientationConstant` — confirming that the two
hyperelliptic walls (`R1Word`-shape symmetry, `R2GramWord`-shape Gram
identity) are exactly the data the elliptic computation supplies, i.e.
non-vacuous and satisfiable at genus 1.
-/
import Submission.Jacobians.RiemannSurface.BoundaryWordPolynomial
import Submission.Jacobians.RiemannSurface.BoundaryWordElliptic

namespace Jacobians.RiemannSurface
namespace BoundaryWordElliptic

open Polynomial Matrix
open Jacobians.ProjectiveCurve
open Jacobians.RiemannSurface.BoundaryWordPolynomial

variable (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂])

/-- The g = 1 polynomial family: the single primitive `c·X` for the
orientation constant `c` (so `F = c·z`, `h = c` — the #225 data). -/
noncomputable def ellipticPoly :
    Fin (genus (Elliptic ω₁ ω₂ h)) → Polynomial ℂ :=
  fun _ => C ((orientationConstant ω₁ ω₂ : ℝ) : ℂ) * X

/-- The g = 1 instance of the R2 Gram word: the elliptic period blocks
against the polynomial cut data, by the #225 area computation. -/
theorem elliptic_R2GramWord (i j : Fin (genus (Elliptic ω₁ ω₂ h))) :
    ((arcAPeriodMatrix (ellipticLoops ω₁ ω₂ h)
          fun m => ellipticFormBasis ω₁ ω₂ h m)ᵀ
          * (arcBPeriodMatrix (ellipticLoops ω₁ ω₂ h)
              fun m => ellipticFormBasis ω₁ ω₂ h m).map (starRingEnd ℂ)
        - (arcBPeriodMatrix (ellipticLoops ω₁ ω₂ h)
              fun m => ellipticFormBasis ω₁ ω₂ h m)ᵀ
          * (arcAPeriodMatrix (ellipticLoops ω₁ ω₂ h)
              fun m => ellipticFormBasis ω₁ ω₂ h m).map (starRingEnd ℂ)) i j
      = - Jacobians.boundaryForm
          (fun z => ((ellipticPoly ω₁ ω₂ h j).derivative).eval z)
          (fun z => (ellipticPoly ω₁ ω₂ h i).eval z) := by
  have hd : (fun z => ((ellipticPoly ω₁ ω₂ h j).derivative).eval z)
      = fun _ : ℂ => ((orientationConstant ω₁ ω₂ : ℝ) : ℂ) := by
    funext z
    simp [ellipticPoly]
  have hFe : (fun z => (ellipticPoly ω₁ ω₂ h i).eval z)
      = fun z : ℂ => ((orientationConstant ω₁ ω₂ : ℝ) : ℂ) * z := by
    funext z
    simp [ellipticPoly]
  rw [hd, hFe]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, arcAPeriodMatrix_elliptic ω₁ ω₂ h,
    arcBPeriodMatrix_elliptic ω₁ ω₂ h, Fintype.sum_unique]
  rw [boundaryForm_const_linear, normSq_orientationConstant]
  exact elliptic_word_R2_lhs ω₁ ω₂

/-- **The g = 1 datum, re-derived through the polynomial engine**: the
engine's three inputs are supplied by the proven elliptic computations
(`elliptic_periodMatrix_symm`, `elliptic_R2GramWord`, nonvanishing of
the orientation constant) — the wall shape is satisfiable at genus 1. -/
noncomputable def ellipticArcBoundaryWordDataPoly :
    ArcBoundaryWordDataInterior (ellipticLoops ω₁ ω₂ h)
      (ellipticFormBasis ω₁ ω₂ h) :=
  polyArcBoundaryWordData (ellipticLoops ω₁ ω₂ h) (ellipticFormBasis ω₁ ω₂ h)
    (ellipticPoly ω₁ ω₂ h)
    (by
      have hc : ((orientationConstant ω₁ ω₂ : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (orientationConstant_pos ω₁ ω₂ h).ne'
      refine linearIndependent_unique_iff.mpr ?_
      simpa [ellipticPoly] using Polynomial.C_ne_zero.mpr hc)
    (elliptic_periodMatrix_symm ω₁ ω₂ h)
    (elliptic_R2GramWord ω₁ ω₂ h)

end BoundaryWordElliptic
end Jacobians.RiemannSurface
