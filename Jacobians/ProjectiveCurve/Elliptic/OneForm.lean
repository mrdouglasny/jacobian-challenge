import Jacobians.ProjectiveCurve.Elliptic
import Jacobians.RiemannSurface.OneForm
import Jacobians.RiemannSurface.Genus

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface
open Jacobians.AbelianVariety

/-- The invariant differential `dz` on an elliptic curve, represented by the constant
chart-local coefficient `1`. -/
noncomputable def ellipticDz (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    HolomorphicOneForm (Elliptic ω₁ ω₂ h) :=
  ⟨fun _ _ => (1 : ℂ), by
    refine ⟨fun _ => analyticOn_const, ?_⟩
    intro x y z hz hyz
    change (1 : ℂ) =
      (1 : ℂ) *
        (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1)
    have hf := ComplexTorus.transition_fderiv_apply_one (L := ellipticLattice ω₁ ω₂ h)
      (p := x) (q := y) hz hyz
    calc
      (1 : ℂ) = (1 : ℂ) * 1 := by norm_num
      _ = (1 : ℂ) *
          (fderiv ℂ ((extChartAt 𝓘(ℂ, ℂ) y) ∘ (extChartAt 𝓘(ℂ, ℂ) x).symm) z 1) := by
            exact (congrArg (fun w : ℂ => (1 : ℂ) * w) hf).symm⟩

theorem ellipticDz_ne_zero (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    ellipticDz ω₁ ω₂ h ≠ 0 := by
  intro hzero
  let x : Elliptic ω₁ ω₂ h := Classical.choice inferInstance
  have hcoeff :
      (ellipticDz ω₁ ω₂ h).coeff x 0 = (0 : HolomorphicOneForm (Elliptic ω₁ ω₂ h)).coeff x 0 :=
    congrArg (fun form : HolomorphicOneForm (Elliptic ω₁ ω₂ h) => form.coeff x 0) hzero
  have hone : (ellipticDz ω₁ ω₂ h).coeff x 0 = 1 := rfl
  have hzeroCoeff : (0 : HolomorphicOneForm (Elliptic ω₁ ω₂ h)).coeff x 0 = 0 := rfl
  have : (1 : ℂ) = 0 := by
    calc
      (1 : ℂ) = (ellipticDz ω₁ ω₂ h).coeff x 0 := hone.symm
      _ = (0 : HolomorphicOneForm (Elliptic ω₁ ω₂ h)).coeff x 0 := hcoeff
      _ = 0 := hzeroCoeff
  exact one_ne_zero this

theorem genus_Elliptic_pos (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    0 < genus (Elliptic ω₁ ω₂ h) := by
  unfold genus
  by_contra hgenus
  have hfinrank : Module.finrank ℂ (HolomorphicOneForm (Elliptic ω₁ ω₂ h)) = 0 :=
    Nat.eq_zero_of_not_pos hgenus
  letI : Subsingleton (HolomorphicOneForm (Elliptic ω₁ ω₂ h)) := Module.finrank_zero_iff.mp hfinrank
  exact ellipticDz_ne_zero ω₁ ω₂ h (Subsingleton.elim _ _)

end Jacobians.ProjectiveCurve
