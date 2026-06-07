import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.OddForm
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.Axioms.HyperellipticOddLiouville

open scoped Manifold ContDiff
open Jacobians.RiemannSurface
open Jacobians.ProjectiveCurve
open Jacobians.ProjectiveCurve.HyperellipticOdd

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- **Level 2 (Odd case):** Every holomorphic 1-form is represented chart-locally on the affine part
by `g(x) dx / y` for some polynomial `g` of degree `< H.genus`. -/
axiom AX_HyperellipticOddForm_polynomial_decomposition
    (form : HolomorphicOneForm (HyperellipticOdd H h)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.genus ∧
      ∀ (a : HyperellipticAffine H) (hpY : a ∈ HyperellipticAffine.smoothLocusY H)
        (q : HyperellipticOdd H h) (_hQ : q = (Option.some a : HyperellipticOdd H h))
        {z : ℂ}
        (_hz : z ∈ ((HyperellipticAffine.affineChartProjX a hpY) :
          OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target),
        form.coeff q z =
          g.eval z /
            (HyperellipticAffine.squareLocalHomeomorph a hpY).symm (H.f.eval z)

/-- **Level 3 (Odd case):** Every holomorphic 1-form on the odd curve
is of the shape `hyperellipticOddForm H h g` for a polynomial `g` of
degree `< H.genus`. -/
axiom AX_HyperellipticOddOneForm_eq_form
    (form : HolomorphicOneForm (HyperellipticOdd H h)) :
    ∃ g : Polynomial ℂ,
      g.natDegree < H.genus ∧
      form = hyperellipticOddForm g

/-- **Upper bound for the genus of the odd curve.** Derived from Level 3 surjectivity. -/
theorem genus_HyperellipticOdd_le (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Jacobians.RiemannSurface.genus (HyperellipticOdd H h) ≤ H.genus := by
  let n := H.genus
  let φ := hyperellipticOddFormLinearMap H h
  have hφ_surj : Function.Surjective φ := by
    intro form
    obtain ⟨g, hg_deg, hgform⟩ := AX_HyperellipticOddOneForm_eq_form form
    have hg_in : g ∈ Polynomial.degreeLT ℂ n := by
      rw [Polynomial.mem_degreeLT]
      by_cases hg : g = 0
      · rw [hg]; simp [Polynomial.degree_zero]
      · rw [Polynomial.degree_eq_natDegree hg]
        exact_mod_cast hg_deg
    refine ⟨⟨g, hg_in⟩, ?_⟩
    change hyperellipticOddForm g = form
    exact hgform.symm
  -- Module.rank inequality from surjective linear map.
  have h_rank_le : Module.rank ℂ (HolomorphicOneForm (HyperellipticOdd H h)) ≤
      Module.rank ℂ (Polynomial.degreeLT ℂ n) :=
    LinearMap.rank_le_of_surjective φ hφ_surj
  -- Convert to finrank.
  have h_target_finite : Module.Finite ℂ (Polynomial.degreeLT ℂ n) :=
    inferInstance
  have h_finrank_le : Module.finrank ℂ (HolomorphicOneForm (HyperellipticOdd H h)) ≤
      Module.finrank ℂ (Polynomial.degreeLT ℂ n) :=
    Module.finrank_le_finrank_of_rank_le_rank (by simpa using h_rank_le)
      (Module.rank_lt_aleph0 ℂ _)
  -- Compute Module.finrank ℂ (Polynomial.degreeLT ℂ n) = n.
  have h_finrank_degreeLT : Module.finrank ℂ (Polynomial.degreeLT ℂ n) = n := by
    rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ n)]; simp
  change Module.finrank ℂ (HolomorphicOneForm (HyperellipticOdd H h)) ≤ n
  rw [← h_finrank_degreeLT]; exact h_finrank_le

end Jacobians.Axioms.HyperellipticOddLiouville
