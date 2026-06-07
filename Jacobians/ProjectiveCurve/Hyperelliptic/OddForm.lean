import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas
import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.RiemannSurface.OneForm
import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff
open Jacobians.RiemannSurface
open Polynomial

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- The unified coefficient family for `g(x) dx / y` on the odd curve `HyperellipticOdd H h`. -/
noncomputable def hyperellipticOddCoeff (g : Polynomial ℂ) :
    HyperellipticOdd H h → ℂ → ℂ := fun p z => by
  classical
  exact p.elim
    (if hz : z ∈ (infinityChart H h).target then
       if z = 0 then
         -2 * g.coeff (H.genus - 1) / H.f.leadingCoeff
       else
         let x := (infinityInverseMap H h z).val.1
         2 * g.eval x * x ^ (H.genus + 2) /
           (x * (Polynomial.derivative H.f).eval x - (2 * H.genus + 2) * H.f.eval x)
     else 0)
    (fun a => HyperellipticAffine.hyperellipticAffineCoeff g a z)

/-- The coefficient family is a holomorphic 1-form coefficient (member of the submodule). -/
axiom hyperellipticOddCoeff_mem_submodule (g : Polynomial ℂ)
    (hdeg : g.natDegree < H.genus) :
    hyperellipticOddCoeff (H := H) (h := h) g ∈
      holomorphicOneFormSubmodule (HyperellipticOdd H h)

/-- Holomorphic 1-form constructor for the odd curve. -/
noncomputable def hyperellipticOddForm (g : Polynomial ℂ) :
    HolomorphicOneForm (HyperellipticOdd H h) :=
  if hdeg : g.natDegree < H.genus then
    ⟨hyperellipticOddCoeff g, hyperellipticOddCoeff_mem_submodule g hdeg⟩
  else 0

/-- On low-degree polynomials, `hyperellipticOddForm` is the real form. -/
theorem hyperellipticOddForm_of_lt {g : Polynomial ℂ}
    (hDeg : g.natDegree < H.genus) :
    hyperellipticOddForm (H := H) (h := h) g =
      ⟨hyperellipticOddCoeff g, hyperellipticOddCoeff_mem_submodule g hDeg⟩ :=
  dif_pos hDeg

/-- The coefficient of a low-degree `hyperellipticOddForm`. -/
theorem hyperellipticOddForm_coeff_of_lt {g : Polynomial ℂ}
    (hDeg : g.natDegree < H.genus) :
    (hyperellipticOddForm (H := H) (h := h) g).coeff = hyperellipticOddCoeff g := by
  rw [hyperellipticOddForm_of_lt hDeg]; rfl

axiom hyperellipticOddCoeff_add (g g' : Polynomial ℂ) :
    hyperellipticOddCoeff (H := H) (h := h) (g + g') =
      hyperellipticOddCoeff g + hyperellipticOddCoeff g'

axiom hyperellipticOddCoeff_smul (c : ℂ) (g : Polynomial ℂ) :
    hyperellipticOddCoeff (H := H) (h := h) (c • g) =
      c • hyperellipticOddCoeff g

/-- `hyperellipticOddForm` of the zero polynomial is the zero form. -/
@[simp] theorem hyperellipticOddForm_zero :
    hyperellipticOddForm (H := H) (h := h) (0 : Polynomial ℂ) = 0 := by
  unfold hyperellipticOddForm
  split
  · apply Subtype.ext
    change hyperellipticOddCoeff (H := H) (h := h) 0 = 0
    have h1 := hyperellipticOddCoeff_smul (H := H) (h := h) 0 0
    simp only [zero_smul] at h1
    exact h1
  · rfl

/-- Every element of `degreeLT ℂ 0` is the zero polynomial. -/
private theorem eq_zero_of_mem_degreeLT_zero {p : Polynomial ℂ}
    (hp : p ∈ Polynomial.degreeLT ℂ 0) : p = 0 := by
  rw [Polynomial.mem_degreeLT, Nat.cast_zero, Nat.WithBot.lt_zero_iff,
    Polynomial.degree_eq_bot] at hp
  exact hp

/-- A polynomial in `degreeLT ℂ n` with `0 < n` has `natDegree < n`. -/
theorem natDegree_lt_of_mem_degreeLT {n : ℕ} (hn : 0 < n) {g : Polynomial ℂ}
    (hg : g ∈ Polynomial.degreeLT ℂ n) : g.natDegree < n := by
  by_cases h0 : g = 0
  · simpa [h0] using hn
  · rw [Polynomial.mem_degreeLT] at hg
    exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hg

/-- The packaged ℂ-linear map version of `hyperellipticOddForm`. -/
noncomputable def hyperellipticOddFormLinearMap (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Polynomial.degreeLT ℂ (H.genus) →ₗ[ℂ]
      HolomorphicOneForm (HyperellipticOdd H h) where
  toFun gd := hyperellipticOddForm gd.1
  map_add' gd gd' := by
    rcases Nat.eq_zero_or_pos (H.genus) with hn | hn
    · have e : ∀ p : Polynomial.degreeLT ℂ (H.genus), p.1 = 0 := by
        intro p; exact eq_zero_of_mem_degreeLT_zero (hn ▸ p.2)
      simp only [e, add_zero, hyperellipticOddForm_zero]
    · have h1 := natDegree_lt_of_mem_degreeLT hn gd.2
      have h2 := natDegree_lt_of_mem_degreeLT hn gd'.2
      have h3 : (gd.1 + gd'.1).natDegree < H.genus :=
        lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (max_lt h1 h2)
      have hEq : (gd + gd').val = gd.val + gd'.val := rfl
      rw [hEq]
      rw [hyperellipticOddForm_of_lt h1, hyperellipticOddForm_of_lt h2,
        hyperellipticOddForm_of_lt h3]
      apply Subtype.ext
      change hyperellipticOddCoeff (H := H) (h := h) (gd.1 + gd'.1) = _
      exact hyperellipticOddCoeff_add gd.1 gd'.1
  map_smul' c gd := by
    rcases Nat.eq_zero_or_pos (H.genus) with hn | hn
    · have e : ∀ p : Polynomial.degreeLT ℂ (H.genus), p.1 = 0 := by
        intro p; exact eq_zero_of_mem_degreeLT_zero (hn ▸ p.2)
      simp only [RingHom.id_apply, e, smul_zero, hyperellipticOddForm_zero]
    · have h1 := natDegree_lt_of_mem_degreeLT hn gd.2
      have h2 : (c • gd.1).natDegree < H.genus :=
        lt_of_le_of_lt (Polynomial.natDegree_smul_le c gd.1) h1
      have hEq : (c • gd).val = c • gd.val := rfl
      rw [hEq]
      rw [hyperellipticOddForm_of_lt h1, hyperellipticOddForm_of_lt h2]
      apply Subtype.ext
      change hyperellipticOddCoeff (H := H) (h := h) (c • gd.1) = _
      exact hyperellipticOddCoeff_smul c gd.1

/-- `hyperellipticOddForm` is injective on the low-degree subspace. -/
axiom hyperellipticOddForm_injective (H : HyperellipticData) (h : Odd H.f.natDegree) :
    Function.Injective (hyperellipticOddFormLinearMap H h)

end Jacobians.ProjectiveCurve.HyperellipticOdd
