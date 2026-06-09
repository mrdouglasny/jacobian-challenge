/-
# Period lattice linear algebra

This module proves the linear-algebra engine behind the normalized period
lattice. If the imaginary part of a period matrix `τ` is positive definite,
then the real map `(x, y) ↦ x + τ y` from `ℝ^g × ℝ^g` to `ℂ^g` is injective.
Consequently the `2g` columns of `[I | τ]` are an `ℝ`-basis of `ℂ^g`, and
their integer span is a full `IsZLattice`.
-/

import Jacobians.AbelianVariety.Lattice

namespace Jacobians.Layer3

open Matrix

noncomputable section

/-- Real coordinate vectors of length `g`. -/
abbrev RealVec (g : ℕ) : Type := Fin g → ℝ

/-- Complex coordinate vectors of length `g`. -/
abbrev ComplexVec (g : ℕ) : Type := Fin g → ℂ

/-- The coordinatewise inclusion `ℝ^g → ℂ^g` as an `ℝ`-linear map. -/
def ofRealVecLinear (g : ℕ) : RealVec g →ₗ[ℝ] ComplexVec g where
  toFun x := fun i => (x i : ℂ)
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

@[simp]
theorem ofRealVecLinear_apply {g : ℕ} (x : RealVec g) (i : Fin g) :
    ofRealVecLinear g x i = (x i : ℂ) :=
  rfl

/-- Matrix multiplication by `τ`, restricted to real input coordinates. -/
def mulVecOfRealLinear {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    RealVec g →ₗ[ℝ] ComplexVec g :=
  (τ.mulVecLin.restrictScalars ℝ).comp (ofRealVecLinear g)

@[simp]
theorem mulVecOfRealLinear_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (y : RealVec g) :
    mulVecOfRealLinear τ y = τ *ᵥ (fun j => (y j : ℂ)) :=
  rfl

/-- The normalized period map `(x, y) ↦ x + τ y`, as an `ℝ`-linear map. -/
def periodLinearMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    (RealVec g × RealVec g) →ₗ[ℝ] ComplexVec g :=
  (ofRealVecLinear g).comp (LinearMap.fst ℝ (RealVec g) (RealVec g)) +
    (mulVecOfRealLinear τ).comp (LinearMap.snd ℝ (RealVec g) (RealVec g))

@[simp]
theorem periodLinearMap_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (x y : RealVec g) :
    periodLinearMap τ (x, y) =
      (fun i => (x i : ℂ) + (τ *ᵥ (fun j => (y j : ℂ))) i) :=
  rfl

/-- Imaginary part commutes with `mulVec` when the vector has real entries. -/
theorem im_mulVec_ofReal {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (y : RealVec g) :
    (fun i => ((τ *ᵥ (fun j => (y j : ℂ))) i).im) = (τ.map Complex.im) *ᵥ y := by
  classical
  ext i
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]

/-- A positive-definite real matrix has trivial kernel for `mulVec`. -/
theorem eq_zero_of_posDef_mulVec_eq_zero {g : ℕ} {A : Matrix (Fin g) (Fin g) ℝ}
    (hA : A.PosDef) {y : RealVec g} (hy : A *ᵥ y = 0) : y = 0 := by
  by_contra hy_ne
  have hpos := hA.dotProduct_mulVec_pos hy_ne
  simp [hy] at hpos

/--
Core period-lattice engine: if `Im τ` is positive definite, then
`(x, y) ↦ x + τ y` is injective over `ℝ`.
-/
theorem periodLinearMap_ker_eq_bot {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : (τ.map Complex.im).PosDef) :
    LinearMap.ker (periodLinearMap τ) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  rintro ⟨x, y⟩ hxy
  have him : (τ.map Complex.im) *ᵥ y = 0 := by
    have him_fun : (fun i => ((τ *ᵥ (fun j => (y j : ℂ))) i).im) = 0 := by
      ext i
      have hi := congr_fun hxy i
      have hi_im := congrArg Complex.im hi
      simpa [periodLinearMap] using hi_im
    simpa [im_mulVec_ofReal τ y] using him_fun
  have hy : y = 0 := eq_zero_of_posDef_mulVec_eq_zero hτ him
  have hx : x = 0 := by
    ext i
    have hi := congr_fun hxy i
    have hi_re := congrArg Complex.re hi
    simpa [periodLinearMap, hy, Matrix.mulVec] using hi_re
  ext i <;> simp [hx, hy]

/--
Function-level version of `periodLinearMap_ker_eq_bot`: the normalized period
map `(x, y) ↦ x + τ y` is injective.
-/
theorem periodLinearMap_injective {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : (τ.map Complex.im).PosDef) :
    Function.Injective (periodLinearMap τ) :=
  LinearMap.ker_eq_bot.mp (periodLinearMap_ker_eq_bot hτ)

/-- The product coordinate basis of `ℝ^g × ℝ^g`. -/
def periodDomainBasis (g : ℕ) : Module.Basis (Fin g ⊕ Fin g) ℝ (RealVec g × RealVec g) :=
  (Pi.basisFun ℝ (Fin g)).prod (Pi.basisFun ℝ (Fin g))

/-- The `2g` columns of `[I | τ]`, as vectors in `ℂ^g`. -/
def periodColumns {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g ⊕ Fin g) → ComplexVec g :=
  periodLinearMap τ ∘ periodDomainBasis g

@[simp]
theorem periodColumns_inl {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (j i : Fin g) :
    periodColumns τ (Sum.inl j) i = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst i
    simp [periodColumns, periodDomainBasis, Matrix.mulVec]
  · simp [periodColumns, periodDomainBasis, Matrix.mulVec, h]

@[simp]
theorem periodColumns_inr {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (j i : Fin g) :
    periodColumns τ (Sum.inr j) i = τ i j := by
  classical
  simp only [periodColumns, Function.comp_apply, periodDomainBasis, Module.Basis.prod_apply,
    Sum.elim_inr, LinearMap.inr_apply, Pi.basisFun_apply, periodLinearMap_apply,
    Pi.zero_apply]
  have hsingle :
      (fun k : Fin g => (((Pi.single j (1 : ℝ) : Fin g → ℝ) k) : ℂ)) =
        Pi.single j (1 : ℂ) := by
    ext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hk]
  simp only [hsingle, Matrix.mulVec_single_one, Matrix.col_apply, Complex.ofReal_zero, zero_add]

/-- The columns of `[I | τ]` are `ℝ`-linearly independent. -/
theorem periodColumns_linearIndependent {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : (τ.map Complex.im).PosDef) :
    LinearIndependent ℝ (periodColumns τ) := by
  simpa [periodColumns] using
    (periodDomainBasis g).linearIndependent.map' (periodLinearMap τ)
      (periodLinearMap_ker_eq_bot hτ)

/-- Cardinality of the column index equals the real dimension of `ℂ^g`. -/
theorem periodColumns_card_eq_finrank (g : ℕ) :
    Fintype.card (Fin g ⊕ Fin g) = Module.finrank ℝ (ComplexVec g) := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, Fintype.card_sum]
  omega

/-- The columns of `[I | τ]` form an `ℝ`-basis of `ℂ^g`. -/
def periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hτ : (τ.map Complex.im).PosDef) :
    Module.Basis (Fin g ⊕ Fin g) ℝ (ComplexVec g) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (b := periodColumns τ) (periodColumns_linearIndependent hτ)
    (periodColumns_card_eq_finrank g)

@[simp]
theorem periodBasis_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hτ : (τ.map Complex.im).PosDef) (k : Fin g ⊕ Fin g) :
    periodBasis τ hτ k = periodColumns τ k := by
  simp [periodBasis]

/-- The integer span of the columns of `[I | τ]`. -/
abbrev periodLattice {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hτ : (τ.map Complex.im).PosDef) : Submodule ℤ (ComplexVec g) :=
  Submodule.span ℤ (Set.range (periodBasis τ hτ))

/-- Discreteness of the integer span of the period columns. -/
instance periodLattice.discreteTopology {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hτ : (τ.map Complex.im).PosDef) :
    DiscreteTopology (periodLattice τ hτ) :=
  inferInstance

/-- Full-rank lattice property for the integer span of the period columns. -/
instance periodLattice.isZLattice {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (hτ : (τ.map Complex.im).PosDef) :
    IsZLattice ℝ (periodLattice τ hτ) :=
  inferInstance

end

end Jacobians.Layer3
