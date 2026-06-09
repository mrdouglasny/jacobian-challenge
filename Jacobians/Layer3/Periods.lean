/-
# Layer 3 — Phase C: the period cluster over basis-free Riemann bilinear primitives

Two primitives — `AX_RBR1` (isotropy / Stokes) and `AX_RBR2` (Hodge positivity) —
stated over the genuine `periodMap` and a symplectic `H₁` basis, routed through the
matrix engine's symplectic form `Q` (which **avoids 2-form integration** in Lean).
The period matrix's symmetry, the positive-definiteness of `Im τ`, and the full
period lattice are then theorems over these primitives plus the merged engines
(`Layer3.PeriodLattice`, `Layer3.RiemannBilinear`).

Both statements were vetted per-axiom by Gemini deep-think (2026-06-09, statement
first): SATISFIABLE / FAITHFUL, with the `AX_RBR2` sign verified on the genus-1
torus. Build plan: `docs/planning/LAYER3_PHASE_C_BUILD.md`.
-/
import Jacobians.Layer3.RiemannBilinear
import Jacobians.Axioms.AnalyticCycleBasis
import Jacobians.RiemannSurface.Periods

namespace Jacobians.Layer3

open scoped Manifold Topology ContDiff
open Jacobians.RiemannSurface Jacobians.Axioms

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The period vector of a holomorphic 1-form `η` over a symplectic `H₁` basis
`b`: its A-periods `(∫_{α_i} η)_i` paired with its B-periods `(∫_{β_i} η)_i`,
as an element of `PeriodVector (genus X) = ℂ^g × ℂ^g`. -/
def periodVec {x₀ : X} (b : AnalyticCycleBasis X x₀) (η : HolomorphicOneForm X) :
    PeriodVector (genus X) :=
  (fun i => periodMap X x₀ (b.isBasis (αEmbed i)) η,
    fun i => periodMap X x₀ (b.isBasis (βEmbed i)) η)

/-- The entrywise complex-conjugate period vector of `η`. -/
def conjPeriodVec {x₀ : X} (b : AnalyticCycleBasis X x₀) (η : HolomorphicOneForm X) :
    PeriodVector (genus X) :=
  (fun i => star (periodMap X x₀ (b.isBasis (αEmbed i)) η),
    fun i => star (periodMap X x₀ (b.isBasis (βEmbed i)) η))

@[simp]
theorem periodVec_fst {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (periodVec b η).1 i = periodMap X x₀ (b.isBasis (αEmbed i)) η :=
  rfl

@[simp]
theorem periodVec_snd {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (periodVec b η).2 i = periodMap X x₀ (b.isBasis (βEmbed i)) η :=
  rfl

/-- **Layer-3 Phase-C axiom (vetted DT 2026-06-09, SATISFIABLE/FAITHFUL; not yet
discharged).** First Riemann bilinear relation (isotropy / Stokes): the period
vectors of any two holomorphic 1-forms are isotropic for the symplectic form `Q`.

Equivalently `∫_X η ∧ ζ = 0`, which holds because the wedge of two `(1,0)`-forms
is a `(2,0)`-form and so vanishes on a curve; stated via `Q` to avoid 2-form
integration in Lean. Forces the normalized period matrix to be symmetric.

Reference: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 2 §2;
Forster, *Lectures on Riemann Surfaces*, §20. -/
axiom AX_RBR1 {x₀ : X} (b : AnalyticCycleBasis X x₀) :
    ∀ η ζ : HolomorphicOneForm X, Q (periodVec b η) (periodVec b ζ) = 0

/-- **Layer-3 Phase-C axiom (vetted DT 2026-06-09, SATISFIABLE/FAITHFUL; not yet
discharged).** Second Riemann bilinear relation (Hodge positivity): for every
nonzero holomorphic 1-form `η`, `i · Q(period η, conj period η)` is a strictly
positive real.

Equivalently `i ∫_X η ∧ η̄ > 0` (the Hodge norm; `η ∧ η̄ = -2i|f|² dx∧dy`
locally), stated via `Q` to avoid 2-form integration. `i · Q` is automatically
real (`Q` is purely imaginary here, each term being `z - z̄`), so `.re` is
lossless. The sign was verified on the genus-1 torus (`ω = dz`: `(i·Q).re = 2 Im τ
> 0`). Forces `Im τ ≻ 0`.

Reference: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 2 §2;
Mumford, *Tata Lectures on Theta I*, Ch. II §2. -/
axiom AX_RBR2 {x₀ : X} (b : AnalyticCycleBasis X x₀) :
    ∀ η : HolomorphicOneForm X, η ≠ 0 →
      0 < (Complex.I * Q (periodVec b η) (conjPeriodVec b η)).re

open scoped Matrix

@[simp]
theorem conjPeriodVec_fst {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (conjPeriodVec b η).1 i = star ((periodVec b η).1 i) :=
  rfl

@[simp]
theorem conjPeriodVec_snd {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (η : HolomorphicOneForm X) (i : Fin (genus X)) :
    (conjPeriodVec b η).2 i = star ((periodVec b η).2 i) :=
  rfl

/-- The A-period matrix of a holomorphic-form basis `cω` against the α-cycles of
the symplectic basis `b`: `A i j = ∫_{α_i} (cω j)`. -/
def aPeriodMatrix {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  fun i j => periodMap X x₀ (b.isBasis (αEmbed i)) (cω j)

/-- The B-period matrix `∫_{β_i} (cω j)` of a form basis (un-normalized). -/
def bPeriodMatrix {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  fun i j => periodMap X x₀ (b.isBasis (βEmbed i)) (cω j)

/-- Periods of a basis combination expand linearly. -/
theorem periodMap_equivFun_symm {x₀ : X}
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (γ : H1 X x₀) (c : Fin (genus X) → ℂ) :
    periodMap X x₀ γ (cω.equivFun.symm c) =
      ∑ j, c j * periodMap X x₀ γ (cω j) := by
  rw [cω.equivFun_symm_apply, map_sum]
  simp_rw [map_smul, smul_eq_mul]

/-- The A-periods of `∑ c_j ω_j` are `A *ᵥ c`. -/
theorem periodVec_fst_eq_aMulVec {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (c : Fin (genus X) → ℂ) :
    (periodVec b (cω.equivFun.symm c)).1 = aPeriodMatrix b cω *ᵥ c := by
  funext i
  rw [periodVec_fst, periodMap_equivFun_symm]
  simp only [aPeriodMatrix, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- The B-periods of `∑ c_j ω_j` are `B *ᵥ c`. -/
theorem periodVec_snd_eq_bMulVec {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (c : Fin (genus X) → ℂ) :
    (periodVec b (cω.equivFun.symm c)).2 = bPeriodMatrix b cω *ᵥ c := by
  funext i
  rw [periodVec_snd, periodMap_equivFun_symm]
  simp only [bPeriodMatrix, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **A-period normalization (from `AX_RBR2`).** No nonzero holomorphic 1-form
has all A-periods zero, so the A-period matrix of any form basis has trivial
kernel: `A *ᵥ c = 0 → c = 0`. -/
theorem aPeriodMatrix_mulVec_eq_zero {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    {c : Fin (genus X) → ℂ} (h : aPeriodMatrix b cω *ᵥ c = 0) : c = 0 := by
  by_contra hc
  have hη0 : cω.equivFun.symm c ≠ 0 := by
    rw [Ne, LinearEquiv.map_eq_zero_iff]; exact hc
  have hAfst : (periodVec b (cω.equivFun.symm c)).1 = 0 := by
    rw [periodVec_fst_eq_aMulVec, h]
  have hQ :
      Q (periodVec b (cω.equivFun.symm c)) (conjPeriodVec b (cω.equivFun.symm c)) = 0 := by
    simp only [Q]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h1 : (periodVec b (cω.equivFun.symm c)).1 k = 0 := congrFun hAfst k
    have h2 : (conjPeriodVec b (cω.equivFun.symm c)).1 k = 0 := by
      rw [conjPeriodVec_fst, h1, star_zero]
    rw [h1, h2]; ring
  have hpos := AX_RBR2 b (cω.equivFun.symm c) hη0
  rw [hQ, mul_zero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- The A-period matrix of any holomorphic-form basis is invertible (trivial
kernel + square over the field `ℂ`). -/
theorem aPeriodMatrix_isUnit {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    IsUnit (aPeriodMatrix b cω) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hvz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hv (aPeriodMatrix_mulVec_eq_zero b cω hvz)

private theorem mulVec_col_eq {g : ℕ} (M N : Matrix (Fin g) (Fin g) ℂ) (j : Fin g) :
    M *ᵥ (fun k => N k j) = fun i => (M * N) i j := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- `A · A⁻¹ = 1` for the (invertible) A-period matrix. -/
theorem aPeriodMatrix_mul_inv {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    aPeriodMatrix b cω * (aPeriodMatrix b cω)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (aPeriodMatrix_isUnit b cω))

/-- The normalized period matrix `τ = B · A⁻¹` (B-periods of the A-normalized
form basis). Symmetric with `Im τ ≻ 0` by the reductions below. -/
def tauMatrix {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Matrix (Fin (genus X)) (Fin (genus X)) ℂ :=
  bPeriodMatrix b cω * (aPeriodMatrix b cω)⁻¹

/-- The `j`-th normalized holomorphic differential `ω̂_j = ∑_k (A⁻¹)_{kj} ω_k`,
chosen so its A-periods are `δ_{·j}`. -/
def normalizedForm {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (j : Fin (genus X)) : HolomorphicOneForm X :=
  cω.equivFun.symm (fun k => (aPeriodMatrix b cω)⁻¹ k j)

/-- The normalized differentials realize the engine's `[I | τ]` columns:
`periodVec b ω̂_j = col τ j`. -/
theorem periodVec_normalizedForm {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (j : Fin (genus X)) :
    periodVec b (normalizedForm b cω j) = col (tauMatrix b cω) j := by
  have hfst : (periodVec b (normalizedForm b cω j)).1 = Pi.single j 1 := by
    rw [normalizedForm, periodVec_fst_eq_aMulVec, mulVec_col_eq, aPeriodMatrix_mul_inv]
    funext i
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hsnd : (periodVec b (normalizedForm b cω j)).2 = fun i => tauMatrix b cω i j := by
    rw [normalizedForm, periodVec_snd_eq_bMulVec, mulVec_col_eq]
    rfl
  rw [show col (tauMatrix b cω) j = (Pi.single j (1 : ℂ), fun i => tauMatrix b cω i j) from rfl]
  exact Prod.ext hfst hsnd

/-- **THM_Tau_Symmetric.** From `AX_RBR1`, the normalized period matrix is
symmetric. -/
theorem tauMatrix_isSymm {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    (tauMatrix b cω).IsSymm := by
  refine tau_symmetric_of_rbr1 (fun i j => ?_)
  have h := AX_RBR1 b (normalizedForm b cω i) (normalizedForm b cω j)
  rwa [periodVec_normalizedForm, periodVec_normalizedForm] at h

theorem conjPeriodVec_eq {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (η : HolomorphicOneForm X) :
    conjPeriodVec b η = (star (periodVec b η).1, star (periodVec b η).2) :=
  rfl

/-- The A-normalized combination `∑_j c_j ω̂_j = ∑ (A⁻¹ *ᵥ c)_k ω_k`. -/
def normalizedCombo {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (c : Fin (genus X) → ℂ) : HolomorphicOneForm X :=
  cω.equivFun.symm ((aPeriodMatrix b cω)⁻¹ *ᵥ c)

/-- The period vector of `∑ c_j ω̂_j` is the engine's `omegaCol τ c = (c, τ *ᵥ c)`. -/
theorem periodVec_normalizedCombo {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (c : Fin (genus X) → ℂ) :
    periodVec b (normalizedCombo b cω c) = omegaCol (tauMatrix b cω) c := by
  have hfst : (periodVec b (normalizedCombo b cω c)).1 = c := by
    rw [normalizedCombo, periodVec_fst_eq_aMulVec, Matrix.mulVec_mulVec,
      aPeriodMatrix_mul_inv, Matrix.one_mulVec]
  have hsnd : (periodVec b (normalizedCombo b cω c)).2 = tauMatrix b cω *ᵥ c := by
    rw [normalizedCombo, periodVec_snd_eq_bMulVec, Matrix.mulVec_mulVec]
    rfl
  rw [show omegaCol (tauMatrix b cω) c = (c, tauMatrix b cω *ᵥ c) from rfl]
  exact Prod.ext hfst hsnd

/-- The conjugate period vector of `∑ c_j ω̂_j` is the engine's `conjCol τ c`. -/
theorem conjPeriodVec_normalizedCombo {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (c : Fin (genus X) → ℂ) :
    conjPeriodVec b (normalizedCombo b cω c) = conjCol (tauMatrix b cω) c := by
  rw [conjPeriodVec_eq, periodVec_normalizedCombo]
  rfl

/-- A nonzero coefficient vector gives a nonzero normalized form (`A⁻¹` is
injective). -/
theorem normalizedCombo_ne_zero {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    {c : Fin (genus X) → ℂ} (hc : c ≠ 0) : normalizedCombo b cω c ≠ 0 := by
  rw [normalizedCombo, Ne, LinearEquiv.map_eq_zero_iff]
  intro h0
  refine hc ?_
  have h1 : aPeriodMatrix b cω *ᵥ ((aPeriodMatrix b cω)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, aPeriodMatrix_mul_inv, Matrix.one_mulVec]
  rw [h0, Matrix.mulVec_zero] at h1
  exact h1.symm

/-- **THM_Tau_PosDef.** From `AX_RBR1` + `AX_RBR2`, the imaginary part of the
normalized period matrix is positive definite. -/
theorem tauMatrix_posDef {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    ((tauMatrix b cω).map Complex.im).PosDef := by
  refine tau_posDef_of_rbr2 (fun i j => ?_) (fun c hc => ?_)
  · have h := AX_RBR1 b (normalizedForm b cω i) (normalizedForm b cω j)
    rwa [periodVec_normalizedForm, periodVec_normalizedForm] at h
  · have h := AX_RBR2 b (normalizedCombo b cω c) (normalizedCombo_ne_zero b cω hc)
    rwa [periodVec_normalizedCombo, conjPeriodVec_normalizedCombo] at h

end

end Jacobians.Layer3
