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
import Jacobians.Axioms.PeriodLatticeBase
import Jacobians.RiemannSurface.Periods
import Jacobians.AbelianVariety.Siegel

namespace Jacobians.Layer3

open scoped Manifold Topology ContDiff
open Jacobians.RiemannSurface Jacobians.Axioms Jacobians.AbelianVariety

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

/-- The normalized period matrix packaged as a Siegel upper-half-space element
(symmetric with `Im ≻ 0`). -/
def tauSiegel {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    SiegelUpperHalfSpace (genus X) :=
  ⟨tauMatrix b cω, tauMatrix_isSymm b cω, tauMatrix_posDef b cω⟩

@[simp]
theorem tauSiegel_val {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    (tauSiegel b cω).val = tauMatrix b cω :=
  rfl

/-- The coordinate-space automorphism given by the invertible matrix `A⁻¹`. -/
private def eInvMat {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    (Fin (genus X) → ℂ) ≃ₗ[ℂ] (Fin (genus X) → ℂ) :=
  LinearEquiv.ofLinear (Matrix.toLin' (aPeriodMatrix b cω)⁻¹)
    (Matrix.toLin' (aPeriodMatrix b cω))
    (by rw [← Matrix.toLin'_mul,
          Matrix.nonsing_inv_mul _
            ((Matrix.isUnit_iff_isUnit_det _).mp (aPeriodMatrix_isUnit b cω)),
          Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul,
          Matrix.mul_nonsing_inv _
            ((Matrix.isUnit_iff_isUnit_det _).mp (aPeriodMatrix_isUnit b cω)),
          Matrix.toLin'_one])

/-- The A-normalized differentials `ω̂` as a `Module.Basis` (`cω` transformed by
the invertible `A⁻¹`). -/
def normalizedBasis {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X) :=
  cω.map (cω.equivFun ≪≫ₗ (eInvMat b cω ≪≫ₗ cω.equivFun.symm))

theorem normalizedBasis_apply {x₀ : X} (b : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) (j : Fin (genus X)) :
    normalizedBasis b cω j = normalizedForm b cω j := by
  rw [normalizedBasis, Module.Basis.map_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply]
  have hself : cω.equivFun (cω j) = Pi.single j 1 := by
    funext k
    simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  rw [hself, normalizedForm]
  congr 1
  show eInvMat b cω (Pi.single j 1) = fun k => (aPeriodMatrix b cω)⁻¹ k j
  rw [eInvMat, LinearEquiv.ofLinear_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

/-- **Riemann bilinear relations, PROVED** (the exact existential of
`AX_RiemannBilinear`): there exist a symplectic `H₁` basis, an A-normalized
basis of holomorphic 1-forms, and a Siegel upper-half-space matrix `τ` whose
entries are the B-periods. Derived from `AX_RBR1` + `AX_RBR2` through the
axiom-free matrix engine — the symplectic basis comes from
`AX_AnalyticCycleBasis`, the starting form basis from `Module.finBasis`
(`genus X` is definitionally `finrank ℂ (HolomorphicOneForm X)`). -/
theorem riemannBilinear_exists (x₀ : X) :
    ∃ (b : AnalyticCycleBasis X x₀)
      (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
      (τ : SiegelUpperHalfSpace (genus X)),
      (∀ i j : Fin (genus X),
        periodMap X x₀ (b.isBasis (αEmbed i)) (cω j) = if i = j then 1 else 0) ∧
      (∀ i j : Fin (genus X),
        τ.val i j = periodMap X x₀ (b.isBasis (βEmbed i)) (cω j)) := by
  obtain ⟨b⟩ := AX_AnalyticCycleBasis x₀
  set cω₀ : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X) :=
    Module.finBasis ℂ (HolomorphicOneForm X) with hcω₀
  refine ⟨b, normalizedBasis b cω₀, tauSiegel b cω₀, fun i j => ?_, fun i j => ?_⟩
  · have h := congrFun (congrArg Prod.fst (periodVec_normalizedForm b cω₀ j)) i
    rw [normalizedBasis_apply, ← periodVec_fst, h]
    simp [col, Pi.single_apply]
  · have h := congrFun (congrArg Prod.snd (periodVec_normalizedForm b cω₀ j)) i
    rw [normalizedBasis_apply, ← periodVec_snd, h, tauSiegel_val]
    rfl

/-! ### Period-lattice discharge

`periodLatticeInBasis X x₀ b` (the lattice consumed by the Jacobian bridge) is
a discrete full `ℤ`-lattice for EVERY form basis `b`: first identify it for the
A-normalized basis with the engine's `periodLattice τ` (`[I | τ]` columns, via
the symmetry of `τ` for the row/column bridge), then transport to an arbitrary
basis along the dual-coordinate change (a `ℂ`-linear automorphism of `ℂ^g`),
using Mathlib's `ZLattice.comap` instances. -/

theorem periodMapInBasis_apply (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (γ : H1 X x₀) (i : Fin (genus X)) :
    periodMapInBasis X x₀ b γ i = periodMap X x₀ γ (b i) := by
  simp [periodMapInBasis, Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr]

private theorem range_eq_span_image {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] {ι : Type*} (v : Module.Basis ι ℤ M) (f : M →ₗ[ℤ] N) :
    LinearMap.range f = Submodule.span ℤ (Set.range (⇑f ∘ ⇑v)) := by
  rw [LinearMap.range_eq_map, ← v.span_eq, Submodule.map_span, Set.range_comp]

/-- The α-cycles of the symplectic basis map to the `I`-columns. -/
theorem periodMapInBasis_normalized_alpha {x₀ : X} (cb : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) (i : Fin (genus X)) :
    periodMapInBasis X x₀ (normalizedBasis cb cω) (cb.isBasis (αEmbed i))
      = periodColumns (tauMatrix cb cω) (Sum.inl i) := by
  funext j
  rw [periodMapInBasis_apply, normalizedBasis_apply, periodColumns_inl]
  have h := congrFun (congrArg Prod.fst (periodVec_normalizedForm cb cω j)) i
  rw [← periodVec_fst, h]
  simp [col, Pi.single_apply, eq_comm]

/-- The β-cycles of the symplectic basis map to the `τ`-columns (via `τ = τᵀ`). -/
theorem periodMapInBasis_normalized_beta {x₀ : X} (cb : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) (i : Fin (genus X)) :
    periodMapInBasis X x₀ (normalizedBasis cb cω) (cb.isBasis (βEmbed i))
      = periodColumns (tauMatrix cb cω) (Sum.inr i) := by
  funext j
  rw [periodMapInBasis_apply, normalizedBasis_apply, periodColumns_inr]
  have h := congrFun (congrArg Prod.snd (periodVec_normalizedForm cb cω j)) i
  rw [← periodVec_snd, h]
  have hs := tauMatrix_isSymm cb cω
  simpa [col] using Matrix.IsSymm.apply hs j i

/-- The symplectic-basis image of the normalized period map is exactly the set
of `[I | τ]` columns. -/
theorem range_periodMapInBasis_normalized {x₀ : X} (cb : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    Set.range (⇑(periodMapInBasis X x₀ (normalizedBasis cb cω)) ∘ ⇑cb.isBasis)
      = Set.range (periodColumns (tauMatrix cb cω)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨k, rfl⟩
    by_cases h : (k : ℕ) < genus X
    · have hkeq : αEmbed (X := X) ⟨(k : ℕ), h⟩ = k := Fin.ext rfl
      refine ⟨Sum.inl ⟨k, h⟩, ?_⟩
      rw [← periodMapInBasis_normalized_alpha cb cω ⟨k, h⟩, Function.comp_apply, hkeq]
    · have hk2 := k.isLt
      have hkeq : βEmbed (X := X) ⟨(k : ℕ) - genus X, by omega⟩ = k := by
        apply Fin.ext
        simp only [βEmbed]
        omega
      refine ⟨Sum.inr ⟨(k : ℕ) - genus X, by omega⟩, ?_⟩
      rw [← periodMapInBasis_normalized_beta cb cω ⟨(k : ℕ) - genus X, by omega⟩,
        Function.comp_apply, hkeq]
  · rintro _ ⟨k, rfl⟩
    cases k with
    | inl i => exact ⟨αEmbed i, periodMapInBasis_normalized_alpha cb cω i⟩
    | inr i => exact ⟨βEmbed i, periodMapInBasis_normalized_beta cb cω i⟩

/-- In normalized coordinates, the period lattice is the engine's `[I | τ]`
column lattice. -/
theorem periodLatticeInBasis_normalized_eq {x₀ : X} (cb : AnalyticCycleBasis X x₀)
    (cω : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    periodLatticeInBasis X x₀ (normalizedBasis cb cω)
      = periodLattice (tauMatrix cb cω) (tauMatrix_posDef cb cω) := by
  rw [periodLatticeInBasis, range_eq_span_image cb.isBasis,
    range_periodMapInBasis_normalized]
  have hb : ⇑(periodBasis (tauMatrix cb cω) (tauMatrix_posDef cb cω))
      = periodColumns (tauMatrix cb cω) :=
    funext (periodBasis_apply _ _)
  rw [periodLattice, hb]

/-- Transport `DiscreteTopology` along an equality of submodules. -/
private theorem discrete_of_eq {E : Type*} [NormedAddCommGroup E]
    {L₁ L₂ : Submodule ℤ E} (h : L₁ = L₂) [DiscreteTopology L₁] :
    DiscreteTopology L₂ := by
  subst h; infer_instance

/-- Transport `IsZLattice` along an equality of submodules. -/
private theorem isZLattice_of_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {L₁ L₂ : Submodule ℤ E} (h : L₁ = L₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂] [hZ : IsZLattice ℝ L₁] :
    IsZLattice ℝ L₂ := by
  subst h; exact hZ

/-- Dual-coordinate change between two form bases: the `ℂ`-linear automorphism
of `ℂ^g` sending the `b₁`-coordinates of a functional to its `b₂`-coordinates. -/
noncomputable def dualCoordChange
    (b₁ b₂ : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    (Fin (genus X) → ℂ) ≃ₗ[ℂ] (Fin (genus X) → ℂ) :=
  b₁.dualBasis.equivFun.symm ≪≫ₗ b₂.dualBasis.equivFun

theorem periodMapInBasis_comp (x₀ : X)
    (b₁ b₂ : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X))
    (γ : H1 X x₀) :
    periodMapInBasis X x₀ b₂ γ
      = dualCoordChange b₁ b₂ (periodMapInBasis X x₀ b₁ γ) := by
  simp [periodMapInBasis, dualCoordChange]

/-- The inverse dual-coordinate change (`b₂`-coordinates back to
`b₁`-coordinates) as a continuous `ℝ`-linear equivalence, in the exact shape
consumed by Mathlib's `ZLattice.comap` instances. -/
noncomputable def dualCoordChangeCLE
    (b₁ b₂ : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    (Fin (genus X) → ℂ) ≃L[ℝ] (Fin (genus X) → ℂ) :=
  ((dualCoordChange b₁ b₂).symm.restrictScalars ℝ).toContinuousLinearEquiv

/-- The `b₂`-coordinate lattice is the pullback of the `b₁`-coordinate lattice
along the dual-coordinate change. -/
theorem periodLatticeInBasis_eq_comap (x₀ : X)
    (b₁ b₂ : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    periodLatticeInBasis X x₀ b₂
      = ZLattice.comap ℝ (periodLatticeInBasis X x₀ b₁)
          (dualCoordChangeCLE b₁ b₂).toLinearMap := by
  ext v
  have hcoe : ∀ w, (dualCoordChangeCLE b₁ b₂) w = (dualCoordChange b₁ b₂).symm w :=
    fun w => rfl
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ, ?_⟩
    rw [periodMapInBasis_comp x₀ b₁ b₂ γ]
    show periodMapInBasis X x₀ b₁ γ
      = (dualCoordChangeCLE b₁ b₂) (dualCoordChange b₁ b₂ (periodMapInBasis X x₀ b₁ γ))
    rw [hcoe, LinearEquiv.symm_apply_apply]
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    rw [periodMapInBasis_comp x₀ b₁ b₂ γ, hγ]
    show (dualCoordChange b₁ b₂) ((dualCoordChange b₁ b₂).symm v) = v
    exact LinearEquiv.apply_symm_apply _ v

/-- **DISCHARGE (for `instPeriodLatticeDiscrete`).** The coordinate period
lattice is discrete for every basis of holomorphic 1-forms. -/
theorem periodLatticeInBasis_discrete (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    DiscreteTopology (periodLatticeInBasis X x₀ b) := by
  obtain ⟨cb⟩ := AX_AnalyticCycleBasis x₀
  set b₁ := normalizedBasis cb (Module.finBasis ℂ (HolomorphicOneForm X)) with hb₁
  haveI h₁ : DiscreteTopology (periodLatticeInBasis X x₀ b₁) :=
    discrete_of_eq
      (periodLatticeInBasis_normalized_eq cb (Module.finBasis ℂ (HolomorphicOneForm X))).symm
  exact discrete_of_eq (periodLatticeInBasis_eq_comap x₀ b₁ b).symm

/-- **DISCHARGE (for `AX_PeriodLattice`).** The coordinate period lattice is a
full `ℤ`-lattice in `ℂ^g` for every basis of holomorphic 1-forms. -/
theorem periodLatticeInBasis_isZLattice (x₀ : X)
    (b : Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForm X)) :
    letI := periodLatticeInBasis_discrete x₀ b
    IsZLattice ℝ (periodLatticeInBasis X x₀ b) := by
  obtain ⟨cb⟩ := AX_AnalyticCycleBasis x₀
  set b₁ := normalizedBasis cb (Module.finBasis ℂ (HolomorphicOneForm X)) with hb₁
  haveI h₁d : DiscreteTopology (periodLatticeInBasis X x₀ b₁) :=
    discrete_of_eq
      (periodLatticeInBasis_normalized_eq cb (Module.finBasis ℂ (HolomorphicOneForm X))).symm
  haveI h₁z : IsZLattice ℝ (periodLatticeInBasis X x₀ b₁) :=
    isZLattice_of_eq
      (periodLatticeInBasis_normalized_eq cb (Module.finBasis ℂ (HolomorphicOneForm X))).symm
  haveI hbd : DiscreteTopology (periodLatticeInBasis X x₀ b) :=
    periodLatticeInBasis_discrete x₀ b
  exact isZLattice_of_eq (periodLatticeInBasis_eq_comap x₀ b₁ b).symm

end

end Jacobians.Layer3
