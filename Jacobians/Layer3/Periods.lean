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

end

end Jacobians.Layer3
