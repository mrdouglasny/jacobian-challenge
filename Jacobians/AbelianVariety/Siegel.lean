/-
`SiegelUpperHalfSpace g` — the space of complex symmetric `g × g` matrices
with positive-definite imaginary part.

This is the moduli space for principally-polarized abelian varieties of
dimension `g`, and the domain of the Riemann theta function. For `g = 1`
it is the usual upper half plane (canonical identification with Mathlib's
`UpperHalfPlane` via the `(· 0 0)` projection).

**Role in this project.**
* Theta domain: `Theta.lean` defines `RiemannTheta (z, τ)` for
  `z : Fin g → ℂ`, `τ : SiegelUpperHalfSpace g`.
* Period-matrix staging: the normalized period matrix `τ(X)` of a compact
  Riemann surface `X` lands in `SiegelUpperHalfSpace (genus X)` by
  Riemann's bilinear relations (`AX_RiemannBilinear`).
* Concrete lattice helper: for `τ : SiegelUpperHalfSpace g`, the columns
  of `[I | τ]` span a full-rank ℤ-lattice in `ℂ^g` — this is the standard
  concrete example of an `IsZLattice ℝ` outside the abstract period
  construction.

See `docs/formalization-plan.md` §3.2.
-/
import Jacobians.AbelianVariety.Lattice

namespace Jacobians.AbelianVariety

open Matrix

/-- The Siegel upper half space `𝔥_g`: complex symmetric `g × g` matrices
whose imaginary part (entrywise) is positive definite. -/
structure SiegelUpperHalfSpace (g : ℕ) where
  /-- Underlying matrix. -/
  val : Matrix (Fin g) (Fin g) ℂ
  /-- The matrix is symmetric: `val = valᵀ`. -/
  isSymm : val.IsSymm
  /-- The imaginary part of `val` (entrywise) is positive definite as a real matrix. -/
  imPosDef : (val.map Complex.im).PosDef

namespace SiegelUpperHalfSpace

variable {g : ℕ}

instance : CoeFun (SiegelUpperHalfSpace g) (fun _ => Matrix (Fin g) (Fin g) ℂ) :=
  ⟨fun τ => τ.val⟩

@[ext]
theorem ext {τ σ : SiegelUpperHalfSpace g} (h : τ.val = σ.val) : τ = σ := by
  cases τ; cases σ; simp_all

-- TODO (g = 1 compatibility): canonical bijection
--   `SiegelUpperHalfSpace 1 ≃ UpperHalfPlane` via `τ ↦ τ 0 0`.
--   Useful as a sanity check and for reusing Mathlib's upper-half-plane API.

-- TODO (lattice from columns): define
--   `SiegelUpperHalfSpace.lattice (τ : SiegelUpperHalfSpace g) : Submodule ℤ (Fin g → ℂ)`
-- spanned by the columns of `[I_g | τ]` (i.e. `Fin g ⊕ Fin g → Fin g → ℂ`
-- sending the first g copies to the standard basis vectors and the next
-- g copies to the columns of τ). Then provide `DiscreteTopology` and
-- `IsZLattice ℝ` instances — the positive-definite imaginary part of τ
-- gives the full real rank.

-- TODO (Siegel as complex manifold): `SiegelUpperHalfSpace g` is an open
-- subset of `Matrix (Fin g) (Fin g) ℂ` (the pos-def imaginary part
-- condition is open). Provide `TopologicalSpace`, `ChartedSpace`, and
-- `IsManifold 𝓘(ℂ, Matrix (Fin g) (Fin g) ℂ) ω` instances.
-- (Not needed for the 24 Challenge sorries; needed for Mumford Vol I
-- §II.4 and the full theta-modular-form story.)

-- TODO (Sp(2g, ℤ)-action): define the `Sp(2g, ℤ)`-action on
-- `SiegelUpperHalfSpace g` by fractional linear transformations
--   τ ↦ (A τ + B)(C τ + D)⁻¹
-- for `((A, B), (C, D)) : Sp(2g, ℤ)`. Not on the critical path for the 24
-- sorries; needed for the dual / polarization story in Mumford Vol I §II.4.

end SiegelUpperHalfSpace

end Jacobians.AbelianVariety
