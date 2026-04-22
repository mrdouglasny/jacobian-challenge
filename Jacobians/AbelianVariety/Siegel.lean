/-
`SiegelUpperHalfSpace g` — the space of complex symmetric `g × g` matrices
with positive-definite imaginary part.

This is the moduli space for principally-polarized abelian varieties of
dimension `g`, and the domain of the Riemann theta function. For `g = 1`
it is the usual upper half plane (canonical identification with Mathlib's
`UpperHalfPlane` via the `(· 0 0)` projection).

**Implementation choice (per Gemini-3-Pro review of 2026-04-21):** defined
as a `Subtype` of `Matrix (Fin g) (Fin g) ℂ`, NOT as a `structure`. Subtype
inherits `TopologicalSpace`, `MetricSpace`, `NormedAddCommGroup` structure
from the ambient matrix space automatically; a `structure` would require
manual instantiation of each.

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
whose imaginary part (entrywise) is positive definite.

Defined as a subtype so that `TopologicalSpace`, `MetricSpace`, and
`NormedAddCommGroup` transfer automatically from the ambient matrix space. -/
def SiegelUpperHalfSpace (g : ℕ) : Type :=
  { τ : Matrix (Fin g) (Fin g) ℂ // τ.IsSymm ∧ (τ.map Complex.im).PosDef }

namespace SiegelUpperHalfSpace

variable {g : ℕ}

/-- Access the underlying matrix of a Siegel upper-half-space point. -/
def val (τ : SiegelUpperHalfSpace g) : Matrix (Fin g) (Fin g) ℂ := τ.1

/-- The symmetry condition `τ = τᵀ`. -/
theorem isSymm (τ : SiegelUpperHalfSpace g) : τ.val.IsSymm := τ.2.1

/-- The imaginary part (entrywise) is positive definite. -/
theorem imPosDef (τ : SiegelUpperHalfSpace g) : (τ.val.map Complex.im).PosDef := τ.2.2

instance : CoeFun (SiegelUpperHalfSpace g) (fun _ => Matrix (Fin g) (Fin g) ℂ) :=
  ⟨fun τ => τ.val⟩

@[ext]
theorem ext {τ σ : SiegelUpperHalfSpace g} (h : τ.val = σ.val) : τ = σ :=
  Subtype.ext h

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
