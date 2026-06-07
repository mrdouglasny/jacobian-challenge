/-
# Elliptic curves

An elliptic curve is presented as a complex torus `ℂ / Λ` where `Λ` is a
rank-2 ℤ-lattice in `ℂ`, i.e. the ℤ-span of two ℂ-numbers `ω₁, ω₂` that
are ℝ-linearly independent.

This module provides:
  - `ellipticLattice ω₁ ω₂ h : Submodule ℤ ℂ` — the lattice `ℤω₁ + ℤω₂`.
  - `IsZLattice ℝ (ellipticLattice ω₁ ω₂ h)` — automatic via Mathlib's
    `instIsZLatticeRealSpan` applied to the ℝ-basis of `ℂ` consisting of
    `{ω₁, ω₂}`.
  - `Elliptic ω₁ ω₂ h : Type` — the quotient `ℂ ⧸ Λ`, defined as
    `ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)`.
  - All seven Buzzard-required typeclass instances inherited from
    `ComplexTorus` **for free** (same mechanism used in
    `Jacobians/Jacobian/Construction.lean`).

## Status

The seven instances land immediately because `ComplexTorus V L` already
has them axiom-free (see `Jacobians/AbelianVariety/ComplexTorus.lean`).
No new axioms are introduced.

## Deferred

* `genus (Elliptic ω₁ ω₂ h) = 1` — requires the `OneForm.lean` predicate
  refinement. At the current stub level, `HolomorphicOneForm = ⊥` for
  all `X`, so `genus = 0`. Once refined, we get `genus (Elliptic) = 1`
  via the meromorphic function `dz` on the torus.
* `Jacobian (Elliptic ω₁ ω₂ h) ≅ Elliptic ω₁ ω₂ h` — the Jacobian of
  an elliptic curve is the curve itself. Needs the above + the
  bridge through the period map. Will be a nice worked example once
  `periodMap` is a real def.
* Concrete instantiation of `AX_AnalyticCycleBasis` on `Elliptic` — the
  `A`- and `B`-cycles are the line segments from `0` to `ω₁` and from
  `0` to `ω₂` in the universal cover `ℂ`, projected down. Provides a
  concrete witness that the axiom is non-vacuous.

## Standard form

When `ω₁ = 1` and `ω₂ = τ` for `τ ∈ SiegelUpperHalfSpace 1 ≃
UpperHalfPlane`, the elliptic curve is in its classical "normalized"
form. A helper `Elliptic.ofUpperHalfPlane τ` can be added later.

## References

* Mumford, *Tata Lectures on Theta I*, Ch. I.
* Silverman, *The Arithmetic of Elliptic Curves*, Ch. VI.
-/
import Jacobians.AbelianVariety.ComplexTorus

namespace Jacobians.ProjectiveCurve

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.AbelianVariety

/-- The ℝ-basis of `ℂ` given by two ℝ-linearly independent complex numbers
`{ω₁, ω₂}`. -/
noncomputable abbrev ellipticRealBasis (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂]) : Module.Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank h (by simp [Complex.finrank_real_complex])

/-- The ℤ-lattice `Λ = ℤω₁ + ℤω₂` in `ℂ`, given two ℝ-linearly
independent complex numbers.

`abbrev` so typeclass search sees through to
`Submodule.span ℤ (Set.range ⇑(ellipticRealBasis ω₁ ω₂ h))` — which
matches Mathlib's `DiscreteTopology` and `IsZLattice` instance
patterns. -/
noncomputable abbrev ellipticLattice (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂]) : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range (ellipticRealBasis ω₁ ω₂ h))

-- `DiscreteTopology` and `IsZLattice ℝ` on `ellipticLattice` are found
-- automatically by the `abbrev` unfolding above plus Mathlib's instances
-- `ZSpan.instDiscreteTopology...` and `instIsZLatticeRealSpan`.

/-- An **elliptic curve** `ℂ / (ℤω₁ + ℤω₂)` presented as a complex torus.

Seven Buzzard-required typeclass instances (see `Jacobian/Construction.lean`
for the analogous bridge on `Jacobian`) land automatically via
`ComplexTorus`:
  - `AddCommGroup`, `TopologicalSpace`, `IsTopologicalAddGroup`,
  - `T2Space`, `CompactSpace`,
  - `ChartedSpace ℂ`, `IsManifold 𝓘(ℂ) ω`, `LieAddGroup 𝓘(ℂ) ω`.

Since `V = ℂ` here, `Fin 1 → ℂ ≃ ℂ` and the model space matches
Buzzard's. -/
noncomputable def Elliptic (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    Type :=
  ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)

namespace Elliptic

variable {ω₁ ω₂ : ℂ} {h : LinearIndependent ℝ ![ω₁, ω₂]}

/-- Inherited: elliptic curve is an additive commutative group. -/
noncomputable instance : AddCommGroup (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (AddCommGroup (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: topological space. -/
noncomputable instance : TopologicalSpace (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (TopologicalSpace (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: topological additive group. -/
instance : IsTopologicalAddGroup (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (IsTopologicalAddGroup (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: Hausdorff. -/
instance : T2Space (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (T2Space (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: compact. -/
instance : CompactSpace (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (CompactSpace (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: connected (quotient of `ℂ`). -/
instance : ConnectedSpace (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (ConnectedSpace (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: charted over ℂ. -/
noncomputable instance : ChartedSpace ℂ (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (ChartedSpace ℂ (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: complex manifold (analytic smoothness class). -/
instance : IsManifold 𝓘(ℂ, ℂ) ω (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (IsManifold 𝓘(ℂ, ℂ) ω (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: Lie group structure. -/
instance : LieAddGroup 𝓘(ℂ, ℂ) ω (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (LieAddGroup 𝓘(ℂ, ℂ) ω (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

/-- Inherited: nonempty (every quotient of a nonempty group is nonempty). -/
instance : Nonempty (Elliptic ω₁ ω₂ h) :=
  inferInstanceAs (Nonempty (ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)))

-- TODO (genus_eq_one): `genus (Elliptic ω₁ ω₂ h) = 1`. Awaits
-- `OneForm.lean` predicate refinement.

-- TODO (analytic basis): concrete `AnalyticCycleBasis (Elliptic ω₁ ω₂ h) 0`
-- with A-cycle = segment [0, ω₁] and B-cycle = segment [0, ω₂]. Witness
-- that `AX_AnalyticCycleBasis` is non-vacuous.

end Elliptic

/-- For `τ ∈ ℂ` with positive imaginary part, `{1, τ}` is an ℝ-basis of `ℂ`.
Proof: the imaginary part of `a • 1 + b • τ = 0` is `b • τ.im`, which vanishes
iff `b = 0`; the real part is then `a = 0`. -/
theorem linearIndependent_one_of_pos_im {τ : ℂ} (hτ : 0 < τ.im) :
    LinearIndependent ℝ ![(1 : ℂ), τ] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h_im : (a • (1 : ℂ) + b • τ).im = (0 : ℂ).im := congrArg Complex.im hab
  simp at h_im
  have hb : b = 0 := h_im.resolve_right (ne_of_gt hτ)
  refine ⟨?_, hb⟩
  subst hb
  have h_re : (a • (1 : ℂ) + (0 : ℝ) • τ).re = (0 : ℂ).re := congrArg Complex.re hab
  simpa using h_re

/-- The **elliptic curve in normalized form** `ℂ / (ℤ + ℤτ)` for
`τ ∈ ℂ` with positive imaginary part. Takes `ω₁ = 1`, `ω₂ = τ`.

`abbrev` for transparent instance inheritance. -/
noncomputable abbrev Elliptic.ofUpperHalfPlane (τ : ℂ) (hτ : 0 < τ.im) : Type :=
  Elliptic 1 τ (linearIndependent_one_of_pos_im hτ)

-- All 8 Buzzard typeclass instances on `Elliptic.ofUpperHalfPlane τ hτ`
-- are inherited automatically via the `Elliptic` definition.
example (τ : ℂ) (hτ : 0 < τ.im) :
    LieAddGroup 𝓘(ℂ, ℂ) ω (Elliptic.ofUpperHalfPlane τ hτ) :=
  inferInstanceAs (LieAddGroup 𝓘(ℂ, ℂ) ω
    (Elliptic 1 τ (linearIndependent_one_of_pos_im hτ)))

end Jacobians.ProjectiveCurve
