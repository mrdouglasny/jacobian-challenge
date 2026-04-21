/-
Lattice conventions for `Jacobians.AbelianVariety`.

Mathlib at the pinned commit already has a `Submodule`-based lattice API:
`Mathlib.Algebra.Module.ZLattice.Basic` provides

  class IsZLattice (K : Type*) [NormedField K] {E : Type*}
      [NormedAddCommGroup E] [NormedSpace K E]
      (L : Submodule ℤ E) [DiscreteTopology L] : Prop where
    span_top : span K (L : Set E) = ⊤

plus `instIsZLatticeRealSpan` (given a real basis `b : Basis ι ℝ E`, the
ℤ-span of `Set.range b` is a ℤ-lattice), `IsZLattice.basis` extracting a
ℤ-basis, `ZLattice.FG` finite-generation, fundamental domains, etc.

Rather than reinvent a parallel `FullRankLattice` type, this project uses
Mathlib's `IsZLattice` directly. We fix the following conventions for
downstream modules (`Siegel`, `ComplexTorus`, `Jacobian.Construction`):

* **Ambient space**: an arbitrary finite-dimensional ℂ-vector space `V`
  (equivalently a finite-dimensional ℝ-vector space with a chosen
  complex structure). We do *not* hardcode `V := Fin g → ℂ`; the
  basis-free Jacobian lives in `HolomorphicOneForm X →ₗ[ℂ] ℂ`, which is
  abstract.
* **Lattice type**: `Submodule ℤ V`, with typeclass instances
  `[DiscreteTopology L]` and `[IsZLattice ℝ L]`. The first is the
  discreteness; the second is full real rank.
* **Quotient**: use `V ⧸ L.toAddSubgroup` (Mathlib's `QuotientAddGroup`
  machinery) rather than `Submodule.Quotient` for consistency with the
  standard `AddCommGroup` / `TopologicalAddGroup` instances.

No new declarations are made in this file; it serves as a nexus for
the shared conventions. Concrete API and instance-providing lemmas
appear in `Siegel.lean` and `ComplexTorus.lean`.
-/
import Mathlib
