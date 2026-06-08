/-
Opaque type stubs for divisors, line bundles, and their sheaf
cohomology on a compact Riemann surface.

## Purpose

Supports the real (non-doc-only) statements of `AX_RiemannRoch`,
`AX_SerreDuality`, `AX_AbelTheorem`. Each axiom needs to reference
`LineBundle D`, `H⁰(X, L)`, `H¹(X, L)`, and the canonical sheaf `Ω¹_X`.
`Divisor X` and `Divisor.deg` are real `FreeAbelianGroup` definitions in
`RiemannSurface/Divisor.lean`; `H0` is now the concrete Riemann-Roch space
`riemannRochSpace D`. The remaining opaque placeholders are the line bundle
object itself, `H1`, the canonical divisor, and `LineBundle.ofDivisor`.

## Discharge route

Eventual discharge for the remaining placeholders: line bundles as
`𝒪(D) := sheaf of meromorphic functions f with div f + D ≥ 0`, and `H1`
via Čech cohomology or derived functors.

For the Jacobian Challenge specifically, the ℂ-dim of `H⁰` and `H¹` is
what matters. Even `Divisor`'s full `FreeAbelianGroup` encoding is not
strictly needed — only that divisors form an ℤ-module with a degree.

## File structure

All declarations in `namespace Jacobians.Axioms`. Each is an `axiom`
(data or Prop) with classical references. When Mathlib's sheaf
cohomology lands, these retire to `def`s.

See `docs/completion-plan.md` workstream A4.
Reference: Forster, *Lectures on Riemann Surfaces*, Ch. I §8 (divisors)
+ Ch. II §15-17 (line bundles + sheaves); Mumford Vol I §II.2.
-/
import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Opaque axiom type.** The line bundle `𝒪(D)` associated to a
divisor `D` on `X`. Forms a rank-1 locally-free sheaf; we only expose
the ℂ-vector spaces `H⁰` and `H¹` below. -/
axiom LineBundle {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) : Type

/-- The space of global sections `H⁰(X, L)` of a line bundle indexed by `D`,
implemented as the concrete Riemann-Roch space `L(D)`. The line-bundle argument
is intentionally ignored until `LineBundle` itself is de-opaqued. -/
noncomputable def H0 {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (_L : LineBundle D) : Type _ :=
  riemannRochSpace D

/-- `H⁰(X, L)` is a ℂ-vector space. -/
noncomputable instance H0.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    AddCommGroup (H0 L) :=
  inferInstanceAs (AddCommGroup (riemannRochSpace D))

noncomputable instance H0.instModule {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    Module ℂ (H0 L) :=
  inferInstanceAs (Module ℂ (riemannRochSpace D))

/-- **Opaque axiom type.** The first sheaf cohomology `H¹(X, L)` of a
line bundle `L`. Classically: Čech cohomology over a Leray cover. -/
axiom H1 {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) : Type

axiom H1.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    AddCommGroup (H1 L)
attribute [instance] H1.instAddCommGroup

axiom H1.instModule {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    Module ℂ (H1 L)
attribute [instance] H1.instModule

/-- **Opaque axiom.** The canonical sheaf `Ω¹_X` is a line bundle,
represented by a distinguished divisor class `K : Divisor X` up to
linear equivalence. -/
axiom canonicalDivisor (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Divisor X

/-- The line bundle `𝒪(D)` as an axiom-level constructor. -/
axiom LineBundle.ofDivisor {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) : LineBundle D

end Jacobians.Axioms

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open Jacobians.Axioms

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- Since `H0 (LineBundle.ofDivisor D)` is definitionally `riemannRochSpace D`,
the comparison is the identity linear equivalence. -/
theorem H0_equiv_riemannRochSpace (D : Divisor X) :
    Nonempty (H0 (LineBundle.ofDivisor D) ≃ₗ[ℂ] riemannRochSpace D) :=
  ⟨LinearEquiv.refl ℂ (riemannRochSpace D)⟩

end Jacobians.RiemannSurface
