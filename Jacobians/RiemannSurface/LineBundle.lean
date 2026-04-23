/-
Opaque type stubs for divisors, line bundles, and their sheaf
cohomology on a compact Riemann surface.

## Purpose

Supports the real (non-doc-only) statements of `AX_RiemannRoch`,
`AX_SerreDuality`, `AX_AbelTheorem`. Each axiom needs to reference
`Divisor X`, `LineBundle D`, `H⁰(X, L)`, `H¹(X, L)`, degree, and the
canonical sheaf `Ω¹_X` — none of which are in Mathlib at this pin.

We axiomatize these as **opaque types with ℂ-vector-space structure
and a `Divisor.deg` map to ℤ**. Each axiom is a classical construction
(divisors as formal ℤ-combinations of points; line bundles via the
`𝒪(D)` correspondence; sheaf cohomology via Čech), well-known but not
yet formalized.

## Discharge route

Eventual discharge: build `Divisor X` as a `FreeAbelianGroup` on `X`
(Mathlib has this) plus a degree map. Line bundles: `𝒪(D) := sheaf of
meromorphic functions `f` with `div f + D ≥ 0`` — needs meromorphic
function theory on complex manifolds. Sheaf cohomology: either Čech
(elementary) or derived functors (heavier).

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
import Jacobians.RiemannSurface.Genus

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Opaque axiom type.** The group of divisors on a compact Riemann
surface `X`. Classically: formal `ℤ`-combinations of points of `X`.
Forms an `AddCommGroup` via the declared instance below. -/
axiom Divisor (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Type

/-- Divisors form an additive commutative group. -/
axiom Divisor.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : AddCommGroup (Divisor X)
attribute [instance] Divisor.instAddCommGroup

/-- The degree of a divisor: for a formal combination `D = ∑ n_P · P`,
`deg D := ∑ n_P`. An `AddMonoidHom` `Divisor X →+ ℤ`. -/
axiom Divisor.deg (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Divisor X →+ ℤ

/-- **Opaque axiom type.** The subgroup of principal divisors: divisors
of meromorphic functions. Kernel of the divisor-to-Jacobian map
(Abel's theorem). -/
axiom PrincipalDivisors (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : AddSubgroup (Divisor X)

/-- **Opaque axiom type.** The line bundle `𝒪(D)` associated to a
divisor `D` on `X`. Forms a rank-1 locally-free sheaf; we only expose
the ℂ-vector spaces `H⁰` and `H¹` below. -/
axiom LineBundle {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) : Type

/-- **Opaque axiom type.** The space of global sections `H⁰(X, L)` of a
line bundle `L`. Classically: meromorphic functions `f` on `X` with
`div f + D ≥ 0` (i.e. holomorphic away from divisor poles, with
constrained orders). -/
axiom H0 {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) : Type

/-- `H⁰(X, L)` is a ℂ-vector space. -/
axiom H0.instAddCommGroup {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    AddCommGroup (H0 L)
attribute [instance] H0.instAddCommGroup

axiom H0.instModule {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    Module ℂ (H0 L)
attribute [instance] H0.instModule

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
