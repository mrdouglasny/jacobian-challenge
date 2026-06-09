/-
Basic line-bundle stubs and the de-opaqued `H0` bridge.
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
