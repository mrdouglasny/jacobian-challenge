/-
Basic line-bundle stubs and the de-opaqued `H0` bridge.

KEYSTONE FLIP (docs/planning/FLIP_CHECKLIST.md §2.1): `canonicalDivisor` is no longer an
opaque axiom — it is the `Classical.choose` of the PROVEN ∃-K Serre-duality package
`serreDuality_equiv_exists` (FlipPrep composition over the T-lane frame-trace
construction), so the verbatim Layer-3 `serreDuality_equiv` statement is its
`Classical.choose_spec`.
-/
import Jacobians.RiemannSurface.Cohomology.RiemannRochSpace
import Jacobians.Layer3.FlipPrep

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- The line bundle `𝒪(D)` associated to a divisor `D` on `X` — **formerly an
opaque axiom type**, de-opaqued (stub-retirement package, 2026-06-12). On a
compact Riemann surface `𝒪(D)` is determined up to isomorphism by `D`, and this
development only ever exposes its cohomology — `H⁰ = riemannRochSpace D` and
`H¹ = Layer3.H1coh D`, both real constructions that depend on `D` alone — so
the bundle object itself is the divisor-indexed tag type. A parameterized
structure (not `PUnit`) keeps `LineBundle D₁` and `LineBundle D₂` definitionally
distinct, so no consumer can silently cross divisors. -/
structure LineBundle {X : Type*} [TopologicalSpace X] [T2Space X]
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

/-- **The unconditional ∃-K Serre package at the `chartDiskCover` pin** (T-lane wall +
FlipPrep composition): a divisor `K` with `dim L(K) = genus X` and, for EVERY `D`, a
linear equivalence `H1coh D ≃ Dual(L(K − D))`. The genus-split trace residual is
discharged by the T-lane's `exists_canonicalData_frameTraceHypothesis`
(`FrameTrace.lean`: the canonical `ω₀ = df` datum carries its own frame-trace datum). -/
theorem serreDuality_equiv_exists (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    ∃ K : Divisor X,
      Module.finrank ℂ (riemannRochSpace K) = genus X ∧
      ∀ D : Divisor X,
        Nonempty (Jacobians.Layer3.H1coh D ≃ₗ[ℂ]
          Module.Dual ℂ (riemannRochSpace (K - D))) :=
  Jacobians.Layer3.serreDuality_equiv_exists_of_frameTrace
    fun _ => Jacobians.Dolbeault.exists_canonicalData_frameTraceHypothesis

/-- The canonical divisor: the chosen Serre-duality divisor — **formerly an opaque
axiom**, de-opaqued by the keystone flip to the `Classical.choose` of the proven
∃-K Serre package `serreDuality_equiv_exists`. -/
noncomputable def canonicalDivisor (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Divisor X :=
  Classical.choose (serreDuality_equiv_exists X)

/-- The defining property of `canonicalDivisor`: `dim L(K) = genus X`, and Serre duality
`H1coh D ≃ Dual(L(K − D))` at every `D` (the verbatim Layer-3 `serreDuality_equiv`
statement is the second component). -/
theorem canonicalDivisor_spec (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    Module.finrank ℂ (riemannRochSpace (canonicalDivisor X)) = genus X ∧
    ∀ D : Divisor X,
      Nonempty (Jacobians.Layer3.H1coh D ≃ₗ[ℂ]
        Module.Dual ℂ (riemannRochSpace (canonicalDivisor X - D))) :=
  Classical.choose_spec (serreDuality_equiv_exists X)

/-- The line bundle `𝒪(D)` of a divisor — **formerly an axiom-level
constructor**, now the canonical inhabitant of the de-opaqued tag type. -/
def LineBundle.ofDivisor {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) : LineBundle D :=
  ⟨⟩

end Jacobians.Axioms

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open Jacobians.Axioms

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ⊤ X]

/-- Since `H0 (LineBundle.ofDivisor D)` is definitionally `riemannRochSpace D`,
the comparison is the identity linear equivalence.

(`Axioms.Divisor` is written qualified: the FlipPrep import closure brings
`Jacobians.RiemannSurface.Divisor` into scope, which would otherwise shadow it
inside this namespace.) -/
theorem H0_equiv_riemannRochSpace (D : Axioms.Divisor X) :
    Nonempty (H0 (LineBundle.ofDivisor D) ≃ₗ[ℂ] riemannRochSpace D) :=
  ⟨LinearEquiv.refl ℂ (riemannRochSpace D)⟩

end Jacobians.RiemannSurface
