/-
Line-bundle cohomology wrappers used by the axiom-level APIs.

`LineBundle`, `H0`, `canonicalDivisor`, and `LineBundle.ofDivisor` live in
`LineBundleBasic` so Layer 3 can refer to them without importing the old RR/Serre
wrappers. This file adds the now de-opaqued first cohomology space by identifying
`H1(O(D))` with the Layer-3 `H1coh D`.
-/
import Jacobians.RiemannSurface.Cohomology.LineBundleBasic
import Jacobians.Layer3.Cohomology

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

universe u

/-- The first sheaf cohomology `H¹(X, L)` of a divisor line bundle, now wired to
the Layer-3 cohomology scaffold. The line-bundle argument is intentionally ignored
in the same way as `H0`; the divisor index carries the sheaf `O(D)`. -/
noncomputable def H1 {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (_L : LineBundle D) : Type u :=
  Jacobians.Layer3.H1coh D

noncomputable instance H1.instAddCommGroup {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    AddCommGroup (H1 L) := by
  change AddCommGroup (Jacobians.Layer3.H1coh D)
  infer_instance

noncomputable instance H1.instModule {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    Module ℂ (H1 L) := by
  change Module ℂ (Jacobians.Layer3.H1coh D)
  infer_instance

noncomputable instance H1.instFiniteDimensional {X : Type u} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {D : Divisor X} (L : LineBundle D) :
    FiniteDimensional ℂ (H1 L) := by
  change FiniteDimensional ℂ (Jacobians.Layer3.H1coh D)
  infer_instance

end Jacobians.Axioms
