/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license; see the LICENSE file vendored alongside the
original source at `vendor/kirov-jacobian-claude/LICENSE`.
Original source: https://github.com/rkirov/jacobian-claude
                 (commit 7ce9e2e8, 2026-04-24).

Vendored into this repository on 2026-04-25 by Michael R Douglas.
Modifications relative to upstream:
- Renamespaced from `Jacobians[.Montel]` to `Jacobians.Vendor.Kirov[.Montel]`.
- Updated transitive imports to match the new namespace.
No mathematical content was altered.
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Genus of a compact Riemann surface

Defined as the ℂ-dimension of global holomorphic 1-forms:
`genus X := Module.finrank ℂ (HolomorphicOneForms X)`.

This matches the analytic definition; with real content
(`FiniteDimensional ℂ (HOF X)` from Cartan–Serre) it agrees with the
topological definition `finrank ℤ (H₁(X, ℤ)) / 2` by Riemann–Roch /
Dolbeault.

The `HolomorphicOneForms` definition is inlined here (rather than
imported from `HolomorphicForms.lean`) to avoid a circular dependency:
`HolomorphicForms.lean` imports `Genus.lean`.
-/

namespace Jacobians.Vendor.Kirov

open scoped Manifold ContDiff Bundle

/-- The ℂ-vector space of global analytic sections of the cotangent bundle
of a compact connected complex 1-manifold.

Mathematically: global holomorphic 1-forms on `X`. Defined here (rather
than in `HolomorphicForms.lean`) so that `genus` below can refer to it. -/
def HolomorphicOneForms (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)

section HOFInstances

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

noncomputable instance : AddCommGroup (HolomorphicOneForms X) :=
  inferInstanceAs (AddCommGroup
    (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)))

noncomputable instance : Module ℂ (HolomorphicOneForms X) :=
  inferInstanceAs (Module ℂ
    (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)))

end HOFInstances

open scoped Manifold ContDiff

/-- The genus of a compact Riemann surface, defined as the ℂ-dimension of
global holomorphic 1-forms. Since `Module.finrank` returns `0` for
non-finite-dimensional modules, this is well-defined unconditionally;
the `FiniteDimensional ℂ (HolomorphicOneForms X)` instance (in
`HolomorphicForms.lean`, content-gated) is required for `genus` to be
the "right" number. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Module.finrank ℂ (Jacobians.Vendor.Kirov.HolomorphicOneForms X)

/-- A compact Riemann surface has genus 0 iff it is homeomorphic to the sphere.
This is the "anti-hack" constraint preventing `∀ X, genus X = 0`.

**Classical result** (Forster §16.3: Uniformization theorem; Miranda §V): a
compact Riemann surface of genus 0 is homeomorphic to the 2-sphere. Real
proof would follow from Uniformization or Riemann–Roch (genus 0 ⇒ a
non-constant meromorphic function with a single simple pole gives a
biholomorphism X → ℂP¹ ≃ S²).

**Stated as `axiom` for handoff** (was `:= sorry` in upstream). To
discharge: prove the same statement and replace this `axiom` with a
`theorem`. See `vendor/kirov-jacobian-claude/HANDOFF.md`. -/
axiom genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))

end Jacobians.Vendor.Kirov
