/-
`AX_H1FreeRank2g`: first homology of a compact Riemann surface is free
abelian of rank twice the genus.

**Status (2026-04-22):** formerly an axiom; now a **theorem** derived
from `AX_AnalyticCycleBasis`, which supplies a ℤ-basis of `H_1(X, ℤ)`
indexed by `Fin (2 * genus X)` consisting of (the homology classes of)
piecewise-real-analytic cycles. Existence of *any* such basis is all
that's required to discharge `AX_H1FreeRank2g`.

The name and signature are preserved so downstream callers that import
`Jacobians.Axioms.H1FreeRank2g` directly continue to work; the declaration
now marks `theorem` instead of `axiom`, and the axiom count decreases by
one.

**Statement.** For `X` a compact, connected, T2 complex 1-manifold of
genus `g`, `H1 X x₀` (≅ `Abelianization (π₁ X x₀)`) is a free ℤ-module
of rank `2 * genus X`.

**Why true.** Classical CW-topology / simplicial homology; see the proof
sketches in `Jacobians/Axioms/AnalyticCycleBasis.lean`.

See `docs/formalization-plan.md` §7 and `docs/history.md`
(2026-04-22 PathIntegral design discussion).
-/
import Mathlib
import Jacobians.RiemannSurface.Homology
import Jacobians.RiemannSurface.Genus
import Jacobians.Axioms.AnalyticCycleBasis

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- For a compact Riemann surface `X`, `H1 X x₀` is free abelian of rank
`2 * genus X`. Derived from `AX_AnalyticCycleBasis`, which supplies a
concrete ℤ-basis indexed by `Fin (2 * genus X)` obtained from a
piecewise-real-analytic symplectic system of cycles. -/
theorem AX_H1FreeRank2g {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (x₀ : X) :
    Nonempty (Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)) := by
  obtain ⟨b⟩ := AX_AnalyticCycleBasis x₀
  exact ⟨b.isBasis⟩

end Jacobians.Axioms
