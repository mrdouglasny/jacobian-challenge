/-
# Finite-dimensionality of holomorphic 1-forms (forwarded to bridge)

**Historical note.** This file used to declare an axiom
`AX_FiniteDimOneForms` asserting `FiniteDimensional ℂ (HolomorphicOneForm X)`
on the strength of Cartan–Serre / normal-families theory, with a single
global instance `instFiniteDimOneForms` discharged by that axiom.

As of 2026-04-25 the axiom is **retired**. Finite-dimensionality is now
derived in `Jacobians/Bridge/KirovHolomorphic.lean` by transferring
Kirov's real Montel-derived `FiniteDimensional ℂ (HolomorphicOneForms X)`
(vendored under `Jacobians.Vendor.Kirov`) along an injective ℂ-linear
bridge `HolomorphicOneForm X →ₗ[ℂ] Jacobians.Vendor.Kirov.HolomorphicOneForms X`.

The bridge has two **structural** axioms in its place
(`bridgeForm` exists; `bridgeForm` is injective). Both are mechanical
constructions in Mathlib's bundle/section formalism — far more
tractable than the original abstract Cartan–Serre claim.

This file is kept as a backward-compatibility shim: external consumers
that imported `Jacobians.Axioms.FiniteDimOneForms` to get the
`FiniteDimensional` instance still see the same global instance via the
re-export below.

See:
* `Jacobians/Bridge/KirovHolomorphic.lean` — the bridge.
* `vendor/kirov-jacobian-claude/HANDOFF.md` — discharge plan for the
  two bridge axioms.
* `docs/formalization-plan.md` §7, §4.6 — original axiom rationale.
-/

import Jacobians.Bridge.KirovHolomorphic

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.RiemannSurface

/-- **Backward-compatibility shim.** Re-export the bridge-derived
`FiniteDimensional` instance under its historical name `instFiniteDimOneForms`
so that consumers that referenced this name continue to work. -/
instance instFiniteDimOneForms {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    FiniteDimensional ℂ (HolomorphicOneForm X) :=
  Jacobians.Bridge.finiteDimensional_holomorphicOneForm

end Jacobians.Axioms
