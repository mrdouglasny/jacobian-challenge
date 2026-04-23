/-
`ofCurveImpl`: axiom-stub for the Abel-Jacobi map.

**Classical content.** For a compact Riemann surface `X` of genus `g`,
fix a basepoint `P₀ : X`. The **Abel-Jacobi map** is
    `ofCurve P₀ : X → Jacobian X`
    `P ↦ [∫_{P₀}^P ω_1, …, ∫_{P₀}^P ω_g]`
in terms of a basis `ω_1, …, ω_g` of `HolomorphicOneForm X`, with
integration along any smooth path from `P₀` to `P` (well-defined modulo
the period lattice).

This is a **classical, canonical definition** — the Abel-Jacobi map is
the central object connecting the complex-analytic and algebraic-
geometric views of a curve.

**Why axiomatized.** The definition requires:
  - A chosen basis of `HolomorphicOneForm X` — we have one via
    `Jacobians.Jacobian.jacobianBasis` (from `Module.finBasis`).
  - Path integrals of holomorphic 1-forms — requires the
    `PathIntegral.lean` subproject (multi-week) or the
    `AX_AnalyticCycleBasis`-based approach.

Following the `periodMap` / `intersectionForm` pattern, we axiomatize
the typed value and let downstream code reference it. The axiom is
retired to a `def` when path integration lands.

## Properties (separate axioms, TODO)

Abel's theorem and related: `ofCurve_contMDiff` (smooth), `ofCurve_self`
(sends basepoint to 0), `ofCurve_inj` (injective for positive genus,
= Abel's theorem). These are separate axioms to be declared when
needed.

See `docs/formalization-plan.md` §7; discharge priority #10
(`AX_AbelTheorem`).
Reference: Mumford Vol I §II.3; Griffiths-Harris Ch. 2.3; Forster Ch. III.
-/
import Jacobians.Jacobian.Construction

namespace Jacobians.Axioms

open scoped Manifold Topology
open scoped ContDiff
open Jacobians Jacobians.RiemannSurface

/-- **Axiom-stub.** The Abel-Jacobi map `ofCurve P₀ : X → Jacobian X`
sending `P` to the integral `[∫_{P₀}^P ω_i]_i` in period-lattice
coordinates. Retired to a `def` when `PathIntegral.lean` is available.

The universe is `Type u` (matching `Jacobian : Type u`), tracking
Buzzard's `Jacobian (X : Type u) : Type u` signature. -/
axiom ofCurveImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ : X) : X → Jacobian X

/-- **Axiom-stub.** The pushforward map
`pushforward f hf : Jacobian X →ₜ+ Jacobian Y` associated to a
holomorphic map `f : X → Y` between compact Riemann surfaces.

Classical definition: `f_*[γ] := [f ∘ γ]` on the level of loops, extended
linearly to `H_1` and then to the period-lattice quotient. Well-defined
because `f` sends loops to loops (continuity) and the period map is
natural. -/
axiom pushforwardImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y

/-- **Axiom-stub.** The pullback map
`pullback f hf : Jacobian Y →ₜ+ Jacobian X` associated to a holomorphic
map `f : X → Y`.

Classical definition: `f^*ω := ω ∘ df` on the level of 1-forms, then
dualised to the Jacobian via `periodMap`. Equal to zero if `f` is
constant (no 1-forms to pull back). -/
axiom pullbackImpl (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (Y : Type v) [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X

/-- **Axiom-stub.** The degree of a holomorphic map between compact
Riemann surfaces. Zero if `f` is constant; otherwise the common
fiber-count `|f⁻¹(q)|` weighted by local multiplicities (well-defined
by `AX_BranchLocus`). -/
axiom degreeImpl {X : Type u} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type v} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ

end Jacobians.Axioms
