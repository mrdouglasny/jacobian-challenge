# Plan #1: Construct `pathIntegralBasepointFunctional`

## Axiom being retired

```lean
axiom pathIntegralBasepointFunctional (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (P₀ P : X) :
    HolomorphicOneForm X →ₗ[ℂ] ℂ
```

Location: `Jacobians/Axioms/AbelJacobiMap.lean:92`.

## Classical content

Given a holomorphic 1-form `ω` on `X`, return the integral `∫_{P₀}^P ω`
(a complex number). Linear in `ω` (ℂ-linear).

The result depends on the choice of path from `P₀` to `P` — two paths
differ by an element of the period lattice. We package the choice via
`Classical.choice` on a path-connected manifold.

## Target replacement

```lean
noncomputable def pathIntegralBasepointFunctional (X : Type*) [...]
    (P₀ P : X) : HolomorphicOneForm X →ₗ[ℂ] ℂ :=
  -- Choose any piecewise-real-analytic arc γ from P₀ to P
  let γ : AnalyticArc X := Classical.choice ⟨someDefaultArc P₀ P⟩
  -- Integrate form along γ via multi-chart path integration
  pathIntegralAnalyticArc γ
```

## Prerequisites

### A. Path existence: any two points on a path-connected manifold are joined by a piecewise-real-analytic arc.

```lean
axiom AX_pathExists (X : Type*) [...] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (P₀ P : X) : Nonempty (AnalyticArc X /- with endpoints P₀, P -/)
```

Mathlib provides path-connectedness for connected manifolds (via local
path-connectedness of manifolds + connected ⇒ path-connected). The
piecewise-real-analytic strengthening is classical — refine the path
into chart-local arcs that are analytic.

Effort: ~100 LOC.

### B. Multi-chart path integration: `pathIntegralAnalyticArc : AnalyticArc X → HolomorphicOneForm X →ₗ[ℂ] ℂ`.

Currently we have `pathIntegralOnChart` in `PathIntegral.lean` (for arcs
that stay in a single chart). Extend to general arcs:

1. Given `γ : AnalyticArc X`, cover `γ`'s image by a finite chart
   subcover (compactness of `[0, 1]`).
2. Partition `[0, 1] = [0, t₁] ∪ [t₁, t₂] ∪ ... ∪ [tₙ, 1]` subordinate
   to the cover.
3. On each `[tᵢ, tᵢ₊₁]`, use `pathIntegralOnChart`.
4. Sum the chart-local integrals.
5. Prove independence of the chart cover / partition via the cocycle
   property of `HolomorphicOneForm` — this is the key lemma and uses
   `SatisfiesCotangentCocycle`.

Effort: ~200 LOC.

### C. Verification against `AX_pathIntegral_local_antiderivative`

The existing axiom `AX_pathIntegral_local_antiderivative` asserts the
FTC-localised-to-chart property. Once the `def` is in place, this
becomes a **theorem** (derived from the chart-local integration
being the antiderivative of the coefficient).

Effort: ~50 LOC.

## Phases

| Phase | Content | Effort |
|---|---|---|
| P1 | `AX_pathExists` — piecewise-analytic path between any two points | 2–3 days |
| P2 | `pathIntegralAnalyticArc` — partition + sum + well-definedness | 5–7 days |
| P3 | `pathIntegralBasepointFunctional` as real def + retire axiom | 1 day |
| P4 | Retire `AX_pathIntegral_local_antiderivative` to theorem | 2 days |

**Total: ~1.5–2 weeks** focused contributor.

## Shared with Plan #2

Phases P1 and P2 also unlock Plan #2 (`loopIntegralToH1`) — a loop is
just an arc with equal endpoints. P3 differs but shares the entire
infrastructure below it.

## References

* Forster, *Lectures on Riemann Surfaces*, Ch. I §10 (path integrals
  on Riemann surfaces — chart-local formulation).
* Mumford, *Tata Lectures on Theta I*, §II.2.
* Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0.2.
* Mathlib: `MeasureTheory.Integral.CurveIntegral.Basic` for the
  chart-local primitive `curveIntegral`; `AnalyticArc` in
  `RiemannSurface/AnalyticArc.lean`.

## Exit criterion

- `pathIntegralBasepointFunctional` is a real `noncomputable def`.
- `AX_pathIntegral_local_antiderivative` is a theorem.
- Build green; 0 axioms for this workstream.
- Net axiom count delta: **–2** (retires `pathIntegralBasepointFunctional` and `AX_pathIntegral_local_antiderivative`; introduces `AX_pathExists` as a minor subsidiary).
