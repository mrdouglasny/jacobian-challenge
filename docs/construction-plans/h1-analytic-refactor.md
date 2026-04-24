# Plan: Replace `H1` with piecewise-analytic simplicial H₁

_Drafted 2026-04-24. Strategic refactor: redefine `H1 X x₀` from the
topological `Additive (Abelianization (FundamentalGroup X x₀))` to the
**piecewise-analytic simplicial homology group** `H1Analytic X x₀`.
Retires `loopIntegralToH1` (function-existence axiom #2) and unblocks
a structural computation `H1Analytic (Elliptic ω₁ ω₂ h) ≃ ℤ²`._

## Motivation

The project uses `H1 X x₀` as the domain of `periodMap X x₀ : H1 X x₀
→+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)`, i.e., the target of "integrate
this holomorphic 1-form along a representative cycle."

Under the current definition `H1 X x₀ = Additive (Abelianization
(FundamentalGroup X x₀))`, a class has no canonical representative
amenable to integration — it's just an equivalence class of continuous
loops, with no piecewise-analytic structure. This forces
`periodMap` to route through `loopIntegralToH1`, currently axiomatized
(function-existence axiom #2 of 5).

The fix: **make the representative analytic by definition.** A 1-chain
is a formal ℤ-linear combination of piecewise-real-analytic arcs; a
cycle is one whose boundary cancels; a boundary is the image of a
2-chain's boundary operator. Then:

- Every cycle has canonical representatives — analytic arcs, piece by
  piece — so chart-local integration + summation yields a real number
  without axiomatisation.
- Stokes on chart 2-simplices makes the integral depend only on the
  homology class.
- `periodMap` becomes a real `def`, and `loopIntegralToH1` retires.

Bonus: for concrete surfaces (Elliptic, Hyperelliptic, ProjectiveLine)
we can **exhibit** the rank-`2g` homology basis as analytic loops
(e.g., α-loop `t ↦ mk(t ω₁)` on an elliptic curve), bypassing the
covering-space π₁ approach that Codex verified is blocked at the
current Mathlib pin.

## Mathematical content

For a topological space `X` with an atlas of `ChartedSpace ℂ` charts:

- **Piecewise-real-analytic arcs** `AnalyticArc X`: already defined in
  `Jacobians/RiemannSurface/AnalyticArc.lean`.
- **1-chains** `C1Analytic X := X →₀ ℤ`-with-arc-support, or cleaner:
  free abelian group on `AnalyticArc X`.
- **0-chains** `C0Analytic X := X →₀ ℤ`.
- **Boundary `∂₁ : C1Analytic X → C0Analytic X`**: `∂₁ γ = γ(1) - γ(0)`
  (endpoint difference).
- **2-simplices** `AnalyticTriangle X`: piecewise-real-analytic maps
  from the standard 2-simplex `Δ² ⊂ ℝ²` to `X` that factor through a
  single chart (or a finite refinement thereof — details in the
  "refinement" question below).
- **2-chains** `C2Analytic X := Σᵢ nᵢ · (analytic triangle Tᵢ)`.
- **Boundary `∂₂ : C2Analytic X → C1Analytic X`**: `∂₂ T = T|_{e₁} -
  T|_{e₂} + T|_{e₃}` (alternating sum of faces).
- **`∂₁ ∘ ∂₂ = 0`**: standard chain-complex identity.
- **`H1Analytic X x₀`**: cycles (ker ∂₁ restricted to x₀-based loops)
  modulo boundaries.

### Integration map

For a holomorphic 1-form `form : HolomorphicOneForm X` and a
1-chain `c = Σ nᵢ γᵢ`:

```
∫_c form := Σ nᵢ · ∫ (form.coeff (γᵢ(0)) ∘ (extChartAt ... γᵢ(0)) ∘ γᵢ) dt
```

(chart-local integration on each arc). Well-defined on cycles modulo
boundaries by Stokes (`∫_{∂T} = ∫∫_T dω = 0` for holomorphic ω since
`dω = 0` in complex dim 1).

## Lean design

### Layer 0: chain groups

```lean
/-- 1-chains with piecewise-analytic arcs as support. -/
structure AnalyticOneChain (X : Type*) [TopologicalSpace X] where
  support : Finset (AnalyticArc X)
  coeffs  : AnalyticArc X → ℤ
  supp_spec : ∀ γ, coeffs γ ≠ 0 → γ ∈ support

-- or simpler:
abbrev AnalyticOneChain (X : Type*) [TopologicalSpace X] : Type _ :=
  AnalyticArc X →₀ ℤ

/-- Boundary: endpoint difference as a ℤ-linear functional. -/
noncomputable def AnalyticOneChain.boundary (c : AnalyticOneChain X) : X →₀ ℤ :=
  c.sum fun γ n => Finsupp.single (γ.extend 1) n - Finsupp.single (γ.extend 0) n
```

Similarly `AnalyticTwoChain X` and `boundary : AnalyticTwoChain X → AnalyticOneChain X`.

### Layer 1: cycles, boundaries, H₁

```lean
/-- Cycles based at x₀: closed 1-chains with every arc endpoint matched
to another arc's start. (More precisely: chains whose boundary is zero,
with each arc-family homotopy rel endpoints based at x₀.) -/
def H1Analytic.cycles (X : Type*) [...] (x₀ : X) : AddSubgroup (AnalyticOneChain X) where
  carrier := { c | c.boundary = 0 ∧ -- plus a base-point constraint }
  -- closure proofs

def H1Analytic.boundaries (X : Type*) [...] (x₀ : X) : AddSubgroup (H1Analytic.cycles X x₀) :=
  -- image of ∂₂ restricted to based 2-chains

noncomputable def H1Analytic (X : Type*) [TopologicalSpace X] (x₀ : X) : Type _ :=
  H1Analytic.cycles X x₀ ⧸ (H1Analytic.boundaries X x₀).toAddSubgroup

instance : AddCommGroup (H1Analytic X x₀) := inferInstance -- via QuotientAddGroup
instance : Module ℤ (H1Analytic X x₀) := inferInstance
```

### Layer 2: path integration as a real `def`

```lean
/-- Integration of a 1-form along an analytic arc, chart-locally. -/
noncomputable def AnalyticArc.integrateOneForm
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (γ : AnalyticArc X) (form : HolomorphicOneForm X) : ℂ :=
  -- sum over chart cover of γ's image; each piece via intervalIntegral
  sorry  -- actual def below

/-- Extension to 1-chains by linearity. -/
noncomputable def AnalyticOneChain.integrate (c : AnalyticOneChain X)
    (form : HolomorphicOneForm X) : ℂ :=
  c.sum fun γ n => n • γ.integrateOneForm form

/-- The integration is zero on boundaries (Stokes). -/
theorem AnalyticTwoChain.boundary_integrate_eq_zero
    (T : AnalyticTwoChain X) (form : HolomorphicOneForm X) :
    T.boundary.integrate form = 0 := by
  -- via Stokes on chart-local 2-simplices + dω = 0 for 1-forms on 1-manifolds
  sorry  -- real proof via chart computation
```

### Layer 3: `periodMap` as real `def`

```lean
noncomputable def periodMap (X : Type*) [...] (x₀ : X) :
    H1Analytic X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ) :=
  QuotientAddGroup.lift _ 
    (fun c form => (c : AnalyticOneChain X).integrate form)
    (by intro c hc; -- hc says c is a boundary; apply Stokes lemma
        exact boundary_integrate_zero ...)
```

Everything downstream (`periodMapInBasis`, `periodLatticeInBasis`,
`Jacobian X`) now routes through a real definition rather than
`loopIntegralToH1`.

### Layer 4: replace the old `H1`

Either:
- **(A)** Define `Jacobians.RiemannSurface.H1 := H1Analytic`. Breaks the
  `Additive (Abelianization π₁)` equivalence (which was never used
  structurally, only as a placeholder).
- **(B)** Keep both; prove `H1Analytic ≃ Additive (Abelianization π₁)`
  as a classical theorem (de Rham + singular Hurewicz — substantial).
  Not necessary for our use case.

Preferred: **(A)** — cleaner, no classical equivalence needed.

## Phases

| Phase | Content | Effort |
|---|---|---|
| P0 | Decide chain-group encoding (Finsupp vs custom structure); settle 2-simplex definition; agree on base-point/cycle convention | 1 day |
| P1 | Define `AnalyticOneChain`, `AnalyticTwoChain`, boundary operators; prove `∂₁ ∘ ∂₂ = 0` chart-locally | 3 days |
| P2 | Define `H1Analytic X x₀` as quotient; verify `AddCommGroup` / `Module ℤ` instances transfer | 1 day |
| P3 | `AnalyticArc.integrateOneForm` via chart-local `intervalIntegral` sums over a chart cover of the arc image | 3 days |
| P4 | `AnalyticTwoChain.boundary_integrate_eq_zero` — Stokes on chart 2-simplices + `dω = 0` for 1-forms on 1-manifolds | 3 days |
| P5 | `periodMap X x₀` as real `def` via `QuotientAddGroup.lift` | 1 day |
| P6 | Replace `Jacobians.RiemannSurface.H1 := H1Analytic`; fix downstream references (`periodMapInBasis`, `periodLatticeInBasis`, `AnalyticCycleBasis`, `intersectionForm`) | 2 days |
| P7 | Elliptic-specific: exhibit α/β-loops, build `ellipticH1Basis : Module.Basis (Fin 2) ℤ (H1Analytic Elliptic x₀)`, derive `genus_Elliptic_pos` from the topological side as well | 2 days |
| P8 | Regression testing: verify `genus_Elliptic_eq_one` (Ω¹ route, already done) is unchanged; verify Challenge.lean still closes | 1 day |

**Total: ~2–2.5 weeks** for a focused contributor.

## Axioms retired

| Currently | After the refactor |
|---|---|
| `loopIntegralToH1` (function-existence axiom #2 of 5) | ✅ Real def via `QuotientAddGroup.lift` on `periodMap` |
| `pathIntegralBasepointFunctional` (#1 of 5) | Partly retired: `pathIntegralBasepointFunctional X P₀ P ω = ∫_{arc from P₀ to P} ω`, real def via chain-integration — but depends on a path-existence axiom still (or a specific chain-existence axiom replacing it) |
| `AX_pathIntegral_local_antiderivative` | Becomes a derived theorem (FTC for chart-local path integrals) |
| `AX_H1FreeRank2g` for `Elliptic` specifically | Retired via explicit α/β-loop basis |
| `AX_H1FreeRank2g` for general X | Still classical (rank = 2g is Hodge-theoretic) |
| `AX_AnalyticCycleBasis` for Elliptic | Explicit via α/β |
| `AX_AnalyticCycleBasis` for general X | Still classical |

**Net**: retires 2 of 5 function-existence axioms + 1 Prop axiom + the
Elliptic cases of 2 more axioms. Deep classical axioms (uniformization,
Riemann-Roch, Serre duality, etc.) unchanged.

## Risks and open questions

1. **Chart cover of an arc image**: `AnalyticArc X` maps `[0,1] → X`.
   To integrate chart-locally, we need a finite partition `0 = t₀ <
   t₁ < ... < tₙ = 1` with each `γ[tᵢ, tᵢ₊₁]` in a single chart. Exists
   by compactness, but needs a Lean helper lemma. **Estimated effort
   ≤ 1 day (Mathlib's `IsCompact.exists_subcover` + Lebesgue-number
   argument).**

2. **2-simplex convention**: do we require 2-simplices to factor through
   a single chart (simpler) or allow multi-chart simplices (more
   general)? Single-chart is sufficient for Stokes at 1-form level
   (chart-local ω = coefficient · dz with `dz ∧ dz = 0`, so `dω = 0`
   is trivial). Recommend single-chart.

3. **Base-point convention**: H₁ is based at `x₀`. Classical: cycles
   modulo boundaries, no base-point needed for the abelian group
   structure. But the project's H₁ API takes `x₀`. Our `H1Analytic X`
   can be independent of `x₀` (as long as X is path-connected); a
   base-point-indexed version is a trivial iso. Match the existing API.

4. **Equivalence with topological `H1`?** The classical fact
   `H1Analytic ≃ Additive (Abelianization π₁)` would let us keep the
   topological H₁ symbol while gaining the constructive content.
   Proof route: Hurewicz + analytic approximation of continuous loops.
   **Scope**: separate, months of work. Not needed if we commit to
   `H1 := H1Analytic`.

5. **Stokes on chart 2-simplices**: standard, but Lean proof requires
   `MeasureTheory.integral_deriv_mul_comp_intervalIntegral` or Stokes
   for `curveIntegral` on a triangular boundary. Mathlib has 2-simplex
   Stokes in some form (`Complex.integral_boundary_rect_eq_zero_of_differentiable`
   or similar). **Verify via `lean_leansearch` in P0.**

6. **The `pathIntegralBasepointFunctional` residual**: even with
   `H1Analytic`, we'd still want a "∫ from P₀ to P" functional (used
   in `ofCurveAmbient`). This is ∫ along an *arc* from P₀ to P, not
   a cycle. Real def via `AnalyticArc.integrateOneForm` applied to a
   chosen arc — but choosing the arc is a `Classical.choice` unless
   we axiomatize existence of a specific arc for each (P₀, P) pair.
   Might still need a small path-choice axiom.

## Consequences

Once this lands, the "5 function-existence axioms" become 3 (plus
some smaller ones). Specifically:

| # | Axiom | Status after refactor |
|---|---|---|
| 1 | `pathIntegralBasepointFunctional` | Real def, but depends on path-existence (smaller axiom) |
| 2 | `loopIntegralToH1` | ✅ **Real def** |
| 3 | `pullbackOneForm` | Unchanged (independent) |
| 4 | `pushforwardOneForm` | Unchanged (independent) |
| 5 | `localOrder` | Unchanged (independent) |

Plus:
- `AX_pathIntegral_local_antiderivative` retires to a theorem.
- Elliptic case of `AX_H1FreeRank2g` / `AX_AnalyticCycleBasis` retires.

**Net axiom count reduction: 2 function-existence + 1 Prop axiom + 2
partial Elliptic retirements.** The project becomes measurably more
constructive.

## Dependencies and prerequisites

- Mathlib: `intervalIntegral`, `Finsupp`, `QuotientAddGroup`,
  `AnalyticOn`, `curveIntegral` — all present.
- Project: `AnalyticArc X` (in `RiemannSurface/AnalyticArc.lean`),
  `HolomorphicOneForm X` (refactored 2026-04-24 with
  `IsZeroOffChartTarget`), chart-local `pathIntegralOnChart` (already
  a real def in `PathIntegral.lean`).
- No new Mathlib additions required.

## Recommendation

This is **the cleanest path** to retiring the project's most structural
function-existence axiom (`loopIntegralToH1`). Does not require
Mathlib PRs or speculative infrastructure. Timeline is tractable
(2–2.5 weeks) for a focused contributor.

**Attempt order**: wait until Elliptic/Hyperelliptic atlas work is
further along, or do concurrently with atlas work since chain/boundary
infrastructure is orthogonal.

## References

- Hatcher, *Algebraic Topology*, Ch. 2 (singular / simplicial
  homology).
- Bott & Tu, *Differential Forms in Algebraic Topology* (de Rham /
  singular equivalence).
- Forster, *Lectures on Riemann Surfaces*, Ch. I §10 (integration on
  Riemann surfaces).
- Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III (homology
  and periods).

## Status

Plan drafted. Not yet executed. When attempted, break into the 9
phases above as separate commits.
