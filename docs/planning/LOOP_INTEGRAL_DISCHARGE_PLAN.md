# Discharging `loopIntegralToH1` — path-independence as a theorem

*2026-06-04. The deepest gap in the Abel–Jacobi layer. Companion to
[`ABEL_JACOBI_DISCHARGE_PLAN.md`](ABEL_JACOBI_DISCHARGE_PLAN.md) and
[`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md).*

## The target

```lean
-- RiemannSurface/PathIntegral.lean:101
axiom loopIntegralToH1 (x₀ : X) : H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)
-- Homology.lean:41 :  H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))
```

This is **the** path-independence axiom: the period pairing `[γ] ↦ (ω ↦ ∮_γ ω)`
is declared on loops **modulo homotopy** (`H1 = π₁ᵃᵇ`). Asserting the map exists
*is* asserting `∮_γ ω` depends only on `[γ]`. Everything period-related rests on
it: `periodMap` (`Periods.lean:39`) routes through it, `periodLatticeInBasis` is
its range, and `Jacobian` / `ofCurve` list it as their one analytic axiom. It is
distinct from — and the honest home of — the path-independence that the *false*
`AX_pathIntegral_local_antiderivative` tried (and failed) to express on a
single-valued ℂ lift (deleted 2026-06-04). Closed-loop invariance into H₁ is
**true and standard**; the single-valued open-path primitive is false.

Its docstring already names the three bundled subfacts: (1) multi-chart path
integral, (2) homotopy invariance, (3) ℂ-linearity.

## Assets in hand

| Asset | File | Role |
|-------|------|------|
| `pathIntegralOnChart` | `PathIntegral.lean:78` | real `def`, **single-chart** integral |
| `SatisfiesCotangentCocycle` | `OneForm.lean:88` | real predicate, ℂ-linear — the chart-independence content |
| `AnalyticArc` / `AnalyticLoop` | `AnalyticArc.lean:54,95` | real struct, real-analytic in chart coords |
| `contourDeformation1D_pathHomotopy_abstract` | `Bridge/ContourDeformation.lean:130` | **chart-local homotopy invariance** (ℂ, via Mathlib Poincaré) — just landed |
| `flatReparam`, `flatSegment`, chart-ball containment | `Bridge/BridgePath.lean` | building blocks for chart-subordinate piecewise-smooth families |
| `AX_AnalyticCycleBasis` | `Axioms/AnalyticCycleBasis.lean` | **explicit analytic loop reps for all H₁ classes** + ℤ-basis of H₁ |

Mathlib: `lebesgue_number_lemma` (`Topology/UniformSpace/Compact`),
`intervalIntegral.integral_add_adjacent_intervals`, `curveIntegral_trans`,
`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl`
(`MeasureTheory/Integral/CurveIntegral/Poincare`). **Euclidean only** — no
manifold-level de Rham / Stokes / homotopy invariance exists in the pin.

## Two structural facts that shape the plan

1. **The Abelianization representative-extraction is non-constructive in
   Mathlib.** There is no `H1 → (loop representative)` map. **Bypass:** never
   extract from `H1`; instead work with the *explicit* analytic loops supplied by
   `AX_AnalyticCycleBasis`, which already form a ℤ-basis of `H1`. Define the
   pairing on those basis loops, prove invariance for them, and extend ℤ-linearly.
2. **Homotopy invariance must be globalized chart-by-chart.** Mathlib's Poincaré
   lemma is over ℂ; the manifold version is built by subdividing the homotopy
   square `[0,1]²` (Lebesgue number) into cells each landing in one chart, applying
   the chart-local lemma per cell, and telescoping.

## Milestones

- **L0 — chart-cover partition (foundational, unblocks everything).**
  ```lean
  lebesgue_partition_of_chart_cover (γ : AnalyticArc X) :
    ∃ (P : Finset ℝ) (c : … → atlas), γ.partition ≤ P ∧
      ∀ i, ∀ t ∈ Ioo (Pᵢ) (Pᵢ₊₁), γ.extend t ∈ (c i).source
  ```
  From `lebesgue_number_lemma` on the compact image `γ '' [0,1]` + the chart
  cover. *Difficulty: low–medium. The single most reused lemma.*

- **L1 — multi-chart path integral.** Define
  `pathIntegralAnalyticArc (γ) (ω) : ℂ` as `∑ᵢ pathIntegralOnChart (γ|cellᵢ) (cᵢ) ω`
  via L0 + `integral_add_adjacent_intervals`. Prove **partition/chart
  independence** from `SatisfiesCotangentCocycle`. ℂ-linearity (subfact 3) is
  immediate here. *Difficulty: medium (~2–3 wk). The cocycle algebra is the work.*

- **L2 — 2D homotopy-square subdivision.** A `Path.Homotopy γ₁ γ₂` gives
  `F : [0,1]² → X`; subdivide the square (L0 in 2D — Lebesgue number on the compact
  square against `F⁻¹` of the chart cover) into cells each in one chart. *Difficulty:
  medium–high; new infra, no Mathlib analogue.*

- **L3 — manifold homotopy invariance.** `pathIntegralAnalyticArc ω γ₁ =
  pathIntegralAnalyticArc ω γ₂` for `γ₁ ≃ γ₂` rel endpoints, by applying
  `contourDeformation1D_pathHomotopy_abstract` on each L2 cell + telescoping the
  shared edges. *Difficulty: highest (~4–6 wk). The geometric heart.*

- **L4 — assemble `loopIntegralToH1`.** Pair on `AX_AnalyticCycleBasis` loops,
  extend ℤ-linearly over the H₁ basis (bypassing rep-extraction), package as
  `H1 →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)`. Retire the axiom. *Difficulty: medium;
  mostly linear-algebra plumbing once L1+L3 land.*

## Sequencing & first dispatch

**L0 → L1** first: concrete, no homotopy, foundational, and independently useful
(it *defines* the multi-chart integral that `periodMap` ultimately needs). L2→L3
(the homotopy-invariance core) is the multi-week crux and comes after L1 gives a
multi-chart integral to be invariant. L4 closes it.

Acceptance: `loopIntegralToH1` becomes a `def`; `#print axioms` of `periodMap` /
`Jacobian` / `ofCurve` no longer lists it.

Guardrail: **no relabelling.** The homotopy-invariance content (L3) must be
*derived* from `ContourDeformation` + subdivision, not re-asserted under a new
axiom name. Same rule that caught the false FTC.

## Sidecar (independent, lands alongside)

De-opaque the open-path lift: `pathIntegralBasepointFunctional :=
Bridge.kirovBackedFunctional` (a real `∫`), killing the zero-functional
degeneracy with no FTC. Its path-dependence is then governed by the (eventually
proven) `loopIntegralToH1`. Gated only on checking `ofCurve_contMDiff` does not
silently need a functional-smoothness obligation.

## Update 2026-06-05 — Route C (cycle-basis discharge; reframes L2/L3 as optional)

`AnalyticCycleBasis` (`Axioms/AnalyticCycleBasis.lean`) already provides both
explicit analytic loop reps `loops : Fin 2g → AnalyticLoop X x₀` **and**
`isBasis : Module.Basis (Fin 2g) ℤ (H1 X x₀)`. So `loopIntegralToH1` can be
discharged directly:

```
loopIntegralToH1 x₀ := (isBasis.constr ℤ (fun i => ∮_{loops i})).toAddMonoidHom
```
— define the period pairing by its (real line-integral) values on the cycle
basis, extended ℤ-linearly. A linear map is determined by its basis values, and
the true period pairing IS ℤ-linear on H₁, so this equals it. **Faithful**
(periods are genuine integrals) and uses only **L1 + `AX_AnalyticCycleBasis`**
(already in-system) — **no L2/L3 needed for the discharge.**

Critical path (both Route C and the L3 route need it): **finish L1** — including
`L1-c.4` partition-independence (so `pathIntegralAnalyticArc` is intrinsic, not
`Classical.arbitrary`-dependent) and bundling it as a real `→ₗ[ℂ]` (prove the
deriv-integrand `IntervalIntegrable` via continuity). Then:
- **Route C (recommended):** `constr` wiring → `loopIntegralToH1` is a `def`,
  −1 axiom, periods real. L2 (done) + L3 = a follow-on *faithfulness* theorem
  (∮ representative-independent for all loops), optional.
- **Route L3:** prove manifold homotopy invariance from `ContourDeformation` +
  L2 grid — maximal faithfulness, much higher cost.

Status: L0 ✅, L1-a/b/c.1/c.2/c.3 ✅, L1-c.4a (good partition) ✅, L2 ✅;
L1-c.4 (partition independence) in flight; then Route C wiring.

### Route C wiring — integrability subtlety (2026-06-05)

`AnalyticLoop` gives `.arc : AnalyticArc X`; `Module.Basis.constr` + `.toAddMonoidHom`
make the wiring mechanical. The one real gap: bundling `form ↦ ∮_{loops i} form` as a
real `→ₗ[ℂ]` needs the period integrand `IntervalIntegrable`, but `AnalyticArc` only
guarantees `continuous'` + analyticity on OPEN gaps — the chart-derivative at
`γ.partition` endpoints is uncontrolled, and good-partition cells END at those points
(a continuous open-analytic arc can have non-integrable boundary derivative). So
"integrable via continuity" is insufficient. Resolution (no homotopy invariance):
add an integrability/regularity field to `AX_AnalyticCycleBasis` (its loops are
classically C¹/rectifiable — an honest strengthening of an existing axiom), OR
strengthen `AnalyticArc.is_analytic` to C¹-up-to-closure. Decide at wiring time;
the cycle-basis option is cleaner. (Route C confirmed by user 2026-06-05; full
homotopy invariance deferred.)

### Route C integrability — design decision (2026-06-05)

L1-c.4 localized the integrability need to a single hypothesis on `canonicalIntegrand`
(the moving-center period integrand). A concrete `ellipticCycleBasis` exists, so a
structure FIELD on `AnalyticCycleBasis` would force proving integrability for the
explicit elliptic loops (invasive). Decision: a **separate narrowly-scoped axiom**
`∀ (cb : AnalyticCycleBasis X x₀) i form, IntervalIntegrable (canonicalIntegrand (cb.loops i).arc form) volume 0 1` — classically trivial (piecewise-analytic loops
are rectifiable), TRUE only for the nice cycle-basis loops (NOT arbitrary arcs,
where a cusp could make it false), doesn't touch concrete builds, dischargeable
later via stronger `AnalyticArc` regularity. Net: `loopIntegralToH1` (opaque) →
real `def` via `constr` of genuine integrals; residual axiom is a trivial
regularity fact, not a hidden homomorphism. Wiring after Route C step 1 (canonical
arc integral + ℂ-linearity) lands:
- `arcPeriodFunctional γ : forms →ₗ[ℂ] ℂ` (using the scoped integrability for map_add'),
- `loopIntegralToH1 x₀ := (cb.isBasis.constr ℤ (fun i => arcPeriodFunctional (cb.loops i).arc)).toAddMonoidHom`,
- rewire `periodMap`; verify `#print axioms periodMap/ofCurve` drop `loopIntegralToH1`.
