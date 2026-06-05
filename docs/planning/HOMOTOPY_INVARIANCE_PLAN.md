# Homotopy invariance of the holomorphic path integral on X

*2026-05-31. MRD un-parked Fork 1 ("let's do homotopy invariance, we started on it
and it's important"). Unlocks basepoint-independence ⇒ the GENERAL genus>1 Abel
injectivity (with G3 genus-obstruction). See [[defer-homotopy-invariance]],
G3_DISCHARGE_PLAN.md (G1 milestone, Gemini verdict).*

## End goal

`loop_integral_mem_periodLattice` (general X): for any loop `γ` (based anywhere),
`canonicalArcIntegral γ ω ∈ Λ` for every holomorphic 1-form `ω` — the THEOREM form
of the would-be `AX_LoopIntegralInLattice`. From it, basepoint-independence of the
degree-0 Abel difference is 5-line path algebra (Gemini), retiring `AX_ofCurve_inj`
for all genus>0.

## What already exists (sorry-free, "we started on it")
- **`Bridge/ContourDeformation.lean`** — `contourDeformation1D_pathHomotopy`: the
  CHART-LOCAL Cauchy theorem. For holomorphic `f` on an open planar `t ⊆ ℂ` and a
  `Path.Homotopy γ₁ γ₂` staying in `t`, `∫ᶜ γ₁ holoOneForm f = ∫ᶜ γ₂ holoOneForm f`.
  (Endpoint-preserving; the closed-form `contourDeformation1D` too.)
- **`RiemannSurface/SquareSubdivision.lean`** — `exists_chart_subordinate_grid`:
  Lebesgue-number subdivision of a continuous map from `[0,1]²` into `X` so each
  grid cell lands in a single chart source. The subdivision engine for patching.
- `canonicalArcIntegral` (moving-chart line integral on `AnalyticArc X`), with
  proven chart-cocycle integrand independence + partition independence
  (`MultiChartIntegral`, `PartitionIndependence`). `H1 = Additive(Abelianization π₁)`;
  `H1.basepointEquiv`. Cycle basis spans H₁ (`AX_AnalyticCycleBasis`).

## What's missing — the global patching

### HI-0 — API bridge (scope first)
Pin the exact relation between the chart-local ℂ-integral `∫ᶜ … (curveIntegral)`
and the global `canonicalArcIntegral` on `X` over a sub-arc lying in one chart.
On a cell mapping into chart `c`, `canonicalArcIntegral (subarc) ω` should equal
`∫ᶜ (c ∘ subarc) (holoOneForm (ω in chart c))` (the moving-center coeff·deriv
reduces to the chart-local curve integral). This is "chart-additivity" (AnalyticArc
docstring). May reuse `MultiChartIntegral` cocycle lemmas. CRUX of the wiring.

### HI-1 — global homotopy invariance (the hard core)
`canonicalArcIntegral_homotopy_invariant`: for paths/arcs `γ₁ γ₂ : a ⤳ b` on `X`
and a `Path.Homotopy F : γ₁ ≃ γ₂` (with the analytic-arc regularity), `∫_{γ₁} ω =
∫_{γ₂} ω`. Proof: `exists_chart_subordinate_grid` on `F` ⇒ grid of cells each in one
chart; on each cell apply `contourDeformation1D_pathHomotopy` (via HI-0); telescope
the cell-boundary integrals (interior edges cancel pairwise; the chart-transition
cocycle cancels by the proven integrand-independence). The boundary of the whole
square = γ₁ − γ₂ (endpoints fixed). Standard but bookkeeping-heavy.

### HI-1 alt (Route B) — disc primitives / primitive-covering (likely cleaner)

*Prompted by K. Buzzard's 2026-06-05 "Jacobian challenge" Zulip note: a Riemann-
surface expert pointed out you CAN integrate ω along any continuous path C —
"write primitives for ω on small discs, cover the path so the primitives agree on
overlaps, take the difference of endpoint − startpoint" — so no piecewise-linear/
analytic approximation is needed.*

This IS the analytic-continuation / covering-space definition, and it makes
homotopy invariance nearly definitional:
- ω holomorphic ⇒ locally exact (a primitive `f_U` on each chart disc; difference
  of two primitives is locally constant). The sheaf of local primitives is a
  **covering space** of `X` (the "period/primitive covering" `π : X̃ω → X`);
  ∫_C ω = (lift of C to X̃ω at the end) − (at the start).
- **Homotopy invariance = the homotopy-lifting property of a covering map** —
  Mathlib already has this (`IsCoveringMap`, `existsUnique_continuousMap_lifts`,
  homotopy lifting). NO square-subdivision telescoping.
- **We already did the genus-1 instance:** `exists_lift_of_continuous_path` on
  `ℂ/Λ` is exactly this — the lift is the global primitive, `liftBP 1 − liftBP 0`
  the endpoint difference. Generalize from the quotient covering `ℂ → ℂ/Λ` to the
  primitive covering of a general `(X, ω)`.
- Cost: constructing `X̃ω` (espace étalé of the primitive sheaf) + showing
  `IsCoveringMap` for a holomorphic ω. `exists_chart_subordinate_grid` still helps
  build local sections. Compare against Route A before committing; Route B reuses
  the elliptic covering-lift machinery and Mathlib covering theory, so it is the
  preferred candidate to evaluate first.

### HI-2 — factor through H₁
`canonicalArcIntegral` of a loop depends only on its homotopy class (HI-1) ⇒
descends to π₁ ⇒ (commutators integrate to 0 by path-additivity = free) descends to
H₁ = π₁ᵃᵇ. Produce `loopIntegralClassFunctional : H1 X x₀ →+ ℂ` (per ω) and identify
it with the existing `periodMap`/`loopIntegralToH1` on the cycle basis.

### HI-3 — loop integral ∈ Λ
Any loop's H₁ class is a ℤ-combination of the cycle basis (`cb.isBasis` spans);
`canonicalArcIntegral` is ℤ-linear in the class (HI-2); each basis loop's integral
∈ Λ by definition of `periodLatticeInBasis`. ⇒ `loop_integral_mem_periodLattice`.

### HI-4 — basepoint-independence + retire the axiom
5-line path algebra (Gemini): `γ_Q := bridge(b,Q)·bridge(b',Q)⁻¹·bridge(b',b)` is a
loop ⇒ `∫_{γ_Q} ∈ Λ` (HI-3) ⇒ `∫_b^P − ∫_{b'}^P ≡ −∫_{b'}^b (mod Λ)`, const in P ⇒
`ofCurveImpl b Q₁ − ofCurveImpl b Q₂` basepoint-independent. Then the G3 assembly
(G1 + AX_AbelTheorem + G3) retires `AX_ofCurve_inj` for all genus>0.

## Sequencing
HI-0 (API bridge) → HI-1 (patching, the big one) → HI-2 → HI-3 → HI-4 → G-assemble.
HI-1 is the genuine effort; HI-2/3/4 are algebra once HI-1 lands. Runs parallel to
the G3 genus-obstruction (C0/C1), which is independent.

## Guardrails
No new axiom (the whole point). Each milestone: `lake build` + kernel `#print axioms`
on fresh oleans (NO sorryAx). The elliptic analogue (`analyticLoop_…_mem_lattice`)
is the genus-1 instance of HI-3 — cross-check the general proof against it.
