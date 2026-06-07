# HI-1 via covering spaces (Route B) — scoping & explicit-construction plan

*2026-06-05. Deep scoping requested before committing to HI-1's route. Companion to
[`HOMOTOPY_INVARIANCE_PLAN`](HOMOTOPY_INVARIANCE_PLAN.md). HI-1a (single-chart
homotopy invariance) is already proven (`0a9250d`) and is Route-A-specific.*

## 1. What Mathlib actually provides (covering construction)

- **`IsEvenlyCovered f x I`** (`Topology/Covering/Basic.lean:40`) — local triviality at
  `x` with discrete fiber `I`. **`IsCoveringMap f`** = `Continuous f ∧ ∀ x,
  IsEvenlyCovered f x (f⁻¹ x)` (fiber discrete + locally a product).
- **`IsAddQuotientCoveringMap`** (`Topology/Covering/Quotient.lean`) — for an additive
  group `G` acting on `E`: `isAddQuotientCoveringMap_of_properlyDiscontinuousSMul`
  (needs `[ProperlyDiscontinuousVAdd G E] [LocallyCompactSpace E] [T2Space E]`) gives
  `E → E ⧸ G` is a covering on the free locus. **This is the ONLY ready-made covering
  constructor.** It is exactly what our elliptic `ℂ → ℂ/Λ` uses
  (`quotient_mk_isCoveringMap`, `Λ` acts properly discontinuously by translation).
- **Lifting** (`Topology/Homotopy/Lifting.lean`): `IsCoveringMap.liftPath`,
  `liftHomotopy`, `existsUnique_continuousMap_lifts` — once we HAVE a covering, path
  and homotopy lifting are free. This is the payoff Route B is after.
- **MISSING:** no universal-cover construction, no "espace étalé of a sheaf is a
  covering", no "covering associated to a subgroup of π₁". The base `X` is GIVEN; we
  must CONSTRUCT the total space `E` and exhibit `X` as `E ⧸ G` (or prove
  `IsCoveringMap` by hand via `IsEvenlyCovered`).

## 2. CRITICAL finding — a single form does NOT give a covering for g > 1

The naive "primitive covering of `(X, ω)`" has fiber the period group
`Λ_ω = {∮_γ ω : γ ∈ H₁} ⊆ ℂ`. For genus `g`, `H₁` has rank `2g`, so `Λ_ω` is generated
by `2g` complex numbers. For **g ≥ 2 these are generically ℚ-independent ⇒ `Λ_ω` is
DENSE in ℂ ⇒ not discrete ⇒ `ℂ ⧸ Λ_ω` is not Hausdorff and the projection is NOT a
covering.** So a per-form primitive covering is a dead end beyond genus 1 (it only
worked elliptically because `Λ_{dz} = ℤω₁+ℤω₂` is a genuine lattice).

**Consequence:** Route B must use **all `g` basis forms simultaneously** — the
developing map lands in `ℂ^g`, and the fiber is the full period lattice
`Λ ⊆ ℂ^g`, which IS discrete **only by Riemann's bilinear relations =
`AX_PeriodLattice`** (`IsZLattice (periodLatticeInBasis …)`). So **Route B
intrinsically depends on `AX_PeriodLattice`**.

### Trade-off this exposes (vs Route A)
- **Route A (telescoping)** proves homotopy invariance of `∫ω` for a single form
  directly from chart-local Cauchy — **no discreteness, no `AX_PeriodLattice`**
  (mirrors the elliptic witness, which deliberately avoided it). loop ∈ Λ then comes
  from cycle-basis spanning. Axiom-lean.
- **Route B (covering)** needs `Λ ⊆ ℂ^g` discrete (`AX_PeriodLattice`) just to HAVE a
  covering, PLUS construction of the total space. So Route B is **not** axiom-free for
  the homotopy step; it leans on a kept (but currently-unproven) axiom.

This is a genuine reason to prefer Route A on axiom-hygiene grounds, independent of
the bookkeeping-vs-construction effort question.

## 3. Three structural realizations of the (ℂ^g) period covering

**(I) Espace-étalé / cocycle gluing (explicit, analytic).**
Finite atlas `{U_i}` (compact `X`). On each `U_i`, the `g` basis forms have a
holomorphic primitive vector `G_i : U_i → ℂ^g` (chart is disc-like ⇒ primitive
exists, Cauchy). On overlaps `G_i − G_j = c_{ij} ∈ ℂ^g` (locally constant), a Čech
1-cocycle. Set `X̃ := (⊔_i U_i × ℂ^g) / ∼` glued by `(x, v)_i ∼ (x, v + c_{ij}(x))_j`.
Covering map = projection; local triviality over `U_i`: `X̃|_{U_i} ≅ U_i × Λ`
(sheets = lattice translates). **Explicit and constructible**, but the gluing
quotient + `IsEvenlyCovered` proof + chart-local primitive existence is real work.

**(II) Universal-cover quotient (topological).**
`Ũ → X` universal cover, period hom `per : π₁ → ℂ^g`, `X̃ := Ũ ⧸ ker per`, deck group
`im per = Λ`. **BLOCKED: Mathlib has no universal-cover construction.** Not viable now.

**(III) Developing map as a FUNCTION, no total space (likely cleanest).**
Do NOT build `X̃`. Instead define the **analytic-continuation primitive**
`P : (paths from x₀) → ℂ^g` by chart-subdivision (`exists_chart_subordinate_grid`) +
summing chart-local primitive increments, and prove `P` is **homotopy-invariant
mod Λ** directly (homotopic paths ⇒ continuations differ by a closed-cocycle sum
that telescopes to 0 in `ℂ^g`, or to a lattice element for loops). `∫_γ ω_k = P(γ)_k`.
This is the disc-primitive recipe (Buzzard's colleague) realized as a function —
it **dodges the étalé-space construction AND the integral-telescoping**, but its
homotopy-invariance proof still uses a subdivision argument (closer to Route A than
to "free from liftHomotopy"). It does NOT need `AX_PeriodLattice` for the mod-nothing
homotopy invariance of the *open-path* `ℂ^g` value (discreteness only enters when
quotienting for loops).

## 4. Recommendation (for decision)

- If **axiom-hygiene** is the priority (keep the general theorem off `AX_PeriodLattice`,
  matching the elliptic witness): **Route A**, or **(III)** — both avoid the covering
  and the discreteness axiom; both are subdivision arguments, differing in whether the
  bookkeeping is on integrals (A) or primitive values (III). (III) may be cleaner
  because primitive increments compose more simply than reparametrized sub-arc
  integrals, and it directly yields the `ℂ^g` developing map needed downstream.
- If **conceptual cleanliness via Mathlib lifting** is the priority and depending on
  `AX_PeriodLattice` is acceptable: **(I)** — build the `ℂ^g` étalé covering, then
  `liftHomotopy` is free. Highest construction cost; novel infra.
- **(II) is out** (no universal cover in Mathlib).

**Leaning: (III) — developing-map-as-function.** It captures Route B's clean idea
(primitives, not integral-telescoping), stays axiom-lean, produces the `ℂ^g`
developing map we need for HI-2/3/4, and reuses `exists_chart_subordinate_grid` +
the chart-local primitive (which `contourDeformation`/HI-0 already touch). It is a
hybrid: "Route B's primitives, Route A's subdivision, no covering space."

## 5. Milestones for (III) (the leaning candidate)

- **B0.** Chart-local primitive: on a chart target (disc-like open in ℂ), a holomorphic
  `f` (= a basis form's coefficient) has a holomorphic primitive `g`, `deriv g = f`.
  (Mathlib: `Complex` primitive on a `Convex`/`StarConvex` set / `DifferentiableOn` ⇒
  `∃ primitive`. Find the exact lemma — `Complex.exists_primitive`-style.)
- **B1.** `continuationIncrement`: along a sub-arc in one chart, `∫ ω = g(end) − g(start)`
  for the chart primitive `g` (this is HI-0 specialized; already essentially have it).
- **B2.** `developing P(γ) ∈ ℂ^g` for a path γ via `exists_chart_subordinate_grid`
  subdivision + summing B1 increments; well-defined (independent of grid) by the
  cocycle agreeing on overlaps.
- **B3.** `P` homotopy-invariant: homotopic γ₁,γ₂ ⇒ `P(γ₁) = P(γ₂)` (subdivide the
  homotopy; each cell contributes 0 by chart-local Cauchy / closed cocycle).
- **B4.** `∫_γ ω_k = P(γ)_k`; for a loop, `P(loop) ∈ Λ` (cycle-basis spanning). ⇒
  `loop_integral_mem_periodLattice` (= HI-3), then HI-4 basepoint-independence.

## 6. Open question to resolve before dispatch

Does **(III)'s** subdivision-homotopy proof (B3) end up as much bookkeeping as
**Route A's** telescoping? They are close cousins. The bet is that primitive-increment
composition (`g(end) − g(start)` telescopes trivially along a subdivision) is
*cleaner* than reparametrizing sub-arcs of `canonicalArcIntegral` and proving arc
concatenation-additivity (the missing Route-A infra). If B3 also bogs down, the
fallback is **(I)** (pay the covering construction, get `liftHomotopy` free, accept
`AX_PeriodLattice`).
