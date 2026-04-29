# Status

_Last full rewrite: 2026-04-23. Header refreshed: 2026-04-29._

> **Read this first** — this document was authored 2026-04-23 and
> describes the API-closure state at that point (24/24 Buzzard sorries
> closed). The "Module progress" sections below are accurate for their
> date; they do not reflect the substantial 1-form framework, S5
> cross-summand cocycle, S7 linear independence, S8 Liouville-hierarchy
> upper bound, or `genus_HyperellipticEven_eq` headline theorem that
> all landed between 2026-04-26 and 2026-04-29.
>
> For the **current** state, see:
> * [`README.md`](../README.md) — public-facing summary, current state
>   table, axiom inventory.
> * [`docs/genus-theorem-discharge-plan.md`](genus-theorem-discharge-plan.md)
>   — S1–S8 sub-task statuses (the genus framework workstream is the
>   bulk of post-2026-04-26 work).
> * [`docs/dependency-trace.md`](dependency-trace.md) — axiom audit; has
>   a 2026-04-29 update note flagging `AX_FiniteDimOneForms` as retired
>   and the new Liouville hierarchy.
>
> Below is the snapshot from 2026-04-23 — kept for historical
> traceability.

---

## Build status (2026-04-23 snapshot)

✅ Green. `lake build` completes 8341 jobs. **Zero sorries** anywhere in the project.

## Sorry inventory

**24/24 Buzzard sorries closed** via the named-axiom framework. **All six Buzzard-exposed definitions (`genus`, `Jacobian`, `ofCurve`, `pushforward`, `pullback`, `ContMDiff.degree`) are now real `def`s**, with axioms pushed to smaller-grained primitives (path-integral functional, ambient-linear maps, branch-locus existential).

| Closure | Lines | Mechanism | Axioms used (beyond Lean core) |
|---|---|---|---|
| `genus` | 58 | real `def` via `Jacobians.RiemannSurface.genus` | — |
| `genus_eq_zero_iff_homeo` | 63 | `AX_genus_eq_zero_iff_homeo` | AX_genus_eq_zero_iff_homeo |
| `Jacobian` def | 77 | real `def`: `ULift (ComplexTorus ...)` | AX_FiniteDimOneForms, AX_PeriodLattice, instPeriodLatticeDiscrete, loopIntegralToH1 |
| `AddCommGroup` instance | 85 | `inferInstanceAs` (ULift transfer) | same as above |
| `TopologicalSpace` instance | 90 | `inferInstanceAs` | same |
| `T2Space` instance | 95 | `inferInstanceAs` | same |
| `CompactSpace` instance | 99 | `inferInstanceAs` | same |
| `ChartedSpace (Fin g → ℂ)` instance | 103 | `chartedSpaceULift` | same |
| `IsManifold` instance | 110 | `uliftHasGroupoid` + `IsManifold.mk'` | same |
| `LieAddGroup` instance | 116 | `AX_jacobian_lieAddGroup` (open ULift-universe issue) | + AX_jacobian_lieAddGroup |
| `ofCurve` def | 119 | real `def`: `ofCurveImpl` (quotient of `ofCurveAmbient`) | + pathIntegralBasepointFunctional |
| `ofCurve_contMDiff` | 123 | `AX_ofCurve_contMDiff` | + AX_ofCurve_contMDiff |
| `ofCurve_self` | 127 | **theorem** (derived, not axiom) | — |
| `ofCurve_inj` | 131 | `AX_ofCurve_inj` | + AX_ofCurve_inj |
| `pushforward` def | 139 | real `def`: `pushforwardImpl` via `QuotientAddGroup.map` | + pushforwardAmbientLinear, AX_pushforwardAmbient_preserves_lattice |
| `pushforward_contMDiff` | 146 | `AX_pushforward_contMDiff` | + AX_pushforward_contMDiff |
| `pushforward_id_apply` | 152 | `AX_pushforward_id_apply` | + AX_pushforward_id_apply |
| `pushforward_comp_apply` | 161 | `AX_pushforward_comp_apply` | + AX_pushforward_comp_apply |
| `pullback` def | 165 | real `def`: `pullbackImpl` via `QuotientAddGroup.map` | + pullbackAmbientLinear, AX_pullbackAmbient_preserves_lattice |
| `pullback_contMDiff` | 173 | `AX_pullback_contMDiff` | + AX_pullback_contMDiff |
| `pullback_id_apply` | 179 | `AX_pullback_id_apply` | + AX_pullback_id_apply |
| `pullback_comp_apply` | 183 | `AX_pullback_comp_apply` | + AX_pullback_comp_apply |
| `ContMDiff.degree` | 187 | real `def`: `degreeImpl` via `AX_BranchLocus` (0 if constant) | + AX_BranchLocus, localOrder |
| `pushforward_pullback` | 193 | `AX_pushforward_pullback` | + AX_pushforward_pullback |

Audit performed 2026-04-23 via `lean_verify`; every closure pulls exactly the expected axioms plus Lean's core three (`propext`, `Classical.choice`, `Quot.sound`). No accidental axiom leakage.

### 2026-04-23 refactor: API defs → real `def`s (two rounds)

**Round 1** (morning, responding to Codex review): the four "hard" Jacobian-side maps became real defs:

- **`ofCurveAmbient`**: `axiom` → `def` via `pathIntegralBasepointFunctional : X → X → (HolomorphicOneForm X →ₗ[ℂ] ℂ)`.
- **`pushforwardImpl`** / **`pullbackImpl`**: `axiom` → `def` via `QuotientAddGroup.map` + ULift wrap + finite-dim automatic continuity.
- **`degreeImpl`**: `axiom` → `def` via `Classical.choose` on `AX_BranchLocus`, with constant-check branch to 0.
- **`AX_ofCurve_self`**: derived theorem from basepoint subtraction.

**Round 2** (afternoon, responding to Gemini deep-think vetting that flagged Round 1 as partially cosmetic — the ambient-linear axioms traded one opaque map for another, and the path-integral functional was disconnected from the 1-form cocycle predicates, admitting a trivial-zero unsoundness pathway):

- Added **`AX_pathIntegral_local_antiderivative`**: the Fundamental Theorem of Calculus localised to a chart. States `HasDerivAt (z ↦ ∫_{P₀}^{φ⁻¹(z)} ω) (form.coeff P (φ P)) (φ P)` where `φ = extChartAt P`. Binds the path-integral functional to the 1-form cocycle, eliminating the trivial-zero exploit.
- Added structured form-level primitives **`pullbackOneForm (f) : HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X`** and **`pushforwardOneForm (f) : HolomorphicOneForm X →ₗ[ℂ] HolomorphicOneForm Y`**.
- `pushforwardAmbientLinear` and `pullbackAmbientLinear` are now **real `def`s** derived from the structured primitives via `.dualMap` + basis-dualisation through `(jacobianBasis _).dualBasis.equivFun`.
- Functoriality on Jacobians now follows from contravariance of `.dualMap` (once the expected `pullbackOneForm_id` / `pullbackOneForm_comp` axioms are stated; currently the property axioms remain in place as TODOs for derivation).

**Net effect**: the six Buzzard-exposed definitions (`genus`, `Jacobian`, `ofCurve`, `pushforward`, `pullback`, `ContMDiff.degree`) are all real `def`s. The ambient-linear maps are `def`s too. The mathematical debt sits at:
- `pathIntegralBasepointFunctional` + `AX_pathIntegral_local_antiderivative` (FTC binding).
- `pullbackOneForm`, `pushforwardOneForm` (structured functorial primitives).
- `AX_pushforwardAmbient_preserves_lattice`, `AX_pullbackAmbient_preserves_lattice` (period-map naturality).
- `AX_BranchLocus` (degree existence).

Vetting: Gemini deep-think review 2026-04-23 afternoon. Verdicts — `degreeImpl`: **Likely correct**; `pathIntegralBasepointFunctional` alone: **Needed revision** (fixed by adding local antiderivative); `pushforwardAmbientLinear` / `pullbackAmbientLinear` axioms: **Flagged as cosmetic** (fixed by replacing with `pullbackOneForm` / `pushforwardOneForm` + derivation).

Buzzard's file required `noncomputable` annotations (unavoidable; `Module.finrank` is noncomputable and basepoint extraction uses `Classical.choice`). Type signatures otherwise identical to v0.2.

## Module progress

### ✅ Complete

- `Jacobians/ProjectiveCurve/Line.lean` — `ProjectiveLine := OnePoint ℂ` with all seven X-side Buzzard instances (TopologicalSpace, T2Space, CompactSpace, ConnectedSpace, Nonempty, ChartedSpace ℂ, IsManifold 𝓘(ℂ) ω). Plus `chart0`, `chart1`, `chartAt`, and `stereographic : ProjectiveLine ≃ₜ S² ⊂ ℝ³`. Zero sorries.
- `Jacobians/AbelianVariety/ComplexTorus.lean` — `ComplexTorus V L := V ⧸ L.toAddSubgroup` for a full-rank ℤ-lattice in a finite-dim ℂ-vector space. **All 7 Buzzard instances** (AddCommGroup, TopologicalSpace, IsTopologicalAddGroup, T2Space, CompactSpace, ChartedSpace V, IsManifold 𝓘(ℂ, V) ω, LieAddGroup 𝓘(ℂ, V) ω). Explicit chart atlas via fixed injectivity-ball around `0` + fixed lifts per point; chart transitions are translations by lattice vectors. Axiom-free, zero sorries.
- `Jacobians/RiemannSurface/Homology.lean` — `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))`. `AddCommGroup` automatic.
- `Jacobians/RiemannSurface/Genus.lean` — `genus X := Module.finrank ℂ (HolomorphicOneForm X)`. At the stub this provably returns `0` (since `HolomorphicOneForm X = ⊥`); refinement of the `OneForm.lean` predicates will widen the submodule and the axiom will become load-bearing.
- `Jacobians/Axioms/FiniteDimOneForms.lean` — `AX_FiniteDimOneForms` axiom declared; `instFiniteDimOneForms` derived from the `⊥`-submodule stub (no axiom invocation at the stub). After 2026-04-22 Gemini review: installing the instance by `:= AX_FiniteDimOneForms` on top of the previous `True ∧ True` carrier injected `False` into the environment (verified exploit in `docs/gemini-review-axioms.md`); fix lands in this same commit.

### ✅ Scaffold only

- `Jacobians/RiemannSurface/OneForm.lean` — `HolomorphicOneForm X` as `↥(⊥ : Submodule ℂ (X → ℂ → ℂ))` at the stub. The two predicates (`IsHolomorphicOneFormCoeff`, `SatisfiesCotangentCocycle`) remain `True`-stubs but are not currently used in the carrier; this keeps the submodule genuinely finite-dim (0-dim) until refinement. `AddCommGroup` + `Module ℂ` live via `abbrev` + `↥`-coercion.
- `Jacobians/AbelianVariety/Siegel.lean` — `SiegelUpperHalfSpace g` as a `Subtype` of `Matrix (Fin g) (Fin g) ℂ` with `isSymm` + `(map Complex.im).PosDef`. Four TODOs for g=1 ↔ `UpperHalfPlane`, concrete lattice from columns of `[I | τ]`, manifold structure, `Sp(2g, ℤ)`-action.
- `Jacobians/AbelianVariety/Theta.lean` — `RiemannTheta (z, τ)` defined via `tsum`. Summability, analyticity, quasi-periodicity, heat equation all TODOs.

### ✅ Scaffolding only

- `Jacobians/AbelianVariety/Lattice.lean` — convention-fixing wrapper around Mathlib's `IsZLattice` class.
- `Jacobians/AbelianVariety.lean` — top-level Part A aggregator.
- `Jacobians/ProjectiveCurve.lean` — top-level Track 2 aggregator.
- `Jacobians/ProjectiveCurve/Charts.lean` — shared-machinery stub for implicit-function-theorem chart constructions.

### ⬜ Not started

Part B (abstract `X`): `PathIntegral.lean`. `IntersectionForm.lean` + `Periods.lean` are scaffold-only.
Track 2: `Elliptic.lean`, `Hyperelliptic.lean`, `PlaneCurve.lean`.
Bridge: `AbelJacobi.lean`, `Abel.lean`, `Functoriality.lean`, `PushPull.lean`. `Jacobian/Construction.lean` is live (7 instances); `ofCurve`, `pushforward`, `pullback` definitions still pending.
Genus 0: `Uniformization.lean`.
Universe lift to match Buzzard's `Jacobian : Type u` signature (current bridge lands in `Type`).

Axioms landing tracker (2026-04-22 post-bridge):
* Declared and live: `AX_FiniteDimOneForms`, `AX_H1FreeRank2g`, `AX_PeriodInjective`, `intersectionForm` + `AX_IntersectionForm_{alternating, nondeg}`, `periodMap` (stub-axiom), `AX_PeriodLattice` + `instPeriodLatticeDiscrete`.
* Declared doc-only (concrete signature pending consumer): `AX_RiemannBilinear`, `AX_RiemannRoch`, `AX_SerreDuality`, `AX_AbelTheorem`, `AX_BranchLocus`, `AX_PluckerFormula`.

### Remaining Challenge.lean sorries (16)

#### Theorem / proof (10)
- `genus_eq_zero_iff_homeo` (58) — can't close at stub since `genus X = 0` always; opens up honestly when OneForm predicates refined.
- `ofCurve_contMDiff` (107), `ofCurve_self` (109), `ofCurve_inj` (112) — need `ofCurve` def.
- `pushforward_contMDiff` (127), `pushforward_id_apply` (130), `pushforward_comp_apply` (140)
- `pullback_contMDiff` (151), `pullback_id_apply` (154), `pullback_comp_apply` (158)
- `pushforward_pullback` (167)

#### Data (5)
- `ofCurve` (104), `pushforward` (122), `pullback` (146), `ContMDiff.degree` (164).

#### Instance (1)
- `LieAddGroup ... (Jacobian X)` (101) — requires `IsTopologicalAddGroup (ULift _)` + `ContMDiff` of add/neg transfer.

### Data sorries (pre-universe-lift breakdown, kept for history) (9)

| Symbol | Line | Kind |
|--------|------|------|
| `genus` | 44 | `def` returning `ℕ` |
| `Jacobian` | 59 | `def` returning `Type u` |
| `AddCommGroup (Jacobian X)` | 65 | instance |
| `TopologicalSpace (Jacobian X)` | 69 | instance |
| `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | 80 | instance |
| `Jacobian.ofCurve` | 89 | `def` |
| `Jacobian.pushforward` | 107 | `def` |
| `Jacobian.pullback` | 131 | `def` |
| `ContMDiff.degree` | 149 | `def` |

### Instance prop sorries (4)

| Symbol | Line |
|--------|------|
| `T2Space (Jacobian X)` | 72 |
| `CompactSpace (Jacobian X)` | 75 |
| `IsManifold (..) ω (Jacobian X)` | 83 |
| `LieAddGroup (..) ω (Jacobian X)` | 86 |

### Theorem sorries (11)

| Symbol | Line |
|--------|------|
| `genus_eq_zero_iff_homeo` | 53 |
| `ofCurve_contMDiff` | 92 |
| `ofCurve_self` | 94 |
| `ofCurve_inj` | 97 |
| `pushforward_contMDiff` | 110 |
| `pushforward_id_apply` | 115 |
| `pushforward_comp_apply` | 123 |
| `pullback_contMDiff` | 134 |
| `pullback_id_apply` | 139 |
| `pullback_comp_apply` | 142 |
| `pushforward_pullback` | 151 |

## Axiom inventory

**Declared, with Lean signatures (22 axioms across 8 files):**

*Infrastructure (consumed by the Jacobian bridge):*
* `AX_FiniteDimOneForms` — `Jacobians/Axioms/FiniteDimOneForms.lean` (now load-bearing after OneForm predicate refinement)
* `intersectionForm` + `AX_IntersectionForm_alternating` + `AX_IntersectionForm_perfect` — `Jacobians/Axioms/IntersectionForm.lean` (**strengthened from `nondeg` to `perfect` / unimodular** per Gemini review #2, 2026-04-23)
* `AX_AnalyticCycleBasis` — `Jacobians/Axioms/AnalyticCycleBasis.lean`
* `AX_PeriodLattice` + `instPeriodLatticeDiscrete` — `Jacobians/Axioms/PeriodLattice.lean`
* `periodMap` — `Jacobians/RiemannSurface/Periods.lean`

*Jacobian API (closing Challenge.lean sorries):*
* `ofCurveImpl`, `pushforwardImpl`, `pullbackImpl`, `degreeImpl` — data defs (4 axioms)
* `AX_ofCurve_{contMDiff, self, inj}` — Abel-Jacobi properties (3 axioms)
* `AX_pushforward_{contMDiff, id_apply, comp_apply}` — pushforward (3 axioms)
* `AX_pullback_{contMDiff, id_apply, comp_apply}` — pullback (3 axioms)
* `AX_pushforward_pullback` — push-pull = deg multiplication (1 axiom)
* `AX_jacobian_lieAddGroup` — LieAddGroup placeholder (1 axiom)
* All in `Jacobians/Axioms/AbelJacobiMap.lean`.

*Uniformization:*
* `AX_genus_eq_zero_iff_homeo` — `Jacobians/Axioms/Uniformization0.lean`

**Former axioms, now theorems (2):**
* `AX_H1FreeRank2g` — `Jacobians/Axioms/H1FreeRank2g.lean` — derived from `AX_AnalyticCycleBasis` (2026-04-22).
* `AX_IntersectionForm_nondeg` — `Jacobians/Axioms/IntersectionForm.lean` — derived from `AX_IntersectionForm_perfect` (2026-04-23).

**Axioms retired via deletion (1):**
* `AX_PeriodInjective` — was `Jacobians/RiemannSurface/IntersectionForm.lean` — strictly redundant given `AX_PeriodLattice` (Gemini review #2, 2026-04-23). No Lean code depended on it; if injectivity is needed, derive via `AX_PeriodLattice` + `IsZLattice`-rank argument.

**Declared doc-only (6):** `AX_RiemannBilinear`, `AX_RiemannRoch`, `AX_SerreDuality`, `AX_AbelTheorem`, `AX_BranchLocus`, `AX_PluckerFormula` — signatures sketched in their respective `Axioms/*.lean` files, concrete Lean statements deferred until the consumer module defines the missing types (`Divisor X`, `SmoothPlaneCurve F`, `localOrder`, etc.). Target signatures revised 2026-04-22 per Gemini review (existentials, `FiniteDimensional` hypotheses, ℤ-subtraction, `tsum`).

**Gemini axiom review (2026-04-22):** see [`docs/gemini-review-axioms.md`](gemini-review-axioms.md).
* ✅ Critical: `AX_FiniteDimOneForms`-as-instance + `True ∧ True` submodule stub injected `False` (verified exploit via `rank_fun_infinite`). Fix applied — submodule now `⊥`, instance derived without axiom invocation.
* ✅ Missing `AX_IntersectionForm` added as a new axiom file (intersection pairing + alternating + non-degenerate).
* ✅ `AX_RiemannBilinear` target signature revised: existentials shifted over basis choice.
* ✅ `AX_RiemannRoch` and `AX_SerreDuality` target signatures revised with `FiniteDimensional` hypotheses and ℤ-subtraction (Serre-duality now stated as an isomorphism).
* ✅ `AX_BranchLocus` target signature revised to use `tsum` + `¬ ∃ c, ∀ x, f = c` non-constant predicate.
* ✅ `AX_PeriodLattice` landed in `Jacobians/Axioms/PeriodLattice.lean`: `IsZLattice ℝ (periodLatticeInBasis X x₀ b)` in the basis-transported ambient `Fin (genus X) → ℂ`. Consumed by the Jacobian bridge.

## Jacobian bridge

`Jacobians/Jacobian/Construction.lean` lands the bridge from the abstract Riemann surface to the complex torus:

* `jacobianBasis X := Module.finBasis ℂ (HolomorphicOneForm X)` — a ℂ-basis of size `Fin (genus X)`, baked into the construction to avoid a dual `ChartedSpace` (one over `HolomorphicOneForm X →ₗ[ℂ] ℂ`, one over `Fin (genus X) → ℂ`).
* `periodLatticeInBasis X x₀ b : Submodule ℤ (Fin (genus X) → ℂ)` via `AddMonoidHom.toIntLinearMap (periodMap X x₀)` then coordinate transfer through `b.dualBasis.equivFun`.
* `Jacobian X := ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X (Classical.choice ‹Nonempty X›) (jacobianBasis X))`.
* Seven Buzzard instances inherited via `change + infer_instance` off `ComplexTorus`.

**Deferred.** (a) Universe-lift wrapper: `ComplexTorus (Fin (genus X) → ℂ)` lives in `Type` but Buzzard's `Jacobian : Type u`. (b) Basepoint-independence of the lattice (needs `AX_RiemannBilinear`). (c) The Abel-Jacobi map `ofCurve P : X → Jacobian X` and its theorems. (d) Pushforward / pullback functoriality. These are the next bridge pieces.

## Dependencies pinned

- Lean: `v4.30.0-rc1`
- Mathlib: commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026)
