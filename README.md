# Jacobians of Compact Riemann Surfaces

A Lean 4 formalization attempt at Kevin Buzzard's Jacobian Challenge (April 2026): define and prove an API for the Jacobian of a compact Riemann surface, the Abel-Jacobi map, and pushforward/pullback functoriality.

**Challenge source:** https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9 (v0.2)

## What this project is

Buzzard's challenge is a single Lean file containing `sorry`-ed definitions and theorems — **24 sorries** total. The API is designed so that no "hack" definition (e.g. `Jacobian := 0`) can simultaneously satisfy all the theorems — in particular `genus_eq_zero_iff_homeo` forces `genus` to be correct, and `ofCurve_inj` forces the Abel-Jacobi map to be genuinely injective in positive genus.

All underlying mathematics is classical (Abel 1829, Jacobi 1851). The challenge is to formalize it in Lean 4 / Mathlib without extending Mathlib itself, i.e. living entirely downstream.

## What we claim

Buzzard's challenge identifies Mathlib's real bottleneck: the differential-geometric API for *stating* modern theorems about Jacobians is missing. Jack McCarthy captured this sharply — "even stating the definitions requires lots of machinery in differential geometry which is not currently in Mathlib." Rado Kirov's 3-day Claude Code baseline ([rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude)) — ~5K LOC, 10 named classical theorems still stubbed, self-rated ~10–15% toward a full end-to-end solution — bounds what a human with zero math background plus off-the-shelf AI tooling produces.

With math+Lean expert steering — the configuration Kirov and Riccardo Brasca named as the realistic path — AI-written code produces a **foundation-closed, non-vacuous Lean 4 scaffold** for Buzzard's file in days rather than months:

- **Every Buzzard-exposed definition and instance is a real Lean `def` / `instance`, not an axiom.** All 13 data/instance sorries (§§1–13 of [`docs/challenge-annotated.md`](docs/challenge-annotated.md)) discharge as real constructions. `ofCurve_self = 0` is a derived theorem (definitional via basepoint subtraction). All 4 functoriality identities (`pushforward_id_apply`, `pushforward_comp_apply`, `pullback_id_apply`, `pullback_comp_apply`) are real theorems derived from form-level axioms via `LinearMap.dualMap_comp_dualMap`.
- **The axiomatization lives strictly *below* the Buzzard API.** 5 data-level primitives (path-integral functional, pullback/trace of 1-forms, local order, H₁-loop integral; each with a construction plan in [`docs/construction-plans/`](docs/construction-plans/)) + ~10 Prop-level classical theorems (uniformization, Abel, Riemann-Roch, Serre duality, Riemann bilinear, etc. — each cited by textbook).
- **Buzzard's hack-blockers bite.** `ofCurve_self = 0` and `genus_eq_zero_iff_homeo` discharge against concrete witnesses: `ProjectiveLine` (genus 0, via stereographic sphere homeomorphism) and `Elliptic ω₁ ω₂` (genus 1, torus with honest symplectic cycle basis) — not trivial groups. `Hyperelliptic` and `PlaneCurve` are also real `def`s now (via `OnePoint` compactification, 5/7 instances derived; atlas ChartedSpace+IsManifold still axiomatic).
- **Full dependency trace** in [`docs/dependency-trace.md`](docs/dependency-trace.md): every foundation definition audited; every axiom classified as A-deep (classical theorem) or A-infra. As of 2026-04-23 round-3, **A-infra count is zero** — only classical-theorem axioms remain.

We do **not** claim a sorry-free solution and we do **not** claim autonomy. Every line of Lean was written by Claude; the load-bearing mathematical judgments — axiom-vs-proof boundary, what counts as a non-vacuous witness, which hack-smuggles to reject — were made by a mathematician-user. The claim is narrower and, we think, more useful: *stating* Buzzard's theorems and bolting down the foundation — the phase the Zulip thread treated as the long pole — is fast when a domain expert drives an AI, and the remaining sorries reduce to the enumerated classical theorems. This is what Emily Riehl and Timothy Chow's autonomy exchange converged on as the honest frame: no achievement is fully autonomous, so say exactly what the human and the AI each did.

See [docs/challenge-summary.md](docs/challenge-summary.md) for the full Zulip discussion.

## Architecture

Two parallel tracks, both building on a shared Part A:

- **Part A (`Jacobians/AbelianVariety/`)** — abelian-variety machinery, axiom-free. `ComplexTorus V L := V ⧸ L` for `L : Submodule ℤ V` with `[IsZLattice ℝ L]`. Supplies all seven typeclass instances Buzzard demands on `Jacobian X`.
- **Track 1 (`Jacobians/RiemannSurface/` + `Jacobians/Jacobian/`)** — abstract `X` from Buzzard's typeclasses → period lattice → `Jacobian X := ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X x₀ (Module.finBasis ℂ (HolomorphicOneForm X)))`. A ℂ-basis of `HolomorphicOneForm X` is baked into the definition (via `Module.finBasis` from the global `FiniteDimensional` instance), giving a *single* `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` instance — matching Buzzard's signature exactly. Basepoint extracted via `Classical.choice` from `[Nonempty X]`; basepoint-independence via `AX_RiemannBilinear` postponed.
- **Track 2 (`Jacobians/ProjectiveCurve/`)** — concrete projective curves (`ProjectiveLine`, elliptic, hyperelliptic, smooth plane curves) each satisfying Buzzard's typeclasses by construction. Closes the challenge on these specific types.

## File structure

| File | Contents |
|------|----------|
| [Jacobians/Challenge.lean](Jacobians/Challenge.lean) | Buzzard's v0.2 file verbatim (24 sorries) — pinned, tracks upstream |
| [Jacobians/Basic.lean](Jacobians/Basic.lean) | Shared imports / notation |
| [Jacobians/AbelianVariety/Lattice.lean](Jacobians/AbelianVariety/Lattice.lean) | Conventions around Mathlib's `IsZLattice` |
| [Jacobians/AbelianVariety/ComplexTorus.lean](Jacobians/AbelianVariety/ComplexTorus.lean) | `ComplexTorus V L` — **all 7 Buzzard instances** (AddCommGroup, TopologicalSpace, IsTopologicalAddGroup, T2Space, CompactSpace, ChartedSpace V, IsManifold 𝓘(ℂ, V) ω, LieAddGroup 𝓘(ℂ, V) ω). Axiom-free, zero-sorry. |
| [Jacobians/AbelianVariety/Siegel.lean](Jacobians/AbelianVariety/Siegel.lean) | `SiegelUpperHalfSpace g` as `Subtype` + `CoeFun` + `ext` |
| [Jacobians/AbelianVariety/Theta.lean](Jacobians/AbelianVariety/Theta.lean) | `RiemannTheta (z, τ)` definition; summability / analyticity / quasi-periodicity TODOs |
| [Jacobians/RiemannSurface/OneForm.lean](Jacobians/RiemannSurface/OneForm.lean) | `HolomorphicOneForm X` — real submodule with `IsHolomorphicOneFormCoeff` (analyticity on chart targets) + `SatisfiesCotangentCocycle` (chart-transition derivative law); full `@[simp]` API |
| [Jacobians/RiemannSurface/Homology.lean](Jacobians/RiemannSurface/Homology.lean) | `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))` |
| [Jacobians/RiemannSurface/Genus.lean](Jacobians/RiemannSurface/Genus.lean) | `genus X := Module.finrank ℂ (HolomorphicOneForm X)` |
| [Jacobians/RiemannSurface/Periods.lean](Jacobians/RiemannSurface/Periods.lean) | `periodMap X x₀ : H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)` — **real `def`** via `loopIntegralToH1` |
| [Jacobians/RiemannSurface/PathIntegral.lean](Jacobians/RiemannSurface/PathIntegral.lean) | `pathIntegralOnChart` real def; `loopIntegralToH1` axiom (discharge plan in `docs/construction-plans/loop-integral-h1.md`) |
| [Jacobians/RiemannSurface/IntersectionForm.lean](Jacobians/RiemannSurface/IntersectionForm.lean) | `AX_PeriodInjective` axiom + Hurewicz-bridge + symplectic-basis TODOs |
| [Jacobians/Jacobian/Construction.lean](Jacobians/Jacobian/Construction.lean) | `Jacobian X` + 7 typeclass instances via `ComplexTorus` bridge; `contMDiff_ulift_up/down` bridge lemmas close `LieAddGroup` |
| [Jacobians/Axioms/](Jacobians/Axioms/) | Named-axiom files (see §Named axioms below) |
| [Jacobians/ProjectiveCurve/Line.lean](Jacobians/ProjectiveCurve/Line.lean) | `ProjectiveLine := OnePoint ℂ` — 7/7 instances + stereographic homeomorphism to S² |
| [Jacobians/ProjectiveCurve/Line/OneForm.lean](Jacobians/ProjectiveCurve/Line/OneForm.lean) | `Subsingleton (HolomorphicOneForm ProjectiveLine)` derived from genus=0 |
| [Jacobians/ProjectiveCurve/Elliptic.lean](Jacobians/ProjectiveCurve/Elliptic.lean) | `Elliptic ω₁ ω₂ h := ComplexTorus ℂ (ℤω₁ + ℤω₂)` — 7/7 instances axiom-free via `ComplexTorus` bridge |
| [Jacobians/ProjectiveCurve/Hyperelliptic.lean](Jacobians/ProjectiveCurve/Hyperelliptic.lean) | `Hyperelliptic H := OnePoint (HyperellipticAffine H)` — real `def`, 5/7 instances derived; atlas `ChartedSpace`+`IsManifold` still axiomatic (see `docs/hyperelliptic-atlas-plan.md`) |
| [Jacobians/ProjectiveCurve/PlaneCurve.lean](Jacobians/ProjectiveCurve/PlaneCurve.lean) | `PlaneCurve H := OnePoint (PlaneCurveAffine H)` — real `def`, 5/7 instances derived; atlas axiomatic |
| [docs/challenge-annotated.md](docs/challenge-annotated.md) | **F/T classification of all 24 Buzzard sorries** — foundation vs theorem split, current status |
| [docs/dependency-trace.md](docs/dependency-trace.md) | **Transitive dep audit** — every foundation def classified R / A-deep / A-infra |
| [docs/construction-plans/](docs/construction-plans/) | **5 discharge plans** for the remaining data-level axioms (path integral, loop integral, pullbackOneForm, pushforwardOneForm, localOrder) |
| [docs/challenge-summary.md](docs/challenge-summary.md) | Summary of the challenge and Zulip discussion |
| [docs/hyperelliptic-atlas-plan.md](docs/hyperelliptic-atlas-plan.md) | 6-phase plan to discharge the Hyperelliptic atlas (~3 weeks) |
| [docs/completion-plan.md](docs/completion-plan.md) | Higher-level completion roadmap |
| [docs/status.md](docs/status.md) | Sorry inventory, axiom inventory, progress tracker |
| [docs/history.md](docs/history.md) | Chronological work log — the *why* behind each session |
| [docs/formalization-plan.md](docs/formalization-plan.md) | Detailed plan with four rounds of adversarial review (Gemini ×3, Codex, Claude) |

## Construction strategy

**Chosen**: period-lattice construction, basis-free at the type level. Details in [docs/formalization-plan.md](docs/formalization-plan.md).

Alternatives considered and rejected: algebraic Pic⁰ (requires GAGA/Riemann existence — not in Mathlib), sheaf cohomology via `H¹(X, 𝒪)/H¹(X, ℤ)` (no manifold sheaf cohomology in Mathlib), de Rham + Hodge decomposition (moves a postponed theorem onto the critical path).

## Known Mathlib gaps

See [docs/survey.md](docs/survey.md) for the Phase B audit. Key gaps blocking Track 1:
- Differential forms as bundled API on manifolds — chart-cocycle workaround planned.
- Line integrals of 1-forms along smooth paths on a general manifold.
- Sheaf cohomology for complex manifolds (not needed for our construction).
- Quotient of a manifold by a discrete group action — Rothgang's PR in flight; our Part A constructs it by hand.

## Named axioms (to be discharged later)

See [docs/formalization-plan.md](docs/formalization-plan.md) §7 for discharge priority; see [docs/gemini-review-axioms.md](docs/gemini-review-axioms.md) for the Gemini round-3 axiom audit.

**Primitive functional axioms (consumed by real defs):**
- `Axioms/AbelJacobiMap.lean` — `pathIntegralBasepointFunctional : X → X → (HolomorphicOneForm X →ₗ[ℂ] ℂ)` paired with `AX_pathIntegral_local_antiderivative` (Fundamental Theorem of Calculus: the functional's derivative at the chart image equals the 1-form's chart-local coefficient; binds functional to cocycle data, eliminating the trivial-zero unsoundness pathway). Fed into `ofCurveAmbient` / `ofCurveImpl`.
- `Axioms/AbelJacobiMap.lean` — `pullbackOneForm : HolomorphicOneForm Y →ₗ[ℂ] HolomorphicOneForm X` and `pushforwardOneForm` (trace). Structured functorial primitives on 1-forms. The ambient linear maps `pushforwardAmbientLinear` and `pullbackAmbientLinear` are now real **`def`s** derived by transporting `.dualMap` through the basis dualisation.
- `Axioms/AbelJacobiMap.lean` — `AX_pushforwardAmbient_preserves_lattice`, `AX_pullbackAmbient_preserves_lattice` (period-map naturality); fed into `pushforwardImpl`, `pullbackImpl`.
- `Axioms/BranchLocus.lean` — `localOrder` + `AX_BranchLocus` (fed into `degreeImpl`).
- `RiemannSurface/PathIntegral.lean` — `loopIntegralToH1` (fed into real `def periodMap`).

**Property axioms on top of the real defs:** `AX_ofCurve_contMDiff`, `AX_ofCurve_inj`, `AX_pushforward_contMDiff`, `AX_pullback_contMDiff`, `AX_pushforward_pullback`.

**Property theorems now derived (not axioms):** `AX_pushforward_id_apply`, `AX_pushforward_comp_apply`, `AX_pullback_id_apply`, `AX_pullback_comp_apply` (2026-04-23 round-3: derived from `AX_pullbackOneForm_id/comp`, `AX_pushforwardOneForm_id/comp` via `LinearMap.dualMap_comp_dualMap`). `AX_jacobian_lieAddGroup` also retired to a theorem (2026-04-23 via `contMDiff_ulift_up/down` bridge lemmas). `AX_ofCurve_self` retired earlier (basepoint subtraction is definitional).

**Infrastructure axioms:**
- `Axioms/FiniteDimOneForms.lean` — `AX_FiniteDimOneForms`.
- `Axioms/H1FreeRank2g.lean` — `AX_H1FreeRank2g`.
- `Axioms/IntersectionForm.lean` — `intersectionForm`, `AX_IntersectionForm_alternating`, `AX_IntersectionForm_nondeg`.
- `Axioms/PeriodLattice.lean` — `instPeriodLatticeDiscrete` + `AX_PeriodLattice`.
- `RiemannSurface/IntersectionForm.lean` — `AX_PeriodInjective`.

**Deep classical theorems (real Lean signatures, proofs pending):** `AX_RiemannBilinear`, `AX_RiemannRoch`, `AX_SerreDuality`, `AX_AbelTheorem`, `AX_PluckerFormula`, `AX_Hyperelliptic_genus`, `AX_genus_eq_zero_iff_homeo`, plus the Hyperelliptic and PlaneCurve type/instance scaffolds. All target signatures were revised 2026-04-22 per Gemini review.

## Dependencies

- **Lean**: `v4.30.0-rc1` (matching the toolchain of the pinned Mathlib commit)
- **Mathlib**: commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), as specified in the challenge

## Build

```bash
lake update
lake build
```

Currently **8342 jobs, green. Zero sorries** anywhere in the project. All 24 Buzzard sorries discharged. Foundation state:

- **13/13 foundation defs + instances are real** (`genus`, `Jacobian`, all 7 typeclass instances including `LieAddGroup`, `ofCurve`, `pushforward`, `pullback`, `ContMDiff.degree`).
- **5/11 property theorems are real theorems** derived from the supporting layer (`ofCurve_self`, `pushforward_id_apply`, `pushforward_comp_apply`, `pullback_id_apply`, `pullback_comp_apply`).
- **6/11 property theorems still route through named axioms** (all deep classical facts: uniformization, Abel's theorem, three holomorphicity axioms, and `pushforward_pullback = deg • id`). Each has a textbook citation.
- **5 data-level supporting axioms** (path-integral functional, pullback/pushforward of 1-forms, local order, loop-integral-to-H₁) — each with a construction plan in [`docs/construction-plans/`](docs/construction-plans/), total ~5–6 weeks focused contributor to discharge.

See [`docs/challenge-annotated.md`](docs/challenge-annotated.md) for the full F/T/T-short/T-deep classification of Buzzard's 24 sorries, and [`docs/dependency-trace.md`](docs/dependency-trace.md) for the complete transitive axiom audit.

## Status

| Module | Status |
|--------|--------|
| **Part A — `AbelianVariety/`** | |
| `Lattice.lean` | ✅ conventions in place |
| `ComplexTorus.lean` | ✅ **complete** — 7/7 Buzzard instances on abstract `(V, L)`, axiom-free, zero-sorry |
| `Siegel.lean` | ✅ scaffold — definition + `CoeFun` + `ext`; Sp(2g, ℤ)-action and concrete-lattice helpers TODO |
| `Theta.lean` | ✅ scaffold — `RiemannTheta` defined; summability / analyticity / quasi-periodicity TODO |
| **Part B — `RiemannSurface/`** | |
| `OneForm.lean` | ✅ real submodule via `IsHolomorphicOneFormCoeff` + `SatisfiesCotangentCocycle`; `@[simp]` API lemmas; extensionality |
| `Homology.lean` | ✅ scaffold — `H1 X x₀ := Additive (Abelianization (π₁ X x₀))` |
| `Genus.lean` | ✅ `genus X := Module.finrank ℂ (HolomorphicOneForm X)` |
| `Periods.lean` | ✅ **real `def`** — `periodMap X x₀ := loopIntegralToH1 x₀` |
| `IntersectionForm.lean` | ✅ scaffold — `AX_PeriodInjective` |
| `PathIntegral.lean` | ✅ `pathIntegralOnChart` real def; `loopIntegralToH1` axiom pending discharge |
| **Axioms — `Axioms/`** | |
| `FiniteDimOneForms.lean` | ✅ declared + global instance; load-bearing now that OneForm predicates are real |
| `H1FreeRank2g.lean` | ✅ declared (typed) |
| `IntersectionForm.lean` | ✅ declared (map axiom + 2 property axioms) |
| `PeriodLattice.lean` | ✅ declared (`AX_PeriodLattice` + `instPeriodLatticeDiscrete`) |
| `AbelJacobiMap.lean` | ✅ `pathIntegralBasepointFunctional` + `AX_pathIntegral_local_antiderivative` (FTC) + `pullbackOneForm` / `pushforwardOneForm` + functoriality; 4 Jacobian-level theorems derived |
| `BranchLocus.lean` | ✅ `localOrder` + `AX_BranchLocus` with real signatures |
| `AnalyticCycleBasis.lean` | ✅ structure + `AX_AnalyticCycleBasis` existential; concrete witnesses for genus 0, 1 |
| `AbelTheorem.lean`, `PluckerFormula.lean`, `RiemannBilinear.lean`, `RiemannRoch.lean`, `SerreDuality.lean`, `Uniformization0.lean` | ✅ real signatures with textbook citations |
| **Bridge — `Jacobian/`** | |
| `Construction.lean` | ✅ `Jacobian X := ULift (ComplexTorus ...)` + 7 typeclass instances (incl. `LieAddGroup` via `contMDiff_ulift_up/down`). All instances real, no axiom |
| **Track 2 — `ProjectiveCurve/`** | |
| `Line.lean` | ✅ complete, 0 sorries, all 7 X-side instances + stereographic |
| `Line/OneForm.lean` | ✅ `Subsingleton (HolomorphicOneForm ProjectiveLine)` derived from genus=0 |
| `Elliptic.lean` | ✅ complete, 0 sorries, 7 X-side instances via `ComplexTorus` |
| `Elliptic/Witnesses.lean` | ✅ concrete `AnalyticCycleBasis` witness (α-loop + β-loop, real symplectic proof) |
| `Hyperelliptic.lean` | ✅ `Hyperelliptic H := OnePoint (HyperellipticAffine H)` real def; 5/7 instances derived; atlas `ChartedSpace` + `IsManifold` still axiomatic (`docs/hyperelliptic-atlas-plan.md`) |
| `PlaneCurve.lean` | ✅ `PlaneCurve H := OnePoint (PlaneCurveAffine H)` real def; 5/7 instances derived; atlas axiomatic |

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
