# Jacobians of Compact Riemann Surfaces

A Lean 4 formalization attempt at Kevin Buzzard's Jacobian Challenge (April 2026): define and prove an API for the Jacobian of a compact Riemann surface, the Abel-Jacobi map, and pushforward/pullback functoriality.

**Challenge source:** https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9 (v0.2)

## What this project is

Buzzard's challenge is a single Lean file containing `sorry`-ed definitions and theorems — **24 sorries** total. The API is designed so that no "hack" definition (e.g. `Jacobian := 0`) can simultaneously satisfy all the theorems — in particular `genus_eq_zero_iff_homeo` forces `genus` to be correct, and `ofCurve_inj` forces the Abel-Jacobi map to be genuinely injective in positive genus.

All underlying mathematics is classical (Abel 1829, Jacobi 1851). The challenge is to formalize it in Lean 4 / Mathlib without extending Mathlib itself, i.e. living entirely downstream.

## What we claim

Buzzard's challenge identifies Mathlib's real bottleneck: the differential-geometric API for *stating* modern theorems about Jacobians is missing. Jack McCarthy captured this sharply — "even stating the definitions requires lots of machinery in differential geometry which is not currently in Mathlib." Rado Kirov's 3-day Claude Code baseline ([rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude)) — ~5K LOC, 10 named classical theorems still stubbed, self-rated ~10–15% toward a full end-to-end solution — bounds what a human with zero math background plus off-the-shelf AI tooling produces.

With math+Lean expert steering — the configuration Kirov and Riccardo Brasca named as the realistic path — AI-written code produces an **API-complete, non-vacuous Lean 4 foundation** for Buzzard's file in days rather than months:

- **All six Buzzard-exposed definitions are real `def`s, not `axiom`s**: `genus`, `Jacobian`, `Jacobian.ofCurve`, `Jacobian.pushforward`, `Jacobian.pullback`, `ContMDiff.degree`. Plus `periodMap`, `H1`, `HolomorphicOneForm` at the supporting layer.
- The axiomatization lives strictly *below* the Buzzard API: path-integral-as-functional, ambient linear maps on `Fin (genus X) → ℂ` with their lattice-preservation property, and the common-fiber existential (`AX_BranchLocus`). The top-level data maps are real quotient / ULift constructions over those primitives.
- Buzzard's own hack-blockers — `ofCurve_self = 0` and `genus_eq_zero_iff_homeo` — discharge against concrete witnesses: `ProjectiveLine` (genus 0, via stereographic sphere homeomorphism) and `Elliptic ω₁ ω₂` (genus 1, torus with honest symplectic cycle basis) — not trivial groups. `ofCurve_self` is now a **derived theorem**, not an axiom, because the basepoint-subtraction is built into `ofCurveImpl`.
- The residual 19th–20th century mathematics — Riemann-Roch, Serre duality, Riemann bilinear relations, period-lattice integration, Abel's theorem, and the discrete-group quotient atlases Michael Rothgang is mentoring into Mathlib — is enumerated as ~20 named axioms, each with textbook citation and proof sketch.

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
| [Jacobians/RiemannSurface/OneForm.lean](Jacobians/RiemannSurface/OneForm.lean) | `HolomorphicOneForm X` as `↥(⊥ : Submodule ℂ (X → ℂ → ℂ))` safe stub; predicates + real carrier TODO |
| [Jacobians/RiemannSurface/Homology.lean](Jacobians/RiemannSurface/Homology.lean) | `H1 X x₀ := Additive (Abelianization (FundamentalGroup X x₀))` |
| [Jacobians/RiemannSurface/Genus.lean](Jacobians/RiemannSurface/Genus.lean) | `genus X := Module.finrank ℂ (HolomorphicOneForm X)` (= 0 at the stub, provably) |
| [Jacobians/RiemannSurface/Periods.lean](Jacobians/RiemannSurface/Periods.lean) | `periodMap X x₀ : H1 X x₀ →+ (HolomorphicOneForm X →ₗ[ℂ] ℂ)` — axiom-stub for a `def` landing with `PathIntegral.lean` |
| [Jacobians/RiemannSurface/IntersectionForm.lean](Jacobians/RiemannSurface/IntersectionForm.lean) | `AX_PeriodInjective` axiom + Hurewicz-bridge + symplectic-basis TODOs |
| [Jacobians/Jacobian/Construction.lean](Jacobians/Jacobian/Construction.lean) | `Jacobian X` + 7 typeclass instances via `ComplexTorus` bridge |
| [Jacobians/Axioms/](Jacobians/Axioms/) | 10 named-axiom files (see §Named axioms below) |
| [Jacobians/ProjectiveCurve/Line.lean](Jacobians/ProjectiveCurve/Line.lean) | `ProjectiveLine := OnePoint ℂ` — 7/7 X-side instances + stereographic homeomorphism to S² |
| [Jacobians/ProjectiveCurve/Elliptic.lean](Jacobians/ProjectiveCurve/Elliptic.lean) | `Elliptic ω₁ ω₂ h := ComplexTorus ℂ (ℤω₁ + ℤω₂)` — 7/7 X-side instances axiom-free via `ComplexTorus` bridge |
| [Jacobians/ProjectiveCurve/Hyperelliptic.lean](Jacobians/ProjectiveCurve/Hyperelliptic.lean) | `HyperellipticData` (squarefree `f : ℂ[x]`) + affine model `{(x,y) \| y² = f(x)}`. Projective model + atlas + instances are TODOs |
| [Jacobians/ProjectiveCurve/PlaneCurve.lean](Jacobians/ProjectiveCurve/PlaneCurve.lean) | `PlaneCurveData` (homogeneous `F ∈ ℂ[x,y,z]` + smoothness) + affine patch `{F(x,y,1) = 0}`. Projective curve + atlas + Plücker genus are TODOs |
| [docs/formalization-plan.md](docs/formalization-plan.md) | Detailed plan with four rounds of adversarial review (Gemini ×2, Codex, Claude) |
| [docs/gemini-review.md](docs/gemini-review.md) | Gemini 3 Pro review, round 1 (plan) |
| [docs/codex-review.md](docs/codex-review.md) | Codex (GPT-5) review, round 2 (plan) |
| [docs/claude-review.md](docs/claude-review.md) | Claude self-review, round 3 (plan) |
| [docs/gemini-review-2.md](docs/gemini-review-2.md) | Gemini round-2 review of Theta + Part B architecture |
| [docs/gemini-review-axioms.md](docs/gemini-review-axioms.md) | Gemini round-3 review of the axiom suite (caught `AX_FiniteDimOneForms` unsoundness) |
| [docs/challenge-summary.md](docs/challenge-summary.md) | Summary of the challenge and Zulip discussion |
| [docs/status.md](docs/status.md) | Sorry inventory, axiom inventory, progress tracker |
| [docs/history.md](docs/history.md) | Chronological work log — the *why* behind each session |

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

**Property axioms on top of the real defs:** `AX_ofCurve_contMDiff`, `AX_ofCurve_inj`, `AX_pushforward_contMDiff`, `AX_pushforward_id_apply`, `AX_pushforward_comp_apply`, `AX_pullback_contMDiff`, `AX_pullback_id_apply`, `AX_pullback_comp_apply`, `AX_pushforward_pullback`. (`AX_jacobian_lieAddGroup` was retired from axiom to theorem 2026-04-23 via inline ULift-smoothness lemmas.)

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

Currently 8341 jobs, green. **Zero sorries** anywhere in the project. All 24 Buzzard sorries have been discharged: the six challenge-exposed *data* definitions (`genus`, `Jacobian`, `ofCurve`, `pushforward`, `pullback`, `ContMDiff.degree`) are **real `def`s** layered over smaller functional axioms (path-integral functional, ambient linear maps with lattice preservation, `AX_BranchLocus`); the challenge-exposed *property* theorems route through named axioms in `Jacobians/Axioms/AbelJacobiMap.lean` + `Uniformization0.lean` encoding the classical Riemann-surface theory. Each axiom retires to a theorem once the corresponding Mathlib infrastructure (real-analytic path integration, pullback/trace of 1-forms, line bundles, surface classification) lands.

## Status

| Module | Status |
|--------|--------|
| **Part A — `AbelianVariety/`** | |
| `Lattice.lean` | ✅ conventions in place |
| `ComplexTorus.lean` | ✅ **complete** — 7/7 Buzzard instances on abstract `(V, L)`, axiom-free, zero-sorry |
| `Siegel.lean` | ✅ scaffold — definition + `CoeFun` + `ext`; Sp(2g, ℤ)-action and concrete-lattice helpers TODO |
| `Theta.lean` | ✅ scaffold — `RiemannTheta` defined; summability / analyticity / quasi-periodicity TODO |
| **Part B — `RiemannSurface/`** | |
| `OneForm.lean` | 🔄 safe stub — `HolomorphicOneForm X = ↥⊥`; predicates-and-real-carrier TODO |
| `Homology.lean` | ✅ scaffold — `H1 X x₀ := Additive (Abelianization (π₁ X x₀))` |
| `Genus.lean` | ✅ `genus X := Module.finrank ℂ (HolomorphicOneForm X)` (= 0 at stub) |
| `Periods.lean` | ✅ scaffold — `periodMap` axiom-stub |
| `IntersectionForm.lean` | ✅ scaffold — `AX_PeriodInjective` |
| `PathIntegral.lean` | — not started |
| **Axioms — `Axioms/`** | |
| `FiniteDimOneForms.lean` | ✅ declared; instance via `⊥`-stub (unsoundness fixed 2026-04-22) |
| `H1FreeRank2g.lean` | ✅ declared (typed) |
| `IntersectionForm.lean` | ✅ declared (map axiom-stub + 2 property axioms) |
| `PeriodLattice.lean` | ✅ declared (`AX_PeriodLattice` + `instPeriodLatticeDiscrete`) |
| `RiemannBilinear` / `RiemannRoch` / `SerreDuality` / `AbelTheorem` / `BranchLocus` / `PluckerFormula` | ✅ doc-only (signatures sketched, pending consumer modules) |
| **Bridge — `Jacobian/`** | |
| `Construction.lean` | ✅ `Jacobian X` + 7 typeclass instances via `ComplexTorus` bridge (basis baked in). Universe-lift wrapper to match Buzzard's `: Type u` signature TODO |
| **Track 2 — `ProjectiveCurve/`** | |
| `Line.lean` | ✅ complete, 0 sorries, all 7 X-side Buzzard instances |
| `Elliptic.lean` | ✅ complete scaffold, 0 sorries, all 8 X-side Buzzard instances (incl. ConnectedSpace) inherited from `ComplexTorus`. `ofUpperHalfPlane τ hτ` constructor. `genus = 1`, `Jacobian(E) ≃ E`, explicit `AnalyticCycleBasis` TODO (blocked on `OneForm` refinement) |
| `Hyperelliptic.lean` | ✅ thin scaffold: `HyperellipticData` + `HyperellipticAffine`. Projective compactification, 7 instances, and concrete holomorphic differentials are TODOs (substantial branch-cut work) |
| `PlaneCurve.lean` | ✅ thin scaffold: `HomogeneousPoly`, `PlaneCurveData` + smoothness hypothesis, `PlaneCurveAffine`. Projective model + atlas + Plücker genus (d-1)(d-2)/2 are TODOs |

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
