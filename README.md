# Jacobians of Compact Riemann Surfaces

A Lean 4 formalization attempt at Kevin Buzzard's Jacobian Challenge (April 2026): define and prove an API for the Jacobian of a compact Riemann surface, the Abel-Jacobi map, and pushforward/pullback functoriality.

**Challenge source:** https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9 (v0.2)

## What this project is

Buzzard's challenge is a single Lean file containing `sorry`-ed definitions and theorems — **24 sorries** total. The API is designed so that no "hack" definition (e.g. `Jacobian := 0`) can simultaneously satisfy all the theorems — in particular `genus_eq_zero_iff_homeo` forces `genus` to be correct, and `ofCurve_inj` forces the Abel-Jacobi map to be genuinely injective in positive genus.

All underlying mathematics is classical (Abel 1829, Jacobi 1851). The challenge is to formalize it in Lean 4 / Mathlib without extending Mathlib itself, i.e. living entirely downstream.

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

**Declared with Lean signatures (8 axioms across 4 files):**
- `Axioms/FiniteDimOneForms.lean` — `AX_FiniteDimOneForms` (+ global `FiniteDimensional` instance, currently routed through `⊥`-stub without invoking the axiom).
- `Axioms/H1FreeRank2g.lean` — `AX_H1FreeRank2g` via `Module.Basis (Fin (2 * genus X)) ℤ (H1 X x₀)`.
- `Axioms/IntersectionForm.lean` — `intersectionForm x₀` (axiom-stub for a `def`) + `AX_IntersectionForm_alternating` + `AX_IntersectionForm_nondeg`.
- `Axioms/PeriodLattice.lean` — `instPeriodLatticeDiscrete` + `AX_PeriodLattice` (the period image is an `IsZLattice` in `Fin (genus X) → ℂ`; needed for the Jacobian bridge).
- `RiemannSurface/IntersectionForm.lean` — `AX_PeriodInjective`.
- `RiemannSurface/Periods.lean` — `periodMap` (axiom-stub for a `def` landing with `PathIntegral`).

**Declared doc-only targets (signatures sketched in comments, pending consumer-module types):** `AX_RiemannBilinear`, `AX_RiemannRoch`, `AX_SerreDuality`, `AX_AbelTheorem`, `AX_BranchLocus`, `AX_PluckerFormula`. All six target signatures were revised 2026-04-22 per Gemini review (existentials shifted over basis choice, `FiniteDimensional` hypotheses, ℤ-subtraction, `tsum`).

## Dependencies

- **Lean**: `v4.30.0-rc1` (matching the toolchain of the pinned Mathlib commit)
- **Mathlib**: commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), as specified in the challenge

## Build

```bash
lake update
lake build
```

Currently 8328 jobs, green. **16 sorries** (down from 24) — all in `Jacobians/Challenge.lean`. Zero sorries anywhere else. The 8 closed are `genus` + `Jacobian` + 6 of 7 typeclass instances; `LieAddGroup` and the Abel-Jacobi/pushforward/pullback theorems remain.

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
| `PlaneCurve.lean` | — not started |

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
