# Jacobians of Compact Riemann Surfaces

A Lean 4 formalization attempt at Kevin Buzzard's Jacobian Challenge (April 2026): define and prove an API for the Jacobian of a compact Riemann surface, the Abel-Jacobi map, and pushforward/pullback functoriality.

**Challenge source:** https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9 (v0.2)

## What this project is

Buzzard's challenge is a single Lean file containing `sorry`-ed definitions and theorems — **24 sorries** total. The API is designed so that no "hack" definition (e.g. `Jacobian := 0`) can simultaneously satisfy all the theorems — in particular `genus_eq_zero_iff_homeo` forces `genus` to be correct, and `ofCurve_inj` forces the Abel-Jacobi map to be genuinely injective in positive genus.

All underlying mathematics is classical (Abel 1829, Jacobi 1851). The challenge is to formalize it in Lean 4 / Mathlib without extending Mathlib itself, i.e. living entirely downstream.

## Architecture

Two parallel tracks, both building on a shared Part A:

- **Part A (`Jacobians/AbelianVariety/`)** — abelian-variety machinery, axiom-free. `ComplexTorus V L := V ⧸ L` for `L : Submodule ℤ V` with `[IsZLattice ℝ L]`. Supplies all seven typeclass instances Buzzard demands on `Jacobian X`.
- **Track 1 (`Jacobians/RiemannSurface/` + `Jacobians/Jacobian/`)** — abstract `X` from Buzzard's typeclasses → period lattice → `Jacobian X := ComplexTorus (HolomorphicOneForm X →ₗ[ℂ] ℂ) (periodLattice X)`. Closes the challenge on arbitrary `X`.
- **Track 2 (`Jacobians/ProjectiveCurve/`)** — concrete projective curves (`ProjectiveLine`, elliptic, hyperelliptic, smooth plane curves) each satisfying Buzzard's typeclasses by construction. Closes the challenge on these specific types.

## File structure

| File | Contents |
|------|----------|
| [Jacobians/Challenge.lean](Jacobians/Challenge.lean) | Buzzard's v0.2 file verbatim (24 sorries) — pinned, tracks upstream |
| [Jacobians/Basic.lean](Jacobians/Basic.lean) | Shared imports / notation |
| [Jacobians/AbelianVariety/Lattice.lean](Jacobians/AbelianVariety/Lattice.lean) | Conventions around Mathlib's `IsZLattice` |
| [Jacobians/AbelianVariety/ComplexTorus.lean](Jacobians/AbelianVariety/ComplexTorus.lean) | `ComplexTorus V L` — 5/7 Buzzard instances (AddCommGroup, TopologicalSpace, IsTopologicalAddGroup, T2Space, CompactSpace). `ChartedSpace / IsManifold / LieAddGroup` TODO |
| [Jacobians/ProjectiveCurve/Line.lean](Jacobians/ProjectiveCurve/Line.lean) | `ProjectiveLine := OnePoint ℂ` — 7/7 X-side instances + stereographic homeomorphism to S² |
| [docs/formalization-plan.md](docs/formalization-plan.md) | Detailed plan with three rounds of adversarial review (Gemini, Codex, Claude) |
| [docs/gemini-review.md](docs/gemini-review.md) | Gemini 3 Pro review, round 1 |
| [docs/codex-review.md](docs/codex-review.md) | Codex (GPT-5) review, round 2 |
| [docs/claude-review.md](docs/claude-review.md) | Claude self-review, round 3 |
| [docs/challenge-summary.md](docs/challenge-summary.md) | Summary of the challenge and Zulip discussion |
| [docs/status.md](docs/status.md) | Sorry inventory, axiom inventory, progress tracker |

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

See [docs/formalization-plan.md](docs/formalization-plan.md) §7. Nine named axioms, led by `AX_RiemannBilinear`, `AX_FiniteDimOneForms`, `AX_BranchLocus`, `AX_RiemannRoch`, `AX_AbelTheorem`.

## Dependencies

- **Lean**: `v4.30.0-rc1` (matching the toolchain of the pinned Mathlib commit)
- **Mathlib**: commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), as specified in the challenge

## Build

```bash
lake update
lake build
```

Currently 8307 jobs, green. 24 sorries — all in `Jacobians/Challenge.lean` (Buzzard's verbatim file). Zero sorries anywhere else.

## Status

| Module | Status |
|--------|--------|
| `AbelianVariety/Lattice.lean` | ✅ conventions in place |
| `AbelianVariety/ComplexTorus.lean` | 🔄 5/7 instances; ChartedSpace + IsManifold + LieAddGroup pending |
| `AbelianVariety/Siegel.lean` | — not started |
| `AbelianVariety/Theta.lean` | — not started |
| `ProjectiveCurve/Line.lean` | ✅ complete, 0 sorries, all 7 X-side Buzzard instances |
| `ProjectiveCurve/Elliptic.lean` | — not started |
| `ProjectiveCurve/Hyperelliptic.lean` | — not started |
| `ProjectiveCurve/PlaneCurve.lean` | — not started |
| `RiemannSurface/*` (Part B) | — not started |
| `Jacobian/*` (bridge) | — not started |

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
