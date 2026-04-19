# Jacobians of Compact Riemann Surfaces

A Lean 4 formalization attempt at Kevin Buzzard's Jacobian Challenge (April 2026): define and prove an API for the Jacobian of a compact Riemann surface, the Abel-Jacobi map, and pushforward/pullback functoriality.

**Challenge source:** https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9 (v0.2)

## What this project is

Buzzard's challenge is a single Lean file containing `sorry`-ed definitions and theorems. The API is designed so that no "hack" definition (e.g. `Jacobian := 0`) can simultaneously satisfy all the theorems — in particular `genus_eq_zero_iff_homeo` forces `genus` to be correct, and `ofCurve_inj` forces the Abel-Jacobi map to be genuinely injective in positive genus.

All underlying mathematics is classical (Abel 1829, Jacobi 1851). The challenge is to formalize it in Lean 4 / Mathlib without extending Mathlib itself, i.e. living entirely downstream.

## File structure

| File | Contents |
|------|----------|
| [Jacobians/Challenge.lean](Jacobians/Challenge.lean) | Buzzard's v0.2 file verbatim — pinned, tracks upstream |
| [Jacobians/Basic.lean](Jacobians/Basic.lean) | Scratch module for lemmas and auxiliary defs |
| [docs/challenge-summary.md](docs/challenge-summary.md) | Summary of the challenge and Zulip discussion |
| [docs/plan.md](docs/plan.md) | Construction-strategy decision and roadmap |
| [docs/status.md](docs/status.md) | Sorry inventory, axiom inventory, progress tracker |

## Construction strategies under consideration

Three classical routes to `Jacobian X`:

1. **Period lattice** `ℂ^g / Λ` — integrate a basis of holomorphic 1-forms over `H₁(X, ℤ)`. Requires: holomorphic 1-forms on a Riemann surface, integration along loops, first homology.
2. **Pic⁰(X)** — degree-0 divisors modulo principal divisors. Needs divisors and meromorphic functions on a Riemann surface, plus Riemann-Roch for the complex-manifold structure.
3. **Sheaf cohomology** `H¹(X, 𝒪) / H¹(X, ℤ)`. Cleanest theoretically; needs sheaf cohomology for complex manifolds.

The real prize is proving all three are equivalent. Decision deferred — see [docs/plan.md](docs/plan.md).

## Known Mathlib gaps

From Michael Rothgang on the Zulip thread:
- Quotient of a manifold by a discrete group: charted-space instance awaiting review; manifold instance sorry-free modulo a missing "smooth Lie group action on a manifold" definition.
- Integration of holomorphic 1-forms over loops on a general Riemann surface (Math Inc. made progress on the ℂ case for the Viazovska autoformalization).
- Riemann-Roch / Serre duality for finite-dimensionality arguments.

## Dependencies

- **Lean**: `v4.30.0-rc1` (matching the toolchain of the pinned Mathlib commit)
- **Mathlib**: commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), as specified in the challenge

## Build

```bash
lake update
lake build
```

## Status

Scaffold only. No sorries have been filled. See [docs/status.md](docs/status.md).

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
