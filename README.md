# Jacobians of Compact Riemann Surfaces

An interface-complete Lean 4 bridge to Kevin Buzzard's [Jacobian Challenge](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9) (v0.2, April 2026): all 24 `sorry`s in `Challenge.lean` discharged as real `def`s and `instance`s, with the remaining mathematical content organized as classified axioms (textbook-citable classical theorems + 5 function-existence axioms with construction plans). Not a from-first-principles proof of Jacobian theory; a scaffold that closes Buzzard's exposed API and enumerates the work below it.

## The challenge

Buzzard ships a single Lean file `Challenge.lean` with **24 `sorry`s**, defining an API for the Jacobian of a compact Riemann surface, the Abel–Jacobi map, and pushforward / pullback functoriality along holomorphic maps. The design is adversarial: the API cannot be satisfied by any "hack" definition (e.g. `Jacobian := 0`) because `genus_eq_zero_iff_homeo` forces `genus` to be correct and `ofCurve_inj` forces Abel–Jacobi to be genuinely injective in positive genus. All underlying mathematics is classical (Abel 1829, Jacobi 1851); the challenge is to formalize it *without extending Mathlib itself*.

## How this repo addresses it

**Interface closed.** All 24 `sorry`s in `Challenge.lean` discharge as real `def`s and real `instance`s — no axiom stub at the Buzzard-API level. Functoriality identities (identity + composition for both `pullback` and `pushforward`) are derived **theorems**, not axioms.

**Architecture.** Period-lattice construction, basis-free at the type level:

- **Part A — `AbelianVariety/`**: `ComplexTorus V L := V ⧸ L` for `L : Submodule ℤ V` with `[IsZLattice ℝ L]`. Supplies all 7 typeclass instances Buzzard requires on `Jacobian X` (`AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace V`, `IsManifold`, `LieAddGroup`), plus the auxiliary `IsTopologicalAddGroup` consumed by `LieAddGroup`. Axiom-free.
- **Track 1 — `RiemannSurface/` + `Jacobian/`**: abstract `X` from Buzzard's typeclasses → period lattice → `Jacobian X := ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X x₀ (Module.finBasis ℂ (HolomorphicOneForm X)))`.
- **Track 2 — `ProjectiveCurve/`**: concrete projective curves as real `def`s satisfying Buzzard's typeclasses by construction — `ProjectiveLine`, `Elliptic`, `HyperellipticOdd` / `HyperellipticEven` (two-chart pushout), with `PlaneCurve` axiom-stubbed pending three-chart atlas.

**Concrete witnesses.** `ProjectiveLine` (genus 0) and `Elliptic ω₁ ω₂` (genus 1) are fully populated — real types, real `AnalyticCycleBasis`, `genus ProjectiveLine = 0` and `genus (Elliptic ω₁ ω₂ h) = 1` are **derived theorems** (the latter via intrinsic Liouville on compact complex manifolds applied to `ellipticDz`). Both parities of hyperelliptic curves are real types; unified `Hyperelliptic H` is an axiom type pinned by homeomorphism (`≃ₜ`) axioms to the real parity cases.

**Axioms are classified, not hidden** ([`docs/dependency-trace.md`](docs/dependency-trace.md)):

- **Classical-theorem axioms** (Riemann–Roch, Serre duality, Abel, Riemann bilinear, period-lattice discreteness, finite-dim 1-forms, branch locus, uniformization): each a textbook citation. The right shape of axiom for a layered formalization.
- **5 data-level function-existence axioms** (`pathIntegralBasepointFunctional`, `loopIntegralToH1`, `pullbackOneForm`, `pushforwardOneForm`, `localOrder`): each has a construction plan in [`docs/construction-plans/`](docs/construction-plans/) summing to ~5–6 weeks focused contributor work.
- **Curve-atlas axioms** for unified `Hyperelliptic` and for `PlaneCurve`: proper axiomatizations of classical atlas constructions; discharge is substantial atlas work.

## Response to Buzzard's diagnosis

Buzzard's challenge post identifies two Mathlib gaps that make the problem hard:

> *"all definitions of Jacobian that I know involve quotienting a manifold by a discrete group, which isn't in mathlib as far as I know. The one where you use `X^g` by the symmetric group involves a delicate local analysis when points coincide and the one where you quotient out the dual of the holomorphic 1-forms by the first homology will involve integrating differentials around loops which we don't have either, at least in this generality."*

We rejected the symmetric-product route `X^g / S_g` precisely because of the coincident-points local analysis Buzzard flags, and took the period-lattice route (quotient of `(HolomorphicOneForm X)*` by the period lattice). This carries Buzzard's two gaps differently:

**Gap 1 — "quotient a manifold by a discrete group" — solved by hand for the specific case.** We don't wait for Mathlib's general theorem (Rothgang's PR in flight) or cite it. `Jacobians/AbelianVariety/ComplexTorus.lean` builds `ComplexTorus V L := V ⧸ L` for `L : Submodule ℤ V` with `[IsZLattice ℝ L]` and supplies all 7 Buzzard-required typeclass instances (`AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace V`, `IsManifold`, `LieAddGroup`) directly via translation atlas + lattice discreteness. Axiom-free, zero sorry. Limited scope (works only for `V ⧸ L`-shaped quotients) but covers the Jacobian construction entirely.

**Gap 2 — "integrating differentials around loops" — isolated, not filled.** We do not supply a general theory of line integrals of 1-forms on manifolds. Instead we name the two function-existence primitives we actually need — `pathIntegralBasepointFunctional` and `loopIntegralToH1` — and carry them as axioms with written construction plans (multi-chart path integration + Stokes homotopy invariance, ~2 weeks focused work, [`docs/construction-plans/path-integral-basepoint.md`](docs/construction-plans/path-integral-basepoint.md), [`docs/construction-plans/loop-integral-h1.md`](docs/construction-plans/loop-integral-h1.md)). The `AX_pathIntegral_local_antiderivative` Prop-level companion (chart-local FTC) binds the functional to cocycle data so `:= 0` is not a valid witness.

So the scoping decision is: solve Gap 1 by hand for the needed shape; isolate Gap 2 cleanly so the rest of the API closes around it. The foundation is complete modulo Gap 2.

## Current state

| | |
|---|---|
| Build | `lake build` — **8345 jobs green, 0 `sorry`** |
| Foundation defs | 13/13 real (`Jacobian X`, all 7 typeclass instances, `ofCurve`, `pushforward`, `pullback`, `degree`) |
| Property theorems derived | `ofCurve_self`, `pushforward_id_apply` / `_comp_apply`, `pullback_id_apply` / `_comp_apply`, `genus_ProjectiveLine_eq_zero`, `genus_Elliptic_eq_one` |
| Concrete real curve types | `ProjectiveLine`, `Elliptic`, `HyperellipticOdd`, `HyperellipticEven` (two-chart pushout) |
| Axiom-stubbed curve types | unified `Hyperelliptic` (pinned by `≃ₜ` to real cases), `PlaneCurve` |

Full axiom inventory and classification: [`docs/challenge-annotated.md`](docs/challenge-annotated.md), [`docs/dependency-trace.md`](docs/dependency-trace.md).

## Resources used

| | |
|---|---|
| **Wall-clock** | 2026-04-19 → 2026-04-24 (6 calendar days, all active) |
| **Commits** | 93 |
| **Lean code** | ~6,600 lines across `Jacobians/` (includes Buzzard's filled-in `Challenge.lean`) |
| **Documentation** | ~6,800 lines: challenge annotation, dependency trace, 5 construction plans, adversarial-review records |
| **Model time** | Claude Opus 4.7 (primary coder), GPT-5.4 Codex (rescue passes on Jacobian functoriality derivations, HyperellipticEven T2 / Compact proofs), Gemini 3 Pro deep-think (axiom audits, type-equality smell-test) |
| **Human effort** | Mathematician-user directing: scope, axiom-vs-proof boundary, hack-blocker judgments, review of all landings. Zero human-written Lean. |

## What this claim does and doesn't say

We claim a **solid foundation with correct definitions** for Buzzard's challenge: the interface is closed with real constructions, genus-0 / genus-1 / hyperelliptic curves are populated as real types, and every remaining axiom is enumerated and classified. We do not claim a sorry-free end-to-end solution — the five data-level axioms and the ten classical-theorem citations remain, each with a discharge plan.

## Build

```bash
lake update
lake build
```

- **Lean:** `v4.30.0-rc1`
- **Mathlib:** commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), as pinned by the challenge.

## Further documentation

- [`Jacobians/Challenge.lean`](Jacobians/Challenge.lean) — Buzzard's v0.2 file verbatim (24 sorries), pinned.
- [`docs/challenge-filled.md`](docs/challenge-filled.md) — filled-in spec, every sorry resolved with its prerequisites inlined.
- [`docs/challenge-annotated.md`](docs/challenge-annotated.md) — F/T classification of the 24 sorries.
- [`docs/dependency-trace.md`](docs/dependency-trace.md) — transitive axiom audit.
- [`docs/construction-plans/`](docs/construction-plans/) — discharge plans for the 5 data-level axioms.
- [`docs/formalization-plan.md`](docs/formalization-plan.md) — construction-strategy rationale.

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
