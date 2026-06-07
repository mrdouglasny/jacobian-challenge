# Jacobians of Compact Riemann Surfaces

A Lean 4 formalization addressing [Kevin Buzzard's **Jacobian Challenge**](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9) (v0.2, April 2026). All **24 `sorry`s** in Buzzard's `Challenge.lean` are closed with real `def`s and `instance`s; the remaining classical mathematics is captured as a **classified, audited axiom layer**; and a set of **real theorems** is proved on top — including the two anti-degeneracy properties Buzzard designed the challenge around (correct genus, injective Abel–Jacobi) plus the Albanese universal property.

> **What this is, honestly.** A scaffold that *closes Buzzard's interface* and proves real theorems on it, with the deep classical inputs isolated as a classified, discharge-planned axiom layer — **not** a from-first-principles proof of Jacobian theory. The axioms are LLM-authored and **have not had independent human-mathematician review**. See [Caveats](#caveats--read-before-relying-on-this) before relying on any result.

## At a glance

| | |
|---|---|
| **Build** | `lake build Jacobians` green (8602 jobs) |
| **Toolchain** | Lean `v4.30.0`; Mathlib pinned in `lake-manifest.json` (rev `c5ea003`) |
| **Buzzard API** | 24/24 `sorry`s closed as real `def`s / `instance`s |
| **Axioms** | 44, all classified + kernel-verified — [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) |
| **`sorry`s** | 0 in the core; 11 in out-of-scope extensions; 8 intentional anchor-statement deferrals |
| **Provenance** | ~26k LOC our own Lean (103 files) + vendored Kirov (Apache 2.0) & Wallace (MIT) |

## The challenge

Buzzard's `Challenge.lean` defines an API for the Jacobian of a compact Riemann surface, the Abel–Jacobi map, and pushforward/pullback functoriality — with 24 `sorry`s to fill. The design is **adversarial**: the API cannot be satisfied by a hack definition (e.g. `Jacobian := 0`), because `genus_eq_zero_iff_homeo` forces `genus` to be correct and `ofCurve_inj` forces Abel–Jacobi to be genuinely injective in positive genus. The underlying mathematics is classical (Abel 1829, Jacobi 1851); the task is to formalize it on top of current Mathlib.

The deeper point is about **validation, not just compilation**: the Lean kernel checks *proofs*, never that a `def` *means* what it should, so a degenerate definition can still compile. Buzzard defends against this by attaching independent obligations to each definition. This repo pushes the same idea further — adding the Albanese **universal property** as an extra target the construction must satisfy, pinning it harder against degeneracy.

## What this repo proves

These are the genuine theorems — what a reader can trust the formalization to have established (modulo the axioms each one names; `#print axioms`-checked, no `sorryAx`).

| Result | Status |
|--------|--------|
| `genus ProjectiveLine = 0` | **axiom-free** (chart-cocycle + Liouville: 1-forms on ℙ¹ are a subsingleton) |
| `genus (Elliptic ω₁ ω₂) = 1` | **axiom-free** (intrinsic Liouville on `ellipticDz`) |
| `genus (HyperellipticEvenProj H) = H.f.natDegree / 2 − 1` | real proof — Liouville L2/L3 **discharged** (PR #96) |
| Abel–Jacobi **injective** for genus > 0 | **theorem** `AX_ofCurve_inj` (`Axioms/OfCurveInjective.lean`) — was an axiom, now derived from the proved period-triangle theorem + Abel's theorem + a proven genus obstruction |
| Albanese **categoricity** `ofCurve_isJacobian` | **theorem** — the concrete `Jacobian`/`ofCurve` satisfy the universal property (`∃!` factorization through holomorphic group homs), pinning the Jacobian up to unique isomorphism |
| Functoriality identities (`pushforward`/`pullback` id + comp) | derived **theorems**, not axioms |
| `FiniteDimensional ℂ (HolomorphicOneForm X)` | derived from Kirov's real ~3,400-LOC Montel proof via an injective bridge |

The elliptic Abel-injectivity witness `elliptic_ofCurve_injective` is proved directly on `ℂ/Λ` as a real computation through the period lattice — the strongest single piece of evidence that the construction is non-degenerate.

## What it assumes — the axiom layer

Every axiom is a staging point with a citation and a discharge plan, classified in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md). They group into seven topics (counts sum to the **45** kernel-verified axioms; topic boundaries are soft — a few axioms could reasonably sit in an adjacent row); difficulty is the *discharge* difficulty (🟢 mechanical / available in Mathlib, 🟡 substantial but standard, 🔴 research-grade — a genuine textbook theorem with no existing Lean proof):

| Topic | Count | Difficulty |
|-------|:-----:|:----------:|
| Period / Hodge / homology core (Riemann bilinear, period lattice, intersection form, H₁ bases) | 8 | 🔴🟡 |
| Abel–Jacobi (`AX_AbelTheorem` + `ofCurve` smoothness; `ofCurve_inj` is now a theorem) | 2 | 🔴 |
| Sheaf cohomology / Riemann–Roch / Serre / Plücker / uniformization (`H0` de-opaqued) | 10 | 🔴 |
| Functoriality (pushforward / pullback naturality + lattice preservation) | 7 | 🟡 |
| Torus / Albanese universal property | 3 | 🟡 |
| Concrete curves (hyperelliptic / plane-curve / ℙ¹ atlases & witnesses) | 15 | 🟢🟡 |
| Liouville hierarchy L2 / L3 (the canonical-differentials theorem) | 0 | ✅ **discharged** (PR #96) |
| **Total** | **45** | |

**Anchor APIs for the deepest axioms.** For the 🔴 research-grade cluster, the real risk is *formulation, not proof* — a degenerate or vacuous statement compiles just as happily as a faithful one. So before attempting those proofs we pin **faithful, cross-model-vetted statements first** (real `def`s + `sorry`-ed theorems, checked against the textbook form), and do the hard proofs last against a known-correct surface. Landed so far: `riemannRochSpace` (the real `L(D)`, a ℂ-submodule of the **meromorphic germ quotient** `MeroField = MeroFunctions ⧸ GermZero` — corrected from an earlier raw-`X→ℂ` version that was *degenerate*: it admitted germ-zero "spike" functions, so was infinite-dimensional with `finrank ≡ 0`; the compiled `germZero_ne_bot` witnesses that bug; this de-opaqued `H0`), and three statement APIs gated by the `SheafCohomologySpec` faithfulness suite. **`PluckerAPI` is complete** — its statements are fully proved (the low-degree corollaries reduce by arithmetic to the `AX_PluckerFormula` axiom), so the remaining Plücker work is the formula axiom and the plane-curve atlas, not the API. **`h⁰(0) = 1` is now proved axiom-free** over the corrected space — `L(0)` = holomorphic functions = constants (via the normal-form honest representative + Liouville → `LinearEquiv (ℂ ≃ L(0))` → `finrank = 1`), the concrete confirmation that the faithfulness fix gives the *right* dimension (it was `finrank ≡ 0` over the old degenerate space). **`RiemannRochAPI` and `SerreDualityAPI` still carry 8 deferred `sorry`s** (the Riemann–Roch identity, `h⁰(K) = g`, general finite-dimensionality of `L(D)`, Serre vanishing) — the genuine open targets, true-but-unproven over the corrected space. Methodology: [`docs/planning/DEEP_AXIOM_ANCHORS_PLAN.md`](docs/planning/DEEP_AXIOM_ANCHORS_PLAN.md). Every axiom additionally has a per-axiom discharge plan under [`docs/planning/`](docs/planning/) (one file each, Gemini-vetted).

## Caveats — read before relying on this

- **The axioms are LLM-authored and not human-reviewed.** Each was written or curated in-session and cross-vetted by a second model (typically Gemini deep-think + Codex), but none has had independent human-mathematician review. **If you are evaluating this work, read [`Jacobians/Axioms/`](Jacobians/Axioms/) and [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) first.**
- **This is a reduction, not a closed proof.** A theorem whose only non-Lean-proven content is a textbook-classical axiom should be read as *"reduced to that classical input"*, not *"proved from Mathlib"*.
- **Zero human-written Lean.** The Lean was written by Claude (Opus) with Codex rescue passes and Gemini axiom audits, directed by a mathematician on scope, the axiom-vs-proof boundary, and review of every landing.
- **`sorry`s, in two honest categories** (the *core* — challenge API, Jacobian construction, curve witnesses, S1–S7 1-form framework — is `sorry`-free):
  - **11 gap-layer** — out-of-scope extension/bridge files (`Extensions/Hyperelliptic.lean` 6, `Extensions/AbelJacobi.lean` 4, `Hyperelliptic/AntiInvariance.lean` 1).
  - **8 anchor-layer** — *intentionally* deferred proofs of the vetted RR/Serre statements above (`RiemannRochAPI` 7, `SerreDualityAPI` 1). `PluckerAPI` is fully proved; `h⁰(0)=1` is proved axiom-free; in `SerreDualityAPI`, the dimension-form duality and the `h⁰−h¹` identity are real (from `AX_SerreDuality` / `AX_RiemannRoch`), leaving only Serre vanishing.

## How it's built

The construction takes the **period-lattice route** — `Jac X = (HolomorphicOneForm X)* / H₁` — rather than the symmetric product `Xᵍ/Sᵍ` (whose coincident-point local analysis Buzzard flags as hard). It is basis-free at the type level.

- **`AbelianVariety/`** — `ComplexTorus V L := V ⧸ L` for a ℤ-lattice `L`, supplying all 7 typeclass instances Buzzard requires on `Jacobian X` directly from a translation atlas + lattice discreteness. **Axiom-free.** This is the concrete answer to Buzzard's "quotient a manifold by a discrete group" gap for the shape the Jacobian needs.
- **`RiemannSurface/` + `Jacobian/`** — the abstract track: from Buzzard's typeclasses → holomorphic 1-forms → period lattice → `Jacobian X`. The Abel–Jacobi map is a real `∫` (multi-chart line integral over an analytic cycle basis), addressing Buzzard's "integrating differentials around loops" gap from underneath via the Kirov bridge.
- **`ProjectiveCurve/`** — the concrete track: real curve `def`s satisfying Buzzard's typeclasses by construction — `ProjectiveLine`, `Elliptic`, `HyperellipticOdd`/`HyperellipticEven`, with `PlaneCurve` atlas-stubbed.
- **`Extensions/`** — test theorems exercising the formalization end-to-end (the regression catch where `Module.finrank` silently returns 0).

## Repository map

| Path | Contents |
|------|----------|
| [`Jacobians/Challenge.lean`](Jacobians/Challenge.lean) | Buzzard's v0.2 file verbatim (pinned), all 24 `sorry`s closed downstream |
| [`Jacobians/AbelianVariety/`](Jacobians/AbelianVariety/) | `ComplexTorus` (axiom-free) |
| [`Jacobians/RiemannSurface/`](Jacobians/RiemannSurface/) | period lattice, line integrals, `riemannRochSpace`, the RR/Serre/Plücker anchor APIs |
| [`Jacobians/ProjectiveCurve/`](Jacobians/ProjectiveCurve/) | concrete curves + the hyperelliptic 1-form framework |
| [`Jacobians/Axioms/`](Jacobians/Axioms/) | the cross-cutting classified axioms (Riemann–Roch, Serre, Abel, Liouville hierarchy, …) |
| [`Jacobians/UniversalProperty.lean`](Jacobians/UniversalProperty.lean) | `IsJacobian` + the categoricity theorem |
| [`Jacobians/Vendor/`](Jacobians/Vendor/) | ported Kirov + Wallace modules (see [Provenance](#vendored-sources--attribution)) |
| [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) | **canonical axiom audit** — start here to review the debt |
| [`docs/`](docs/) | status snapshots, discharge plans, dependency trace, construction plans |

## Building

```bash
lake build
```

Lean `v4.30.0`; Mathlib at the revision pinned in `lake-manifest.json`. CI runs `lake build` end-to-end plus a golden `#print axioms` check and a guard keeping the core `sorry`-free.

## Vendored sources & attribution

We build on real Lean from two sibling Jacobian-Challenge attempts, each vendored under its **upstream** license with per-file attribution headers, the upstream `LICENSE`, and a `PROVENANCE.md`. Full adoption record: [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md).

- **[rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude)** (Apache 2.0) — Montel finite-dimensionality of holomorphic 1-forms, line integrals, the ℤ-lattice/complex-torus quotient infrastructure. Used to retire `AX_FiniteDimOneForms` and `pullbackOneForm` and to back the Abel–Jacobi integral. Ported under `Jacobians/Vendor/Kirov/`.
- **[tangentstorm/JacobianChallenge](https://github.com/tangentstorm/JacobianChallenge)** (MIT) — self-contained, sorry-free analytic modules (holomorphic maps, meromorphic order, branched covers). Ported under `Jacobians/Vendor/Wallace/`; used in the genus-obstruction proof behind Abel injectivity.

Both vendored subtrees are **axiom-free**; their headline theorems `#print axioms`-verify to the three standard Lean axioms only.

## Contributors & acknowledgments

An agent-assisted community project. Contributions span code, vendored proofs, and the issue/triage layer that maps the open problems.

- **[Michael R. Douglas](https://github.com/mrdouglasny)** — project lead.
- **Jack McCarthy ([@Deicyde](https://github.com/Deicyde))** — the axiom-discharge issue tracker ([#77](https://github.com/mrdouglasny/jacobian-challenge/issues/77)) and the per-axiom tracking issues that structure the project's open-problem surface.
- **Rado Kirov ([@rkirov](https://github.com/rkirov))** and **[@tangentstorm](https://github.com/tangentstorm)** — vendored Lean proofs (see [Vendored sources](#vendored-sources--attribution)).

> GitHub's *Contributors* graph counts commits only; issue, review, and vendored-code contributions are credited here.

## Further reading

- [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) — canonical, kernel-verified axiom audit (per-axiom file:line, ratings, discharged table).
- [`docs/status-2026-06-06.md`](docs/status-2026-06-06.md) — current verified status snapshot (build, exact counts, open workstreams).
- [`docs/axiom-report.txt`](docs/axiom-report.txt) — golden `#print axioms` trace of every headline (regenerate via [`scripts/axiom_report.lean`](scripts/axiom_report.lean)); confirms no `sorryAx` under any closed declaration.
- [`docs/challenge-annotated.md`](docs/challenge-annotated.md) — F/T classification of Buzzard's 24 `sorry`s.
- [`docs/dependency-trace.md`](docs/dependency-trace.md) — transitive axiom audit per foundation definition.
- [`docs/planning/`](docs/planning/) — per-axiom discharge plans (Gemini-vetted) + the dependency DAG.
- [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md) — what we took from the sibling repos, considered, and rejected.
