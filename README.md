# Jacobians of Compact Riemann Surfaces

A Lean 4 formalization addressing [Kevin Buzzard's **Jacobian Challenge**](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9) (v0.4, May 2026). All **24 `sorry`s** in Buzzard's `Challenge.lean` are closed with real `def`s and `instance`s; the remaining classical mathematics is captured as a **classified, audited axiom layer**; and a set of **real theorems** is proved on top — including the two anti-degeneracy properties Buzzard designed the challenge around (correct genus, injective Abel–Jacobi) plus the Albanese universal property.

> **What this is, honestly.** A scaffold that *closes Buzzard's interface* and proves real theorems on it, with the deep classical inputs isolated as a classified, discharge-planned axiom layer — **not** a from-first-principles proof of Jacobian theory. The axioms are LLM-authored and **have not had independent human-mathematician review**. See [Caveats](#caveats--read-before-relying-on-this) before relying on any result.

## At a glance

| | |
|---|---|
| **Build** | `lake build Jacobians` green; Kirov Dolbeault port compiled as a `require` dependency |
| **Toolchain** | Lean `v4.30.0`; Mathlib pinned in `lake-manifest.json` (rev `c5ea003`) |
| **Buzzard API** | 24/24 `sorry`s closed as real `def`s / `instance`s |
| **Axioms** | 22 active, of which **6 are challenge-critical** (kernel-verified per-headline: [`docs/CHALLENGE_AXIOM_CLOSURE.md`](docs/CHALLENGE_AXIOM_CLOSURE.md); PR #183 (@daouid, 2026-06-11) discharged the **7-axiom odd-atlas infinity-chart cluster** with the correct analytic branch (`y = z·x^(g+1)`, the #178-review route) — `Hyperelliptic.instChartedSpace`/`instIsManifold` are now standard-3, net −7, none challenge-critical; the D1 merge 2026-06-10 fused `AX_AnalyticCycleBasis`+`AX_RBR1`+`AX_RBR2` into the single `AX_PeriodCycleBasis` and dropped `intersectionForm` from every headline closure; PR #179 (@Deicyde, 2026-06-11) discharged `AX_ofCurve_contMDiff` — Abel–Jacobi smoothness is now a **theorem**, standard-3 + `AX_PeriodCycleBasis` only, with the DT-flagged HI/lattice-completeness condition transferred into `AX_PeriodCycleBasis`'s discharge obligation); RR + Serre and the period cluster are **theorems** over the Layer-3 scaffold; the trace cluster (`pushforwardOneForm` + its id/comp laws) is **discharged** via the port's fibre-sum trace (`Bridge/KirovDolbeaultTrace.lean`, #26/#27/#28); Phase D discharged `H1coh`+3 instances and `cohomologyLES` to the real Čech cohomology + skyscraper LES of the vendored Kirov Dolbeault port — Riemann-Roch now rests on the single axiom `h1coh_zero_finrank`; `PlaneCurve` now carries a fully proved manifold structure (`instChartedSpace` #117 + `instIsManifold` #52). All classified + kernel-verified — [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) |
| **`sorry`s** | 0 in the core; 11 in out-of-scope extensions; 3 in an optional adelic `H¹` construction (kept around, not on the critical path) |
| **Provenance** | ~50k LOC our own Lean (135 files) + Kirov Dolbeault port (~86k LOC, compiled via `require`) + vendored Kirov/Wallace modules (Apache 2.0 / MIT) |

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

## How the work divides — three separable parts

The repository is **three clearly separable parts**, and only the first is "the challenge". A map before the details:

| Part | What it is | Required for the challenge? | `sorry` status |
|------|-----------|:---:|---|
| **1. Buzzard's challenge** — `Challenge.lean` + the construction | the interface Buzzard posed | — *(it **is** the challenge)* | **core `sorry`-free**; rests on the 22-axiom layer |
| **2. RR/Serre/sheaf subchallenge** — `RiemannSurface/Cohomology/` | discharge the deep axioms via the Layer-3 tower | **no** — the challenge *rests on* the axioms; this *proves* them | RR/Serre and the period cluster now **theorems** (Layer-3 tower); + an **optional** adelic `H¹` construction kept around (3 `sorry`s) |
| **3. Hyperelliptic extension projects** — `Extensions/`, `ProjectiveCurve/Hyperelliptic/` | exercise the formalization on real curves | **no** — real-example vetting | **even completed** (PR #96); **odd** = 6-`sorry` stretch |

**Part 1 — Buzzard's challenge (the interface). *Closed.*** All 24 `sorry`s in `Challenge.lean` are filled with real `def`s/`instance`s, and the anti-degeneracy headlines (correct genus, injective Abel–Jacobi, Albanese universal property) are proved — **resting on** the axiom layer. The core is `sorry`-free; every headline is `#print axioms`-checked to depend only on the axioms it names plus the three Lean-core axioms, never `sorryAx`. In Buzzard's own terms ("sorry-free ⇒ done"), Part 1 is **met modulo a declared, audited axiom layer**.

**Part 2 — the RR/Serre/sheaf subchallenge: prove the axioms.** The axiom layer (22 axioms) is itself the open research program, and discharging it is *not* required for Part 1. It is the deeper goal of reducing the whole challenge to **a single classical spine: Riemann–Roch + Serre duality** (the sheaf-cohomology anchor under `RiemannSurface/Cohomology/`). The reduction target is *"Buzzard challenge = axiom table + RR/Serre"*: once RR/Serre are in hand, the rest of the table follows. **RR and Serre are now themselves theorems, not axioms.** The **Layer-3 tower** ([`Jacobians/Layer3/`](Jacobians/Layer3/), [#126](https://github.com/mrdouglasny/jacobian-challenge/issues/126) / [#131](https://github.com/mrdouglasny/jacobian-challenge/issues/131)) proves both — `AX_RiemannRoch` and `AX_SerreDuality` are now `theorem`s — over a small cohomology scaffold: the 6-term sheaf-cohomology long exact sequence `0 → L(D) → L(D+P) → ℂ_P → H¹(D) → H¹(D+P) → 0`, finiteness of `H¹`, `h¹(𝒪) = g`, and the Serre-duality isomorphism `H¹(D) ≃ L(K−D)*` (7 axioms in the original scaffold), via an axiom-free Euler-characteristic engine. So the trust floor descended one notch — from *"RR + Serre asserted"* to *"the standard cohomology LES + `h¹(𝒪) = g` + Serre-duality iso asserted,"* each a step closer to Mathlib. **Phase D** then discharged 5 of those 7 scaffold axioms — `H1coh` + 3 instances + `cohomologyLES` — to real constructions via the Kirov Dolbeault port (the Čech `H¹` model and the skyscraper LES); the remaining 2 (`h1coh_zero_finrank` and `serreDuality_equiv`) are the current research frontier. **How the same research debt appears from two routes** — the 🔴 research-grade debt appears in *two* places in the axiom table below that are really **the same content seen from two routes**:

- the **Period / Hodge / homology axioms** (originally 7; now **4 remain** as axioms: `intersectionForm` + its alternating/perfect laws + `AX_PeriodCycleBasis` (the D1 merge of `AX_AnalyticCycleBasis` with the RBR primitives) — *postulated directly*, the Griffiths–Harris / Hodge route) — `AX_RiemannBilinear`, `AX_PeriodLattice`, and `instPeriodLatticeDiscrete` are now **theorems** (Phase C, over the R1/R2 fields of the cycle-basis bundle), and `AX_H1FreeRank2g` is a **theorem** (derived from the cycle basis); and
- the **axiom-based anchor `sorry`s** — faithful, cross-model-vetted *statements* of Riemann–Roch (§16) and Serre duality (§17) in `Cohomology/RiemannRochAPI` / `Cohomology/SerreDualityAPI`, originally **proof-deferred** (the Forster cohomological route) and **now fully closed**: `#113` proved the `riemannRoch` identity and `h⁰(K) = g`; the `L(D)`-finiteness fact they rest on — formerly the axiom `riemannRochSpace_finiteDimensional` — is **itself now discharged**, proved elementarily ([#116](https://github.com/mrdouglasny/jacobian-challenge/issues/116)); **Serre vanishing is proved** ([#120](https://github.com/mrdouglasny/jacobian-challenge/issues/120)) — `deg(div f) = 0` (the degree theorem, axiom-free over the standard three) closes `h0_of_deg_gt`/`h1_eq_zero_of_deg_gt`; and the last two corollaries `riemannRoch_consistent_with_AX` and `h0_point_eq_one_of_genus_pos` (the latter axiom-free) are now closed too. Separately, an **optional** adelic route (`Cohomology/RiemannRochAnchor`, Weil repartitions, **3** `sorry`s) builds a concrete `H¹` (`adeleH1`) — a candidate *deeper* discharge of the Layer-3 cohomology axioms — that we keep around but do **not** need for RR/Serre (which are theorems via the tower).

These routes are **not independent mathematical content**, but their Lean status is now different. The historical Forster route (Forster, *Lectures on Riemann Surfaces*, GTM 81, §§14–21 — see [`refs/`](refs/)) explains why a completed cohomological build would also retire the remaining period/Hodge/homology axioms downstream: Serre §17.10 gives `dim H⁰(Ω¹) = g` (an alternative proof that `AX_PeriodLattice` is already a theorem via Phase C's matrix engine), Abel §20 + harmonic-period nondegeneracy §19 give the lattice, and `H₁ ≅ ℤ^{2g}` falls out as a §21.5 byproduct (⇒ the cycle-basis content of `AX_PeriodCycleBasis`, still an axiom). The `L(D)`-finiteness half (which feeds `H¹` finiteness via Serre) is **now proved elementarily** — `riemannRochSpace_finiteDimensional`, the `ℓ(D) ≤ 1 + deg D⁺` upper bound, **Montel-free** ([#116](https://github.com/mrdouglasny/jacobian-challenge/issues/116)) — while the separate adelic route remains a candidate deeper construction of `H¹`, not the active RR/Serre path.

So the period cluster and the cohomology route are **two views of the same roof**, not two unrelated proof obligations. Route comparison: [`refs/JACOBIAN_ROUTE_COMPARISON.md`](refs/JACOBIAN_ROUTE_COMPARISON.md).

**The current method — the Layer-3 tower.** Part 2 is being executed by a *tower of reductions* ([`Jacobians/Layer3/`](Jacobians/Layer3/)): rather than continue through the separate adelic construction, the active route **axiomatizes a thin layer of standard cohomology / differential-geometry infrastructure and proves the axiom-table entries as theorems over it**, pushing the trust floor toward Mathlib one stratum at a time. Three strata so far — **Phase B** put RR + Serre over the 7-axiom cohomology scaffold (`H¹` + the divisor-addition LES + `h¹(𝒪)=g` + Serre iso; cross-model-vetted satisfiable/faithful, [#126](https://github.com/mrdouglasny/jacobian-challenge/issues/126)/[#131](https://github.com/mrdouglasny/jacobian-challenge/issues/131)); **Phase C** (landed) **discharged the period/Hodge cluster** — `AX_RiemannBilinear`, `AX_PeriodLattice`, `instPeriodLatticeDiscrete` are now `theorem`s over the Riemann bilinear relations through an axiom-free period-lattice engine (net −1 axiom; since the **D1 merge**, 2026-06-10, the two relations are the arc-level `R1`/`R2` fields of the single `AX_PeriodCycleBasis` bundle — formerly the separate `AX_RBR1`/`AX_RBR2` + `AX_AnalyticCycleBasis`, net −2 more); and **Phase D** (landed, #143/#144) **discharged 5 of the 7 Layer-3 cohomology scaffold axioms** — `H1coh` + 3 instances + `cohomologyLES` — by integrating the Kirov Dolbeault port as a `require` dependency and wiring its real Čech `H¹` model and skyscraper LES directly into the Layer-3 scaffold, reducing the trust floor from "cohomology LES asserted" to "Forster §14–§16 Čech machinery proved." The remaining 2 Layer-3 cohomology axioms (`h1coh_zero_finrank` and `serreDuality_equiv`) are the current frontier. This is **still Part 2** — *discharge the axiom layer* — not a fourth part: the tower is the *how*, complementary to (and now the primary execution of) the Forster/cohomology perspective above.

**Part 3 — the hyperelliptic extension projects: vetting on real curves.** Orthogonal to Parts 1–2: concrete curve families that exercise the whole formalization end-to-end (cocycle 1-forms → finite-dim bridge → genus → Jacobian → functoriality) on a non-trivial example, forcing the API to *compute correctly*, not merely type-check. They neither close the challenge nor sit on any axiom's critical path. Two parities, structured symmetrically (core atlas in `ProjectiveCurve/Hyperelliptic/{Even,Odd}Atlas/` + an extension file in `Extensions/Hyperelliptic{Even,Odd}.lean`):

- the **even-degree** track is **completed** — `genus_HyperellipticEven_eq` is a real proved theorem (Liouville L2/L3 discharged, PR #96), the strongest evidence that genus computes correctly on a whole family;
- the **odd-degree** track (`Extensions/HyperellipticOdd.lean`, 6 `sorry`s) is a deliberate parallel **stretch project** mirroring the even one decl-for-decl — its lower genus bound is proved, the upper bound and warm-ups remain `sorry`. It is **not required for Buzzard's challenge**; it exists to mirror the completed even case on the single-∞ parity and to host the hyperelliptic-involution / Weierstrass-point material.

## What it assumes — the axiom layer

Every axiom is a staging point with a citation and a discharge plan, classified in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md). They group into eight topics (counts sum to the **22** kernel-verified axioms; topic boundaries are soft — a few axioms could reasonably sit in an adjacent row); difficulty is the *discharge* difficulty (🟢 mechanical / available in Mathlib, 🟡 substantial but standard, 🔴 research-grade — a genuine textbook theorem with no existing Lean proof):

| Topic | Count | Difficulty |
|-------|:-----:|:----------:|
| Period / Hodge / homology core (intersection form + laws — D2: kept, no longer in any headline closure; `AX_PeriodCycleBasis` = H₁ cycle basis + arc-level R1/R2, the D1 merge; **Riemann bilinear + period lattice now theorems**, Phase C) | 4 | 🔴🟡 |
| Abel–Jacobi (`AX_AbelTheorem`; `ofCurve_inj` and `ofCurve` smoothness — `AX_ofCurve_contMDiff`, PR #179 — are now theorems) | 1 | 🔴 |
| Sheaf cohomology stubs / Plücker / uniformization (`LineBundle`/`canonicalDivisor`/`ofDivisor` type stubs; `AX_PluckerFormula`; `AX_genus_eq_zero_iff_homeo`; **RR + Serre now theorems**; `H0` = `riemannRochSpace`, `H1` = `Layer3.H1coh`) | 5 | 🔴 |
| Layer-3 scaffold: cohomology (`h1coh_zero_finrank` + `serreDuality_equiv`, 2 — **Phase D discharged** `H1coh`+3 instances+`cohomologyLES` to the Kirov Čech model; [#126](https://github.com/mrdouglasny/jacobian-challenge/issues/126)/[#131](https://github.com/mrdouglasny/jacobian-challenge/issues/131)/#143/#144). The 2 period primitives `RBR1`/`RBR2` were **merged into `AX_PeriodCycleBasis`** (D1, 2026-06-10) as its arc-level R1/R2 fields | 2 | 🔴 |
| Functoriality (pushforward / pullback naturality + lattice preservation; **the trace cluster — `pushforwardOneForm` + id/comp — discharged 2026-06-10** via the Kirov-Dolbeault `traceFormTotal` bridge, #26/#27/#28) | 4 | 🟡 |
| Torus / Albanese universal property | 3 | 🟡 |
| Concrete curves (elliptic `H₁`-symplectic witness; hyperelliptic genus formula — the **7-axiom odd-atlas ∞-chart cluster discharged PR #183** (2026-06-11, correct analytic branch; `Hyperelliptic.instChartedSpace`/`instIsManifold` now standard-3); plane-curve affine-connected — `instIsManifold` **discharged #52**, the plane-curve manifold structure is now fully proved; **ℙ¹ is axiom-free**) | 3 | 🟢🟡 |
| Liouville hierarchy L2 / L3 (the canonical-differentials theorem) | 0 | ✅ **discharged** (PR #96) |
| **Total** | **22** | |

**Anchor APIs for the deepest axioms.** For the 🔴 research-grade cluster, the real risk is *formulation, not proof* — a degenerate or vacuous statement compiles just as happily as a faithful one. So before attempting those proofs we pin **faithful, cross-model-vetted statements first** (real `def`s + `sorry`-ed theorems, checked against the textbook form), and do the hard proofs last against a known-correct surface. Landed so far: `riemannRochSpace` (the real `L(D)`, a ℂ-submodule of the **meromorphic germ quotient** `MeroField = MeroFunctions ⧸ GermZero` — corrected from an earlier raw-`X→ℂ` version that was *degenerate*: it admitted germ-zero "spike" functions, so was infinite-dimensional with `finrank ≡ 0`; the compiled `germZero_ne_bot` witnesses that bug; this de-opaqued `H0`), and three statement APIs gated by the `SheafCohomologySpec` faithfulness suite. **`PluckerAPI` is complete** — its statements are fully proved (the low-degree corollaries reduce by arithmetic to the `AX_PluckerFormula` axiom), so the remaining Plücker work is the formula axiom and the plane-curve atlas, not the API. **`h⁰(0) = 1` is now proved axiom-free** over the corrected space — `L(0)` = holomorphic functions = constants (via the normal-form honest representative + Liouville → `LinearEquiv (ℂ ≃ L(0))` → `finrank = 1`), the concrete confirmation that the faithfulness fix gives the *right* dimension (it was `finrank ≡ 0` over the old degenerate space). **`#113` landed the core:** `riemannRoch` (the RR identity) and `h⁰(K) = g` are now **proved** from the `AX_RiemannRoch`/`AX_SerreDuality` anchor (themselves now `theorem`s over the Layer-3 cohomology scaffold, [#131](https://github.com/mrdouglasny/jacobian-challenge/issues/131)) + the now-discharged `riemannRochSpace_finiteDimensional` finiteness theorem (was an axiom; proved elementarily, #116). `RiemannRochAPI` and `SerreDualityAPI` now carry **0** deferred `sorry`s — fully closed. `canonicalDivisor_deg` = `deg K = 2g − 2` is **proved** from `riemannRoch`; **Serre vanishing** `h0_of_deg_gt` + `h1_eq_zero_of_deg_gt` is **proved** via the degree theorem `deg_divisor_eq_zero` (`deg(div f) = 0`, over only the three Lean-core axioms, [#120](https://github.com/mrdouglasny/jacobian-challenge/issues/120)); and the last two corollaries are closed — `riemannRoch_consistent_with_AX` (subsumed by `riemannRoch`) and `h0_point_eq_one_of_genus_pos` (**axiom-free**: a single-simple-pole function would be a degree-1 cover ⇒ `genus 0`, contradiction). The only remaining anchor `sorry`s are the **3** in the **optional** adelic Weil-repartition route (`Cohomology/RiemannRochAnchor`: `riemannRoch_anchor`, `adeleH1_finiteDim`, `serre_anchor`) — a concrete `H¹` construction kept around as a candidate deeper discharge of the Layer-3 cohomology axioms, not on the critical path. Methodology: [`docs/planning/DEEP_AXIOM_ANCHORS_PLAN.md`](docs/planning/DEEP_AXIOM_ANCHORS_PLAN.md). Every axiom additionally has a per-axiom discharge plan under [`docs/planning/`](docs/planning/) (one file each, Gemini-vetted).

## Caveats — read before relying on this

- **The axioms are LLM-authored and not human-reviewed.** Each was written or curated in-session and cross-vetted by a second model (typically Gemini deep-think + Codex), but none has had independent human-mathematician review. **If you are evaluating this work, read [`Jacobians/Axioms/`](Jacobians/Axioms/) and [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) first.**
- **This is a reduction, not a closed proof.** A theorem whose only non-Lean-proven content is a textbook-classical axiom should be read as *"reduced to that classical input"*, not *"proved from Mathlib"*.
- **Zero human-written Lean.** The Lean was written by Claude (Opus) with Codex rescue passes and Gemini axiom audits, directed by a mathematician on scope, the axiom-vs-proof boundary, and review of every landing.
- **`sorry`s, in two honest categories** (the *core* — challenge API, Jacobian construction, curve witnesses, S1–S7 1-form framework — is `sorry`-free):
  - **11 gap-layer** — out-of-scope extension/bridge files (`Extensions/HyperellipticOdd.lean` 6 — the odd-degree extension project, deliberately mirroring the *completed* `Extensions/HyperellipticEven.lean`; `Extensions/AbelJacobi.lean` 4; `Hyperelliptic/AntiInvariance.lean` 1).
  - **3 optional-adelic** — the axiom-based RR/Serre anchors (`Cohomology/RiemannRochAPI`, `Cohomology/SerreDualityAPI`) are **fully closed** (`PluckerAPI` proved; `h⁰(0)=1` axiom-free; `#113` proved `riemannRoch`/`h⁰(K)=g`; `#120` proved Serre vanishing; and `riemannRoch_consistent_with_AX` + `h0_point_eq_one_of_genus_pos` closed here). The remaining **3** are an **optional** adelic Weil-repartition construction (`Cohomology/RiemannRochAnchor`: `riemannRoch_anchor`, `adeleH1_finiteDim`, `serre_anchor`) — a concrete `H¹` kept around as a candidate deeper discharge, **not** on the critical path.

## How it's built

The construction takes the **period-lattice route** — `Jac X = (HolomorphicOneForm X)* / H₁` — rather than the symmetric product `Xᵍ/Sᵍ` (whose coincident-point local analysis Buzzard flags as hard). It is basis-free at the type level.

- **`AbelianVariety/`** — `ComplexTorus V L := V ⧸ L` for a ℤ-lattice `L`, supplying all 7 typeclass instances Buzzard requires on `Jacobian X` directly from a translation atlas + lattice discreteness. **Axiom-free.** This is the concrete answer to Buzzard's "quotient a manifold by a discrete group" gap for the shape the Jacobian needs.
- **`RiemannSurface/` + `Jacobian/`** — the abstract track: from Buzzard's typeclasses → holomorphic 1-forms → period lattice → `Jacobian X`. The Abel–Jacobi map is a real `∫` (multi-chart line integral over an analytic cycle basis), addressing Buzzard's "integrating differentials around loops" gap from underneath via the Kirov bridge.
- **`ProjectiveCurve/`** — the concrete track: real curve `def`s satisfying Buzzard's typeclasses by construction — `ProjectiveLine`, `Elliptic`, `HyperellipticOdd`/`HyperellipticEven`, and `PlaneCurve` (atlas complete via Euler + IFT, #117; `instIsManifold` still an axiom).
- **`Extensions/`** — test theorems exercising the formalization end-to-end (the regression catch where `Module.finrank` silently returns 0).

## Repository map

| Path | Contents |
|------|----------|
| [`Jacobians/Challenge.lean`](Jacobians/Challenge.lean) | Buzzard's v0.4 statements verbatim, all 24 `sorry`s closed downstream |
| [`challenge_spec_v0.4.lean`](challenge_spec_v0.4.lean) | Buzzard's v0.4 spec pinned byte-identical (gist rev `cdc146c3`; uncompiled reference) |
| [`Jacobians/ChallengeConformance.lean`](Jacobians/ChallengeConformance.lean) | machine-check: each v0.4 signature restated as an `example`, discharged by our decls |
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

Lean `v4.30.0`; Mathlib at the revision pinned in `lake-manifest.json`. CI runs `lake build` end-to-end, a `ChallengeConformance.lean` machine-check (`lake env lean ChallengeConformance.lean`, exit 0) verifying every v0.4 signature exactly, a golden `#print axioms` check, and a guard keeping the core `sorry`-free.

## Vendored sources & attribution

We build on real Lean from two sibling Jacobian-Challenge attempts, each vendored under its **upstream** license with per-file attribution headers, the upstream `LICENSE`, and a `PROVENANCE.md`. Full adoption record: [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md).

- **[rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude)** (Apache 2.0) — Montel finite-dimensionality of holomorphic 1-forms, line integrals, the ℤ-lattice/complex-torus quotient infrastructure. Used to retire `AX_FiniteDimOneForms` and `pullbackOneForm` and to back the Abel–Jacobi integral. Ported under `Jacobians/Vendor/Kirov/`. **A second, larger snapshot** of the same repo (commit `4437c2b`, 2026-06-09) is preserved as a standalone forward-ported build under [`vendor/kirov-dolbeault-port/`](vendor/kirov-dolbeault-port/) — this snapshot contains the first sorry-free Lean proof of the 1-form residue theorem `∑ Res = 0` (`residueTheorem_unconditional`, `#print axioms`-clean at standard-3) together with the Čech `H¹` finiteness (Forster §14), the skyscraper χ-step (§16), and the §17.6 easy half of Serre duality. It compiles under our exact toolchain (Mathlib `c5ea003`) and is **integrated into the main build** as a Lake `require` dependency (`vendor/kirov-dolbeault-port/`, S2 strategy) — Phase D wired its Čech `H¹` model and skyscraper LES into our Layer-3 scaffold, retiring 5 axioms. See [`docs/planning/PHASE_D_BRIDGE_PLAN.md`](docs/planning/PHASE_D_BRIDGE_PLAN.md).
- **[tangentstorm/JacobianChallenge](https://github.com/tangentstorm/JacobianChallenge)** (MIT) — self-contained, sorry-free analytic modules (holomorphic maps, meromorphic order, branched covers). Ported under `Jacobians/Vendor/Wallace/`; used in the genus-obstruction proof behind Abel injectivity.

The in-build vendored subtrees (`Jacobians/Vendor/Kirov/` and `Jacobians/Vendor/Wallace/`) are **axiom-free**; their headline theorems `#print axioms`-verify to the three standard Lean axioms only.

## Contributors & acknowledgments

An agent-assisted community project. Contributions span code, vendored proofs, and the issue/triage layer that maps the open problems.

- **[Michael R. Douglas](https://github.com/mrdouglasny)** — project lead.
- **Jack McCarthy ([@Deicyde](https://github.com/Deicyde))** — the axiom-discharge issue tracker ([#77](https://github.com/mrdouglasny/jacobian-challenge/issues/77)) and the per-axiom tracking issues that structure the project's open-problem surface.
- **Rado Kirov ([@rkirov](https://github.com/rkirov))** and **[@tangentstorm](https://github.com/tangentstorm)** — vendored Lean proofs (see [Vendored sources](#vendored-sources--attribution)).

> GitHub's *Contributors* graph counts commits only; issue, review, and vendored-code contributions are credited here.

## Further reading

- [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) — canonical, kernel-verified axiom audit (per-axiom file:line, ratings, discharged table).
- [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) (already listed above) is the authoritative live record; for a point-in-time snapshot see [`docs/status-2026-06-06.md`](docs/status-2026-06-06.md) (pre-Phase-D baseline) or the current `AXIOM_AUDIT.md` header.
- [`docs/axiom-report.txt`](docs/axiom-report.txt) — golden `#print axioms` trace of every headline (regenerate via [`scripts/axiom_report.lean`](scripts/axiom_report.lean)); confirms no `sorryAx` under any closed declaration.
- [`docs/challenge-annotated.md`](docs/challenge-annotated.md) — F/T classification of Buzzard's 24 `sorry`s.
- [`docs/dependency-trace.md`](docs/dependency-trace.md) — transitive axiom audit per foundation definition.
- [`docs/planning/`](docs/planning/) — per-axiom discharge plans (Gemini-vetted) + the dependency DAG.
- [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md) — what we took from the sibling repos, considered, and rejected.
