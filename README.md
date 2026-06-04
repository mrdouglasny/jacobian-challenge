# Jacobians of Compact Riemann Surfaces

An interface-complete Lean 4 bridge to Kevin Buzzard's [Jacobian Challenge](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9) (v0.2, April 2026): all 24 `sorry`s in `Challenge.lean` discharged as real `def`s and `instance`s, with the remaining mathematical content organized as classified axioms (textbook-citable classical theorems, function-existence axioms with construction plans, and a layered Liouville-hierarchy axiom system used by the headline genus theorem). Not a from-first-principles proof of Jacobian theory; a scaffold that closes Buzzard's exposed API and enumerates the work below it. Concrete headline theorems landed: `genus ProjectiveLine = 0`, `genus (Elliptic ω₁ ω₂) = 1`, and `genus (HyperellipticEvenProj H) = H.f.natDegree / 2 - 1`.

> **Primarily our own formalization, with contributions from borrowed proofs.** We vendor and build on real Lean from two sibling Jacobian-Challenge attempts — each under its upstream license, with per-file attribution headers and a vendored `LICENSE` + `PROVENANCE.md` (summary table at the [bottom](#vendored-sources--attribution); full record in [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md)): **[rkirov/jacobian-claude](https://github.com/rkirov/jacobian-claude)** (Apache 2.0, ~5,800 LOC — Montel finite-dimensionality of holomorphic 1-forms, line integrals, ℤ-lattice/complex-torus quotient) and **[tangentstorm/JacobianChallenge](https://github.com/tangentstorm/JacobianChallenge)** (MIT, ~2,900 LOC — holomorphic maps between Riemann surfaces, meromorphic order, branched covers). The **bulk of the repo is our own work — ~15,900 LOC across 73 Lean files** (plus ~11,700 LOC of design/plan docs): closing Buzzard's 24-`sorry` API via a period-lattice Jacobian construction; concrete curve models and the headline genus theorems (`ℙ¹`, elliptic, hyperelliptic); the S1–S7 hyperelliptic 1-form framework and Liouville hierarchy; the `IsJacobian` universal property; and the vetted-axiom audit/discharge methodology.

## The challenge

Buzzard ships a single Lean file `Challenge.lean` with **24 `sorry`s**, defining an API for the Jacobian of a compact Riemann surface, the Abel–Jacobi map, and pushforward / pullback functoriality along holomorphic maps. The design is adversarial: the API cannot be satisfied by any "hack" definition (e.g. `Jacobian := 0`) because `genus_eq_zero_iff_homeo` forces `genus` to be correct and `ofCurve_inj` forces Abel–Jacobi to be genuinely injective in positive genus. All underlying mathematics is classical (Abel 1829, Jacobi 1851); the challenge is to formalize it on top of current Mathlib (extending Mathlib would be a bonus, not a requirement).

**Proving targets validates the definitions.** The kernel checks *proofs*, never that a `def` *means* what it should — so a degenerate definition can compile. Buzzard's design defends against this by making any candidate `genus`/`Jacobian`/`ofCurve` clear independent obligations (`genus_eq_zero_iff_homeo`, `ofCurve_inj`) that a hack definition would fail. We push the idea further by adding **our own additional target** — the Albanese **universal property** (`Jacobians.IsJacobian`, [below](#how-this-repo-addresses-it)) — so the construction must satisfy *more* independent theorems, pinning it harder against degeneracy. The more genuine targets a definition is forced to prove, the more its meaning is validated.

## How this repo addresses it

**Interface closed.** All 24 `sorry`s in `Challenge.lean` discharge as real `def`s and real `instance`s — no axiom stub at the Buzzard-API level. Functoriality identities (identity + composition for both `pullback` and `pushforward`) are derived **theorems**, not axioms.

**Categorical pin (beyond the API).** Buzzard's API characterizes the Jacobian *operationally* (functoriality + degree + Abel injectivity); it never states the Albanese **universal property** that pins `(Jac X, aj)` up to unique isomorphism. We add it as a compiling, cross-model-vetted statement — `Jacobians.IsJacobian` in [`Jacobians/UniversalProperty.lean`](Jacobians/UniversalProperty.lean): `aj : X → J` to a complex torus, universal among pointed holomorphic maps to complex tori. Vetted by Gemini + Codex (→ minimal hypotheses `AddGroup`, `T2Space`); elaborates against v4.30. Proving Buzzard's concrete `Jacobian`/`ofCurve` *satisfy* it (categoricity) is the open next target.

**Architecture.** Period-lattice construction, basis-free at the type level:

- **Part A — `AbelianVariety/`**: `ComplexTorus V L := V ⧸ L` for `L : Submodule ℤ V` with `[IsZLattice ℝ L]`. Supplies all 7 typeclass instances Buzzard requires on `Jacobian X` (`AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace V`, `IsManifold`, `LieAddGroup`), plus the auxiliary `IsTopologicalAddGroup` consumed by `LieAddGroup`. Axiom-free.
- **Track 1 — `RiemannSurface/` + `Jacobian/`**: abstract `X` from Buzzard's typeclasses → period lattice → `Jacobian X := ComplexTorus (Fin (genus X) → ℂ) (periodLatticeInBasis X x₀ (Module.finBasis ℂ (HolomorphicOneForm X)))`.
- **Track 2 — `ProjectiveCurve/`**: concrete projective curves as real `def`s satisfying Buzzard's typeclasses by construction — `ProjectiveLine`, `Elliptic`, `HyperellipticOdd` / `HyperellipticEven` (two-chart pushout), with `PlaneCurve` axiom-stubbed pending three-chart atlas.

**Concrete witnesses.** `ProjectiveLine` (genus 0) and `Elliptic ω₁ ω₂` (genus 1) are fully populated — real types, real `AnalyticCycleBasis`, `genus ProjectiveLine = 0` and `genus (Elliptic ω₁ ω₂ h) = 1` are **derived theorems depending only on Lean's core axioms** (no project axioms). `genus ℙ¹ = 0` is proved directly via a chart-cocycle + Liouville argument showing `HolomorphicOneForm ProjectiveLine` is a subsingleton (`Line/OneForm.lean`) — *not* through the uniformization axiom; `genus (Elliptic …) = 1` via intrinsic Liouville on `ellipticDz`. Both parities of hyperelliptic curves are real types; **`genus (HyperellipticEvenProj H) = H.f.natDegree / 2 - 1` is a derived theorem** via the S1–S7 1-form framework + the Liouville hierarchy axioms (see below). The cross-summand cocycle is now a real theorem (task #21, 2026-06-01) — the two unsound axioms it used to rest on are retired — so the only remaining inputs are the true-but-unproven Liouville L2/L3 axioms (`AXIOM_AUDIT.md` Class 2d). Unified `Hyperelliptic H` is an axiom type pinned by homeomorphism (`≃ₜ`) axioms to the real parity cases.

**Test theorems beyond the challenge API** ([`Jacobians/Extensions/`](Jacobians/Extensions/)). A ladder of concrete theorems that exercise the formalization end-to-end and catch the regression where `Module.finrank` silently returns `0` (a real failure mode if the cocycle definition or the Kirov-Montel finite-dim bridge is wired wrong):

```
-- Hyperelliptic.lean (odd-degree)
genus (HyperellipticOdd H h) = (H.f.natDegree - 1) / 2          -- headline test
hyperellipticDxOverY        : HolomorphicOneForm (HyperellipticOdd H h)
hyperellipticBasisDifferential k (k < g) : HolomorphicOneForm _    -- the canonical basis
... linearIndependent                                              -- → lower bound on genus
hyperellipticInvolution      : HyperellipticOdd H h → HyperellipticOdd H h
... involutive, ContMDiff, pullback acts as -id, |Fix| = deg f + 1

-- HyperellipticEven.lean (even-degree twins)
genus (HyperellipticEvenProj H) = H.f.natDegree / 2 - 1            -- even headline
hyperellipticEvenDxOverY, ...BasisDifferential, ...linearIndependent

-- AbelJacobi.lean (Jacobian / period-lattice side)
periodLattice_rank_HyperellipticOdd_eq        : Z-rank = 2g
abelJacobi_hyperellipticInvolution             : A(σ P) = -A(P) at a Weierstrass basepoint
abelJacobi_fiber_sum_eq_zero                   : A(P₁) + A(P₂) = 0 for the σ-pair over x₀
riemannBilinear_hyperellipticOdd               : period matrix in SiegelUpperHalfSpace
```

The HyperellipticOdd extensions are still mostly `:= by sorry` with proof sketches + classical references inline (mirror them from the even side, now that the cross-summand cocycle is a real theorem). **The HyperellipticEven extensions are now sorry-free** — `hyperellipticEvenDxOverY`, `hyperellipticEvenBasisDifferential`, `_linearIndependent`, `hyperellipticEvenGenus_lower_bound`, the headline `genus_HyperellipticEven_eq`, and the deg-4 specialization are all real theorems (modulo the Liouville-hierarchy axiom layer described below). The Abel-Jacobi layer has Riemann-bilinear and the Weierstrass-fixpoint fact as real one-liners; the rest are `sorry`. Forster §17, Miranda Ch. VII, Mumford *Tata I* §III.3 are the textbook references.

**Hyperelliptic 1-form framework (S1–S7 landed).** A reusable cocycle constructor `hyperellipticForm (g : Polynomial ℂ) : HolomorphicOneForm` reducing the genus theorem to ~30 LOC. Lives across four files:

- [`Hyperelliptic/AffineForm.lean`](Jacobians/ProjectiveCurve/Hyperelliptic/AffineForm.lean) — 1140 LOC, real `affineProjXCoeff` / `affineProjYCoeff` with linearity, analyticity on chart targets, and all four affine-affine cocycle equations. Behind two narrow IFT axioms about Mathlib's `ContDiffAt.toOpenPartialHomeomorph` source.
- [`AffineInfinityForm.lean`](Jacobians/ProjectiveCurve/Hyperelliptic/AffineInfinityForm.lean) — sorry-free transfer to the infinity summand via the EA1 `reverseData` definitional equality.
- [`EvenForm.lean`](Jacobians/ProjectiveCurve/Hyperelliptic/EvenForm.lean) — unified coefficient family on the `EvenProj` quotient; same-summand cocycles real. The cross-summand `inl_inr` direction now has a **real proof** `hyperellipticEvenCoeff_cocycle_inl_inr` (~1100 LOC across four sub-cases — projX×projU, projY×projU, projX×projV, projY×projV — each via Möbius-derivative + reverse-polynomial identities) under the low-degree hypothesis `g_aff.natDegree < N/2 - 1`. The `inr_inl` direction is also a real theorem (`hyperellipticEvenCoeff_cocycle_inr_inl`), derived from `inl_inr` by chart-transition symmetry (`GeneralResults/ChartTransition.lean`). **The two cross-summand axioms are retired (task #21, 2026-06-01)**; `hyperellipticForm` is now total-but-axiom-free (zero form above degree `N/2−1`), with its linear-algebra API on `Polynomial.degreeLT ℂ (N/2−1)`.
- [`Form.lean`](Jacobians/ProjectiveCurve/Hyperelliptic/Form.lean) — top-level `hyperellipticForm` constructor + linearity (`_add`, `_smul`, `_zero`, packaged `hyperellipticFormLinearMap`) and the linear-independence chain (`hyperellipticForm_injOn_lowDegree`, `hyperellipticFormLinearMap_injective`, `hyperellipticForm_linearIndependent`) — **all real, sorry-free and axiom-free**.

**Genus upper bound via Liouville hierarchy.** [`Jacobians/Axioms/HyperellipticLiouville.lean`](Jacobians/Axioms/HyperellipticLiouville.lean) introduces a 3-level hierarchy (abstract Liouville on compact connected complex manifolds → polynomial decomposition of holomorphic 1-forms in the projX chart → form-level surjectivity onto `hyperellipticForm H g` for low-degree `g`) and derives `genus_HyperellipticEven_le H : genus (HyperellipticEvenProj H) ≤ H.f.natDegree / 2 - 1` as a real theorem. **Level 1 (`liouville_compact_complex_manifold`, the global maximum-modulus principle on a compact connected Riemann surface) is now a proven theorem, axiom-free** (2026-05-31), via Mathlib's chart-local max-modulus + a clopen connectedness argument; Levels 2–3 remain axiomatized (the function-field decomposition + degree-at-infinity bounds — the classical canonical-differentials theorem, not in Mathlib). A key structural finding (`hyperellipticForm_coeff_projX`) shows L3 reduces to L2 + cocycle propagation; the L2 core (branch-point regularity + degree-at-∞) is the deepest result left, scoped in [`docs/genus-L2-L3-discharge-plan.md`](docs/genus-L2-L3-discharge-plan.md). Combined with the S7 lower bound this gives the headline `genus_HyperellipticEven_eq` as `le_antisymm` of two real proofs. The hierarchy was Gemini-vetted on 2026-04-29 and chosen over a single project-specific axiom so each level can be discharged independently as Mathlib catches up. See the "Axiom hygiene and vetting" section below.

Discharge plan: [`docs/genus-theorem-discharge-plan.md`](docs/genus-theorem-discharge-plan.md) (8 sub-tasks S1–S8). S1–S7 landed as real proofs; S8 upper bound discharged via the Liouville hierarchy above (replacing the original Riemann-Roch route — Riemann-Roch is heavier and was deferred). Progress: **task #21 done** (the two cross-summand cocycle axioms are now real theorems — `genus_HyperellipticEven_eq` is sound); **Liouville L1 + L2-step-4 proven, axiom-free**. Remaining for a *fully axiom-clean* even-genus: Liouville L2/L3 (see [`docs/genus-L2-L3-discharge-plan.md`](docs/genus-L2-L3-discharge-plan.md), ~1–2 months — the canonical-differentials theorem); and mirror the framework into HyperellipticOdd for `genus_HyperellipticOdd_eq`.

**Axioms are classified, not hidden** ([`docs/dependency-trace.md`](docs/dependency-trace.md)):

- **Classical-theorem axioms** (Riemann–Roch, Serre duality, Abel, Riemann bilinear, period-lattice discreteness, branch locus, uniformization): each a textbook citation. The right shape of axiom for a layered formalization. *Finite-dimensionality of holomorphic 1-forms is no longer in this list — see "Cross-pollination" below.*
- **3 data-level function-existence axioms** (`pathIntegralBasepointFunctional`, `loopIntegralToH1`, `pushforwardOneForm`): each has a construction plan in [`docs/construction-plans/`](docs/construction-plans/).
- **Liouville hierarchy, Levels 2–3** (`AX_HyperellipticForm_polynomial_decomposition`, `AX_HyperellipticOneForm_eq_form` in [`Jacobians/Axioms/HyperellipticLiouville.lean`](Jacobians/Axioms/HyperellipticLiouville.lean)): used by `genus_HyperellipticEven_le`. Layered so each level discharges independently — **Level 1 (`liouville_compact_complex_manifold`) is now proven, axiom-free**; L2-step-4 (entire + polynomial growth ⇒ polynomial, [`differentiable_eq_polynomial_of_growth`](Jacobians/GeneralResults/EntireGrowth.lean)) is proven, axiom-free; and L3 is shown to reduce to L2 + cocycle propagation (`hyperellipticForm_coeff_projX`). The remaining L2 core (branch-point regularity + degree-at-∞) is the canonical-differentials theorem — scoped in [`docs/genus-L2-L3-discharge-plan.md`](docs/genus-L2-L3-discharge-plan.md).
- **Cross-summand cocycle for the unified `EvenProj` 1-form framework — retired (task #21, 2026-06-01).** Both directions (`hyperellipticEvenCoeff_cocycle_inl_inr`, `…_inr_inl`) are now real, axiom-free theorems (the `inr_inl` direction via chart-transition symmetry, `GeneralResults/ChartTransition.lean`). These were the only *unsound* axioms in the repo; their retirement makes `genus_HyperellipticEven_eq` sound modulo Liouville L2/L3.
- **Curve-atlas axioms** for unified `Hyperelliptic` and for `PlaneCurve`: proper axiomatizations of classical atlas constructions; discharge is substantial atlas work.

### Per-axiom discharge plans + Gemini 3.1 Pro vetting

A complete per-axiom discharge plan lives in [`docs/planning/`](docs/planning/): one markdown file per axiom (90 total), every plan **vetted by Gemini 3.1 Pro** (`gemini-3.1-pro-preview`, extended thinking, 2026-06-03). Tally: **13 accept / 36 revise / 41 reject**; all 77 flagged plans rewritten in place per the critiques. A second Gemini pass on each route cluster surfaced **15 cross-plan inconsistencies** (Mathlib-decl drift, signature splits, mutual-no-anchor cycles, duplicate effort, stale prereqs), all 15 applied as patches across 60 plans.

- [`docs/planning/ROADMAP.md`](docs/planning/ROADMAP.md) — the index. Summary by route, sections (`mathlib-now`, `provable-from-other-axioms`, `needs-infra`, `genuine-textbook`) ordered by effort, full per-axiom table by source location with Gemini's verdict on every row.
- [`docs/planning/CROSS_DOC_ANALYSIS.md`](docs/planning/CROSS_DOC_ANALYSIS.md) — the dependency DAG over all 90 plans (164 internal edges, 18 leaves, 7 cycles with break strategies, top-15 fulcrum, Mermaid subgraphs, phased build sequence ordered by `(dep-depth, verdict, effort)`).
- [`docs/planning/<axiom-name>.md`](docs/planning/) — 90 recipe files (statement → why-axiomatized → numbered proof recipe with `file:line` citations → files touched → acceptance criteria → escalation triggers), each with a `Gemini critique addressed:` subsection and `Vetting trail.` footer.
- [`docs/planning/_vetting/`](docs/planning/_vetting/) — 90 referee-grade Gemini critiques (one per plan, ~3.5K chars each), four route-cluster cross-plan audits, raw-results JSON.
- [`docs/planning/dependency-graph.json`](docs/planning/dependency-graph.json) — the raw graph artifact (nodes + edges + cycles + leaves + fulcrum scores) for tool consumption.

The recommended Phase 1 starting cluster is the 13 `accept`-verdict plans that sit on validated dep chains: `bridgePath_at_{zero,one}`, `infinityChart_mem_source`, `Hyperelliptic.instCompactSpace`, `Divisor.deg`, etc. The highest-leverage move on the board is `Divisor` itself (unblocks 11 downstream plans for an effort-1 `FreeAbelianGroup X` discharge).

## Cross-pollination from Kirov's Montel theorem

After [Rado Kirov's 3-day Claude Code attempt](https://github.com/rkirov/jacobian-claude) was relicensed to Apache 2.0 (2026-04-25, Lean Zulip `#Autoformalization > Jacobian challenge` msg #61), we adopted the strongest pieces of his work: a **real ~3,400 LOC proof of Montel's theorem** for holomorphic 1-forms (yielding `instance : FiniteDimensional ℂ HolomorphicOneForms X`), a sorry-free **`LineIntegral`** module (path speed via chart-local `fderiv`, line integral linearity, concat, reversal, the `pathSpeed_comp_eq_mfderiv` chain rule), and the sorry-free **`ZLatticeQuotient`** quotient-manifold infrastructure.

**Adoption results (axiom changes):**
- ✅ **`AX_FiniteDimOneForms` retired.** A ℂ-linear bridge `bridgeForm : HolomorphicOneForm X →ₗ[ℂ] Vendor.Kirov.HolomorphicOneForms X` and its injectivity are now **real proofs** (no sorries, no structural axioms in the bridge file), so `FiniteDimensional ℂ (HolomorphicOneForm X)` derives from Kirov's Montel via `Module.Finite.of_injective`. The deep finite-dim content is genuinely Lean-checked, not asserted.
- ✅ **`pullbackOneForm` retired.** `bridgeForm` is upgraded to `bridgeFormEquiv : HolomorphicOneForm X ≃ₗ[ℂ] Vendor.Kirov.HolomorphicOneForms X`, and pullback is transported from Kirov's real `pullbackForm`; the identity and composition laws are now theorems.
- 🚧 **`pathIntegralBasepointFunctional` retirement in flight via `kirovBackedFunctional`** — see the Gap 2 paragraph below for current state. Linearity in the form is real; FTC theorem and `bridgePath` smooth-existence still open.

Layout:

- [`vendor/kirov-jacobian-claude/`](vendor/kirov-jacobian-claude/) — verbatim copy of Kirov's tree at upstream commit `7ce9e2e8` (Apache 2.0). Outside the build root. See [`PROVENANCE.md`](vendor/kirov-jacobian-claude/PROVENANCE.md) and [`HANDOFF.md`](vendor/kirov-jacobian-claude/HANDOFF.md).
- [`Jacobians/Vendor/Kirov/`](Jacobians/Vendor/Kirov/) — six modules ported into our build under namespace `Jacobians.Vendor.Kirov.*` (`Genus`, `Montel.*`, `HolomorphicForms`, `LineIntegral`, `ChartedSpaceOfLocalHomeomorph`, `ZLatticeQuotient`), ~5,600 LOC total, with per-file Apache 2.0 attribution headers; mathematics unchanged. Two of Kirov's `:= sorry` declarations are stated as named `axiom`s (`genus_eq_zero_iff_homeo` for Uniformization; `ambientPhi_ambientPsi_eq` for the degree identity) for handoff.
- [`Jacobians/Bridge/`](Jacobians/Bridge/) — `KirovHolomorphic.lean` (real `bridgeForm` + injectivity, derived `FiniteDimensional` instance), `KirovHolomorphicEquiv.lean` (real inverse/equivalence and pullback transport support), and `KirovLineIntegral.lean` (real `kirovBackedFunctional` + `chartLine` + endpoint lemmas; FTC theorem in flight).

This is precisely the cooperation pattern Kirov suggested in the Zulip thread ("anyone can take my attempt and remix into theirs ... if going for more experimental purity"). The two repos remain independent attempts; we pull in his real proof rather than re-build it.

## Cross-pollination from Wallace's analytic infrastructure

From [Michal Wallace's (tangentstorm) attempt](https://github.com/tangentstorm/JacobianChallenge) (MIT) we vendored six **self-contained, sorry-free, axiom-free** Riemann-surface analytic modules under `Jacobians.Vendor.Wallace.*` (~2,900 LOC): `HolomorphicMap` (holomorphic maps between Riemann surfaces, local k-fold ramification, weighted fiber conservation), `VanishingOrder` (manifold-level meromorphic order + chart-independence), `BranchedCover` (branched-cover data + `branchedDegree`), `AnalyticLocalMapping`, `CotangentBundle`, and `CurveIntegralSubpath`. Selection criterion: transitive import closure Mathlib-only (or within the set) and **decoupled from the placeholder layer** in the rest of his repo. Each headline theorem was verified via `#print axioms` to depend only on `[propext, Classical.choice, Quot.sound]`; def-vetting caught and stripped a vacuous `ramificationIndexStub := 1` before import. Held as a reusable analytic library (meromorphic / branched-cover / genus-0 strands), not yet wired to retire a specific axiom.

- [`vendor/wallace-jacobian-challenge/`](vendor/wallace-jacobian-challenge/) — upstream MIT `LICENSE` + [`PROVENANCE.md`](vendor/wallace-jacobian-challenge/PROVENANCE.md) (source commit `82349bc8`, vetting record, modifications). Outside the build root.
- [`Jacobians/Vendor/Wallace/`](Jacobians/Vendor/Wallace/) — the six modules in our build under `Jacobians.Vendor.Wallace.*`, with per-file MIT attribution headers; mathematics unchanged apart from the stripped stub. See [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md).

## Response to Buzzard's diagnosis

Buzzard's challenge post identifies two Mathlib gaps that make the problem hard:

> *"all definitions of Jacobian that I know involve quotienting a manifold by a discrete group, which isn't in mathlib as far as I know. The one where you use `X^g` by the symmetric group involves a delicate local analysis when points coincide and the one where you quotient out the dual of the holomorphic 1-forms by the first homology will involve integrating differentials around loops which we don't have either, at least in this generality."*

We rejected the symmetric-product route `X^g / S_g` precisely because of the coincident-points local analysis Buzzard flags, and took the period-lattice route (quotient of `(HolomorphicOneForm X)*` by the period lattice). This carries Buzzard's two gaps differently:

**Gap 1 — "quotient a manifold by a discrete group" — solved by hand for the specific case.** We don't wait for Mathlib's general theorem (Rothgang's PR in flight) or cite it. `Jacobians/AbelianVariety/ComplexTorus.lean` builds `ComplexTorus V L := V ⧸ L` for `L : Submodule ℤ V` with `[IsZLattice ℝ L]` and supplies all 7 Buzzard-required typeclass instances (`AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace V`, `IsManifold`, `LieAddGroup`) directly via translation atlas + lattice discreteness. Axiom-free, zero sorry. Limited scope (works only for `V ⧸ L`-shaped quotients) but covers the Jacobian construction entirely.

**Gap 2 — "integrating differentials around loops" — isolated, partially filled via the Kirov bridge.** We do not supply a general theory of line integrals of 1-forms on manifolds, but we now have the **path-side** of the original `pathIntegralBasepointFunctional` axiom retired down to a real composition:

```
kirovBackedFunctional (P₀ P : X) : HolomorphicOneForm X →ₗ[ℂ] ℂ        -- real def
   = lineIntegral ∘ bridgeForm ∘ bridgePath
```

`Vendor.Kirov.lineIntegral` (sorry-free, 616 LOC) gives `pathSpeed`, `lineIntegral`, `lineIntegral_{add, smul, neg, concat, reverse}`, and the chain rule `pathSpeed_comp_eq_mfderiv` as **derived theorems**. `bridgeForm` (real, sorry-free) translates between our cocycle 1-forms and Kirov's section-bundle 1-forms. The `kirovBackedFunctional`'s linearity in the form is therefore not axiomatized — it is `lineIntegral_add` / `_smul` composed with `bridgeForm.map_add'` / `_smul'`. That's a substantive piece of the original abstract axiom retired.

What remains:

* **The chart-local FTC theorem** (`kirovBackedFunctional_local_antiderivative`, currently `sorry`) — binds the functional to the chart coefficient of the 1-form. Smaller piece `chartLine_FTC` (FTC on the concrete affine chart-line) closes first; honest derivation route via `pathSpeed_comp_eq_mfderiv` + `mfderiv_extChartAt_self` + `intervalIntegral` FTC. A previous attempt that closed it via a verbatim-relabelled structural axiom was correctly reverted.
* **`bridgePath` + 5 structural companions** (existence, continuity, chart-local `DifferentiableAt`, endpoints, integrability of the line-integrand) — small, concrete axioms with discharge plan via `PathConnectedSpace.somePath` + smoothing. Net axiom count goes UP by ~4 in raw count, but the **shape** is much better: each is a one-line concrete fact rather than a single large abstract function-existence claim.
* **`loopIntegralToH1`** (the H₁-level companion in `RiemannSurface/PathIntegral.lean`) — still axiomatic. Multi-chart `pathIntegralAnalyticArc` and Stokes-style homotopy invariance are still TODO. We have `pathIntegralOnChart` as a real single-chart def via `intervalIntegral`.
* **`pathIntegralBasepointFunctional`** in `Axioms/AbelJacobiMap.lean` is still declared as an axiom; the swap `noncomputable def ... := kirovBackedFunctional` lands once the FTC theorem closes.

Construction plans are written: [`docs/construction-plans/path-integral-basepoint.md`](docs/construction-plans/path-integral-basepoint.md), [`docs/construction-plans/loop-integral-h1.md`](docs/construction-plans/loop-integral-h1.md), and [`docs/KirovHolomorphicLessons.md`](docs/KirovHolomorphicLessons.md) for the bridge-side subtleties.

So the scoping decision is: solve Gap 1 by hand for the needed shape; isolate Gap 2 cleanly so the rest of the API closes around it, then close it from underneath via the Kirov bridge as the line-integral primitives become available. The path-side / linearity content of Gap 2 is now real Lean; the FTC-binding and the H₁ descent are the two remaining pieces.

## Current state

_Verified snapshot with exact sorry/axiom counts and remote-sync state:_
[`docs/status-2026-05-31.md`](docs/status-2026-05-31.md).

| | |
|---|---|
| Build | `lake build` green (8567 jobs, verified 2026-06-03); zero `sorry` in `Challenge.lean`, the core construction, the concrete-curve witnesses, and the S1–S7 1-form framework; **13 `sorry` total**, all outside the core (`Extensions/Hyperelliptic.lean` 6, `Extensions/AbelJacobi.lean` 4, `Bridge/KirovLineIntegral.lean` 2, `ProjectiveCurve/Hyperelliptic/AntiInvariance.lean` 1). **68 axioms (66 ours + 2 vendored)**, kernel-verified and triaged in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md). Discharged 2026-06-04: the Phase-2 `Hyperelliptic` leaf instances; the **entire 6-axiom bridgePath cluster** (`Bridge/BridgePath.lean`, smooth path-connectedness, ~1450 LOC); and the **Phase-3 prerequisite-type batch** — the unified `Hyperelliptic` type became a real parity-dispatch `def` (+ `instTopologicalSpace`/`instChartedSpace`/`instIsManifold`/`oddEquiv`/`evenEquiv`; the carrier transitively depends on the *sound* atlas axioms — not standard-3), and `PlaneCurve` became a faithful `Projectivization`-subtype `def` (+ topology). The remaining sheaf-cohomology cluster (`H0`/`H1`/`LineBundle`) is kept as **honest classified axioms** with a machine-checkable faithfulness gate — [`SheafCohomologySpec.lean`](Jacobians/RiemannSurface/SheafCohomologySpec.lean), Buzzard's anti-degeneracy strategy one layer down (see [`docs/planning/PHASE_3_INFRA_PLAN.md`](docs/planning/PHASE_3_INFRA_PLAN.md)). *A 2026-06-04 review reverted two unsound/faithless discharges (`infinityInverseMap` arbitrary-root, `PlaneCurve.instNonempty` on a false axiom) and hardened `PlaneCurveData`.* `genus ℙ¹ = 0`, `genus Elliptic = 1`, Liouville Level 1, and pullback of holomorphic 1-forms are axiom-free |
| Foundation defs | 13/13 real (`Jacobian X`, all 7 typeclass instances, `ofCurve`, `pushforward`, `pullback`, `degree`) |
| Property theorems derived | `ofCurve_self`, `pushforward_id_apply` / `_comp_apply`, `pullback_id_apply` / `_comp_apply`, `genus_ProjectiveLine_eq_zero` (axiom-free), `genus_Elliptic_eq_one` (axiom-free), **`genus_HyperellipticEven_eq` = `H.f.natDegree / 2 - 1`** (modulo Liouville L2/L3 only; the 2 unsound cocycle axioms were retired by task #21) |
| Concrete real curve types | `ProjectiveLine`, `Elliptic`, `HyperellipticOdd`, `HyperellipticEven` / `HyperellipticEvenProj` (two-chart pushout, full instance chain via `[Fact (¬ Odd ...)]`) |
| Hyperelliptic 1-form framework | S1–S7 done as real proofs (~3,200 LOC); S8 upper bound via Liouville hierarchy (`Jacobians/Axioms/HyperellipticLiouville.lean`); both cross-summand cocycle directions now real theorems (**task #21 done**, the 2 unsound axioms retired); fully-axiom-clean even-genus gated on Liouville L2/L3 — see [`docs/genus-L2-L3-discharge-plan.md`](docs/genus-L2-L3-discharge-plan.md) |
| Axiom-stubbed curve types | unified `Hyperelliptic` (pinned by `≃ₜ` to real cases), `PlaneCurve` |

Full axiom inventory and classification: [`docs/challenge-annotated.md`](docs/challenge-annotated.md), [`docs/dependency-trace.md`](docs/dependency-trace.md).

**On the remaining `sorry`s.** Our working discipline is sorry-free, and the **core challenge is** — Buzzard's `Challenge.lean` API, the `Jacobian X` construction, the concrete-curve witnesses, and the S1–S7 1-form framework all carry **zero `sorry`**. The 13 that remain are a deliberate, documented exception to that discipline: they live entirely *outside* the challenge proper.

- **`Extensions/`** (10: `Hyperelliptic.lean` 6, `AbelJacobi.lean` 4) — *test theorems* that exercise the formalization **beyond** Buzzard's API (odd-degree hyperelliptic involution / Abel–Jacobi / period exercises), kept with inline proof sketches + classical references rather than closed; the even-degree side is already sorry-free.
- **`Bridge/KirovLineIntegral.lean`** (2) — the FTC theorem and `bridgePath` smoothness, the not-yet-finished half of the Kirov line-integral bridge.
- **`ProjectiveCurve/Hyperelliptic/AntiInvariance.lean`** (1) — the σ-anti-invariance step (a route-D obstruction).

We leave them because closing the **core** was the goal: they are optional extensions or in-progress bridges, not load-bearing for the challenge API, the Jacobian construction, or the headline genus theorems.

## Resources used

| | |
|---|---|
| **Wall-clock** | 2026-04-19 → 2026-04-29 (11 calendar days, all active) |
| **Commits** | 209 on `main` (the `kirov-import` branch is fully merged in) |
| **Lean code** | ~10,000 lines across `Jacobians/` (incl. ~3,200 LOC of 1-form framework + Liouville axiom hierarchy) + ~5,600 lines vendored from `rkirov/jacobian-claude` (Apache 2.0) under `Jacobians/Vendor/Kirov/` |
| **Documentation** | ~7,500 lines: challenge annotation, dependency trace, 5 construction plans, adversarial-review records, genus-theorem discharge plan, S5 cocycle architecture, Kirov-bridge subtleties |
| **Model time** | Claude Opus 4.7 (primary coder), GPT-5.4 Codex (rescue passes on Jacobian functoriality derivations, HyperellipticEven T2 / Compact proofs, affine cocycle equations), Gemini 3 Pro deep-think (axiom audits, type-equality smell-test) |
| **Human effort** | Mathematician-user directing: scope, axiom-vs-proof boundary, hack-blocker judgments, review of all landings. Zero human-written Lean. |

## Axiom hygiene and vetting

**Caveat for outside reviewers.** This repo introduces axioms as a deliberate part of its workflow — they are how we make progress on a piece of mathematics that is bigger than what one contributor can prove from first principles in Lean today. Every axiom currently in the repo has been authored or curated in this session and **none has yet received independent human-mathematician review**. If you are evaluating the formalization, the axiom files are where to look first.

**When we introduce an axiom.** An axiom is added when (a) the statement is a classical textbook theorem we are not going to redo (Riemann–Roch, Serre duality, Liouville on compact complex manifolds, etc.), (b) the statement is a concrete data-level fact whose construction is scoped out (e.g. `pathIntegralBasepointFunctional`), or (c) we are deferring a proof that is in flight elsewhere in the repo and want the downstream theorem to compile in the meantime. Axioms are never used to "make a proof go through" without a documented discharge story.

**Procedure for each new axiom.**

1. **Cross-cutting and API-shaped axioms live in `Jacobians/Axioms/*.lean`** (Riemann–Roch, Serre duality, Branch locus, the Liouville hierarchy, etc.). Curve-type-local axioms — atlas compatibility for a specific projective curve, narrow IFT-shape infrastructure, vendored sorries upgraded to named axioms, and scaffolding axioms inside an in-progress framework module — live alongside the consumer (e.g. `ProjectiveCurve/Hyperelliptic.lean`, `Hyperelliptic/EvenForm.lean`, `RiemannSurface/LineBundle.lean`, `Bridge/KirovLineIntegral.lean`, `Vendor/Kirov/*.lean`). What we *don't* do is bury an `axiom` inside an unrelated proof file or use one to silently close a `sorry`.
2. **Classification** — every axiom is tagged in [`docs/dependency-trace.md`](docs/dependency-trace.md) as one of: classical-theorem (textbook citation), data-level function-existence (with construction plan), or atlas/structure axiom (with atlas-completion plan).
3. **Discharge plan** — for non-textbook axioms a written plan lives under [`docs/construction-plans/`](docs/construction-plans/) or alongside the axiom file as a doc comment. The plan names the Mathlib pieces it would consume and estimates effort.
4. **LLM cross-vetting** — before landing, axiom statements are reviewed by a second LLM family (typically Gemini 3 Pro deep-think) against six criteria: type-correctness in Lean, mathematical correctness as stated, faithfulness to the classical statement, soundness of any derivation chain among the axioms, absence of accidental existential collapse (e.g. vacuous statements), and consistency with the repo's existing typeclass shapes. The reviewer's verdicts and any tightenings are recorded in commit messages and, for substantive findings, in [`docs/adversarial-review/`](docs/) (example: the `EvenForm` Möbius axioms were caught as unsound on 2026-04-26 and tightened with an explicit `g_inf = infReverse H g_aff` hypothesis in `ea35935`).
5. **Layered axioms over single big axioms.** Where a result is structurally a chain (Liouville → polynomial decomposition → form surjectivity), we prefer a **hierarchy of axioms** so each level can be discharged independently as Mathlib catches up. The genus upper bound for `HyperellipticEvenProj` is the current example, sitting on a 3-level Liouville hierarchy in [`Jacobians/Axioms/HyperellipticLiouville.lean`](Jacobians/Axioms/HyperellipticLiouville.lean).
6. **Soundness checks.** Every commit that lands an axiom or a theorem consuming axioms runs `lake env lean` locally before push (per [`CLAUDE.md`](CLAUDE.md)), and CI runs `lake build` end-to-end. Mathlib has no inconsistency detector; we rely on the kernel + the hierarchy structure (no axiom asserts a contradiction, each is a known-true classical statement or a clearly-scoped existence claim).

**What outside reviewers can do.** The highest-value reviews are: (i) read [`Jacobians/Axioms/`](Jacobians/Axioms/) and challenge any statement whose classical version is misquoted or whose Lean encoding is too strong; (ii) point at Mathlib lemmas that would let us discharge an axiom directly; (iii) flag any axiom whose discharge plan is wishful. Open an issue or post in the Lean Zulip `#Autoformalization > Jacobian challenge` thread.

## What this claim does and doesn't say

We claim a **solid foundation with correct definitions** for Buzzard's challenge: the interface is closed with real constructions, genus-0 / genus-1 / hyperelliptic curves are populated as real types, and every remaining axiom is enumerated and classified. We do not claim a sorry-free end-to-end solution — the remaining data-level axioms and classical-theorem citations each have a discharge plan. Axioms have been LLM-vetted but not yet human-mathematician-reviewed; downstream theorems whose only non-Lean-proven content is a textbook-classical axiom should be read as "reduced to that classical input", not as "fully proven from Mathlib".

## Build

```bash
lake update
lake build
```

- **Lean:** `v4.30.0-rc1`
- **Mathlib:** commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), as pinned by the challenge.

## Further documentation

- [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) — **canonical axiom audit** (top-level): kernel-verified count (68), triaged into Class 1 (standard/textbook) and Class 2 (form/proof unclear), per-axiom File:Line + ratings, flagged axioms, recently-discharged table.
- [`docs/status-2026-05-31.md`](docs/status-2026-05-31.md) — current verified status snapshot (build, exact sorry/axiom inventory, open workstreams, remote-sync state).
- [`docs/validation-plan.md`](docs/validation-plan.md) — how to judge the definitions and axioms before proving them: mechanical `#print axioms` guard, axiom taxonomy by validation risk, the prioritized validation backlog, and a human-readable contract + AI-modelable specification-first pipeline.
- [`docs/contracts/`](docs/contracts/) — per-object contract cards (judge an object without reading its proofs): [`genus`](docs/contracts/genus.md) (validated on `Elliptic` from core axioms), [`ofCurve`](docs/contracts/ofCurve.md) (anti-hack property found opaque-blocked).
- [`docs/axiom-report.txt`](docs/axiom-report.txt) — golden `#print axioms` trace of every headline (regenerate with [`scripts/axiom_report.lean`](scripts/axiom_report.lean)); confirms no `sorryAx` under any closed declaration.
- [`Jacobians/Challenge.lean`](Jacobians/Challenge.lean) — Buzzard's v0.2 file verbatim (24 sorries), pinned.
- [`docs/challenge-filled.md`](docs/challenge-filled.md) — filled-in spec, every sorry resolved with its prerequisites inlined.
- [`docs/challenge-annotated.md`](docs/challenge-annotated.md) — F/T classification of the 24 sorries.
- [`docs/dependency-trace.md`](docs/dependency-trace.md) — transitive axiom audit.
- [`docs/construction-plans/`](docs/construction-plans/) — discharge plans for the remaining data-level axioms.
- [`docs/formalization-plan.md`](docs/formalization-plan.md) — construction-strategy rationale.
- [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md) — what we take from `rkirov/jacobian-claude` and `tangentstorm/JacobianChallenge`, what we considered and didn't.
- [`docs/genus-theorem-discharge-plan.md`](docs/genus-theorem-discharge-plan.md) — 8-task plan (S1–S8) for the hyperelliptic genus theorems via the 1-form framework.
- [`docs/genus-L2-L3-discharge-plan.md`](docs/genus-L2-L3-discharge-plan.md) — plan for the last gap (Liouville L2/L3 = the canonical-differentials theorem): the L3⟸L2 reduction, L2 decomposition (L2-a..e), realistic estimate.
- [`docs/task-21-discharge-plan.md`](docs/task-21-discharge-plan.md) — task #21 (retiring the unsound cocycle axioms), completed 2026-06-01.

## Vendored sources & attribution

We build on real Lean from two sibling Jacobian-Challenge attempts. Each is vendored under its **upstream** license, with per-file attribution headers, the upstream `LICENSE`, and a `PROVENANCE.md` recording the source commit and any modifications. Full adoption record (what we took, considered, and rejected): [`docs/cross-repo-adoption.md`](docs/cross-repo-adoption.md).

| Source | License | In our build | ~LOC | Mathematical content used |
|--------|---------|--------------|-----:|---------------------------|
| [`rkirov/jacobian-claude`](https://github.com/rkirov/jacobian-claude) | Apache 2.0 | `Jacobians.Vendor.Kirov.*` (13 files) | ~5,800 | Montel's theorem ⇒ finite-dimensionality of holomorphic 1-forms; line integrals (path speed, linearity, concat/reverse, chain rule); ℤ-lattice quotient `V ⧸ Λ` as a complex torus (`ChartedSpace` + `LieAddGroup`); the `HolomorphicForms` / genus-0 bridge. Attribution: [`vendor/kirov-jacobian-claude/`](vendor/kirov-jacobian-claude/). |
| [`tangentstorm/JacobianChallenge`](https://github.com/tangentstorm/JacobianChallenge) | MIT | `Jacobians.Vendor.Wallace.*` (6 files) | ~2,900 | Holomorphic maps between Riemann surfaces (local k-fold ramification, weighted fiber conservation); manifold-level meromorphic order + chart-independence; branched-cover data + `branchedDegree`; local k-th-root biholomorphism; cotangent-space instances; curve-integral subpath lemmas. Attribution: [`vendor/wallace-jacobian-challenge/`](vendor/wallace-jacobian-challenge/). |

These directly discharged project axioms — e.g. `AX_FiniteDimOneForms` (Kirov Montel), `localOrder` (Wallace `mapAnalyticOrderAt`), and the `pullbackOneForm` cluster (Kirov `pullbackForm` via the `bridgeForm` isomorphism). The two repos remain independent attempts; we import their real proofs rather than re-deriving them.

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
