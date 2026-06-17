# Cross-repo adoption — what we take from sibling solutions

Three Jacobian-Challenge attempts have been published on the Lean Zulip
(`#Autoformalization > Jacobian challenge`) as of 2026-04-25:

| Repo | Author | License | First commit | LOC (Lean) | Build state |
|---|---|---|---|---|---|
| `mrdouglasny/jacobian-challenge` | Michael R Douglas | Apache 2.0 | 2026-04-19 | ~6,600 (own) + ~4,200 (vendored) | green, 0 sorry |
| `rkirov/jacobian-claude` | Rado Kirov | Apache 2.0 (relicensed from MIT 2026-04-25) | 2026-04-21 | ~7,800 | green, 62 sorry |
| `tangentstorm/JacobianChallenge` | Michal Wallace | MIT (repo `LICENSE`; some files carry Apache-2.0 headers) | 2026-04-25 | ~2,400 → now much larger | green, 24 sorry (challenge) intact |

This document records what this repository (`mrdouglasny/jacobian-challenge`)
adopts from the other two attempts, what we considered and rejected, and
why.

## From `rkirov/jacobian-claude`

**Branch where adoption lives**: `kirov-import` (commits `c3c7911`,
`c109163`, `ebff6f3`, `cc02dc3`).

### Adopted (now in our build)

| Module | Provenance file | LOC | Status in our build |
|---|---|---|---|
| `Genus.lean` | upstream `Jacobians/Genus.lean` | 95 | Compiled under namespace `Jacobians.Vendor.Kirov`. **Axiom-free.** The upstream `:= sorry` (`genus_eq_zero_iff_homeo`, Uniformization) was named as an `axiom` on import, then **deleted 2026-06-04** as unused. |
| `Montel.lean` + `Montel/{Cover,LocalRep,ChartNorm,SupNorm,Compactness,ChartTransition,Complete}.lean` | upstream `Jacobians/Montel*.lean` | ~3,400 | Compiled under namespace `Jacobians.Vendor.Kirov.Montel`. Real proof of compactness of holomorphic 1-forms (Arzelà–Ascoli + normal families, Ahlfors–Sario style) — the `closedBall_isCompact` step that was Kirov's "single structural sorry" is **closed** in his `7ce9e2e` commit. |
| `HolomorphicForms.lean` | upstream `Jacobians/HolomorphicForms.lean` | 380 | Compiled under namespace `Jacobians.Vendor.Kirov`. **Axiom-free.** Yields `instance : FiniteDimensional ℂ (HolomorphicOneForms X)` from Montel, plus `pullbackForm`, `ambientPhi`, `ambientPsi`. The upstream `:= sorry` (`ambientPhi_ambientPsi_eq`, degree identity) was named as an `axiom` on import, then **deleted 2026-06-04** as unused. |
| `LineIntegral.lean` | upstream `Jacobians/LineIntegral.lean` | 602 | Compiled under namespace `Jacobians.Vendor.Kirov`. Sorry-free upstream and after the port. Provides `pathSpeed`, `lineIntegral` with linearity (add/smul/zero/neg/const), reverse, concat, and the key chain-rule identity `pathSpeed_comp_eq_mfderiv`. Used by `Jacobians/Bridge/KirovLineIntegral.lean` to build `kirovBackedFunctional`. |
| `ChartedSpaceOfLocalHomeomorph.lean` | upstream `Jacobians/ChartedSpaceOfLocalHomeomorph.lean` | 55 | Extends Mathlib's `IsLocalHomeomorph` namespace with a `ChartedSpace` constructor; helper for `ZLatticeQuotient`. |
| `ZLatticeQuotient.lean` | upstream `Jacobians/ZLatticeQuotient.lean` | 740 | Compiled under namespace `Jacobians.Vendor.Kirov.ZLatticeQuotient`. Sorry-free. The quotient `V ⧸ Λ` for `Λ : Submodule ℤ V` with `[IsZLattice ℝ Λ]`: covering-map structure, `ChartedSpace` and `LieAddGroup` instance transfer. Candidate to replace the `ULift`-transfer workaround in `Jacobians/Jacobian/Construction.lean`. Not yet wired in. |

**Total adopted**: ~5,600 LOC, 12 modules, **0 axioms** — the 2 upstream
`:= sorry`-handoff axioms (`genus_eq_zero_iff_homeo`, `ambientPhi_ambientPsi_eq`)
were **deleted 2026-06-04** as unused (no references beyond their own
declarations; the challenge uses the main-tree `AX_genus_eq_zero_iff_homeo`), so
the vendored Kirov subtree is now axiom-free like Wallace. The statements remain
in the pristine upstream copy under
[`vendor/kirov-jacobian-claude/`](../vendor/kirov-jacobian-claude/).

**Mathematical content unchanged.** The only modifications relative to
upstream are:

1. Namespace rename `Jacobians[.Montel]` → `Jacobians.Vendor.Kirov[.Montel]`,
   and matching imports / qualified references.
2. Apache 2.0 attribution headers prepended to each file.
3. `Jacobians/Vendor/Kirov/Genus.lean`: extended the namespace block to
   enclose the trailing `genus` / `genus_eq_zero_iff_homeo` decls (in
   upstream they live at root namespace; root collides with our
   `Challenge.lean`).
4. The two `:= sorry` declarations were converted to `axiom` form on import,
   then **deleted entirely 2026-06-04** once confirmed unused — the vendored
   subtree carries no axioms.

The full upstream tree (including modules we have not pulled into the
build, design docs, and Kirov's own session log) is preserved verbatim
in [`vendor/kirov-jacobian-claude/`](../vendor/kirov-jacobian-claude/).

### How adopted code is wired in

Two bridge files in [`Jacobians/Bridge/`](../Jacobians/Bridge/):

1. [`KirovHolomorphic.lean`](../Jacobians/Bridge/KirovHolomorphic.lean): a ℂ-linear bridge `bridgeForm : HolomorphicOneForm X →ₗ[ℂ] Jacobians.Vendor.Kirov.HolomorphicOneForms X` (real, sorry-free), with `bridgeForm_injective` (real). Delivers `instance : FiniteDimensional ℂ (HolomorphicOneForm X)` via `Module.Finite.of_injective` applied to Kirov's Montel-built instance. **Retires `AX_FiniteDimOneForms` truly** — no structural axioms in the bridge file. The shim [`Jacobians/Axioms/FiniteDimOneForms.lean`](../Jacobians/Axioms/FiniteDimOneForms.lean) forwards the historical instance name `instFiniteDimOneForms` to the bridge-derived instance.

2. [`KirovLineIntegral.lean`](../Jacobians/Bridge/KirovLineIntegral.lean): `kirovBackedFunctional P₀ P : HolomorphicOneForm X →ₗ[ℂ] ℂ` defined as `lineIntegral ∘ bridgeForm` along a chosen path; linearity derived from Kirov's `lineIntegral_add` / `lineIntegral_smul`. The corresponding FTC theorem (`kirovBackedFunctional_local_antiderivative`) is **in flight** — currently a single open `sorry` with a concrete 5-step derivation chain (the first reduction, `extChartAt_chartLine`, already lands; the chain depends on no new axioms beyond five small structural `bridgePath*` axioms scoped to path selection). When the FTC theorem closes, `pathIntegralBasepointFunctional` and `AX_pathIntegral_local_antiderivative` retire from `Axioms/AbelJacobiMap.lean`.

### Considered but not yet adopted

| Module | Why not (yet) |
|---|---|
| Kirov's `Abel.lean` chart-invariance of `meromorphicOrderAt` | Could retire `localOrder` from our `Axioms/BranchLocus.lean`. Smaller payoff than Montel/LineIntegral; deferred. |
| Kirov's `PeriodLattice.lean`, `Jacobians.lean` (his answer file) | His Abel-Jacobi machinery is tightly coupled to his own definitions of `genus`, `HolomorphicOneForms`, etc. Not a clean lift; we have our own period-lattice route working. |
| `ZLatticeQuotient` rewiring of `Jacobian/Construction.lean` | The module is ported (above) but not yet used as a replacement for the `ULift`-transfer workaround. Lateral refactor, not an axiom retirement — strictly an internal cleanup. |

### Considered and rejected

| Aspect of Kirov's repo | Why rejected |
|---|---|
| **"All `sorry`, no `axiom`" hygiene** | Kirov's design choice (after a typeclass-gated detour) is to leave classical content as visible `sorry`s rather than name them as axioms. This is defensible — `sorry` is tracked by Lean's warning mechanism, axiom is visible only via `#print axioms`. We chose the opposite hygiene (named axioms with citations) because for a **layered** formalization, naming a hole makes it a tractable handoff target and lets the build go green. Both are legitimate; they're not compatible to mix without confusion. We keep the hygiene split: vendored Kirov material under `Vendor.Kirov` is axiom-clean; main tree continues to use `AX_*`-named axioms. |

## From `tangentstorm/JacobianChallenge`

**Adopted: 6 modules (2026-06-02).** A faithfulness audit of his repo
found the period/Stokes/trace core to be `:= 0`/`⊥`/`True` placeholder,
*but* a set of analytic-infrastructure files are genuinely
self-contained and real. We selected those whose transitive import
closure is Mathlib-only (or within the set) and **decoupled from the
placeholder layer**, vetted each, and vendored them under
`Jacobians.Vendor.Wallace.*` (MIT; `vendor/wallace-jacobian-challenge/`).

### Adopted (now in our build)

| Module | LOC | Content | Vetting |
|---|---|---|---|
| `HolomorphicForms/HolomorphicMap.lean` | 1349 | holomorphic maps between Riemann surfaces; local k-fold ramification; weighted fiber conservation | `#print axioms` ⊆ {propext, Classical.choice, Quot.sound} |
| `HolomorphicForms/VanishingOrder.lean` | 550 | manifold-level meromorphic order + chart-independence | clean (`#print axioms`) |
| `HolomorphicForms/BranchedCover.lean` | ~330 | branched-cover data, `branchedDegree`, fiber-sum constancy. **Vacuous `ramificationIndexStub (_f)(_x) := 1` stripped on import** (caught by def-vetting) | clean (`#print axioms`) |
| `HolomorphicForms/AnalyticLocalMapping.lean` | 247 | local k-fold / k-th-root biholomorphism | clean |
| `HolomorphicForms/CotangentBundle.lean` | 114 | cotangent-space/fiber instances | clean |
| `Periods/CurveIntegralSubpath.lean` | ~130 | curve-integral subpath lemmas over Mathlib `curveIntegral` | clean (`#print axioms`) |

Every module is **sorry-free and axiom-free**; headline theorems were
verified via `#print axioms` to depend only on the three standard Lean
axioms (details in `vendor/wallace-jacobian-challenge/PROVENANCE.md`).
Builds under our v4.30 pin (upstream is v4.31-rc1). Held as a reusable
analytic library — especially for the meromorphic / branched-cover /
genus-0 strands — not yet wired to discharge a specific project axiom.

### Considered (not adopted)

| Piece | Why not (yet) |
|---|---|
| **`FullComplexLattice` bundled structure** (`Jacobian/WorkPackets/StatementBank.lean`) | A `structure` packaging `subgroup`, `isClosed`, `isDiscrete`, `fundamentalDomain` (compact), and a covering property. We already use Mathlib's `IsZLattice` directly in `Jacobians/AbelianVariety/Lattice.lean`, plus our own `ComplexTorus` quotient construction in `AbelianVariety/ComplexTorus.lean` — no need for a parallel bundled type. |
| **`IsolationAtZero.exists_pos_le_norm_of_discreteTopology`** + **`MkInjOnSmallBall`** + **`ChartBall.exists_chart_ball`** | Small clean lemmas that *could* simplify lines 53–98 of our `AbelianVariety/ComplexTorus.lean` (the lattice-discreteness chart-radius argument). Lateral cleanup, not an axiom retirement. **Worth revisiting** if we end up extracting that chart-radius argument as standalone PR-ready content. |
| **`ZLatticeRecon.lean` ZLattice → FullComplexLattice bridge** | Useful as a Mathlib-PR template if we ever upstream the lattice work, but not directly liftable while we keep `IsZLattice` as our primary type. |
| **Mathlib v4.28.0 inventory work** (`Jacobian/WorkPackets/Inventory.md`) | Tangentstorm did a careful audit of Mathlib at v4.28.0 against the challenge's needs. Our pin is `8e3c989...` (a slightly later commit) so the inventory isn't directly transferable, but it's a cross-reference for our own Mathlib-prerequisites tracking. |

### Watching

Tangentstorm is in active development with daily milestone updates on
the Zulip thread. As pieces of his work mature into self-contained
proofs (specifically the **quotient-manifold chart construction** he is
currently at 15% on, and any **path-integration** work later), we will
re-survey and adopt anything that beats our existing implementation or
fills an open axiom.

## Pre-existing Mathlib dependency

For completeness: we also depend on Mathlib at commit
`8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026), as pinned by
Buzzard's challenge. We do not vendor any Mathlib content — that
dependency is managed via `lakefile.toml` `[[require]]`. Specific
Mathlib types we lean on heavily:

- `Submodule ℤ V` + `IsZLattice ℝ L` — as the lattice for the period
  construction.
- `QuotientAddGroup`, `ChartedSpace`, `IsManifold 𝓘(ℂ) ω`, `LieAddGroup`
  — the typeclass stack required by Buzzard's `Jacobian X`.
- `ContMDiffSection` of vector bundles — the home of Kirov's
  `HolomorphicOneForms`.
- `Module.Finite.of_injective` (= `FiniteDimensional.of_injective`) —
  the transfer step in our bridge.

## Maintenance

To re-sync the vendored Kirov tree against a newer upstream commit, see
the recipe in
[`vendor/kirov-jacobian-claude/PROVENANCE.md`](../vendor/kirov-jacobian-claude/PROVENANCE.md).
After any re-sync, also re-apply the namespace rewrites and re-check
the two converted-to-`axiom` declarations.

### 2026-06-16 — warning-cleanup sweep (PR #256, @sqrt-of-2, *open*)

Verified by an isolated clean build (worktree, exit 0, 9015 jobs): the tree now
builds with **zero non-`sorry` warnings**. Six `declaration uses sorry` warnings
remain, all off the headline path:
`KirovDolbeault/{CutSurfaceRelations, Abel, DegreeOneSphere}.lean` and
`RiemannSurface/Cohomology/RiemannRochAnchor.lean:{35,43,53}`.

Provenance impact (two kinds, treat differently):
- **Compiled Kirov port** (`vendor/kirov-dolbeault-port/`, `Jacobians/Vendor/Kirov/`):
  warning-cleaned. Expected — this is the working dependency (already a forward-port,
  not byte-verbatim). Fine.
- **Non-compiled *verbatim* snapshots** (`vendor/kirov-jacobian-claude/`,
  `vendor/kirov-jacobian-claude-dolbeault/`, ~20 files): #256 **content-edits** these
  (e.g. `support_single_ne_zero → support_single`, `SmoothSection → ContMDiffSection`)
  — i.e. forward-ports them to current Mathlib, *despite their not being built*. This
  breaks the "preserved verbatim" claim above (line ~55) and the `CLAUDE.md`
  vendored-material section (owner-protected). **Open decision before merge:**
  (a) revert the snapshot edits to keep them byte-verbatim (they need not compile), or
  (b) accept them and re-label those dirs as "forward-ported" here and in `CLAUDE.md`.
  Until resolved, the line-55 "verbatim" claim is accurate for `main` but would be
  false post-#256-merge under option (b).
