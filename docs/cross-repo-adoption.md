# Cross-repo adoption — what we take from sibling solutions

Three Jacobian-Challenge attempts have been published on the Lean Zulip
(`#Autoformalization > Jacobian challenge`) as of 2026-04-25:

| Repo | Author | License | First commit | LOC (Lean) | Build state |
|---|---|---|---|---|---|
| `mrdouglasny/jacobian-challenge` | Michael R Douglas | Apache 2.0 | 2026-04-19 | ~6,600 (own) + ~4,200 (vendored) | green, 0 sorry |
| `rkirov/jacobian-claude` | Rado Kirov | Apache 2.0 (relicensed from MIT 2026-04-25) | 2026-04-21 | ~7,800 | green, 62 sorry |
| `tangentstorm/JacobianChallenge` | Michal Wallace | (Apache 2.0 per his portfolio) | 2026-04-25 | ~2,400 | green, 24 sorry (challenge) + 11 (support) |

This document records what this repository (`mrdouglasny/jacobian-challenge`)
adopts from the other two attempts, what we considered and rejected, and
why.

## From `rkirov/jacobian-claude`

**Branch where adoption lives**: `kirov-import` (commits `c3c7911`,
`c109163`, `ebff6f3`, `cc02dc3`).

### Adopted (now in our build)

| Module | Provenance file | LOC | Status in our build |
|---|---|---|---|
| `Genus.lean` | upstream `Jacobians/Genus.lean` | 81 | Compiled under namespace `Jacobians.Vendor.Kirov`. One `:= sorry` (`genus_eq_zero_iff_homeo`, Uniformization) converted to a named `axiom` for handoff. |
| `Montel.lean` + `Montel/{Cover,LocalRep,ChartNorm,SupNorm,Compactness,ChartTransition,Complete}.lean` | upstream `Jacobians/Montel*.lean` | ~3,400 | Compiled under namespace `Jacobians.Vendor.Kirov.Montel`. Real proof of compactness of holomorphic 1-forms (Arzelà–Ascoli + normal families, Ahlfors–Sario style) — the `closedBall_isCompact` step that was Kirov's "single structural sorry" is **closed** in his `7ce9e2e` commit. |
| `HolomorphicForms.lean` | upstream `Jacobians/HolomorphicForms.lean` | 366 | Compiled under namespace `Jacobians.Vendor.Kirov`. Yields `instance : FiniteDimensional ℂ (HolomorphicOneForms X)` from Montel, plus `pullbackForm`, `ambientPhi`, `ambientPsi`. One `:= sorry` (`ambientPhi_ambientPsi_eq`, degree identity) converted to named `axiom`. |

**Total adopted**: 4,234 LOC, 9 modules, 2 axioms (handed off in
[`vendor/kirov-jacobian-claude/HANDOFF.md`](../vendor/kirov-jacobian-claude/HANDOFF.md)).

**Mathematical content unchanged.** The only modifications relative to
upstream are:

1. Namespace rename `Jacobians[.Montel]` → `Jacobians.Vendor.Kirov[.Montel]`,
   and matching imports / qualified references.
2. Apache 2.0 attribution headers prepended to each file.
3. `Jacobians/Vendor/Kirov/Genus.lean`: extended the namespace block to
   enclose the trailing `genus` / `genus_eq_zero_iff_homeo` decls (in
   upstream they live at root namespace; root collides with our
   `Challenge.lean`).
4. The two `:= sorry` declarations converted to `axiom` form (same
   fully-qualified name, same signature, no `:= sorry`) — keeps the
   build axiom-clean and gives a named handoff target.

The full upstream tree (including modules we have not pulled into the
build, design docs, and Kirov's own session log) is preserved verbatim
in [`vendor/kirov-jacobian-claude/`](../vendor/kirov-jacobian-claude/).

### How adopted code is wired in

The single load-bearing use is in
[`Jacobians/Bridge/KirovHolomorphic.lean`](../Jacobians/Bridge/KirovHolomorphic.lean):
a small ℂ-linear bridge `bridgeForm : HolomorphicOneForm X →ₗ[ℂ]
Jacobians.Vendor.Kirov.HolomorphicOneForms X`, with `bridgeForm_injective`,
delivers `instance : FiniteDimensional ℂ (HolomorphicOneForm X)` via
`Module.Finite.of_injective` applied to Kirov's
Montel-built instance.

This **retires our previous abstract axiom `AX_FiniteDimOneForms`**.
[`Jacobians/Axioms/FiniteDimOneForms.lean`](../Jacobians/Axioms/FiniteDimOneForms.lean)
is now a backward-compat shim: the historical name `instFiniteDimOneForms`
forwards to the bridge-derived instance, so external consumers continue
to resolve `FiniteDimensional` via typeclass synthesis without change.

### Considered but not yet adopted

| Module | Why not (yet) |
|---|---|
| Kirov's `LineIntegral.lean` (602 LOC) | High value: would let us start retiring `pathIntegralBasepointFunctional` and `loopIntegralToH1` — our two largest data-level axioms in `Axioms/AbelJacobiMap.lean`. **Planned next.** Deferred only because it is a separate work item with its own type-bridging needs (his `pathSpeed` uses chart-local `fderiv` to dodge an `IsScalarTower` diamond, which is exactly the trick our discharge plan needs). |
| Kirov's `ZLatticeQuotient.lean` (740 LOC, sorry-free) | Could replace the `ULift`-transfer workaround in our `Jacobians/Jacobian/Construction.lean`. Lateral refactor, not an axiom retirement — strictly an internal cleanup. Deferred. |
| Kirov's `Abel.lean` chart-invariance of `meromorphicOrderAt` | Could retire `localOrder` from our `Axioms/BranchLocus.lean`. Smaller payoff than Montel; deferred. |
| Kirov's `PeriodLattice.lean`, `Jacobians.lean` (his answer file) | His Abel-Jacobi machinery is tightly coupled to his own definitions of `genus`, `HolomorphicOneForms`, etc. Not a clean lift; we have our own period-lattice route working. |

### Considered and rejected

| Aspect of Kirov's repo | Why rejected |
|---|---|
| **"All `sorry`, no `axiom`" hygiene** | Kirov's design choice (after a typeclass-gated detour) is to leave classical content as visible `sorry`s rather than name them as axioms. This is defensible — `sorry` is tracked by Lean's warning mechanism, axiom is visible only via `#print axioms`. We chose the opposite hygiene (named axioms with citations) because for a **layered** formalization, naming a hole makes it a tractable handoff target and lets the build go green. Both are legitimate; they're not compatible to mix without confusion. We keep the hygiene split: vendored Kirov material under `Vendor.Kirov` is axiom-clean; main tree continues to use `AX_*`-named axioms. |

## From `tangentstorm/JacobianChallenge`

**Adopted: nothing yet.** Tangentstorm's repo is at an earlier stage
than ours (24 challenge `sorry`s open vs our 0; ~2.4 kLOC vs our
~6.6 kLOC own + 4.2 kLOC vendored). His clean modular phase plan is
admirable but he has not yet produced a self-contained mathematical
result of the kind we'd lift.

### Considered

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
