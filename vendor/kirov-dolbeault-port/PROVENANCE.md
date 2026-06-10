# Provenance — Kirov / jacobian-claude (Dolbeault snapshot)

This directory is a **verbatim copy** of Rado Kirov's repository
[`rkirov/jacobian-claude`](https://github.com/rkirov/jacobian-claude),
captured on **2026-06-10** at upstream commit:

```
4437c2b32d40b76089a84c2ae659d6cec9126d05  2026-06-09  "README: 7→4 sorries; chokepoint is now the Serre §17 pairing"
```

## License

All Lean source files carry the header:

```
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
```

No separate `LICENSE` file was present at the root of the upstream repository
at the time of capture. The per-file headers assert Apache License, Version 2.0.
The upstream repository was relicensed from MIT to Apache 2.0 on 2026-04-25
(commit `7ce9e2e`, "Relicense from MIT to Apache 2.0").

## Why this snapshot exists

This snapshot was taken to preserve the state of Kirov's repository at the point
where **Gate A — the 1-form residue theorem — was fully closed**: the theorem
`residueTheorem_unconditional` (`Jacobians/Dolbeault/SerreResidueRamifiedRealSlitGeometry.lean`)
is **sorry-free and axiom-clean** (`[propext, Classical.choice, Quot.sound]` only)
as of this commit. This is the first sorry-free Lean proof of the general
`∑ Res = 0` for a meromorphic 1-form on a compact Riemann surface.

## Contents

- **271 Lean source files**, 6.1 MB, ~86k LOC
- Mathlib pinned at `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (2026-04-15),
  Lean toolchain `v4.30.0-rc1`
- *Note:* our project (`mrdouglasny/jacobian-challenge`) pins Mathlib at
  `c5ea00351c28e24afc9f0f84379aa41082b1188f` (2026-05-26, `v4.30.0`), which
  is **1,218 commits ahead** of this snapshot's pin. A forward port is
  required before any of these files can be compiled under our build.

## Key headline result

```
theorem residueTheorem_unconditional (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (poles : Finset X)
    (hpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0
```

For any compact connected Riemann surface `X`, holomorphic 1-form `ω₀`, and
genuinely meromorphic function `g`, the total residue of `ω₀·g` vanishes.
Proof follows Miranda §VIII.3 (trace to ℙ¹).

## Other sorry-free results in this snapshot

- `MeromorphicFunction.deg_div` — Forster Cor. 4.25 (`∑ ord = 0`)
- `MittagLefflerForm.res_eq_zero_of_globalMeromorphic` — Forster §17.3
  well-definedness of `Res : H¹(X,Ω) → ℂ`
- `injective_of_residueOne_witness`, `lDim_le_h1Dim_of_residueOne_witness` —
  Forster §17.6 easy-half injectivity: `lDim(K−D) ≤ h1Dim(D)`
- `exists_cechModel` — Forster §14 finiteness of Čech `H¹`
- `exists_skyscraperLES` — skyscraper χ-step (Forster §16)
- `cechH1_dolbeault_comparison_proof` — Čech↔Dolbeault comparison

## Remaining sorries in this snapshot (4 walls)

| Sorry | File | Content |
|---|---|---|
| `exists_serreDualityData` | `Dolbeault/SerreDualityPairing.lean:127` | §17.5 connecting map + §17.9 surjectivity — the chokepoint for RR |
| `abelJacobi_twoPoint_ne_zero` | `Abel.lean:671` | Abel's theorem core |
| `exists_cutSurface` | `CutSurfaceRelations.lean:161` | Cut surface / surface topology |
| `HasHolomorphicPrimitives` | `DegreeOneSphere.lean:678` | Manifold de Rham (period slice) |

## Relationship to the earlier Kirov vendor (`vendor/kirov-jacobian-claude/`)

The earlier vendor (`vendor/kirov-jacobian-claude/`, snapshot 2026-04-25 at
commit `7ce9e2e`) captured only the 6 modules we actively ported into our
build: `Montel/`, `HolomorphicForms`, `LineIntegral`, `ZLatticeQuotient`,
`ChartedSpaceOfLocalHomeomorph`, `Genus`. This snapshot captures the full
repository at a much later commit (1,010+ upstream commits later) and is
intended as a **reference copy only** — nothing from this directory is compiled
into our build as of 2026-06-10.
