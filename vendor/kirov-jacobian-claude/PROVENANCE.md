# Provenance — Kirov / jacobian-claude

This directory is a **verbatim copy** of Rado Kirov's repository
[`rkirov/jacobian-claude`](https://github.com/rkirov/jacobian-claude),
imported on **2026-04-25** at upstream commit:

```
7ce9e2e84a227d267134a33a124acd4cbf8df6bf  2026-04-24  "Relicense from MIT to Apache 2.0"
```

## License

Original work © 2026 Rado Kirov, licensed under the **Apache License, Version 2.0**.
The full license text is preserved in [`LICENSE`](./LICENSE) and the upstream
attribution notice in [`NOTICE`](./NOTICE), both unchanged from upstream.

## Why this exists

This repository (`mrdouglasny/jacobian-challenge`) and `rkirov/jacobian-claude`
are independent attempts at Kevin Buzzard's Jacobian Challenge
(Lean Zulip, `#Autoformalization > Jacobian challenge`, 2026-04-19).

After comparing the two attempts (see `/docs/challenge-summary.md`, "Update
2026-04-24 / 2026-04-25"), several pieces of Kirov's work were judged worth
adopting into ours — most importantly:

- **`Jacobians/Montel.lean` + `Jacobians/Montel/`** (~3,400 LOC, real proof
  modulo one structural sorry): Montel's theorem / compactness of holomorphic
  1-forms. Adopting this retires our `AX_FiniteDimOneForms` axiom.
- **`Jacobians/HolomorphicForms.lean`**: definition of `HolomorphicOneForms X`
  as a `ContMDiffSection` of the cotangent bundle. Used as the type Montel
  delivers compactness on.
- **`Jacobians/LineIntegral.lean`** (602 LOC, 1 sorry): chart-local `pathSpeed`
  + line-integral assembly. Starting point for retiring our
  `pathIntegralBasepointFunctional` and related axioms in
  `Axioms/AbelJacobiMap.lean`.
- **`Jacobians/ZLatticeQuotient.lean`** (740 LOC, sorry-free): generic
  `ChartedSpace` + `LieAddGroup` transfer for quotients by a `ZLattice`. Could
  replace the `ULift`-transfer workaround in `Jacobians/Jacobian/Construction.lean`.
- **`Jacobians/Abel.lean`**: chart-invariance of `meromorphicOrderAt`. Could
  retire `localOrder` in `Axioms/BranchLocus.lean`.

The rest of the tree (Kirov's `Jacobians.lean` challenge fill-in,
`PeriodLattice.lean`, `Genus.lean`, design docs, session log) is included for
context and easy reference, not because it's currently planned for adoption.

## Build isolation

This directory is **outside** the `Jacobians/` lean_lib root declared in
`/lakefile.toml`. Nothing here is compiled by `lake build` in our project. Files
imported into our build will be ported one at a time into the main tree under
their own modules (e.g. `Jacobians/Mathlib/HolomorphicForms/`), with per-file
Apache 2.0 headers attributing Kirov as original author and noting any
modifications, per Apache 2.0 §4(b).

## Updating

To re-sync against a newer upstream commit:

```bash
cd ~/Desktop/work/jacobian-comparison/jacobian-claude && git pull
rm -rf vendor/kirov-jacobian-claude/{Jacobians,Jacobians.lean,docs,LICENSE,NOTICE,README.md,human_input.md,lakefile.lean,lean-toolchain}
cp -R ~/Desktop/work/jacobian-comparison/jacobian-claude/{Jacobians,Jacobians.lean,docs,LICENSE,NOTICE,README.md,human_input.md,lakefile.lean,lean-toolchain} vendor/kirov-jacobian-claude/
```

Then update the commit SHA at the top of this file.
