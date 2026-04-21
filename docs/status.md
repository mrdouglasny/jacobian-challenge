# Status

_Last updated: 2026-04-21_

## Build status

✅ Green. `lake build` completes 8307 jobs.

## Sorry inventory

All 24 sorries in `Jacobians/Challenge.lean` remain as originally stated by Buzzard (v0.2). None have been filled yet at the abstract-`X` level; work on closing them is in progress through Part A + Track 2 modules. **Zero sorries** in any non-Challenge file.

(The early scaffold commits and initial docs mistakenly said 22; verified by `grep -c 'sorry' Jacobians/Challenge.lean` on 2026-04-20 — actual count is 24.)

## Module progress

### ✅ Complete

- `Jacobians/ProjectiveCurve/Line.lean` — `ProjectiveLine := OnePoint ℂ` with all seven X-side Buzzard instances (TopologicalSpace, T2Space, CompactSpace, ConnectedSpace, Nonempty, ChartedSpace ℂ, IsManifold 𝓘(ℂ) ω). Plus `chart0`, `chart1`, `chartAt`, and `stereographic : ProjectiveLine ≃ₜ S² ⊂ ℝ³`. Zero sorries.

### 🔄 In progress

- `Jacobians/AbelianVariety/ComplexTorus.lean` — `ComplexTorus V L := V ⧸ L.toAddSubgroup` for a full-rank ℤ-lattice. **5/7** Buzzard instances land (AddCommGroup, TopologicalSpace, IsTopologicalAddGroup, T2Space, CompactSpace). **ChartedSpace V, IsManifold, LieAddGroup** remain as TODO; detailed route in file-level comments.

### ✅ Scaffolding only

- `Jacobians/AbelianVariety/Lattice.lean` — convention-fixing wrapper around Mathlib's `IsZLattice` class.
- `Jacobians/AbelianVariety.lean` — top-level Part A aggregator.
- `Jacobians/ProjectiveCurve.lean` — top-level Track 2 aggregator.
- `Jacobians/ProjectiveCurve/Charts.lean` — shared-machinery stub for implicit-function-theorem chart constructions.

### ⬜ Not started

Part A: `Siegel.lean`, `Theta.lean`.
Part B (abstract `X`): `OneForm.lean`, `PathIntegral.lean`, `Homology.lean`, `IntersectionForm.lean`, `Periods.lean`, `Genus.lean`.
Track 2: `Elliptic.lean`, `Hyperelliptic.lean`, `PlaneCurve.lean`.
Bridge: `Jacobian/Construction.lean`, `AbelJacobi.lean`, `Abel.lean`, `Functoriality.lean`, `PushPull.lean`.
Genus 0: `Uniformization.lean`.
Axioms: all 9 named axioms (stubs not yet generated; see [formalization-plan.md §7](formalization-plan.md)).

### Data sorries (9)

| Symbol | Line | Kind |
|--------|------|------|
| `genus` | 44 | `def` returning `ℕ` |
| `Jacobian` | 59 | `def` returning `Type u` |
| `AddCommGroup (Jacobian X)` | 65 | instance |
| `TopologicalSpace (Jacobian X)` | 69 | instance |
| `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` | 80 | instance |
| `Jacobian.ofCurve` | 89 | `def` |
| `Jacobian.pushforward` | 107 | `def` |
| `Jacobian.pullback` | 131 | `def` |
| `ContMDiff.degree` | 149 | `def` |

### Instance prop sorries (4)

| Symbol | Line |
|--------|------|
| `T2Space (Jacobian X)` | 72 |
| `CompactSpace (Jacobian X)` | 75 |
| `IsManifold (..) ω (Jacobian X)` | 83 |
| `LieAddGroup (..) ω (Jacobian X)` | 86 |

### Theorem sorries (11)

| Symbol | Line |
|--------|------|
| `genus_eq_zero_iff_homeo` | 53 |
| `ofCurve_contMDiff` | 92 |
| `ofCurve_self` | 94 |
| `ofCurve_inj` | 97 |
| `pushforward_contMDiff` | 110 |
| `pushforward_id_apply` | 115 |
| `pushforward_comp_apply` | 123 |
| `pullback_contMDiff` | 134 |
| `pullback_id_apply` | 139 |
| `pullback_comp_apply` | 142 |
| `pushforward_pullback` | 151 |

## Axiom inventory

None introduced by this project yet. The [formalization plan](formalization-plan.md) defines nine named axioms (`AX_FiniteDimOneForms`, `AX_RiemannRoch`, `AX_SerreDuality`, `AX_RiemannBilinear`, `AX_H1FreeRank2g`, `AX_PeriodInjective`, `AX_AbelTheorem`, `AX_BranchLocus`, `AX_PluckerFormula`) that will be introduced as `Axioms/*.lean` files once the consuming modules need them.

## Dependencies pinned

- Lean: `v4.30.0-rc1`
- Mathlib: commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026)
