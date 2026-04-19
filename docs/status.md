# Status

## Build status

Not yet verified. Phase A task: `lake update && lake build`.

## Sorry inventory

All 22 sorries in `Jacobians/Challenge.lean` are as originally stated by Buzzard (v0.2). None filled.

### Data sorries (8)

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

### Theorem sorries (10)

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

None introduced by this project. Challenge file uses only sorries, no axioms.

## Dependencies pinned

- Lean: `v4.30.0-rc1`
- Mathlib: commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026)
