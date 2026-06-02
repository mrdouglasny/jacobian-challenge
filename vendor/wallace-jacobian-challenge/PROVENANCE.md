# Provenance — vendored from tangentstorm/JacobianChallenge

- **Source:** https://github.com/tangentstorm/JacobianChallenge (Michal Wallace)
- **Commit:** `82349bc8` (2026-06-01)
- **License:** MIT (repository `LICENSE`, © Michal J Wallace), vendored alongside
  this file. Some upstream files additionally carry Apache-2.0 headers; the files
  vendored here carried no per-file header, so the repository MIT license governs.
- **Vendored:** 2026-06-02 by Michael R Douglas.

## Modifications
- Renamespaced `JacobianChallenge.*` → `Jacobians.Vendor.Wallace.*`; internal
  imports retargeted to the vendored module paths.
- Per-file `set_option linter.style.*`/`linter.flexible` suppressions (vendored
  code is not held to this repo's mathlib-standard style linting).
- **Removed the unused vacuous helper** `ramificationIndexStub (_f) (_x) := 1`
  from `BranchedCover.lean` (argument-ignoring constant; not used by the real
  branched-degree machinery). No other mathematical content altered.

## Vetting (all adopted modules)
Every module is **sorry-free and axiom-free**. Headline theorems verified via
`#print axioms` to depend only on `[propext, Classical.choice, Quot.sound]`:
`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`, `isHolomorphic_of_contMDiff`,
`local_kfold_ramified_of_contMDiff`, `branchedDegree_eq_weightedFiberCard`,
`branchedDegree_pos`, `curveIntegral_subpath_of_le`.

## Files
| Module | Upstream |
|---|---|
| `HolomorphicForms/AnalyticLocalMapping.lean` | `Jacobian/HolomorphicForms/AnalyticLocalMapping.lean` |
| `HolomorphicForms/CotangentBundle.lean` | `Jacobian/HolomorphicForms/CotangentBundle.lean` |
| `HolomorphicForms/VanishingOrder.lean` | `Jacobian/HolomorphicForms/VanishingOrder.lean` |
| `HolomorphicForms/HolomorphicMap.lean` | `Jacobian/HolomorphicForms/HolomorphicMap.lean` |
| `HolomorphicForms/BranchedCover.lean` | `Jacobian/HolomorphicForms/BranchedCover.lean` |
| `Periods/CurveIntegralSubpath.lean` | `Jacobian/Periods/CurveIntegralSubpath.lean` |
