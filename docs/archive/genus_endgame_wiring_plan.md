# Wiring `genus_eq_zero_iff_homeo` to the DegreeOneSphere endgame — DONE (2026-06-01)

**Status: COMPLETE** (commit `8c92864`). This doc is kept as a record of how it was resolved.

`genus_eq_zero_iff_homeo` (the #1 challenge theorem) is now **proven modulo two isolated analytic
inputs**, wired to the proven-modulo degree-one endgame:
- forward: `genus 0 → exists_singleSimplePole_of_genus_zero` (RR consequence `l(P)=2`, sorry) →
  `nonempty_homeo_sphere_of_singleSimplePole` (degree-one endgame).
- backward: `genus_zero_of_nonempty_homeo_sphere` (`Ω(ℂℙ¹)=0`, sorry).

## How the two apparent blockers were resolved
1. **Import cycle** (`DegreeOneSphere → ProjectiveLine → Genus`) — REAL. Resolved by **moving the
   theorem out of `Genus.lean` into `DegreeOneSphere.lean`** (downstream of both). Genus.lean now has
   a pointer comment, 0 sorries.
2. **`[Nonempty X]` gap — was a FALSE ALARM.** `ConnectedSpace` extends `Nonempty`
   (`attribute [instance 50] ConnectedSpace.toNonempty`), so `[ConnectedSpace X]` supplies `[Nonempty X]`
   for free. The spec signature is unchanged; no extra instance was added.

## The namespace subtlety that bit once (worth remembering)
`genus` and `genus_eq_zero_iff_homeo` live in the **ROOT namespace**, NOT `namespace Jacobians`
(in `Genus.lean`, `def genus` is *after* `end Jacobians`). The challenge-conformance file
(`ChallengeConformance.lean`) references them BARE with no `open Jacobians`, so they MUST be in root
namespace or conformance fails with `unknownIdentifier`. First attempt placed the moved theorem inside
`namespace Jacobians` → conformance broke. Fix: declare it in root namespace, qualify the
Jacobians-namespace helpers it calls (`Jacobians.MeromorphicFunction`,
`Jacobians.nonempty_homeo_sphere_of_singleSimplePole`) while keeping `genus` (root) bare.

## Verification
`lake build` green (8392 jobs); `lake env lean ChallengeConformance.lean` PASSES;
`genus_eq_zero_iff_homeo` axiom set `[propext, sorryAx, Classical.choice, Quot.sound]` (no new custom
axioms — `sorryAx` only via the isolated inputs).

## Remaining genuine gaps under this theorem (the real math — unchanged by wiring)
- `exists_singleSimplePole_of_genus_zero` (Riemann–Roch `l(P)=2`; Dolbeault/Serre wall).
- `genus_zero_of_nonempty_homeo_sphere` (`Ω(ℂℙ¹)=0`; uses `ProjectiveLine.holomorphicOneForm_eq_zero`).
- the endgame's own 3: `contMDiff_toSphere`, `toSphere_regular_at_pole`, `degreeOne_homeo`.
