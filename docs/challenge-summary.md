# Buzzard's Jacobian Challenge — summary

Posted 19 April 2026 by Kevin Buzzard to the Lean Zulip (stream `#Autoformalization`, topic `Jacobian challenge`). Canonical URL: https://tinyurl.com/JacobianChallenge, gist `kbuzzard/778bc714030b3e974ab5f4038783d1a9`. Version v0.2 as of the scaffolding of this repo.

## The challenge

A single Lean file pinned to Mathlib commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 April 2026). `Jacobians/Challenge.lean` in this repo is a verbatim copy.

### Data sorries (defs and instances)

- `genus X : ℕ`
- `Jacobian X : Type u`
- `AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace (Fin (genus X) → ℂ)`, `IsManifold`, `LieAddGroup` instances on `Jacobian X`
- `Jacobian.ofCurve : X → X → Jacobian X` — the Abel-Jacobi map
- `ContMDiff.degree` — degree of a holomorphic map between compact Riemann surfaces
- `Jacobian.pushforward`, `Jacobian.pullback` — continuous additive morphisms

### Prop sorries (theorems)

- `genus_eq_zero_iff_homeo` — genus 0 ↔ homeomorphic to the 2-sphere (blocks the `Jacobian := 0` hack)
- `ofCurve_self`, `ofCurve_inj` — the second forces Abel-Jacobi to be genuinely injective in positive genus
- Holomorphicity: `ofCurve_contMDiff`, `pushforward_contMDiff`, `pullback_contMDiff`
- Functoriality: `pushforward_id_apply`, `pushforward_comp_apply`, `pullback_id_apply`, `pullback_comp_apply`
- `pushforward_pullback`: `f_* ∘ f^* = deg(f) • id` — the key nontrivial identity

### Why this shape

Buzzard explicitly designed the API to prevent hack answers. Defining `Jacobian := 0` satisfies the type signatures and many of the functorial lemmas, but `ofCurve_inj` forces the Abel-Jacobi map to be injective in positive genus, and `genus_eq_zero_iff_homeo` forces `genus` to track the actual topology of the surface. The two combined close the hack gap.

## Buzzard's framing

- Everything was known by the 1850s (Abel 1829, Jacobi 1851).
- "If you can't do this 200-year-old math, stop claiming FLT-scale autoformalization is close."
- Real motivation: is AI useful for Mathlib? The Jacobian of a compact Riemann surface appears in recent top-journal papers whose *statements* are not even expressible in current Mathlib. A clean AI-produced definition + sufficient API could be PR'd (just the definition and basic API); the remaining AI proofs can live in `merely-true` or similar.

## Discussion highlights

- **Michael Stoll**: could a universal property make it hack-proof? Buzzard: the Jacobian is universal for maps from curves to abelian varieties, but Mathlib doesn't have abelian varieties either.
- **Sébastien Gouëzel**: idiomatic fixes (`Type*` over `Type u`, `𝓘(ℂ)` over `modelWithCornersSelf ℂ ℂ`, drop `Nonempty` under `ConnectedSpace`). Folded into v0.2.
- **Michael Rothgang**: manifold-quotient-by-discrete-group is actively under review in Mathlib (charted-space instance awaiting approval; manifold instance sorry-free modulo a missing "smooth Lie group action on a manifold" def). Likely lands soon.
- **Rado Kirov / Julian Berman**: asked Claude in plan mode. Claude listed three strategies (period lattice, Pic⁰, sheaf cohomology), then — in Berman's case — honestly said "I can't do it, multi-month project." When pushed, Claude recommended the canonical basis-free form `Jacobian X := (H⁰(X, Ω¹_X))ᵛ / image of H₁(X, ℤ)`.
- **Buzzard on strategies**:
  - Option 1 (period lattice): hard part is integrating 1-forms over loops on a general Riemann surface. Math Inc. did the ℂ case for Viazovska autoformalization.
  - Option 2 (Pic⁰): hard part is the complex-manifold structure — needs Riemann-Roch.
  - Option 3 (sheaf cohomology): hard part is finite-dimensionality — Serre duality.
  - "The real challenge is proving all three are equivalent. But it is hard work to even write down some of these definitions."
- **Riccardo Brasca / Rado Kirov**: consensus that math+Lean-expert human steering produces the best results, but AI companies can't sell that story.
- **Jason Rute**: will a company bragging about a solution be offensive? Buzzard: scope overlap is low — nobody's currently working on Jacobians.
- **Michael Stoll**: "Can we also have the corresponding challenge in Algebraic Geometry? :innocent:" (asked jokingly; Buzzard noted abelian varieties aren't in Mathlib either, and the Annals paper he cares about is about compact Riemann surfaces specifically).
