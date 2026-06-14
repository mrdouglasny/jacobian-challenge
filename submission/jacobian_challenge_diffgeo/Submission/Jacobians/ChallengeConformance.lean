/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license; see the LICENSE file vendored alongside the
original source at `vendor/kirov-jacobian-claude/LICENSE`.
Original source: https://github.com/rkirov/jacobian-claude
                 `ChallengeConformance.lean` (commit 4437c2b, 2026-05-22).

Adapted into this repository on 2026-06-10 (Task D1,
`docs/planning/CONFORMANCE_V02_V04.md`). Modifications relative to upstream:
- Header comment rewritten for this repository; `import Jacobians` narrowed to
  `import Jacobians.Challenge` (where our spec-facing declarations live), so
  this file can sit inside the `Jacobians` library without an import cycle.
- The 24 `example`s, the `variable` blocks, and the discharge terms are
  upstream's, which are in turn mechanical restatements of the spec.
-/

/-
# v0.4 challenge conformance check

CI NOTE: this file should be checked on every push via
`lake env lean Jacobians/ChallengeConformance.lean` (seconds, once `lake build`
has produced the oleans). Until a workflow step is added (`.github/` edits are
owner-vetted), it is also imported from the root module `Jacobians.lean`, so
the existing `lake build` CI gate already compiles it.

Verifies that this repository's declarations satisfy the API of Kevin
Buzzard's challenge spec (v0.4, gist revision `cdc146c3fd…`, pinned verbatim
at `challenge_spec_v0.4.lean`) **exactly**: same names, same statements, no
`[Nonempty X]` (v0.3), `𝓘(ℂ, E)` notation (v0.4). Each `example` restates a
v0.4 signature verbatim and discharges it by our declaration, so this file
compiling is a machine-check that the implementation conforms to the
challenge.

The whole file is a `noncomputable section`: the data declarations (`Jacobian`,
`ofCurve`, `pushforward`, …) are noncomputable, and we only care that the
*types* are inhabited by our declarations, not about code generation.

`Jacobian` is genuinely `Type u` (universe-polymorphic), matching the spec:
the construction `ULift`s the concrete `Type 0` torus to the surface's
universe. The `Jacobian` example below pins the `Type u` signature.

Limit of the check: an `example` discharged by a declaration whose proof rests
on an `axiom` (or `sorry`) compiles fine — conformance certifies *signatures*,
not axiom-freeness; that is what the axiom-report CI gate is for.
-/
import Submission.Jacobians.Challenge

open scoped ContDiff -- for ω notation
open scoped Manifold -- for 𝓘 notation

universe u

noncomputable section

-- `genus`
example (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  genus X

-- let X be a compact Riemann surface (v0.3: no `[Nonempty X]`)
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- `genus_eq_zero_iff_homeo`
example :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  genus_eq_zero_iff_homeo

-- `Jacobian` — genuinely universe-polymorphic `Type u`, matching the spec.
example (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u := Jacobian X

namespace Jacobian

-- the seven instances
example : AddCommGroup (Jacobian X) := inferInstance
example : TopologicalSpace (Jacobian X) := inferInstance
example : T2Space (Jacobian X) := inferInstance
example : CompactSpace (Jacobian X) := inferInstance
example : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := inferInstance
example : IsManifold 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X) := inferInstance
example : LieAddGroup 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X) := inferInstance

-- `ofCurve`, `ofCurve_contMDiff`, `ofCurve_self`, `ofCurve_inj`
example (P : X) : X → Jacobian X := ofCurve P
example (P : X) : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (ofCurve P) := ofCurve_contMDiff P
example (P : X) : ofCurve P P = 0 := ofCurve_self P
example (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) := ofCurve_inj P h

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

-- `pushforward`, `pushforward_contMDiff`, `pushforward_id_apply`
example : Jacobian X →ₜ+ Jacobian Y := pushforward f hf
example :
    ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω (pushforward f hf) :=
  pushforward_contMDiff f hf
example (P : Jacobian X) : pushforward id contMDiff_id P = P := pushforward_id_apply P

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- `pushforward_comp_apply`
example (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  apply pushforward_comp_apply

-- `pullback`, `pullback_contMDiff`, `pullback_id_apply`, `pullback_comp_apply`
example : Jacobian Y →ₜ+ Jacobian X := pullback f hf
example :
    ContMDiff 𝓘(ℂ, Fin (genus Y) → ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (pullback f hf) :=
  pullback_contMDiff f hf
example (P : Jacobian X) : pullback id contMDiff_id P = P := pullback_id_apply P
example (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  apply pullback_comp_apply

-- `ContMDiff.degree`
example : ℕ := ContMDiff.degree f hf

-- `pushforward_pullback`
example (P : Jacobian Y) :
    pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P := by
  apply pushforward_pullback

end Jacobian

end
