/-
`ProjectiveLine` — the Riemann sphere `ℙ¹(ℂ)`, realized as the one-point
compactification of `ℂ` with its standard two-chart atlas.

Purpose: genus-0 worked example for Buzzard's challenge. Discharges Buzzard's
seven typeclass instances explicitly, without appealing to any abstract-X
infrastructure.

Mathlib already gives us the topology and the coarse separation/compactness/
connectedness facts (`OnePoint.CompactSpace`, `NormalSpace`, `ConnectedSpace`
for `OnePoint ℂ`). What we have to add:
* The `ChartedSpace ℂ ProjectiveLine` structure (two standard charts).
* `IsManifold 𝓘(ℂ) ω ProjectiveLine` (analyticity of the transition `w = 1/z`).
* Instance-level bridges to match Buzzard's signature exactly
  (`Nonempty`, `T2Space` from `NormalSpace`, etc.).

See `docs/formalization-plan.md` §3.5.1.
-/
import Mathlib

open scoped Manifold Topology
open scoped ContDiff -- for `ω` notation
open Complex

namespace Jacobians.ProjectiveCurve

/-- The Riemann sphere. We use `OnePoint ℂ` (= `ℂ ∪ {∞}`) as the carrier; it
already has a compact, Hausdorff, connected topology from Mathlib. The complex
manifold structure (two charts, analytic transition) is built below. -/
def ProjectiveLine : Type := OnePoint ℂ

namespace ProjectiveLine

/-! ### Transfer of basic topological instances from `OnePoint ℂ`. -/

instance : TopologicalSpace ProjectiveLine :=
  inferInstanceAs (TopologicalSpace (OnePoint ℂ))

instance : T2Space ProjectiveLine :=
  inferInstanceAs (T2Space (OnePoint ℂ))

instance : CompactSpace ProjectiveLine :=
  inferInstanceAs (CompactSpace (OnePoint ℂ))

instance : ConnectedSpace ProjectiveLine :=
  inferInstanceAs (ConnectedSpace (OnePoint ℂ))

instance : Nonempty ProjectiveLine :=
  inferInstanceAs (Nonempty (OnePoint ℂ))

/-! ### Charts.

The Riemann sphere has the standard atlas with two charts:
* `chart0 : U₀ := {[z : 1]} → ℂ`, sending `[z : 1] ↦ z`. In `OnePoint ℂ` terms,
  this is the identity on the copy of `ℂ` and is undefined at `∞`.
* `chart1 : U₁ := {[1 : w]} → ℂ`, sending `[1 : w] ↦ w`. In `OnePoint ℂ` terms,
  `0 ↔ ∞` and `z ↔ 1/z` away from `0`.

Transition on the overlap `U₀ ∩ U₁ = ℂ \ {0}`: `w = 1/z`, holomorphic.
-/

-- TODO (chart0):       `PartialHomeomorph` on source `ℂ ⊂ OnePoint ℂ`, target `ℂ`.
-- TODO (chart1):       `PartialHomeomorph` on source `ProjectiveLine \ {0 : ℂ}`,
--                      target `ℂ`, sending `∞ ↦ 0` and `z ↦ 1/z` elsewhere.
-- TODO (ChartedSpace): `instance : ChartedSpace ℂ ProjectiveLine` via the two-chart atlas.
-- TODO (IsManifold):   `instance : IsManifold 𝓘(ℂ) ω ProjectiveLine` via analytic `w = 1/z`.
-- TODO (stereographic):`ProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`
--                      for the `⇐` direction of `genus_eq_zero_iff_homeo`.

end ProjectiveLine

end Jacobians.ProjectiveCurve
