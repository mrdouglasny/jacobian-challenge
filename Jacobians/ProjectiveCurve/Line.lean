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

See `docs/formalization-plan.md` §3.5.1.

API note: at the pinned Mathlib commit, `PartialHomeomorph` has been renamed
to `OpenPartialHomeomorph` (with the same fields + open-source/open-target).
-/
import Mathlib

open scoped Manifold Topology
open scoped ContDiff -- for `ω` notation
open Complex Set OnePoint Topology

namespace Jacobians.ProjectiveCurve

/-- The Riemann sphere. We use `OnePoint ℂ` (= `ℂ ∪ {∞}`) as the carrier; it
already has a compact, Hausdorff, connected topology from Mathlib. The complex
manifold structure (two charts, analytic transition) is built below.

`abbrev` (not `def`) so that the coercion `(↑) : ℂ → OnePoint ℂ` and all
typeclass instances transfer transparently. -/
abbrev ProjectiveLine : Type := OnePoint ℂ

namespace ProjectiveLine

/-! ### Charts.

The Riemann sphere has the standard atlas with two charts:
* `chart0 : {z | z ≠ ∞} → ℂ`, sending `(z : ℂ) ↦ z` — the identity on the
  copy of `ℂ` embedded in `OnePoint ℂ`, undefined at `∞`.
* `chart1 : {z | z ≠ (0 : ℂ)} → ℂ`, sending `∞ ↦ 0` and `(z : ℂ) ↦ 1/z` for
  `z ≠ 0`.

Transition on the overlap `ℂ \ {0}` is `w = 1/z`, holomorphic.

We build `chart0` as the symm of the open-embedding partial homeomorphism
coming from `(↑) : ℂ → OnePoint ℂ`. `chart1` we build directly.
-/

/-- First chart: identity on the copy of `ℂ ⊂ OnePoint ℂ`, undefined at `∞`.

Built from the open embedding `(↑) : ℂ → OnePoint ℂ` via
`IsOpenEmbedding.toOpenPartialHomeomorph`, then `.symm` to flip the direction. -/
noncomputable def chart0 : OpenPartialHomeomorph ProjectiveLine ℂ :=
  (OnePoint.isOpenEmbedding_coe (X := ℂ)).toOpenPartialHomeomorph
    ((↑) : ℂ → OnePoint ℂ) |>.symm

-- Convenience simp lemmas for `chart0` can be added later; the
-- `IsOpenEmbedding.toOpenPartialHomeomorph` helper already provides
-- `toOpenPartialHomeomorph_apply`, `toOpenPartialHomeomorph_source`,
-- `toOpenPartialHomeomorph_target`, and `_left_inv`/`_right_inv` lemmas
-- that we can use after `.symm` where needed.

/-- Second chart: `∞ ↦ 0` and `z ↦ 1/z` on `ℂ \ {0}`. The `toFun` is
undefined at `(0 : ℂ)`, the `invFun` maps `0 ↦ ∞` and otherwise inverts.

TODO: fill in the five continuity/inverse/well-definedness obligations.
Key ingredient: `Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0)` (so the
extension `∞ ↦ 0` is continuous at `∞` via `OnePoint.continuous_iff`). -/
noncomputable def chart1 : OpenPartialHomeomorph ProjectiveLine ℂ where
  toFun := fun p => p.elim 0 (fun z => z⁻¹)
  invFun := fun w => if w = 0 then ∞ else (((w⁻¹ : ℂ) : ProjectiveLine))
  source := {p : ProjectiveLine | p ≠ ((0 : ℂ) : ProjectiveLine)}
  target := univ
  map_source' := fun _ _ => mem_univ _
  map_target' := by
    intro w _
    by_cases hw : w = 0
    · simp [hw]
    · simp only [if_neg hw, mem_setOf_eq, ne_eq, OnePoint.coe_eq_coe]
      exact inv_ne_zero hw
  left_inv' := by
    rintro p hp
    induction p using OnePoint.rec with
    | infty => simp
    | coe z =>
      have hz : z ≠ 0 := fun h => hp (by simp [h])
      have : z⁻¹ ≠ 0 := inv_ne_zero hz
      simp [OnePoint.elim_some, this, inv_inv]
  right_inv' := by
    rintro w _
    by_cases hw : w = 0
    · simp [hw]
    · simp [hw, OnePoint.elim_some, inv_inv]
  open_source := by
    have h : ({p : ProjectiveLine | p ≠ ((0 : ℂ) : ProjectiveLine)} : Set ProjectiveLine) =
             {((0 : ℂ) : ProjectiveLine)}ᶜ := by
      ext p; simp
    rw [h]
    exact isClosed_singleton.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    sorry
    -- TODO (chart1 continuity).
    -- Goal: ContinuousOn (fun p => p.elim 0 (fun z => z⁻¹)) {p | p ≠ (0 : ProjectiveLine)}.
    -- Strategy: use `OnePoint.continuous_iff`-style patching.
    -- At (z : ℂ) ≠ 0: `z ↦ z⁻¹` is continuous on ℂ \ {0} (`continuousOn_inv₀`).
    -- At ∞: `Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0)` ⇒ continuity at ∞
    -- (via `OnePoint.tendsto_nhds_infty` or by unfolding `nhds ∞`).
  continuousOn_invFun := by
    sorry
    -- TODO (chart1 inverse continuity).
    -- Goal: ContinuousOn (fun w => if w = 0 then ∞ else ((w⁻¹ : ℂ) : ProjectiveLine)) univ.
    -- Strategy: `Continuous` suffices; split at w = 0.
    -- At w ≠ 0: `w ↦ some w⁻¹ : ProjectiveLine` is continuous (composition of
    --   `inv₀` with `OnePoint.continuous_coe`).
    -- At w = 0: need `Tendsto (fun w => (w⁻¹ : ℂ) → ProjectiveLine) (𝓝 0) (𝓝 ∞)`.
    --   Same as: `Tendsto (·⁻¹) (𝓝[≠] 0) atTop` in ℂ-norm, then `OnePoint` filter.

-- TODO (ChartedSpace): `instance : ChartedSpace ℂ ProjectiveLine` via the two-chart atlas.
-- Plan:
--   atlas := {chart0, chart1}
--   chartAt p := if p = (0 : ℂ) then chart1 else chart0   -- chart0 covers everything except ∞
--   ...or use chart0 when p ≠ ∞, chart1 when p = ∞ (cleaner: chart0 fails only at ∞).
--
-- TODO (IsManifold): `instance : IsManifold 𝓘(ℂ) ω ProjectiveLine` via analytic `w = 1/z`
-- on the transition domain `chart0.source ∩ chart1.source = {z : ℂ | z ≠ 0}`.

-- TODO (stereographic): `ProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`
-- for the `⇐` direction of `genus_eq_zero_iff_homeo`.

end ProjectiveLine

end Jacobians.ProjectiveCurve
