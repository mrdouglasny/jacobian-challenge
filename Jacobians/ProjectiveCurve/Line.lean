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
    -- Pointwise `ContinuousAt`:
    -- · at ∞: `Tendsto (·⁻¹) (cocompact ℂ) (𝓝 0)` via `tendsto_inv₀_cobounded`
    --   and `Metric.cobounded_eq_cocompact`, then `OnePoint.continuousAt_infty'`.
    -- · at `↑z` with `z ≠ 0`: `OnePoint.continuousAt_coe` + `continuousAt_inv₀`.
    intro p hp
    refine ContinuousAt.continuousWithinAt ?_
    induction p using OnePoint.rec with
    | infty =>
      refine OnePoint.continuousAt_infty'.mpr ?_
      simpa [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        using Filter.tendsto_inv₀_cobounded (α := ℂ)
    | coe z =>
      have hz : z ≠ 0 := fun h => hp (by simp [h])
      have : ContinuousAt (fun z : ℂ => z⁻¹) z := continuousAt_inv₀ hz
      exact OnePoint.continuousAt_coe.mpr this
  continuousOn_invFun := by
    -- Rewrite the `if` as `Function.update` of the naive inversion map at `0 ↦ ∞`.
    -- Then `continuousOn_update_iff` splits into continuity on the complement
    -- of `{0}` (coe ∘ inv, smooth away from 0) and the tendsto condition at `0`
    -- (inv → cocompact, then coe → 𝓝 ∞).
    let f : ℂ → ProjectiveLine := fun w => (((w⁻¹ : ℂ) : ProjectiveLine))
    have hupdate :
        (fun w : ℂ => if w = 0 then ((∞ : ProjectiveLine)) else (((w⁻¹ : ℂ) : ProjectiveLine))) =
          Function.update f 0 (∞ : ProjectiveLine) := by
      funext w
      by_cases hw : w = 0
      · subst hw
        simp [Function.update]
      · simp [f, Function.update, hw]
    rw [hupdate, continuousOn_update_iff]
    constructor
    · intro z hz
      have hz0 : z ≠ 0 := by simpa using hz.2
      exact (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz0)).continuousWithinAt
    · intro _
      have hset : (univ \ {(0 : ℂ)} : Set ℂ) = ({(0 : ℂ)}ᶜ : Set ℂ) := by
        ext z
        simp
      have hinv :
          Filter.Tendsto Inv.inv (𝓝[univ \ {(0 : ℂ)}] (0 : ℂ)) (Filter.coclosedCompact ℂ) := by
        simpa [hset, Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] using
          (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ))
      simpa [f] using
        (OnePoint.tendsto_coe_infty.comp hinv)

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
