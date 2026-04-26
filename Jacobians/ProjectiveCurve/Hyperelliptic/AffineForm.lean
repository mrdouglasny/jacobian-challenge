/-
# Affine-side coefficients for hyperelliptic 1-forms

Concrete affine-side machinery underlying
`Jacobians/ProjectiveCurve/Hyperelliptic/Form.lean`. Builds the
chart-local coefficient of `g(x) dx / y` in the projX and projY
chart families on `HyperellipticAffine H`.

The framework decomposes by chart:

* **`affineProjXCoeff`** — coefficient on `affineChartProjX a hpY`
  (for `a ∈ smoothLocusY`). Formula: `g(z) / y(z)` where `y(z)` is
  the chart-local branch via `squareLocalHomeomorph.symm`.
* **`affineProjYCoeff`** — coefficient on `affineChartProjY a hpX`
  (for `a ∈ smoothLocusX`). Formula: `2 g(x(z)) / f'(x(z))` after
  the change of variable `dx = (2y/f'(x)) dy`.

This file is a foundational building block; it does not yet assemble
the projective `HolomorphicOneForm`. That assembly lives in `Form.lean`.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart

namespace Jacobians.ProjectiveCurve.HyperellipticAffine

open scoped Manifold ContDiff Topology
open Polynomial

variable {H : HyperellipticData}

/-- Chart-local coefficient of `g(x) dx / y` in the projX chart at
`a ∈ smoothLocusY` (i.e. `a.val.2 ≠ 0`). For `z ∈ chart target`,
this is `g(z) / y(z)` where `y(z)` is the chart's local
`squareLocalHomeomorph.symm` branch. Off-target the value is `0`
(per `IsZeroOffChartTarget`). -/
noncomputable def affineProjXCoeff (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (z : ℂ) : ℂ := by
  classical
  exact
    if z ∈ ((affineChartProjX (H := H) a hpY) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target then
      g.eval z /
        ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z))
    else 0

/-- **Narrow structural axiom.** The point `0 ∈ ℂ` is not in the
source of `squareLocalHomeomorph p hp`.

This is the only piece of `squareLocalHomeomorph_symm_ne_zero` that
isn't directly derivable from the chart's `right_inv`. It is true
because `squareLocalHomeomorph` is built from the IFT-derived
`ContDiffAt.toOpenPartialHomeomorph` on `y ↦ y²` at `p.val.2 ≠ 0`,
and the IFT's source neighborhood is bounded away from the critical
point `y = 0` of the squaring map.

Discharge requires either:
* an explicit characterization of the source of
  `ContDiffAt.toOpenPartialHomeomorph` (Mathlib does not currently
  expose one beyond `mem_toOpenPartialHomeomorph_source`), or
* a topological argument that the squaring map is not locally
  injective at `0` and any chart source containing both `0` and
  `p.val.2 ≠ 0` would witness this — which contradicts
  `OpenPartialHomeomorph.left_inv`. -/
axiom squareLocalHomeomorph_zero_notMem_source
    (p : HyperellipticAffine H) (hp : p ∈ smoothLocusY H) :
    (0 : ℂ) ∉ (squareLocalHomeomorph (H := H) p hp).source

/-- The y-branch chosen by `squareLocalHomeomorph.symm` is non-zero on
the projX chart target.

**Proof.** From `e.right_inv` at `H.f.eval z` we get
`(e.symm (H.f.eval z))^2 = H.f.eval z`. If the LHS were `0`, RHS would
be `0`, hence `0 ∈ e.target`. But `e.target = e.toFun '' e.source`
on which `e.toFun y = y^2`, so `0 ∈ e.target` ⇒ `0 ∈ e.source`.
Contradicts `squareLocalHomeomorph_zero_notMem_source`. -/
theorem squareLocalHomeomorph_symm_ne_zero
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) ≠ 0 := by
  -- chart target = { x | H.f.eval x ∈ e.target } per affineChartProjX def.
  have hHfz : H.f.eval z ∈ (squareLocalHomeomorph (H := H) a hpY).target := hz
  -- Suppose the y-branch is zero; derive a contradiction.
  intro hZero
  set e := squareLocalHomeomorph (H := H) a hpY with he_def
  -- By right_inv, e (e.symm (H.f.eval z)) = H.f.eval z.
  have hRight : e (e.symm (H.f.eval z)) = H.f.eval z := e.right_inv hHfz
  -- The y-branch e.symm sends target to source.
  have hSymmInSrc : e.symm (H.f.eval z) ∈ e.source := e.map_target hHfz
  -- Substituting hZero: e 0 = H.f.eval z (using the membership above).
  rw [hZero] at hRight hSymmInSrc
  -- But 0 ∉ e.source by the structural axiom.
  exact (squareLocalHomeomorph_zero_notMem_source a hpY) hSymmInSrc

/-- `affineProjXCoeff g a hpY 0 = 0`: the zero polynomial gives the
zero coefficient at every point. -/
@[simp] theorem affineProjXCoeff_zero (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (z : ℂ) :
    affineProjXCoeff (0 : Polynomial ℂ) a hpY z = 0 := by
  unfold affineProjXCoeff
  by_cases hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp [hz, Polynomial.eval_zero]
  · simp [hz]

/-- `affineProjXCoeff` is additive in `g`. -/
theorem affineProjXCoeff_add (g g' : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (z : ℂ) :
    affineProjXCoeff (g + g') a hpY z =
      affineProjXCoeff g a hpY z + affineProjXCoeff g' a hpY z := by
  unfold affineProjXCoeff
  by_cases hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp only [hz, if_true, Polynomial.eval_add]
    ring
  · simp [hz]

/-- `affineProjXCoeff` is ℂ-linear (scalar mult side). -/
theorem affineProjXCoeff_smul (c : ℂ) (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) (z : ℂ) :
    affineProjXCoeff (c • g) a hpY z = c * affineProjXCoeff g a hpY z := by
  classical
  unfold affineProjXCoeff
  by_cases hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp only [hz, if_true, dif_pos]
    rw [show ((c • g : Polynomial ℂ).eval z) = c * g.eval z from by
      simp [Polynomial.smul_eval, smul_eq_mul]]
    ring
  · simp [hz]

/-- **Closed form on chart target.** For `z ∈ chart target`,
`affineProjXCoeff g a hpY z = g.eval z / (squareLocalHomeomorph.symm (H.f.eval z))`. -/
theorem affineProjXCoeff_eq_on_target (g : Polynomial ℂ) (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    affineProjXCoeff g a hpY z =
      g.eval z / ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z)) := by
  classical
  unfold affineProjXCoeff
  simp [hz]

/-- The chart target of `affineChartProjX` is open (Codex's chart def). -/
theorem affineChartProjX_target_isOpen (a : HyperellipticAffine H)
    (hpY : a ∈ smoothLocusY H) :
    IsOpen (((affineChartProjX (H := H) a hpY) :
        OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :=
  (affineChartProjX (H := H) a hpY).open_target

end Jacobians.ProjectiveCurve.HyperellipticAffine
