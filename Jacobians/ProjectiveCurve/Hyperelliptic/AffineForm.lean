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
    (hpY : a ∈ smoothLocusY H) (z : ℂ) : ℂ :=
  if z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target then
    g.eval z /
      ((squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z))
  else 0

/-- The y-branch chosen by `squareLocalHomeomorph.symm` is non-zero on
the projX chart target.

By construction, the chart at `a` (with `a.val.2 ≠ 0`) restricts the
branch choice so that the y-coordinate of `chart.symm z` matches the
chosen branch — and that y-coordinate is the second coordinate of an
affine point on the curve, which lies in a neighborhood of `a.val.2 ≠ 0`. -/
theorem squareLocalHomeomorph_symm_ne_zero
    (a : HyperellipticAffine H) (hpY : a ∈ smoothLocusY H)
    {z : ℂ}
    (hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target) :
    (squareLocalHomeomorph (H := H) a hpY).symm (H.f.eval z) ≠ 0 := by
  -- The chart-symm of z has y-coordinate equal to this expression.
  -- That y-coordinate is the .val.2 of an affine point.
  -- We need to argue it's in the smoothLocusY (y ≠ 0).
  -- This requires more work than fits a one-liner; sketch:
  -- 1. By `affineChartProjX_symm_apply_snd` (Codex's simp-lemma in
  --    OddAtlas/AffineChart.lean:264), the y-coord of chart-symm z is
  --    exactly `(squareLocalHomeomorph a hpY).symm (H.f.eval z)`.
  -- 2. The chart's source is contained in `smoothLocusY`, so the
  --    affine point chart-symm-z has `.val.2 ≠ 0`.
  -- 3. Combine: `(squareLocalHomeomorph a hpY).symm (H.f.eval z) ≠ 0`.
  sorry

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
  unfold affineProjXCoeff
  by_cases hz : z ∈ ((affineChartProjX (H := H) a hpY) :
      OpenPartialHomeomorph (HyperellipticAffine H) ℂ).target
  · simp only [hz, if_true, Polynomial.smul_eval, smul_eq_mul]
    ring
  · simp [hz]

end Jacobians.ProjectiveCurve.HyperellipticAffine
