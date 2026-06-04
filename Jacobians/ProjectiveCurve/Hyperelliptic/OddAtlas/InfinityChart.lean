/-
# Phase OA2 — Chart at infinity on `HyperellipticOdd H h`

In the odd-degree case `deg f = 2g + 1`, the smooth model
`HyperellipticOdd H h := OnePoint (HyperellipticAffine H)` has a single
point at infinity, which is also a **branch point** of the
hyperelliptic projection `(x, y) ↦ x`.

The standard chart at infinity uses the uniformizer `t := y / x^{g+1}`.
Near `t = 0`, on the curve `y² = f(x)` with `deg f = 2g + 1`:
* `x = 1 / (lc(f) · t²) · (1 + O(t))` (where `lc(f)` is the leading
  coefficient);
* `y = 1 / (lc(f)^{(2g+1)/2} · t^{2g+1}) · (1 + O(t))`.

So the inverse `t ↦ (x(t), y(t))` is an analytic bijection from a
punctured disk `0 < |t| < ε` onto a punctured neighborhood of `∞`,
extending continuously by `t = 0 ↦ OnePoint.infty`.

## Mathlib API

* `OnePoint.openEmbedding_coe : OpenEmbedding ((↑) : X → OnePoint X)` —
  affine charts pull back to `OnePoint X` for points coming from `X`.
* `OnePoint.continuous_iff_continuousAt_infty` — for verifying
  continuity at `∞`.
* No general "chart at the added point" lemma in Mathlib; we construct
  the `PartialHomeomorph` by hand.

See `docs/hyperelliptic-odd-atlas-plan.md` §OA2.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff Topology
open OnePoint

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- The local inverse `t ↦ (x(t), y(t))` on a punctured disk near
`t = 0`, mapping into `HyperellipticAffine H`. Concretely, with
`g := (deg f - 1) / 2`, we have `x = 1/t²·(1 + O(t))` and
`y = 1/t^{2g+1}·(1 + O(t))` after normalizing by `lc(f)`. Domain:
`{ t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < someRadius }`. -/
axiom infinityInverseMap (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ℂ → HyperellipticAffine H

/-- The chart at infinity: `PartialHomeomorph (HyperellipticOdd H h) ℂ`
sending a neighborhood of `OnePoint.infty` to a neighborhood of
`0 ∈ ℂ`, with `OnePoint.infty ↦ 0`.

The forward map (going `HyperellipticOdd → ℂ`) is `(x, y) ↦ y / x^{g+1}`
on the affine part where `x ≠ 0`, extended by `infty ↦ 0`. The inverse
map is `infinityInverseMap` extended by `0 ↦ infty`. -/
axiom infinityChart (H : HyperellipticData) (h : Odd H.f.natDegree) :
    OpenPartialHomeomorph (HyperellipticOdd H h) ℂ

/-- The infinity chart is defined at the point `∞`. -/
axiom infinityChart_mem_source (H : HyperellipticData) (h : Odd H.f.natDegree) :
    (∞ : HyperellipticOdd H h) ∈ (infinityChart H h).source

/-- Remaining OA2 local boundary: infinity chart followed by the lifted affine `x`-chart. -/
axiom infinityChart_compat_affineLiftProjX
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) : ℂ → ℂ)
      ((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source

/-- Remaining OA2 local boundary: the lifted affine `x`-chart followed by the infinity chart. -/
axiom affineLiftProjX_compat_infinityChart
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpY : p ∈ HyperellipticAffine.smoothLocusY H) :
    ContDiffOn ℂ ω
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) : ℂ → ℂ)
      ((((HyperellipticAffine.affineChartProjX (H := H) p hpY).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source

/-- Remaining OA2 local boundary: infinity chart followed by the lifted affine `y`-chart. -/
axiom infinityChart_compat_affineLiftProjY
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpX : p ∈ HyperellipticAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      (((infinityChart H h).symm.trans
          ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
            (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))) : ℂ → ℂ)
      ((infinityChart H h).symm.trans
        ((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H)))).source

/-- Remaining OA2 local boundary: the lifted affine `y`-chart followed by the infinity chart. -/
axiom affineLiftProjY_compat_infinityChart
    (H : HyperellipticData) (h : Odd H.f.natDegree) (p : HyperellipticAffine H)
    (hpX : p ∈ HyperellipticAffine.smoothLocusX H) :
    ContDiffOn ℂ ω
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h)) : ℂ → ℂ)
      ((((HyperellipticAffine.affineChartProjY (H := H) p hpX).lift_openEmbedding
          (OnePoint.isOpenEmbedding_coe (X := HyperellipticAffine H))).symm.trans
          (infinityChart H h))).source

end Jacobians.ProjectiveCurve.HyperellipticOdd
