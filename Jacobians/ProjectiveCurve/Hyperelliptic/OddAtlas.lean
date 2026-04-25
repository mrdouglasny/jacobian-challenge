/-
# HyperellipticOdd atlas — entry point (Phases OA3 + OA4)

Assembles `Phase OA1` (affine charts via implicit function theorem on
the smooth loci) and `Phase OA2` (chart at infinity via the local
uniformizer `t = y / x^{g+1}`) into:

* `instance : ChartedSpace ℂ (HyperellipticOdd H h)`
* `instance : IsManifold 𝓘(ℂ) ω (HyperellipticOdd H h)`

Once these compile, the two **temporary `axiom`s** at the top of
`Jacobians/Extensions/Hyperelliptic.lean` (OA4) can be deleted; instance
resolution picks up the real ones from this file.

See `docs/hyperelliptic-odd-atlas-plan.md`.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart
import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.InfinityChart

namespace Jacobians.ProjectiveCurve.HyperellipticOdd

open scoped Manifold ContDiff Topology

variable {H : HyperellipticData} {h : Odd H.f.natDegree}

/-- **Charted-space instance on `HyperellipticOdd H h`.** Combines:

* affine chart via `affineChartProjX` for points `(x, y)` with `y ≠ 0`
  pulled back through `OnePoint.openEmbedding_coe`;
* affine chart via `affineChartProjY` for points `(x, y)` with `y = 0`
  (necessarily `f'(x) ≠ 0`);
* `infinityChart` for the single added point `OnePoint.infty`. -/
noncomputable instance instChartedSpace (H : HyperellipticData) (h : Odd H.f.natDegree) :
    ChartedSpace ℂ (HyperellipticOdd H h) := by
  -- Combine the three chart families. `chartAt OnePoint.infty := infinityChart`;
  -- `chartAt ↑p` picks the appropriate affine chart by case on
  -- whether `p ∈ smoothLocusY` or `p ∈ smoothLocusX`.
  sorry

/-- **Manifold instance on `HyperellipticOdd H h`.** Verifies that all
pairwise chart transitions are analytic (`ContDiffOn ω`):

* `affineProjX × affineProjY` (Phase OA1, overlap where both `y ≠ 0`
  and `f'(x) ≠ 0`) — analytic by the implicit function theorem;
* `affine × infinity` (Phase OA2 compat lemma) — analytic via
  `t ↦ x(t) = 1 / (lc(f) · t²) (1 + O(t))`. -/
noncomputable instance instIsManifold (H : HyperellipticData) (h : Odd H.f.natDegree) :
    IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticOdd H h) := by
  -- Verify each transition is in `contDiffGroupoid ω 𝓘(ℂ)`.
  sorry

end Jacobians.ProjectiveCurve.HyperellipticOdd
