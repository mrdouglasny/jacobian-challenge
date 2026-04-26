/-
# Phase EA1 — `HyperellipticAffineInfinity` charted-space + manifold

`HyperellipticAffineInfinity H` is definitionally
`HyperellipticAffine (reverseData H h)` (per `Even.lean:155–170`,
where `reverseData H h` is the `HyperellipticData` packaging
`Polynomial.reverse H.f` with its squarefree and degree-≥-3 proofs).

So the entire affine atlas Codex built in
`OddAtlas/AffineChart.lean` (smooth-locus split, two
`OpenPartialHomeomorph` chart families via the implicit function
theorem, all four pairwise compatibility theorems, and the assembled
`ChartedSpace + IsManifold` instances) transfers verbatim through
`change ... infer_instance`. No copy-paste needed.

This file is therefore tiny — just two instance declarations forwarding
to the `HyperellipticAffine` versions via the definitional equality.

See `docs/hyperelliptic-even-atlas-plan.md` §EA1.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.OddAtlas.AffineChart
import Jacobians.ProjectiveCurve.Hyperelliptic.Even

namespace Jacobians.ProjectiveCurve.HyperellipticAffineInfinity

open scoped Manifold ContDiff Topology

variable {H : HyperellipticData}

/-- Charted-space instance on `HyperellipticAffineInfinity H` for
even-degree `H.f`, transferred from `HyperellipticAffine (reverseData H h)`
via the definitional equality. -/
noncomputable instance instChartedSpace (H : HyperellipticData)
    (h : ¬ Odd H.f.natDegree) :
    ChartedSpace ℂ (HyperellipticAffineInfinity H) := by
  let Hrev := HyperellipticAffineInfinity.reverseData H h
  change ChartedSpace ℂ (HyperellipticAffine Hrev)
  infer_instance

/-- Manifold instance on `HyperellipticAffineInfinity H` for
even-degree `H.f`, transferred from `HyperellipticAffine (reverseData H h)`
via the definitional equality. -/
noncomputable instance instIsManifold (H : HyperellipticData)
    (h : ¬ Odd H.f.natDegree) :
    IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticAffineInfinity H) := by
  let Hrev := HyperellipticAffineInfinity.reverseData H h
  change IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticAffine Hrev)
  infer_instance

end Jacobians.ProjectiveCurve.HyperellipticAffineInfinity
