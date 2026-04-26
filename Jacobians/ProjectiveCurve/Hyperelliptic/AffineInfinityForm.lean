/-
# Affine-infinity-side coefficients for hyperelliptic 1-forms

Mirror of `AffineForm.lean` for `HyperellipticAffineInfinity H`. Since
`HyperellipticAffineInfinity H` is **definitionally**
`HyperellipticAffine (HyperellipticAffineInfinity.reverseData H h)`
(per `EvenAtlas/InfinityAffineChart.lean`), the entire affine bundle
(`hyperellipticAffineCoeff` + analyticity + cocycle + off-target)
transfers verbatim by substituting the reversed `HyperellipticData`.

This file is a thin wrapper that exposes the transferred declarations
under names callers expect (`hyperellipticAffineInfinityCoeff` etc.).
No new mathematical content; just renames.

Geometric interpretation: the form `g_inf(u) du / v` on the
affine-infinity chart, where `(u, v) = (1/x, y / x^(g+1))` are the
affine-infinity coordinates and `g_inf` is an arbitrary polynomial.
The relation between `g_inf` and the affine-side polynomial
`g_aff` (so that the two forms agree on the gluing region) is the
content of S5 (cross-summand cocycle).
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.AffineForm
import Jacobians.ProjectiveCurve.Hyperelliptic.EvenAtlas.InfinityAffineChart

namespace Jacobians.ProjectiveCurve.HyperellipticAffineInfinity

open scoped Manifold ContDiff Topology
open Polynomial
open Jacobians.RiemannSurface

variable {H : HyperellipticData}

/-- Affine-infinity-side coefficient family for a form `g(u) du / v` on
the affine-infinity chart. Defined by transfer from the affine bundle
applied to the reversed `HyperellipticData`. -/
noncomputable def hyperellipticAffineInfinityCoeff
    [hf : Fact (¬ Odd H.f.natDegree)] (g : Polynomial ℂ) :
    HyperellipticAffineInfinity H → ℂ → ℂ :=
  Jacobians.ProjectiveCurve.HyperellipticAffine.hyperellipticAffineCoeff
    (H := HyperellipticAffineInfinity.reverseData H hf.out) g

/-- The affine-infinity coefficient family is analytic on each chart target. -/
theorem hyperellipticAffineInfinityCoeff_isHolomorphicOneFormCoeff
    [hf : Fact (¬ Odd H.f.natDegree)] (g : Polynomial ℂ) :
    IsHolomorphicOneFormCoeff (HyperellipticAffineInfinity H)
      (hyperellipticAffineInfinityCoeff (H := H) g) :=
  Jacobians.ProjectiveCurve.HyperellipticAffine.hyperellipticAffineCoeff_isHolomorphicOneFormCoeff
    (H := HyperellipticAffineInfinity.reverseData H hf.out) g

/-- The affine-infinity coefficient family vanishes off each chart target. -/
theorem hyperellipticAffineInfinityCoeff_isZeroOffChartTarget
    [hf : Fact (¬ Odd H.f.natDegree)] (g : Polynomial ℂ) :
    IsZeroOffChartTarget (HyperellipticAffineInfinity H)
      (hyperellipticAffineInfinityCoeff (H := H) g) :=
  Jacobians.ProjectiveCurve.HyperellipticAffine.hyperellipticAffineCoeff_isZeroOffChartTarget
    (H := HyperellipticAffineInfinity.reverseData H hf.out) g

/-- The affine-infinity coefficient family satisfies the cotangent cocycle on chart overlaps. -/
theorem hyperellipticAffineInfinityCoeff_satisfiesCotangentCocycle
    [hf : Fact (¬ Odd H.f.natDegree)] (g : Polynomial ℂ) :
    SatisfiesCotangentCocycle (HyperellipticAffineInfinity H)
      (hyperellipticAffineInfinityCoeff (H := H) g) :=
  Jacobians.ProjectiveCurve.HyperellipticAffine.hyperellipticAffineCoeff_satisfiesCotangentCocycle
    (H := HyperellipticAffineInfinity.reverseData H hf.out) g

/-- Bundled membership: `hyperellipticAffineInfinityCoeff g` is in the
holomorphic-one-form submodule of `HyperellipticAffineInfinity H`. -/
theorem hyperellipticAffineInfinityCoeff_mem_submodule
    [hf : Fact (¬ Odd H.f.natDegree)] (g : Polynomial ℂ) :
    hyperellipticAffineInfinityCoeff (H := H) g ∈
      holomorphicOneFormSubmodule (HyperellipticAffineInfinity H) :=
  Jacobians.ProjectiveCurve.HyperellipticAffine.hyperellipticAffineCoeff_mem_submodule
    (H := HyperellipticAffineInfinity.reverseData H hf.out) g

end Jacobians.ProjectiveCurve.HyperellipticAffineInfinity
