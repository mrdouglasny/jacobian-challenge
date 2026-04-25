/-
# Phase OA1 — Affine smooth-locus charts on `HyperellipticAffine H`

Builds two families of `PartialHomeomorph`s on `HyperellipticAffine H`:
* `affineChartProjX` — chart `(x, y) ↦ x`, valid where `y ≠ 0`.
* `affineChartProjY` — chart `(x, y) ↦ y`, valid where `f'(x) ≠ 0`
  (equivalently, where `(x, 0)` is a simple root of `f` — the
  "branch points" of the hyperelliptic projection).

Squarefreeness of `f` ⇒ at every affine point, at least one of these
is well-defined; together they cover `HyperellipticAffine H`.

## Mathlib API

* `Mathlib.Analysis.Calculus.InverseFunctionTheorem` — extracts
  `PartialHomeomorph` from a smooth bijection with invertible
  differential.
* `Polynomial.IsRoot`, `Polynomial.derivative`, `Polynomial.squarefree_iff_no_repeated_roots`
  — for the squarefree-implies-`f'(α) ≠ 0` argument at roots.

See `docs/hyperelliptic-odd-atlas-plan.md` §OA1.
-/

import Jacobians.ProjectiveCurve.Hyperelliptic.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace Jacobians.ProjectiveCurve.HyperellipticAffine

open scoped Manifold ContDiff Topology

variable {H : HyperellipticData}

/-- The smooth locus where the projection `(x, y) ↦ x` is a local chart:
the set of points `(x, y)` with `y ≠ 0`. Open in `HyperellipticAffine H`. -/
def smoothLocusY (H : HyperellipticData) : Set (HyperellipticAffine H) :=
  { p | p.val.2 ≠ 0 }

/-- The smooth locus where the projection `(x, y) ↦ y` is a local chart:
the set of points `(x, y)` with `f'(x) ≠ 0` (equivalently, `(x, 0)` is
a simple root of `f`). Open in `HyperellipticAffine H`. -/
def smoothLocusX (H : HyperellipticData) : Set (HyperellipticAffine H) :=
  { p | (Polynomial.derivative H.f).eval p.val.1 ≠ 0 }

/-- **Squarefree ⇒ smooth locus covers everything.** Every point of
`HyperellipticAffine H` lies in `smoothLocusY ∪ smoothLocusX`. -/
theorem smoothLocus_cover (H : HyperellipticData) :
    smoothLocusY H ∪ smoothLocusX H = Set.univ := by
  -- At any point (x₀, y₀) with y₀² = f(x₀):
  -- if y₀ ≠ 0 then (x₀, y₀) ∈ smoothLocusY;
  -- if y₀ = 0 then f(x₀) = 0, and squarefreeness ⇒ f'(x₀) ≠ 0,
  -- so (x₀, y₀) ∈ smoothLocusX.
  sorry

/-- **The `(x, y) ↦ x` chart on `smoothLocusY`.** Returns a
`PartialHomeomorph (HyperellipticAffine H) ℂ` whose source is a
neighborhood of `p` in `smoothLocusY` and whose target is a
neighborhood of `p.val.1` in `ℂ`.

Construction: at a point `(x₀, y₀)` with `y₀ ≠ 0`, the function
`F(x, y) := y² - f(x)` has `∂F/∂y = 2y₀ ≠ 0`, so the implicit function
theorem yields an analytic local inverse `x ↦ (x, y(x))` near `x₀`. -/
noncomputable def affineChartProjX (p : HyperellipticAffine H)
    (_hp : p ∈ smoothLocusY H) :
    PartialHomeomorph (HyperellipticAffine H) ℂ := by
  -- Use `ContDiffAt.toPartialHomeomorph` on the projection
  -- `(x, y) ↦ x`, with non-degeneracy provided by `2y₀ ≠ 0`.
  sorry

/-- The `(x, y) ↦ y` chart on `smoothLocusX`, dual to `affineChartProjX`. -/
noncomputable def affineChartProjY (p : HyperellipticAffine H)
    (_hp : p ∈ smoothLocusX H) :
    PartialHomeomorph (HyperellipticAffine H) ℂ := by
  sorry

/-- **Affine `ChartedSpace` instance.** Combine the two chart families
above; `chartAt p` chooses `affineChartProjX p hp` if `p ∈ smoothLocusY`,
otherwise `affineChartProjY p hp`. -/
noncomputable instance affine_chartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (HyperellipticAffine H) := by
  sorry

end Jacobians.ProjectiveCurve.HyperellipticAffine
