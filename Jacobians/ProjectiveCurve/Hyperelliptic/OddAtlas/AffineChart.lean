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
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic

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
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hpY : p.val.2 ≠ 0
  · exact Or.inl hpY
  · right
    have hpY0 : p.val.2 = 0 := by
      simpa using hpY
    have hf_ne : H.f ≠ 0 := by
      intro h0
      have hdeg := H.h_degree
      rw [h0, Polynomial.natDegree_zero] at hdeg
      omega
    have hroot_eval : H.f.eval p.val.1 = 0 := by
      have htmp : (0 : ℂ) = H.f.eval p.val.1 := by
        simpa [hpY0] using p.property
      exact htmp.symm
    have hroot : H.f.IsRoot p.val.1 := Polynomial.IsRoot.def.mpr hroot_eval
    by_contra hpX
    change ¬ ((Polynomial.derivative H.f).eval p.val.1 ≠ 0) at hpX
    have hpX0 : H.f.derivative.eval p.val.1 = 0 := by
      simpa using hpX
    have hrootder : H.f.derivative.IsRoot p.val.1 := Polynomial.IsRoot.def.mpr hpX0
    have hmult : 1 < H.f.rootMultiplicity p.val.1 := by
      rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hf_ne]
      exact ⟨hroot, hrootder⟩
    have hsq_dvd : (Polynomial.X - Polynomial.C p.val.1) ^ 2 ∣ H.f := by
      rw [← Polynomial.le_rootMultiplicity_iff hf_ne]
      omega
    have hsq_dvd' :
        (Polynomial.X - Polynomial.C p.val.1) *
          (Polynomial.X - Polynomial.C p.val.1) ∣ H.f := by
      simpa [pow_two] using hsq_dvd
    have hirr : Irreducible (Polynomial.X - Polynomial.C p.val.1 : Polynomial ℂ) :=
      Polynomial.irreducible_X_sub_C p.val.1
    have hsqfree :=
      (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hf_ne).1 H.h_squarefree
    exact hsqfree _ hirr hsq_dvd'

/-- **The `(x, y) ↦ x` chart on `smoothLocusY`.** Returns a
`PartialHomeomorph (HyperellipticAffine H) ℂ` whose source is a
neighborhood of `p` in `smoothLocusY` and whose target is a
neighborhood of `p.val.1` in `ℂ`.

Construction: at a point `(x₀, y₀)` with `y₀ ≠ 0`, the function
`F(x, y) := y² - f(x)` has `∂F/∂y = 2y₀ ≠ 0`, so the implicit function
theorem yields an analytic local inverse `x ↦ (x, y(x))` near `x₀`. -/
axiom affineChartProjX (p : HyperellipticAffine H)
    (_hp : p ∈ smoothLocusY H) :
    OpenPartialHomeomorph (HyperellipticAffine H) ℂ

/-- The `(x, y) ↦ y` chart on `smoothLocusX`, dual to `affineChartProjX`. -/
axiom affineChartProjY (p : HyperellipticAffine H)
    (_hp : p ∈ smoothLocusX H) :
    OpenPartialHomeomorph (HyperellipticAffine H) ℂ

/-- **Affine `ChartedSpace` instance.** Combine the two chart families
above; `chartAt p` chooses `affineChartProjX p hp` if `p ∈ smoothLocusY`,
otherwise `affineChartProjY p hp`. -/
axiom affine_chartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (HyperellipticAffine H)

attribute [instance] affine_chartedSpace

end Jacobians.ProjectiveCurve.HyperellipticAffine
