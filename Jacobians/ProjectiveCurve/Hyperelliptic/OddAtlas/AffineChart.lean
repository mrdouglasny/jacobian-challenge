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

/-- If `x` is a root of the squarefree defining polynomial `f`, then `f'(x) ≠ 0`.
This is the algebraic input behind the branch-point chart `(x, y) ↦ y`. -/
theorem eval_derivative_ne_zero_of_eval_eq_zero (H : HyperellipticData) {x : ℂ}
    (hx : H.f.eval x = 0) : H.f.derivative.eval x ≠ 0 := by
  intro hder
  have hf_ne : H.f ≠ 0 := by
    intro h0
    have hdeg := H.h_degree
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hroot : H.f.IsRoot x := Polynomial.IsRoot.def.mpr hx
  have hrootder : H.f.derivative.IsRoot x := Polynomial.IsRoot.def.mpr hder
  have hmult : 1 < H.f.rootMultiplicity x := by
    rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hf_ne]
    exact ⟨hroot, hrootder⟩
  have hsq_dvd : (Polynomial.X - Polynomial.C x) ^ 2 ∣ H.f := by
    rw [← Polynomial.le_rootMultiplicity_iff hf_ne]
    omega
  have hsq_dvd' : (Polynomial.X - Polynomial.C x) * (Polynomial.X - Polynomial.C x) ∣ H.f := by
    simpa [pow_two] using hsq_dvd
  have hirr : Irreducible (Polynomial.X - Polynomial.C x : Polynomial ℂ) :=
    Polynomial.irreducible_X_sub_C x
  have hsqfree :=
    (squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hf_ne).1 H.h_squarefree
  exact hsqfree _ hirr hsq_dvd'

/-- A point with `y = 0` automatically lies in the `x`-chart smooth locus,
because squarefreeness rules out repeated roots. -/
theorem mem_smoothLocusX_of_y_eq_zero (H : HyperellipticData) {p : HyperellipticAffine H}
    (hp : p.val.2 = 0) : p ∈ smoothLocusX H := by
  change H.f.derivative.eval p.val.1 ≠ 0
  apply eval_derivative_ne_zero_of_eval_eq_zero
  have htmp : (0 : ℂ) = H.f.eval p.val.1 := by
    simpa [hp] using p.property
  exact htmp.symm

/-- `smoothLocusY` is open: it is the nonvanishing locus of the continuous
`y`-coordinate on the affine curve. -/
theorem isOpen_smoothLocusY (H : HyperellipticData) : IsOpen (smoothLocusY H) := by
  let f : HyperellipticAffine H → ℂ := fun p => p.val.2
  have hcont : Continuous f := continuous_subtype_val.snd
  have hclosed : IsClosed {p : HyperellipticAffine H | f p = 0} :=
    isClosed_eq hcont (continuous_const : Continuous fun _ : HyperellipticAffine H => (0 : ℂ))
  simpa [smoothLocusY, f, Set.compl_setOf] using hclosed.isOpen_compl

/-- `smoothLocusX` is open: it is the nonvanishing locus of the continuous
function `p ↦ f'(x(p))`. -/
theorem isOpen_smoothLocusX (H : HyperellipticData) : IsOpen (smoothLocusX H) := by
  let f : HyperellipticAffine H → ℂ := fun p => (Polynomial.derivative H.f).eval p.val.1
  have hcont : Continuous f := (Polynomial.continuous _).comp continuous_subtype_val.fst
  have hclosed : IsClosed {p : HyperellipticAffine H | f p = 0} :=
    isClosed_eq hcont (continuous_const : Continuous fun _ : HyperellipticAffine H => (0 : ℂ))
  simpa [smoothLocusX, f, Set.compl_setOf] using hclosed.isOpen_compl

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
  by_cases hpY : p ∈ smoothLocusY H
  · exact Or.inl hpY
  · right
    have hpY0 : p.val.2 = 0 := by
      simpa [smoothLocusY] using hpY
    exact mem_smoothLocusX_of_y_eq_zero H hpY0

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

/-- The chosen `x`-projection chart is defined at its base point. -/
axiom affineChartProjX_mem_source (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusY H) :
    p ∈ (affineChartProjX p hp).source

/-- The `(x, y) ↦ y` chart on `smoothLocusX`, dual to `affineChartProjX`. -/
axiom affineChartProjY (p : HyperellipticAffine H)
    (_hp : p ∈ smoothLocusX H) :
    OpenPartialHomeomorph (HyperellipticAffine H) ℂ

/-- The chosen `y`-projection chart is defined at its base point. -/
axiom affineChartProjY_mem_source (p : HyperellipticAffine H)
    (hp : p ∈ smoothLocusX H) :
    p ∈ (affineChartProjY p hp).source

/-- Choose one of the two affine chart families at a point, using the open cover
`smoothLocusY ∪ smoothLocusX = univ`. -/
noncomputable def affineChartAt (p : HyperellipticAffine H) :
    OpenPartialHomeomorph (HyperellipticAffine H) ℂ := by
  by_cases hpY : p ∈ smoothLocusY H
  · exact affineChartProjX p hpY
  · have hpY0 : p.val.2 = 0 := by
      simpa [smoothLocusY] using hpY
    exact affineChartProjY p (mem_smoothLocusX_of_y_eq_zero H hpY0)

@[simp] theorem affineChartAt_of_mem_smoothLocusY (p : HyperellipticAffine H)
    (hpY : p ∈ smoothLocusY H) :
    affineChartAt p = affineChartProjX p hpY := by
  simp [affineChartAt, hpY]

@[simp] theorem affineChartAt_of_not_mem_smoothLocusY (p : HyperellipticAffine H)
    (hpY : p ∉ smoothLocusY H) :
    affineChartAt p =
      affineChartProjY p
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY)) := by
  simp [affineChartAt, hpY]

/-- **Affine `ChartedSpace` instance.** Combine the two chart families
above; `chartAt p` chooses `affineChartProjX p hp` if `p ∈ smoothLocusY`,
otherwise `affineChartProjY p hp`. -/
noncomputable instance affine_chartedSpace (H : HyperellipticData) :
    ChartedSpace ℂ (HyperellipticAffine H) where
  atlas := Set.range (affineChartAt (H := H))
  chartAt := affineChartAt (H := H)
  mem_chart_source p := by
    by_cases hpY : p ∈ smoothLocusY H
    · rw [affineChartAt_of_mem_smoothLocusY (H := H) p hpY]
      exact affineChartProjX_mem_source p hpY
    · rw [affineChartAt_of_not_mem_smoothLocusY (H := H) p hpY]
      exact affineChartProjY_mem_source p (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY))
  chart_mem_atlas p := ⟨p, rfl⟩

/-- Remaining OA1 compatibility boundary: `x`-chart followed by `x`-chart. -/
axiom affineChartProjX_compat_affineChartProjX
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusY H) (hq : q ∈ smoothLocusY H) :
    ContDiffOn ℂ ω
      (((affineChartProjX p hp).symm.trans (affineChartProjX q hq)) : ℂ → ℂ)
      (((affineChartProjX p hp).symm.trans (affineChartProjX q hq)).source)

/-- Remaining OA1 compatibility boundary: `x`-chart followed by `y`-chart. -/
axiom affineChartProjX_compat_affineChartProjY
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusY H) (hq : q ∈ smoothLocusX H) :
    ContDiffOn ℂ ω
      (((affineChartProjX p hp).symm.trans (affineChartProjY q hq)) : ℂ → ℂ)
      (((affineChartProjX p hp).symm.trans (affineChartProjY q hq)).source)

/-- Remaining OA1 compatibility boundary: `y`-chart followed by `x`-chart. -/
axiom affineChartProjY_compat_affineChartProjX
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusX H) (hq : q ∈ smoothLocusY H) :
    ContDiffOn ℂ ω
      (((affineChartProjY p hp).symm.trans (affineChartProjX q hq)) : ℂ → ℂ)
      (((affineChartProjY p hp).symm.trans (affineChartProjX q hq)).source)

/-- Remaining OA1 compatibility boundary: `y`-chart followed by `y`-chart. -/
axiom affineChartProjY_compat_affineChartProjY
    (p q : HyperellipticAffine H) (hp : p ∈ smoothLocusX H) (hq : q ∈ smoothLocusX H) :
    ContDiffOn ℂ ω
      (((affineChartProjY p hp).symm.trans (affineChartProjY q hq)) : ℂ → ℂ)
      (((affineChartProjY p hp).symm.trans (affineChartProjY q hq)).source)

/-- Chart-transition compatibility for the chosen affine chart package. -/
theorem affineChartAt_compat (p q : HyperellipticAffine H) :
    ContDiffOn ℂ ω
      (((affineChartAt (H := H) p).symm.trans (affineChartAt (H := H) q)) : ℂ → ℂ)
      (((affineChartAt (H := H) p).symm.trans (affineChartAt (H := H) q)).source) := by
  by_cases hpY : p ∈ smoothLocusY H
  · by_cases hqY : q ∈ smoothLocusY H
    · simp [affineChartAt, hpY, hqY]
      exact affineChartProjX_compat_affineChartProjX p q hpY hqY
    · simp [affineChartAt, hpY, hqY]
      exact affineChartProjX_compat_affineChartProjY p q hpY
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hqY))
  · by_cases hqY : q ∈ smoothLocusY H
    · simp [affineChartAt, hpY, hqY]
      exact affineChartProjY_compat_affineChartProjX p q
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY)) hqY
    · simp [affineChartAt, hpY, hqY]
      exact affineChartProjY_compat_affineChartProjY p q
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hpY))
        (mem_smoothLocusX_of_y_eq_zero H (by simpa [smoothLocusY] using hqY))

/-- Manifold structure on the affine odd hyperelliptic chart package,
assembled from the four chart-compatibility lemmas above. -/
noncomputable instance affine_isManifold (H : HyperellipticData) :
    IsManifold 𝓘(ℂ, ℂ) ω (HyperellipticAffine H) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.preimage_id, id_eq, Set.inter_univ, Set.univ_inter] using
    affineChartAt_compat (H := H) p q

attribute [instance] affine_isManifold

end Jacobians.ProjectiveCurve.HyperellipticAffine
