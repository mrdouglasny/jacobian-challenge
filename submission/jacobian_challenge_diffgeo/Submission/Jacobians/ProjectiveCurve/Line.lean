/-
`ProjectiveLine` — the Riemann sphere `ℙ¹(ℂ)`, realized as the one-point
compactification of `ℂ` with its standard two-chart atlas.

Purpose: genus-0 worked example for Buzzard's challenge. Discharges Buzzard's
seven typeclass instances explicitly, without appealing to any abstract-X
infrastructure.

Mathlib already gives us the topology and the coarse separation/compactness/
connectedness facts (`OnePoint.CompactSpace`, `NormalSpace`, `ConnectedSpace`
for `OnePoint ℂ`). The complex-manifold structure (`ChartedSpace ℂ` + analytic
`IsManifold`) is **Kirov's**, imported from `KirovDolbeault.ProjectiveLine`.

See `docs/formalization-plan.md` §3.5.1.

API note: at the pinned Mathlib commit, `PartialHomeomorph` has been renamed
to `OpenPartialHomeomorph` (with the same fields + open-source/open-target).

## ℙ¹ unification (Option A, 2026-06-13)

`ProjectiveLine` and Kirov's `RiemannSphere` are **the same type**
(`OnePoint ℂ`). Previously each carried its *own* `ChartedSpace ℂ` /
`IsManifold` instance, producing a fragile instance diamond once the
axiom-free period-lattice route (K-LITE) pulled the port's ℙ¹ in
transitively. We now keep **one** instance — Kirov's — and make our chart
names thin aliases of his (`chart0 := chartCoe`, `chart1 := chartInfty`,
`chartAt := chartAtRS`). Importing `KirovDolbeault.ProjectiveLine` costs only
~15 light modules (its closure has no Serre/residue machinery). See
`docs/planning/OPTION_A_P1_UNIFICATION.md`.
-/
import Mathlib
import Submission.KirovDolbeault.ProjectiveLine

section
open scoped Manifold Topology
open scoped ContDiff -- for `ω` notation
open Complex Set OnePoint Topology

namespace Jacobians.ProjectiveCurve

/-- The Riemann sphere. We use `OnePoint ℂ` (= `ℂ ∪ {∞}`) as the carrier; it
already has a compact, Hausdorff, connected topology from Mathlib. The complex
manifold structure (`ChartedSpace ℂ` + analytic `IsManifold`) is **Kirov's**,
from `KirovDolbeault.ProjectiveLine` on `RiemannSphere = OnePoint ℂ`.

`abbrev` (not `def`) so that the coercion `(↑) : ℂ → OnePoint ℂ` and all
typeclass instances transfer transparently. -/
abbrev ProjectiveLine : Type := OnePoint ℂ

namespace ProjectiveLine

/-! ### Charts.

The Riemann sphere has the standard two-chart atlas; we reuse Kirov's
(`RiemannSphere.chartCoe`/`chartInfty`/`chartAtRS`) under our historical
names so the rest of our development is unchanged:
* `chart0 = chartCoe`  — the affine chart, identity on `ℂ ⊂ OnePoint ℂ`.
* `chart1 = chartInfty` — the chart at `∞`, `∞ ↦ 0` and `z ↦ 1/z`.
* `chartAt = chartAtRS` — the preferred chart selector.

Sharing the charts means we share the single `ChartedSpace ℂ` / `IsManifold`
instance from `KirovDolbeault.ProjectiveLine`; no instance is declared here. -/

/-- First chart: the affine chart, identity on the copy of `ℂ ⊂ OnePoint ℂ`.
Alias of Kirov's `RiemannSphere.chartCoe`. -/
@[reducible] noncomputable def chart0 : OpenPartialHomeomorph ProjectiveLine ℂ :=
  Jacobians.RiemannSphere.chartCoe

/-- Second chart: `∞ ↦ 0` and `z ↦ 1/z`. Alias of Kirov's
`RiemannSphere.chartInfty`. -/
@[reducible] noncomputable def chart1 : OpenPartialHomeomorph ProjectiveLine ℂ :=
  Jacobians.RiemannSphere.chartInfty

/-- The preferred chart at `p`. Alias of Kirov's `RiemannSphere.chartAtRS`
(`chartInfty` at `∞`, `chartCoe` on the finite part). -/
@[reducible] noncomputable def chartAt (p : ProjectiveLine) :
    OpenPartialHomeomorph ProjectiveLine ℂ :=
  Jacobians.RiemannSphere.chartAtRS p

/-- Stereographic projection `ProjectiveLine ≃ₜ S² ⊂ ℝ³`.

Derived from Mathlib's `onePointEquivSphereOfFinrankEq`, which gives a
homeomorphism between the one-point compactification of any finite-dimensional
real vector space `V` and the unit sphere in `EuclideanSpace ℝ ι` whenever
`finrank ℝ V + 1 = Fintype.card ι`. For `V := ℂ` (with `finrank ℝ ℂ = 2`) and
`ι := Fin 3`, the condition `2 + 1 = 3` holds.

This will give the `⇐` direction of `genus_eq_zero_iff_homeo` on
`ProjectiveLine` via transport of `Nonempty (ProjectiveLine ≃ₜ sphere …)`. -/
noncomputable def stereographic :
    ProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := ℂ) (by simp [Complex.finrank_real_complex])

end ProjectiveLine

end Jacobians.ProjectiveCurve

end  -- close the `section`
