/-
# General-X route to property (P): analytic approximation ⟹ T-GEN (TGEN lane)

The **general-X** discharge of property **(P)** (`pi1AnalyticClasses x₀ = ⊤`,
`AnalyticPi1Generation.lean`), independent of the hyperelliptic /
branched-cover route (`CoveringGeneration.lean`). It rests on one named
Mathlib-absent topological fact — the **analytic-approximation wall** — and
glues it to T-GEN with elementary `FundamentalGroup` / `Path.Homotopic`
algebra that is fully proved here (sorry-free, standard-3 axioms only).

## The mathematics

A compact connected Riemann surface `X` is a complex 1-manifold, hence a
real-analytic manifold. The classical *Whitney analytic approximation*
theorem says every continuous map is homotopic (rel endpoints) to a
piecewise-real-analytic one:

  **(AAW)** every continuous loop `p : Path x₀ x₀` is `Path.Homotopic` to the
  underlying path `loopToPath γ` of some piecewise-real-analytic
  `γ : AnalyticLoop X x₀`.

References: Whitney, *Differentiable manifolds* (Ann. of Math. 1936) for the
smooth case; Grauert, *On Levi's problem and the imbedding of real-analytic
manifolds* (Ann. of Math. 1958) for the smooth → real-analytic upgrade. For a
1-dimensional path one does not need the analytic sheaf machinery: once a path
is piecewise-smooth one approximates it chart-locally by polynomials, and a
short geodesic homotopy in a tubular neighbourhood closes the loop rel
endpoints. The "piecewise" (finitely many corner points at the partition) is
essential: globally-analytic loops are not closed under concatenation and
cannot pin `p(0) = p(1) = x₀` across the `1 ∼ 0` junction (cf. the
`AnalyticArc.partition` design and the project's `IsAnalyticArcStrong`).

## Why this is the named wall, not a proof

Mathlib (mid-2026) supplies `Continuous.exists_contMDiff_approx_and_eqOn`
(uniform `C^n` approximation of a continuous map into a **normed space**, with
`EqOn` on a closed set), but **none** of: a manifold-target approximation, the
smooth → real-analytic homotopy, "`C⁰`-close maps into a manifold are
homotopic rel endpoints" (no tubular-neighbourhood API), nor "a continuous
loop has a smooth/analytic representative". The alternative routes
(triangulation = Radó, uniformization, Whitney embedding + tubular retraction)
each require an even larger absent block. So **(AAW)** is named here as the
single Mathlib-absent input, threaded as an explicit hypothesis to every
downstream theorem; nothing in this file is a `sorry` or an `axiom`.

This is the *general-X* twin of `CoveringGeneration.lean`'s
`CoveringGeneratesPi1` / `BranchCutGeneratesPi1` (which name the
hyperelliptic-specific covering-space wall). Either wall, once discharged,
feeds K0 (`analyticLoopsGenerateH1_of_pi1_closure`) to close T-GEN.

No new axiom; nothing depends on `AX_PeriodCycleBasis`.
-/
import Submission.Jacobians.RiemannSurface.AnalyticPi1Generation

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open scoped ContDiff
open Jacobians.Axioms (loopToPath)

noncomputable section

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

local notation "Qmk" => Path.Homotopic.Quotient.mk

/-! ## The named analytic-approximation wall (AAW) -/

/-- **Named residual (AAW) — the analytic-approximation wall, general X.**
Every continuous loop based at `x₀` is path-homotopic (rel endpoints) to the
underlying path of some piecewise-real-analytic loop. This is the
1-dimensional Whitney analytic approximation theorem specialised to loops; it
is the single Mathlib-absent input of the general-X route to T-GEN. -/
def ContinuousLoopHasAnalyticRep (x₀ : X) : Prop :=
  ∀ p : Path x₀ x₀, ∃ γ : AnalyticLoop X x₀, (loopToPath γ).Homotopic p

/-! ## Elementary glue: (AAW) ⟹ `loopToPi1` surjective ⟹ property (P) ⟹ T-GEN

Everything below is proved (no axiom, no `sorry`): pure
`FundamentalGroup` / `Path.Homotopic.Quotient` algebra. -/

/-- If a continuous loop `p` is homotopic to an analytic loop `γ`'s underlying
path, then `γ`'s π₁ class is exactly the class of `p`. -/
theorem loopToPi1_eq_fromPath_of_homotopic {x₀ : X} {p : Path x₀ x₀}
    {γ : AnalyticLoop X x₀} (h : (loopToPath γ).Homotopic p) :
    loopToPi1 γ = FundamentalGroup.fromPath (Qmk p) := by
  rw [loopToPi1]
  exact congrArg FundamentalGroup.fromPath (Path.Homotopic.Quotient.eq.mpr h)

/-- **(AAW) ⟹ `loopToPi1` surjective.** Under the analytic-approximation wall,
*every* π₁ class is the class of some analytic loop. -/
theorem loopToPi1_surjective_of_analyticRep {x₀ : X}
    (hAAW : ContinuousLoopHasAnalyticRep x₀) :
    Function.Surjective
      (loopToPi1 : AnalyticLoop X x₀ → FundamentalGroup X x₀) := by
  intro g
  -- `g = fromPath (toPath g)` and `toPath g = Qmk p` for some path `p`.
  obtain ⟨p, hp⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  obtain ⟨γ, hγ⟩ := hAAW p
  exact ⟨γ, by rw [loopToPi1_eq_fromPath_of_homotopic hγ, hp]⟩

/-- **(AAW) ⟹ property (P).** Under the analytic-approximation wall, the
analytic-loop classes generate `π₁(X, x₀)`: `pi1AnalyticClasses x₀ = ⊤`. -/
theorem pi1AnalyticClasses_eq_top_of_analyticRep {x₀ : X}
    (hAAW : ContinuousLoopHasAnalyticRep x₀) :
    pi1AnalyticClasses x₀ = ⊤ := by
  rw [pi1AnalyticClasses, (loopToPi1_surjective_of_analyticRep hAAW).range_eq,
    Subgroup.closure_univ]

/-- **(AAW) ⟹ T-GEN (general X).** The general-X discharge of the named
topological residual **T-GEN** (`AnalyticLoopsGenerateH1`): under the
analytic-approximation wall, the homology classes of piecewise-analytic loops
ℤ-span `H1 X x₀`. The wall (AAW) is the *only* input; the reduction is the K0
keystone bridge (`analyticLoopsGenerateH1_of_pi1_closure`). Axiom-free; no
`AX_PeriodCycleBasis`. -/
theorem analyticLoopsGenerateH1_of_analyticRep {x₀ : X}
    (hAAW : ContinuousLoopHasAnalyticRep x₀) :
    AnalyticLoopsGenerateH1 x₀ :=
  analyticLoopsGenerateH1_of_pi1_closure
    (pi1AnalyticClasses_eq_top_of_analyticRep hAAW)

end

end Jacobians.RiemannSurface
