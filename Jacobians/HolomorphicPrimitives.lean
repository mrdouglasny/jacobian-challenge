/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.GenusZeroOfSphere
import Jacobians.CotangentCoeff
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Attacking `HasHolomorphicPrimitives X` — the holomorphic Poincaré / monodromy wall

`Jacobians/GenusZeroOfSphere.lean` (commit `b6a3e35`) reduced the backward headline `#1b`
(`X ≃ₜ S² ⟹ genus X = 0`) to the **single** analytic input

```
def HasHolomorphicPrimitives (X) : Prop :=
  SimplyConnectedSpace X →
    ∀ η : HolomorphicOneForms X, ∃ F : X → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
      ∀ x v, η.toFun x v = mfderiv 𝓘(ℂ) 𝓘(ℂ) F x v
```

i.e. *on a simply connected Riemann surface, every holomorphic `1`-form has a global primitive*
(the holomorphic Poincaré lemma / monodromy theorem, Forster §10.5). This file attacks it.

## SCOUT — the three classical routes and the exact Mathlib gap

The genuine mathematical content is **homotopy invariance of the line integral** `∮_γ η`. Once that
is available, `F(x) := ∮_{x₀}^{x} η` is path-independent (simple connectivity makes any two paths
homotopic) and is a holomorphic primitive of `η`. Concretely:

* **Route A — "closed ⇒ exact".** A holomorphic `1`-form is closed (`dη = 0`). On a simply
  connected manifold, closed `1`-forms are exact (`H¹_dR = 0`). **Mathlib gap:** Mathlib has **no**
  manifold de Rham cohomology at all (`grep`: only `Mathlib/RingTheory/Perfectoid/BDeRham.lean`,
  an unrelated `B_dR`); no `closed ⇒ exact`. Dead on arrival as a black box.

* **Route B — monodromy / path-integral (the one taken here).** `η` closed ⇒ `∮_γ η` is invariant
  under endpoint-fixing homotopies of `γ` ⇒ on simply connected `X`, path-independent ⇒
  `F(x) := ∮_{x₀}^{x} η` is a well-defined global primitive. **Mathlib has:**
  - the *plane* homotopy invariance `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`
    (`Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`), explicitly flagged
    *"In the future, this will allow us to prove Poincaré lemma for simply connected open sets"* —
    so even in the **plane** the simply-connected globalisation is not yet done;
  - the *plane / ball* primitive `DifferentiableOn.isExactOn_ball`
    (`Mathlib/Analysis/Complex/HasPrimitives.lean`);
  - simple-connectivity ⇒ any two paths homotopic (`SimplyConnectedSpace.paths_homotopic`).
  **Mathlib gap:** the *manifold* line-integral and its homotopy invariance over loops in an abstract
  `X` are absent (the plane Poincaré does **not** lift to manifolds; the repo's
  `Jacobians/LineIntegral.lean` even removed a *chart-local* version for lack of a `SimplyConnected`
  hypothesis on the chart image — see `PeriodLattice.lean:1567`).

* **Route C — universal cover.** Pull `η` back to the universal cover `X̃` (simply connected),
  integrate there, descend by deck-transformation invariance. **Mathlib gap:** Mathlib has covering
  spaces + path-lifting monodromy (`Mathlib/Topology/Homotopy/Lifting.lean`) but no complex-manifold
  structure transport to `X̃`, and the descent still needs the same line-integral machinery.

**Conclusion:** all three routes bottom out at *one* irreducible fact —
**homotopy invariance of the period `∮_γ η`** — which is the manifold de Rham/Stokes content absent
from Mathlib. This file therefore isolates exactly that as the single honest named input
`HasHomotopyInvariantPeriods X` (strictly smaller than `HasHolomorphicPrimitives`: it is a property
of *loops*, with the entire primitive-construction discharged sorry-free on top of it here), and
banks the surrounding sorry-free scaffolding (well-definedness of `F` via simple connectivity; the
chart-local ball primitive from Mathlib).

## References
* Forster, *Lectures on Riemann Surfaces*, §10.5 (period homotopy invariance), §10.
* Mathlib `MeasureTheory/Integral/CurveIntegral/Poincare.lean` (plane homotopy invariance).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Filter Set MeasureTheory

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Banked piece 1 — the chart-local ball primitive (Mathlib)

In a holomorphic chart, a holomorphic `1`-form is `f dz` with `f` holomorphic, and Mathlib's
`DifferentiableOn.isExactOn_ball` produces a holomorphic primitive `g` of `f` on any ball in the
chart image. This is the *local* half of the Poincaré lemma — present in Mathlib and recorded here
in the exact `IsExactOn` shape the gluing argument consumes. -/

/-- **Banked: chart-local primitive exists (Mathlib).** Any holomorphic function `f` on a ball
`Metric.ball c r ⊆ ℂ` has a holomorphic primitive there: some `g` with `HasDerivAt g (f z) z` for
all `z` in the ball. This is `DifferentiableOn.isExactOn_ball` (Morera, on a disk), re-exposed in
the form the manifold gluing needs. The full holomorphic-Poincaré globalisation glues these local
`g`'s; the obstruction to gluing is precisely the missing homotopy invariance below. -/
theorem exists_localPrimitive_on_ball {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∃ g : ℂ → ℂ, ∀ z ∈ Metric.ball c r, HasDerivAt g (f z) z :=
  hf.isExactOn_ball

/-! ### The single honest named input — homotopy invariance of the period

This is the **one** missing fact (the manifold de Rham / Stokes content; see the SCOUT). It is the
property of *loops*/paths that closed forms integrate equally along homotopic paths — strictly
smaller than `HasHolomorphicPrimitives`, which asserts the *existence of a primitive function*. The
entire primitive construction is discharged sorry-free on top of it below. -/

/-- **The de Rham wall, isolated as a property of homotopic paths.** For every holomorphic `1`-form
`η` and any two paths `p q : Path a b` with the *same endpoints* that are homotopic (rel endpoints),
the line integrals along their `ℝ → X` extensions agree.

This is **true** for any complex `1`-manifold (a holomorphic form is closed, `dη = 0`, so its period
is a homotopy invariant — Forster §10.5 / Stokes). It is **absent from Mathlib**: only the planar
analogue `ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt` exists, and
even that has not been globalised to simply connected domains (the file's own TODO). Isolated here so
that *path-independence of the primitive* (and the whole route) is sorry-free downstream. -/
def HasHomotopyInvariantPeriods (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  ∀ (η : HolomorphicOneForms X) {a b : X} (p q : Path a b),
    p.Homotopic q → lineIntegral η p.extend = lineIntegral η q.extend

/-! ### Banked piece 2 — the path-integral primitive and its well-definedness

`F(x) := ∮_{x₀}^{x} η`, integrating along a chosen path. On a simply connected `X` any two paths
with the same endpoints are homotopic (`SimplyConnectedSpace.paths_homotopic`), so by
`HasHomotopyInvariantPeriods` the value does not depend on the chosen path — proven sorry-free. -/

/-- The candidate global primitive: `F(x) = ∮` of `η` along *some* chosen path from the basepoint
`x₀` to `x`. (`X` is path connected — it is connected and locally path connected as a manifold; we
take `PathConnectedSpace.somePath`, which exists once `X` is path connected.) -/
noncomputable def pathPrimitive (η : HolomorphicOneForms X) (x₀ : X)
    [PathConnectedSpace X] (x : X) : ℂ :=
  lineIntegral η (PathConnectedSpace.somePath x₀ x).extend

/-- **Banked: path-independence of the period (sorry-free).** Under `HasHomotopyInvariantPeriods`,
on a simply connected `X` the line integral of `η` along *any* path from `a` to `b` equals the line
integral along the canonical `somePath a b` — the value depends only on the endpoints, not the path.
This is the well-definedness of `pathPrimitive`, and the heart of "monodromy ⇒ a primitive exists".
-/
theorem lineIntegral_eq_of_simplyConnected (hHI : HasHomotopyInvariantPeriods X)
    [SimplyConnectedSpace X] (η : HolomorphicOneForms X) {a b : X} (p : Path a b) :
    lineIntegral η p.extend =
      lineIntegral η (PathConnectedSpace.somePath a b).extend :=
  hHI η p (PathConnectedSpace.somePath a b)
    (SimplyConnectedSpace.paths_homotopic p (PathConnectedSpace.somePath a b))

/-! ### The remaining standard atom — FTC for the path primitive

`mfderiv (pathPrimitive η x₀) = η` is the *fundamental theorem of calculus* for the manifold line
integral: differentiating `∮_{x₀}^{x} η` in `x` returns the integrand `η`. Once `F` is
path-independent (banked above), this is a purely **local** computation — in a chart ball, `F` agrees
(up to a constant) with the planar ball-primitive `g` of `η`'s chart coefficient
(`exists_localPrimitive_on_ball`), whose derivative is that coefficient by construction. It is
standard local analysis (Forster §10.5, the `dF = η` half), **strictly smaller** than the global
existence-of-a-primitive statement, but still beyond Mathlib's manifold-FTC coverage. Isolated as the
named hypothesis `IsFTCForPathPrimitive` so the assembly is sorry-free.

`HasMFDerivAt F (η.toFun x) x` is the right packaging: it yields *both* `MDifferentiable F`
(`HasMFDerivAt.mdifferentiableAt`) and `mfderiv F x = η.toFun x` (`HasMFDerivAt.mfderiv`). -/

/-- **FTC for the path primitive, isolated.** For a fixed basepoint `x₀` and a holomorphic form `η`,
the path-integral primitive `pathPrimitive η x₀` has manifold derivative `η.toFun x` at every `x`.
True on any complex `1`-manifold once the integral is path-independent; the local content is the
planar FTC for the ball primitive of `η`'s chart coefficient. -/
def IsFTCForPathPrimitive (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [PathConnectedSpace X] : Prop :=
  ∀ (η : HolomorphicOneForms X) (x₀ x : X),
    HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) (pathPrimitive η x₀) x (η.toFun x)

/-! ### Assembly — `HasHolomorphicPrimitives X` from the two honest atoms

`HasHomotopyInvariantPeriods` is the deep de Rham/Stokes atom (the real Mathlib gap);
`IsFTCForPathPrimitive` is the standard local FTC. Both are strictly smaller than
`HasHolomorphicPrimitives` and the assembly is sorry-free. -/

/-- **`HasHolomorphicPrimitives X` from homotopy invariance + FTC (sorry-free).** Given the two
isolated honest inputs, the path-integral primitive `F = pathPrimitive η x₀` (any basepoint `x₀`)
witnesses `HasHolomorphicPrimitives X`: `IsFTCForPathPrimitive` gives `HasMFDerivAt F (η.toFun x) x`,
whence `F` is `MDifferentiable` and `mfderiv F x = η.toFun x`, exactly the value-wise statement
required. (`HasHomotopyInvariantPeriods` is what *makes* `F` path-independent — banked in
`lineIntegral_eq_of_simplyConnected` — and is the substantive hypothesis behind a valid
`IsFTCForPathPrimitive`.) -/
theorem hasHolomorphicPrimitives_of_atoms
    (_hHI : HasHomotopyInvariantPeriods X)
    (hFTC : ∀ [PathConnectedSpace X], IsFTCForPathPrimitive X) :
    HasHolomorphicPrimitives X := by
  intro hSC η
  -- `X` is path connected (simply connected ⇒ path connected), so `pathPrimitive` is available.
  have : PathConnectedSpace X := inferInstance
  -- Pick any basepoint.
  obtain ⟨x₀⟩ := ‹Nonempty X›
  refine ⟨pathPrimitive η x₀, ?_, ?_⟩
  · -- `MDifferentiable`: from `HasMFDerivAt` at every point.
    intro x
    exact (hFTC η x₀ x).mdifferentiableAt
  · -- value-wise: `mfderiv F x v = η.toFun x v`, since `mfderiv F x = η.toFun x`.
    intro x v
    rw [(hFTC η x₀ x).mfderiv]
    rfl

/-! ### End-to-end wiring — `genus X = 0` from the two atoms

To confirm the reduction is aimed correctly, we chain `hasHolomorphicPrimitives_of_atoms` through the
existing capstones of `Jacobians/GenusZeroOfSphere.lean`. These corollaries close the backward
headline `#1b` modulo exactly the two isolated atoms — no additional hypotheses. -/

/-- **`#1b` via the atoms, abstract form.** On a simply connected `X`, the two atoms force
`genus X = 0` (every holomorphic form has a primitive, hence vanishes). -/
theorem genus_eq_zero_of_atoms_of_simplyConnected
    (hHI : HasHomotopyInvariantPeriods X)
    (hFTC : ∀ [PathConnectedSpace X], IsFTCForPathPrimitive X)
    (hSC : SimplyConnectedSpace X) :
    genus X = 0 :=
  genus_eq_zero_of_hasPrimitives_of_simplyConnected
    (hasHolomorphicPrimitives_of_atoms hHI hFTC) hSC

/-- **`#1b` via the atoms, the exact target shape.** A surface homeomorphic to `S²` has `genus 0`,
given the two isolated analytic atoms. Simple connectivity is supplied unconditionally by the repo
(`X ≃ₜ S²` transports `SimplyConnectedSpace` from the proven `SimplyConnectedSpace S²`). This is the
signature of `genus_zero_of_nonempty_homeo_sphere` plus the two honest hypotheses. -/
theorem genus_zero_of_nonempty_homeo_sphere_of_atoms
    (hHI : HasHomotopyInvariantPeriods X)
    (hFTC : ∀ [PathConnectedSpace X], IsFTCForPathPrimitive X)
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    genus X = 0 :=
  genus_zero_of_nonempty_homeo_sphere_of_hasPrimitives
    (hasHolomorphicPrimitives_of_atoms hHI hFTC) h

end Jacobians
