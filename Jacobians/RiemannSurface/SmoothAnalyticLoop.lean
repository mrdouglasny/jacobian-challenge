/-
# Real-analytic curves into a complex 1-manifold, and the smooth → analytic wall

This module isolates the **deepest factor of T-GEN**: the reduction of a
continuous loop on a compact Riemann surface to a piecewise-real-analytic
(`AnalyticLoop`) representative homotopic to it rel endpoints. The
sibling-lane factorisation is

```
continuous loop  ⇝  smooth loop  ⇝  AnalyticLoop   (rel endpoints)
```

and this file owns the **smooth ⇝ analytic** arrow, which is classically the
Grauert/Whitney real-analytic approximation theorem.

## The cheapest sufficient formulation

`AnalyticLoop.ofMovingChart` (`AnalyticArcMovingChart.lean`) shows that the
predicate an `AnalyticLoop` must satisfy is the **moving-chart, pointwise**
condition

```
hmov : ∀ r, AnalyticAt ℝ (fun u => extChartAt 𝓘(ℂ) (γ r) (γ u)) r
```

— for every parameter `r`, the readout of `γ` *in the chart based at `γ r`* is
real-analytic at `r`. This is strictly weaker than a global real-analytic
parametrisation, and it is **exactly** the unfolding of "the chart readout is
`C^ω` at every point". We package that as `IsAnalyticCurve` and show it is the
moving-chart condition (both directions, `ContDiffAt ℝ ω ↔ AnalyticAt ℝ` via
`ContDiffAt.analyticAt` / `AnalyticAt.contDiffAt`). Hence:

* **`AnalyticLoop.ofAnalyticCurve`** — *any* continuous, closed,
  `IsAnalyticCurve` loop is an `AnalyticLoop`, **unconditionally** (no axiom,
  no Grauert). This is the payoff of the moving-chart definition: a genuinely
  real-analytic loop needs no approximation at all.

## Why C^∞ → C^ω needs Grauert (honest gap)

The remaining content — turning a merely **smooth** (`C^∞`) loop into an
analytic one rel endpoints — is genuinely Grauert/Whitney and absent from
Mathlib. The obstruction (confirmed by a deep-think review) is global: a loop
leaves any single chart, so one cannot Fourier/Stone–Weierstrass-approximate in
one chart's coordinates and be done; gluing `C^ω` approximations across
overlapping charts fails because a non-constant real-analytic partition of
unity does not exist (identity theorem). The standard proof needs a
real-analytic embedding `X ↪ ℝ^N` with a real-analytic tubular-neighbourhood
retraction — neither is in Mathlib (and the `IsManifold 𝓘(ℝ, ℂ) ω X` instance
that would even let one *state* `ContMDiff … ω` for a curve into `X` is itself
absent).

We therefore name the wall as a single hypothesis,
`SmoothLoopAnalyticApprox`, with a precise signature, and prove the target
conditionally on it: `analyticLoop_homotopic_of_smooth`.

## Main results

* `IsAnalyticCurve` / `IsSmoothCurve` — chart-readout `C^ω` / `C^∞` curve
  predicates (portable; need only `IsManifold 𝓘(ℂ) ω X`).
* `isAnalyticCurve_iff_movingChart` — `IsAnalyticCurve` is the moving-chart
  condition.
* `AnalyticLoop.ofAnalyticCurve` — analytic loop ⇒ `AnalyticLoop`
  (unconditional).
* `SmoothLoopAnalyticApprox` — the named Grauert residual (one hypothesis).
* `analyticLoop_homotopic_of_smooth` — smooth loop ⇒ homotopic-rel-endpoints
  `AnalyticLoop`, conditional on `SmoothLoopAnalyticApprox`.
-/
import Jacobians.RiemannSurface.AnalyticArcMovingChart
import Jacobians.Axioms.PeriodCycleBasis

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open Jacobians.Axioms (loopToPath)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-! ### Real-analytic and smooth curve predicates -/

/-- A curve `γ : ℝ → X` is a **real-analytic curve** when, at every parameter
`r`, its readout in the chart based at `γ r` is `C^ω` (real-analytic) at `r`.

This is the typeclass-light, portable formulation of "real-analytic curve into
`X`": it refers only to `extChartAt 𝓘(ℂ)` and `ContDiffAt ℝ ω`, so it is
well-typed against the complex-analytic manifold structure
`IsManifold 𝓘(ℂ) ω X` alone — no `IsManifold 𝓘(ℝ, ℂ) ω X` instance (absent
from Mathlib) is required. By `isAnalyticCurve_iff_movingChart` it is exactly
the moving-chart condition consumed by `AnalyticLoop.ofMovingChart`. -/
def IsAnalyticCurve (γ : ℝ → X) : Prop :=
  ∀ r : ℝ, ContDiffAt ℝ ω (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ r)) (γ u)) r

/-- A curve `γ : ℝ → X` is a **smooth curve** when, at every parameter `r`, its
readout in the chart based at `γ r` is `C^∞` at `r`. The `C^∞` analogue of
`IsAnalyticCurve`; `IsAnalyticCurve.toSmooth` shows analytic ⇒ smooth. -/
def IsSmoothCurve (γ : ℝ → X) : Prop :=
  ∀ r : ℝ, ContDiffAt ℝ (∞ : ℕ∞ω) (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ r)) (γ u)) r

omit [IsManifold 𝓘(ℂ) ω X] in
/-- `IsAnalyticCurve` is *literally* the moving-chart pointwise analyticity
condition consumed by `AnalyticLoop.ofMovingChart`, via the Mathlib bridge
`ContDiffAt ℝ ω ↔ AnalyticAt ℝ`. -/
theorem isAnalyticCurve_iff_movingChart (γ : ℝ → X) :
    IsAnalyticCurve γ ↔
      ∀ r : ℝ, AnalyticAt ℝ (fun u : ℝ => (extChartAt 𝓘(ℂ) (γ r)) (γ u)) r :=
  ⟨fun h r => (h r).analyticAt, fun h r => (h r).contDiffAt⟩

omit [IsManifold 𝓘(ℂ) ω X] in
/-- A real-analytic curve is smooth. -/
theorem IsAnalyticCurve.toSmooth {γ : ℝ → X} (h : IsAnalyticCurve γ) :
    IsSmoothCurve γ :=
  fun r => (h r).of_le le_top

/-! ### Unconditional: a real-analytic loop is an `AnalyticLoop` -/

/-- **A continuous, closed, real-analytic curve is an `AnalyticLoop`.**

No axiom, no Grauert: the moving-chart definition of `AnalyticLoop` is satisfied
*directly* by a genuinely real-analytic loop. This is the payoff of the
moving-chart formulation — the deep approximation theorem is only needed to
*produce* such a loop from a merely smooth one (see
`analyticLoop_homotopic_of_smooth`). -/
noncomputable def AnalyticLoop.ofAnalyticCurve (γ : ℝ → X) (hcont : Continuous γ)
    (hγ : IsAnalyticCurve γ) (hclosed : γ 1 = γ 0) :
    AnalyticLoop X (γ 0) :=
  AnalyticLoop.ofMovingChart γ hcont
    ((isAnalyticCurve_iff_movingChart γ).mp hγ) hclosed

@[simp] theorem AnalyticLoop.ofAnalyticCurve_arc_extend (γ : ℝ → X)
    (hcont : Continuous γ) (hγ : IsAnalyticCurve γ) (hclosed : γ 1 = γ 0) :
    (AnalyticLoop.ofAnalyticCurve γ hcont hγ hclosed).arc.extend = γ :=
  rfl

/-- The underlying `Path` of `AnalyticLoop.ofAnalyticCurve γ …` is the path of
`γ` itself: its `toFun` is `γ ∘ Subtype.val`. Lets one compare it (up to
homotopy) with a smooth loop's path. -/
theorem AnalyticLoop.ofAnalyticCurve_loopToPath_apply (γ : ℝ → X)
    (hcont : Continuous γ) (hγ : IsAnalyticCurve γ) (hclosed : γ 1 = γ 0)
    (t : unitInterval) :
    loopToPath (AnalyticLoop.ofAnalyticCurve γ hcont hγ hclosed) t = γ t.val :=
  rfl

/-! ### The named Grauert residual and the conditional smooth → analytic theorem -/

/-- The `Path x₀ x₀` underlying a continuous, closed curve `γ` based at `x₀`
(its restriction to `unitInterval`). Mirrors `loopToPath` for raw curves, so the
two can be compared up to `Path.Homotopic`. -/
def curveToPath {γ : ℝ → X} (hcont : Continuous γ) {x₀ : X}
    (hsrc : γ 0 = x₀) (hclosed : γ 1 = γ 0) : Path x₀ x₀ where
  toFun := fun t => γ t.val
  continuous_toFun := hcont.comp continuous_subtype_val
  source' := by simpa using hsrc
  target' := by simpa [hclosed] using hsrc

/-- **The smooth → real-analytic approximation wall (Grauert/Whitney), named.**

Hypothesis: every continuous, closed *smooth* curve `γ` based at `x₀` admits a
real-analytic `AnalyticLoop` based at `x₀` whose underlying path is homotopic to
`γ`'s path **rel endpoints** (`Path.Homotopic`, which for paths is automatically
rel endpoints).

This is the single Mathlib-absent fact in the smooth → analytic arrow of T-GEN.
It is classical (Grauert 1958 / Whitney–Bruhat real-analytic approximation):
embed `X` real-analytically in `ℝ^N`, take a real-analytic tubular-neighbourhood
retraction `π`, globally polynomial/Fourier-approximate the loop in `ℝ^N`
`C¹`-closely (so the straight-line homotopy stays in the tube and fixes the
basepoint), then push down by `π`. Neither the analytic embedding nor the
analytic tubular neighbourhood is presently in Mathlib, so this is named, not
proved here. Provided as a hypothesis (not a global `axiom`) so consumers see it
explicitly and a future Grauert formalisation discharges it in place.

`Reference:` Grauert, *On Levi's problem and the imbedding of real-analytic
manifolds*, Ann. of Math. 68 (1958); Whitney–Bruhat, Comment. Math. Helv. 33
(1959). -/
def SmoothLoopAnalyticApprox (x₀ : X) : Prop :=
  ∀ (γ : ℝ → X) (hcont : Continuous γ), IsSmoothCurve γ →
    (hclosed : γ 1 = γ 0) → (hsrc : γ 0 = x₀) →
      ∃ δ : AnalyticLoop X x₀,
        Path.Homotopic (loopToPath δ) (curveToPath hcont hsrc hclosed)

/-- **Smooth loop ⇒ homotopic-rel-endpoints `AnalyticLoop`, conditional on the
named Grauert wall `SmoothLoopAnalyticApprox`.**

This is the deepest factor of T-GEN ("(AAW) smooth ⇝ analytic"). It is stated
conditionally on the single Mathlib-absent approximation hypothesis; the rest is
definitional repackaging. A genuinely real-analytic loop needs no hypothesis at
all — use `AnalyticLoop.ofAnalyticCurve` directly. -/
theorem analyticLoop_homotopic_of_smooth {x₀ : X}
    (happrox : SmoothLoopAnalyticApprox x₀)
    (γ : ℝ → X) (hcont : Continuous γ) (hsmooth : IsSmoothCurve γ)
    (hclosed : γ 1 = γ 0) (hsrc : γ 0 = x₀) :
    ∃ δ : AnalyticLoop X x₀,
      Path.Homotopic (loopToPath δ) (curveToPath hcont hsrc hclosed) :=
  happrox γ hcont hsmooth hclosed hsrc

end Jacobians.RiemannSurface
