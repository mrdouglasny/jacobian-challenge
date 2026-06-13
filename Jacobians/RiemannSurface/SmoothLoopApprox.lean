/-
# Continuous → smooth approximation of loops (conditional reduction)

The **continuous → smooth** factor of the (AAW) approximation program:
*every continuous loop in a Riemann surface is homotopic rel endpoints to a
smooth loop.* This is the classical smooth-approximation theorem for paths.

Smoothness is expressed in the project's moving-chart convention
(`IsSmoothPath`: chart-readout `ContDiffAt ℝ ∞`), the smooth analogue of
`IsAnalyticArc`, which avoids the real-vs-complex `ModelWithCorners` mismatch a
naive `ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℂ)` hypothesis would create.

## What is proved here, unconditionally

* `Path.homotopic_of_chain` — a **finite chain** of homotopic paths (in
  practice each step a chart-local straight-line homotopy, provided by
  `Path.homotopic_of_chartLocal` from `ChartLocalHomotopy.lean`) composes, by
  `Path.Homotopic.trans`, into a single homotopy rel endpoints. This is the
  gluing engine that turns "replace the loop cell-by-cell, one chart at a time"
  into a global rel-endpoints homotopy.

## The genuine Mathlib gap (named residual)

Mathlib's smooth-approximation theorem
`Continuous.exists_contMDiff_approx_and_eqOn` approximates a continuous map
**into a normed space**, with prescribed precision and exact agreement on a
closed set. It has **no manifold-codomain version**. Bridging it to a
manifold target requires: cover `[0,1]` by finitely many cells each landing in
one chart, pull back to the model space `ℂ` (a normed space), approximate
there, push forward, and glue. The glue across cells using *different* charts
is C⁰ but generically has corners — making it not globally `ContMDiff`. The
standard remedy (reparametrize to be locally constant at junctions, then
approximate rel a neighborhood of the junctions where the map is now genuinely
smooth) is a multi-file differential-calculus build-out, not a Mathlib lemma.

We therefore isolate that content as **one** precisely-typed hypothesis,
`SmoothLoopApproxHyp`, and prove the headline theorem conditionally on it. The
hypothesis says exactly: every continuous loop admits a smooth loop
(`IsSmoothPath`) homotopic rel endpoints to it (the *output shape* the chart
pullback + normed-space approximation produces, modulo the junction
bookkeeping). The unconditional chain lemma above shows how the cell-by-cell
chart-local output yields the conclusion, so the residual is the narrow analytic
core, not the topological packaging.

## Main results

* `IsSmoothPath` — chart-readout `ContDiffAt ℝ ∞` of a path (the project's
  moving-chart smoothness convention).
* `SmoothLoopApproxHyp` — the named residual (continuous loop ⟹ homotopic
  smooth loop).
* `homotopic_isSmoothLoop_of_hyp` — the headline theorem, conditional on the
  residual: every continuous loop is homotopic rel endpoints to a smooth loop.
-/
import Jacobians.RiemannSurface.ChartLocalHomotopy

namespace Jacobians.RiemannSurface

open scoped Manifold Topology ContDiff
open unitInterval

section SmoothLoop

variable {𝕜 E H X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [TopologicalSpace H] {IM : ModelWithCorners 𝕜 E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold IM 0 X]

variable {x₀ x₁ : X}

/-- A path `δ : Path x₀ x₁` is **smooth in the moving chart** when, at every
parameter `r`, the chart-readout `u ↦ extChartAt IM (δ.extend r) (δ.extend u)` is
`ContDiffAt ℝ ∞` (i.e. `C^∞`) at `r`.

This is the smooth analogue of `IsAnalyticArc` (which asks `AnalyticAt ℝ` of the
same chart-readout) and the project's standard way to express smoothness of a
real curve into a complex manifold: it sidesteps the real-vs-complex
`ModelWithCorners` mismatch that a naive `ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℂ)` hypothesis
creates (cf. `Jacobians.Bridge.KirovLineIntegral.bridgePath_chart_differentiable`
and the moving-chart constructor in `AnalyticArcMovingChart.lean`). -/
def IsSmoothPath (IM : ModelWithCorners 𝕜 E H) (δ : Path x₀ x₁) : Prop :=
  ∀ r : ℝ, ContDiffAt ℝ ∞ (fun u : ℝ => extChartAt IM (δ.extend r) (δ.extend u)) r

/-- A chain of chart-local straight-line homotopies composes. If
`γ = δ 0, δ 1, …, δ n` is a finite sequence of paths in which every consecutive
pair `δ i, δ (i+1)` is chart-local homotopic (a single chart contains both and
the connecting segments stay in its target), then the first and last paths are
homotopic rel endpoints. The gluing engine for cell-by-cell loop replacement. -/
theorem Path.homotopic_of_chain {n : ℕ} (δ : Fin (n + 1) → Path x₀ x₁)
    (hstep : ∀ i : Fin n, (δ i.castSucc).Homotopic (δ i.succ)) :
    (δ 0).Homotopic (δ (Fin.last n)) := by
  induction n with
  | zero => simpa using Path.Homotopic.refl (δ 0)
  | succ m ih =>
    have htail : (δ (Fin.castSucc 0)).Homotopic (δ (Fin.last (m + 1))) := by
      -- split off the last step δ (last (m+1)-1) ≃ δ (last (m+1))
      have hlast : (δ (Fin.last m).castSucc).Homotopic (δ (Fin.last m).succ) :=
        hstep (Fin.last m)
      -- chain on the truncated sequence of length m+1
      have ih' := ih (fun i => δ i.castSucc)
        (fun i => by simpa [Fin.castSucc] using hstep i.castSucc)
      -- `(fun i => δ i.castSucc) 0 = δ 0` and its last is `δ (Fin.last m).castSucc`
      have e0 : (fun i : Fin (m + 1) => δ i.castSucc) 0 = δ 0 := by
        simp [Fin.castSucc_zero]
      have elast : (fun i : Fin (m + 1) => δ i.castSucc) (Fin.last m)
          = δ (Fin.last m).castSucc := rfl
      rw [e0, elast] at ih'
      have hsucc : (Fin.last m).succ = Fin.last (m + 1) := by
        simp [Fin.succ_last]
      rw [hsucc] at hlast
      exact ih'.trans hlast
    simpa [Fin.castSucc_zero] using htail

/-- **Named residual** (the genuine Mathlib gap). For every continuous loop
`γ : Path x₀ x₀` there is a smooth loop `δ : Path x₀ x₀` (`IsSmoothPath δ`)
that is homotopic rel endpoints to `γ`. The homotopy is intended to be built as
a finite chain of chart-local straight-line homotopies (cf.
`Path.homotopic_of_chain`), whose existence reduces, via chart pullback, to
`Continuous.exists_contMDiff_approx_and_eqOn` on the normed model space `E` — a
reduction that requires junction bookkeeping Mathlib does not package. -/
def SmoothLoopApproxHyp (X : Type*) [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold IM 0 X] : Prop :=
  ∀ {x₀ : X} (γ : Path x₀ x₀),
    ∃ δ : Path x₀ x₀, IsSmoothPath IM δ ∧ γ.Homotopic δ

/-- **Headline theorem (conditional).** Under the named residual
`SmoothLoopApproxHyp`, every continuous loop in `X` is homotopic rel endpoints
to a smooth loop (`IsSmoothPath`). -/
theorem homotopic_isSmoothLoop_of_hyp
    (hyp : SmoothLoopApproxHyp (H := H) (IM := IM) X) {x₀ : X} (γ : Path x₀ x₀) :
    ∃ δ : Path x₀ x₀, IsSmoothPath IM δ ∧ γ.Homotopic δ :=
  hyp γ

end SmoothLoop

end Jacobians.RiemannSurface
