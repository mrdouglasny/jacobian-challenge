/-
# Chart-local straight-line homotopy of paths

The self-contained geometric primitive underpinning the **continuous → smooth**
factor of the (AAW) approximation program: two paths that agree at their
endpoints and stay *together inside one chart* (their chart readouts are joined
by a straight segment that never leaves the chart target) are homotopic rel
endpoints, via the straight-line homotopy pulled back through the chart.

This is the geometric heart of smooth/analytic approximation on a manifold: a
`C⁰`-close approximation read in a chart differs from the original by a segment
that stays inside the (open) chart target, so the chart-local straight-line
homotopy connects them. No smoothness is used here — only the topology of the
chart — so the lemma is reusable for *any* C⁰-close-in-a-chart pair.

## Design: model-agnostic

The primitive is stated for an **arbitrary** `PartialEquiv X E` `e` into a real
normed space `E`, with continuity of `e` on its source and of `e.symm` on its
target supplied as hypotheses. `extChartAt I p` of any (boundaryless or not)
manifold is exactly such a map, with continuity given by `continuousOn_extChartAt`
and `continuousOn_extChartAt_symm`; the convenience wrappers
`Path.homotopyOfExtChartLocal` / `Path.homotopic_of_extChartLocal` specialise to
it. Keeping `e` as data rather than tying it to a `ModelWithCorners` avoids the
real-vs-complex scalar diamond (`NormedSpace ℝ E` vs `NormedSpace 𝕜 E`) that
would otherwise stall unification when applying the lemma to a complex chart
such as `extChartAt 𝓘(ℂ) p`.

## Main results

* `Path.homotopyOfPartialEquivLocal` / `Path.homotopic_of_partialEquivLocal` —
  the model-agnostic primitive (the `Path.Homotopy` and its relation form).
* `Path.homotopic_of_extChartLocal` — the manifold specialisation to
  `extChartAt I p`, directly usable on a Riemann surface (`I = 𝓘(ℂ)`).

The chart target is open but **not** convex in general, so the
segment-containment is a genuine hypothesis — precisely what a `C⁰`-closeness
bound supplies (a segment of length `< ε` around a point at chart-distance `> ε`
from the target's complement).
-/
import Mathlib

namespace Jacobians.RiemannSurface

open scoped Manifold Topology
open unitInterval

section PartialEquivLocal

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
variable {x₀ x₁ : X}

/-- **Chart-local straight-line homotopy (model-agnostic).** Let `f g : Path x₀ x₁`
and let `e : PartialEquiv X E` map into a real normed space, continuous on its
source and with continuous inverse on its target. If both paths land in `e.source`
and for every parameter the straight segment between the two `e`-readouts stays in
`e.target`, then `f` is homotopic to `g` rel endpoints, by the straight-line
homotopy `(s, t) ↦ e.symm (lineMap (e (f t)) (e (g t)) s)`. -/
noncomputable def Path.homotopyOfPartialEquivLocal (f g : Path x₀ x₁)
    (e : PartialEquiv X E) (he : ContinuousOn e e.source)
    (he' : ContinuousOn e.symm e.target)
    (hf : ∀ t : I, f t ∈ e.source) (hg : ∀ t : I, g t ∈ e.source)
    (hseg : ∀ t : I, segment ℝ (e (f t)) (e (g t)) ⊆ e.target) :
    f.Homotopy g where
  toFun := fun st => e.symm (AffineMap.lineMap (e (f st.2)) (e (g st.2)) (st.1 : ℝ))
  continuous_toFun := by
    have hcf : Continuous fun st : I × I => e (f st.2) :=
      he.comp_continuous (f.continuous.comp continuous_snd) (fun st => hf st.2)
    have hcg : Continuous fun st : I × I => e (g st.2) :=
      he.comp_continuous (g.continuous.comp continuous_snd) (fun st => hg st.2)
    have hs : Continuous fun st : I × I => (st.1 : ℝ) := continuous_subtype_val.comp continuous_fst
    have hline : Continuous fun st : I × I =>
        AffineMap.lineMap (e (f st.2)) (e (g st.2)) (st.1 : ℝ) := by
      simp only [AffineMap.lineMap_apply_module]
      exact (((continuous_const.sub hs).smul hcf).add (hs.smul hcg))
    refine he'.comp_continuous hline ?_
    intro st
    exact hseg st.2 (lineMap_mem_segment (𝕜 := ℝ) (e (f st.2)) (e (g st.2)) st.1.2)
  map_zero_left := by
    intro t
    simp only [Path.coe_toContinuousMap]
    rw [show ((0 : I) : ℝ) = 0 from rfl, AffineMap.lineMap_apply_zero]
    exact e.left_inv (hf t)
  map_one_left := by
    intro t
    simp only [Path.coe_toContinuousMap]
    rw [show ((1 : I) : ℝ) = 1 from rfl, AffineMap.lineMap_apply_one]
    exact e.left_inv (hg t)
  prop' := by
    intro s t ht
    have hft : f t = g t := by
      rcases ht with ht | ht
      · rw [ht]; simp
      · rw [Set.mem_singleton_iff] at ht; rw [ht]; simp
    simp only [Path.coe_toContinuousMap]
    change e.symm (AffineMap.lineMap (e (f t)) (e (g t)) (s : ℝ)) = f t
    rw [hft, AffineMap.lineMap_same, AffineMap.coe_const, Function.const_apply, e.left_inv (hg t)]

/-- **Chart-local homotopy (relation form, model-agnostic).** Two paths whose
images lie in the source of a continuous `PartialEquiv` `e` into a real normed
space, joined parameterwise by `e.target` segments, are homotopic rel endpoints. -/
theorem Path.homotopic_of_partialEquivLocal (f g : Path x₀ x₁)
    (e : PartialEquiv X E) (he : ContinuousOn e e.source)
    (he' : ContinuousOn e.symm e.target)
    (hf : ∀ t : I, f t ∈ e.source) (hg : ∀ t : I, g t ∈ e.source)
    (hseg : ∀ t : I, segment ℝ (e (f t)) (e (g t)) ⊆ e.target) :
    f.Homotopic g :=
  ⟨Path.homotopyOfPartialEquivLocal f g e he he' hf hg hseg⟩

end PartialEquivLocal

section ExtChartLocal

variable {𝕜 E H X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  [TopologicalSpace H] {IM : ModelWithCorners 𝕜 E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold IM 0 X]
variable {x₀ x₁ : X}

set_option linter.unusedSectionVars false in
/-- **Chart-local homotopy via `extChartAt`.** The manifold specialisation of
`Path.homotopic_of_partialEquivLocal` to `e := extChartAt IM p`. Two paths whose
images lie in `(extChartAt IM p).source`, joined parameterwise by segments inside
`(extChartAt IM p).target`, are homotopic rel endpoints. Applies on any manifold
whose model space is a real normed space — in particular a Riemann surface,
`IM = 𝓘(ℂ)`. -/
theorem Path.homotopic_of_extChartLocal (f g : Path x₀ x₁) (p : X)
    (hf : ∀ t : I, f t ∈ (extChartAt IM p).source)
    (hg : ∀ t : I, g t ∈ (extChartAt IM p).source)
    (hseg : ∀ t : I,
      segment ℝ (extChartAt IM p (f t)) (extChartAt IM p (g t)) ⊆ (extChartAt IM p).target) :
    f.Homotopic g :=
  Path.homotopic_of_partialEquivLocal f g (extChartAt IM p)
    (continuousOn_extChartAt p) (continuousOn_extChartAt_symm p) hf hg hseg

end ExtChartLocal

end Jacobians.RiemannSurface
