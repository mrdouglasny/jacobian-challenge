/-
# Chart-transition derivative identities

General facts about the overlap of two charts on an analytic ℂ-manifold,
used to prove that a cotangent cocycle that holds in one chart-direction
also holds in the reverse direction.

`transition_fderiv_mul`: the derivatives of the two mutually-inverse chart
transitions multiply to `1`. Axiom-free. Used in
`Hyperelliptic/EvenForm.lean` to derive the `inr_inl` cross-summand cocycle
from the `inl_inr` one (retiring the two flagged cocycle axioms — task #21).
-/
import Mathlib

namespace Jacobians.GeneralResults

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- The extended coordinate chart of a complex manifold is manifold-differentiable
at every point of its source. -/
theorem chart_mdiff (q' : M) {p : M} (hp : p ∈ (extChartAt 𝓘(ℂ) q').source) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑(extChartAt 𝓘(ℂ) q')) p := by
  have hsrc : p ∈ (chartAt ℂ q').source := by rw [← extChartAt_source 𝓘(ℂ)]; exact hp
  exact ((contMDiffOn_extChartAt (n := 
      ω)).mdifferentiableOn WithTop.top_ne_zero _ hsrc).mdifferentiableAt
    (IsOpen.mem_nhds (chartAt ℂ q').open_source hsrc)

/-- The inverse of an extended coordinate chart of a complex manifold is
manifold-differentiable at every point of its target. -/
theorem chartsymm_mdiff (q : M) {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ) q).target) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑(extChartAt 𝓘(ℂ) q).symm) z :=
  ((contMDiffOn_extChartAt_symm q).mdifferentiableOn WithTop.top_ne_zero _ hz).mdifferentiableAt
    (IsOpen.mem_nhds (isOpen_extChartAt_target q) hz)

/-- The derivatives of the two mutually-inverse chart transitions
`φ_{q'} ∘ φ_q⁻¹` and `φ_q ∘ φ_{q'}⁻¹` multiply to `1`. -/
lemma transition_fderiv_mul (q q' : M) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) q).target)
    (hzs : (extChartAt 𝓘(ℂ) q).symm z ∈ (extChartAt 𝓘(ℂ) q').source) :
    (fderiv ℂ (⇑(extChartAt 𝓘(ℂ) q') ∘ ⇑(extChartAt 𝓘(ℂ) q).symm) z 1) *
      (fderiv ℂ (⇑(extChartAt 𝓘(ℂ) q) ∘ ⇑(extChartAt 𝓘(ℂ) q').symm)
        ((extChartAt 𝓘(ℂ) q') ((extChartAt 𝓘(ℂ) q).symm z)) 1) = 1 := by
  set φq := extChartAt 𝓘(ℂ) q with hφq
  set φq' := extChartAt 𝓘(ℂ) q' with hφq'
  set F : ℂ → ℂ := ⇑φq' ∘ ⇑φq.symm with hF
  set G : ℂ → ℂ := ⇑φq ∘ ⇑φq'.symm with hG
  set w := φq' (φq.symm z) with hw
  have hFdiff : DifferentiableAt ℂ F z :=
    mdifferentiableAt_iff_differentiableAt.mp ((chart_mdiff q' hzs).comp z (chartsymm_mdiff q hz))
  have hwt : w ∈ φq'.target := φq'.map_source hzs
  have hsymm_w : φq'.symm w = φq.symm z := φq'.left_inv hzs
  have hws : φq'.symm w ∈ φq.source := by rw [hsymm_w]; exact φq.map_target hz
  have hGdiff : DifferentiableAt ℂ G w :=
    mdifferentiableAt_iff_differentiableAt.mp ((chart_mdiff q hws).comp w (chartsymm_mdiff q' hwt))
  -- G ∘ F =ᶠ id near z
  have hGF : (G ∘ F) =ᶠ[𝓝 z] id := by
    have hpre : φq.symm ⁻¹' φq'.source ∈ 𝓝 z := by
      have hcont : ContinuousAt φq.symm z :=
        (continuousOn_extChartAt_symm q).continuousAt (IsOpen.mem_nhds
          (isOpen_extChartAt_target q) hz)
      exact hcont.preimage_mem_nhds (IsOpen.mem_nhds (isOpen_extChartAt_source q') hzs)
    have hS : (φq.target ∩ φq.symm ⁻¹' φq'.source) ∈ 𝓝 z :=
      Filter.inter_mem (IsOpen.mem_nhds (isOpen_extChartAt_target q) hz) hpre
    filter_upwards [hS] with x hx
    obtain ⟨hxt, hxs⟩ := hx
    change G (F x) = x
    simp only [hF, hG, Function.comp_apply]
    rw [φq'.left_inv hxs, φq.right_inv hxt]
  have hF' : HasDerivAt F (deriv F z) z := hFdiff.hasDerivAt
  have hG' : HasDerivAt G (deriv G w) w := hGdiff.hasDerivAt
  have hcomp : HasDerivAt (G ∘ F) (deriv G w * deriv F z) z :=
    (show w = F z from rfl) ▸ hG' |>.comp z hF'
  have hid : HasDerivAt (G ∘ F) 1 z :=
    (hasDerivAt_id z).congr_of_eventuallyEq hGF
  have hmul : deriv G w * deriv F z = 1 := hcomp.unique hid
  have e1 : fderiv ℂ F z 1 = deriv F z := rfl
  have e2 : fderiv ℂ G w 1 = deriv G w := rfl
  rw [e1, e2, mul_comm]; exact hmul

end Jacobians.GeneralResults
