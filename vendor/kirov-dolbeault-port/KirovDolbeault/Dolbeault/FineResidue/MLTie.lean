/-
Copyright (c) 2026 Michael R Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R Douglas
-/
import KirovDolbeault.Dolbeault.FineResidue.Integral
import KirovDolbeault.Dolbeault.FineResidue.OmegaWitness
import KirovDolbeault.Dolbeault.FineResidue.Stokes
import KirovDolbeault.Dolbeault.FineResidue.CoboundaryVanish

/-!
# R6 — the simple-pole Mittag-Leffler tie

The keystone rung of the fine-sheaf residue ladder
(`docs/planning/R6_HANDOFF.md`): on a chart-disk cover where the pole `a`
lies in a single cover set (`MLIsolated`), the residue functional of the
glued `(1,1)` family of the simple-pole Mittag-Leffler cocycle equals the
residue:

  `resFunctional 𝔇 (mlGlue ...) = r · g j₀ (chartMap 𝔇 j₀ a)`

and, normalized (`g j₀ = 1` at the pole), exactly `r` — the END-TO-END SIGN
TEST `resFunctional_mlCocycle_residue_one` demanded by the R0 contract.

## Orientation contract (IMPORTANT for R7)

The ML cocycle here is `mlCocycle i j := mlPart i − mlPart j` (NOT `j − i`).
With this orientation the split is `s_j = B − p_j` (`B = ρ_{j₀}·P` the
smeared pole), `∂̄s_j = ∂̄B̃` off the pole, and the functional evaluates to
`+r` under `resNormalization = −π⁻¹` (R0). The opposite orientation gives
`−r`. R7's descent into the port's Čech `δ` MUST match this orientation;
the sign-test lemma pins it kernel-side.

Sign derivation (R0 cited, never re-derived):
`resIntegralFun = ∫ ∂̄(χ·r/(z−α))·g̃ = r·(−π)·χ(α)·g̃(α)` (Cauchy-Pompeiu via
`integral_dbar_smearedSimplePole`'s mechanism, `χ(α) = 1` since the other
PoU weights vanish near the isolated pole), times `resNormalization = −π⁻¹`
gives `+ r·g̃(α)`.
-/

noncomputable section

open scoped Manifold ContDiff Topology Classical
open MeasureTheory

namespace Jacobians.Dolbeault.FineResidue

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]
    (𝔇 : ChartDiskCover X)

/-- The pole `a` lies in the cover set `U j₀` and in NO other cover set —
the K-point/pole refinement discipline (Glue/OmegaWitness docstrings). -/
def MLIsolated (j₀ : 𝔇.toFiniteCover.ι) (a : X) : Prop :=
  a ∈ (𝔇.U j₀ : Set X) ∧ ∀ i, i ≠ j₀ → a ∉ (𝔇.U i : Set X)

/-- The global principal-part function of a simple pole at `a` with residue
`r`, read through the distinguished chart: `P x = r·(z(x) − z(a))⁻¹`.
Junk-valued off `U j₀`; holomorphic on `U j₀ \ {a}` in the chart. -/
def mlPrincipal (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) : X → ℂ :=
  fun x => r * (chartMap 𝔇 j₀ x - chartMap 𝔇 j₀ a)⁻¹

/-- The one-point ML part family: the principal part on the distinguished
set, `0` elsewhere. -/
def mlPart (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) :
    𝔇.toFiniteCover.ι → X → ℂ :=
  fun i => if i = j₀ then mlPrincipal 𝔇 j₀ a r else 0

/-- The simple-pole ML overlap cocycle, in the ORIENTATION the sign test
pins (see the module docstring): `w i j = p_i − p_j`. -/
def mlCocycle (j₀ : 𝔇.toFiniteCover.ι) (a : X) (r : ℂ) :
    𝔇.toFiniteCover.ι → 𝔇.toFiniteCover.ι → X → ℂ :=
  fun i j x => mlPart 𝔇 j₀ a r i x - mlPart 𝔇 j₀ a r j x

section Hypotheses

variable {𝔇} {j₀ : 𝔇.toFiniteCover.ι} {a : X} {r : ℂ}

/-- Difference families are overlap cocycles (both orientations). -/
theorem isOverlapCocycle_mlCocycle :
    IsOverlapCocycle 𝔇 (mlCocycle 𝔇 j₀ a r) := by
  intro i j k x hx
  simp only [mlCocycle]
  ring

/-- The chart denominator of the principal part is nonvanishing away from
the pole (chart injectivity on the source). -/
theorem mlDenom_ne_zero (hiso : MLIsolated 𝔇 j₀ a) {x : X}
    (hxj : x ∈ (𝔇.U j₀ : Set X)) (hxa : x ≠ a) :
    chartMap 𝔇 j₀ x - chartMap 𝔇 j₀ a ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => hxa ((chartAt ℂ (𝔇.center j₀)).injOn
    (mem_chartSource_of_mem_U 𝔇 hxj) (mem_chartSource_of_mem_U 𝔇 hiso.1) h)

/-- The principal part is `ℝ`-smooth away from the pole (chart coordinate
smooth via `contMDiffAt_extChartAt'`, denominator nonvanishing). -/
theorem contMDiffAt_mlPrincipal (hiso : MLIsolated 𝔇 j₀ a) {x : X}
    (hxj : x ∈ (𝔇.U j₀ : Set X)) (hxa : x ≠ a) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (mlPrincipal 𝔇 j₀ a r) x := by
  have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartMap 𝔇 j₀) x :=
    contMDiffAt_extChartAt' (I := 𝓘(ℝ, ℂ)) (mem_chartSource_of_mem_U 𝔇 hxj)
  have houter : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : ℂ => r * (z - chartMap 𝔇 j₀ a)⁻¹) (chartMap 𝔇 j₀ x) :=
    contDiffAt_const.mul
      ((contDiffAt_id.sub contDiffAt_const).inv (mlDenom_ne_zero hiso hxj hxa))
  exact (contMDiffAt_iff_contDiffAt.2 houter).comp x hchart

/-- One ML part is `ℝ`-smooth at any non-pole point of its set. -/
theorem contMDiffAt_mlPart (hiso : MLIsolated 𝔇 j₀ a) {k : 𝔇.toFiniteCover.ι}
    {x : X} (hxa : x ≠ a) (hxj : k = j₀ → x ∈ (𝔇.U j₀ : Set X)) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (mlPart 𝔇 j₀ a r k) x := by
  unfold mlPart
  by_cases hk : k = j₀
  · subst hk
    rw [if_pos rfl]
    exact contMDiffAt_mlPrincipal hiso (hxj rfl) hxa
  · rw [if_neg hk]
    exact contMDiffAt_const

/-- Under isolation, every overlap avoids the pole, so the cocycle is
smooth on overlaps. -/
theorem smoothOnOverlaps_mlCocycle (hiso : MLIsolated 𝔇 j₀ a) :
    SmoothOnOverlaps 𝔇 (mlCocycle 𝔇 j₀ a r) := by
  intro i j x hx
  by_cases hij : i = j₀ ∧ j = j₀
  · refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => ?_)
    simp [mlCocycle, hij.1, hij.2]
  · have hxa : x ≠ a := by
      rcases not_and_or.mp hij with hi | hj
      · exact fun h => hiso.2 i hi (h ▸ hx.1)
      · exact fun h => hiso.2 j hj (h ▸ hx.2)
    exact (contMDiffAt_mlPart hiso hxa fun h => h ▸ hx.1).sub
      (contMDiffAt_mlPart hiso hxa fun h => h ▸ hx.2)

/-- The chart-`i` read of one ML part is `ℂ`-differentiable at non-pole
overlap coordinates: it is `r·(φ_{i j₀} z − α)⁻¹` (or `0`), with the
transition holomorphic and the denominator nonvanishing. -/
theorem differentiableAt_mlPart_read (hiso : MLIsolated 𝔇 j₀ a)
    {i k : 𝔇.toFiniteCover.ι} {x : X} (hxi : x ∈ (𝔇.U i : Set X)) (hxa : x ≠ a)
    (hxj : k = j₀ → x ∈ (𝔇.U j₀ : Set X)) :
    DifferentiableAt ℂ
      (fun z => mlPart 𝔇 j₀ a r k ((chartAt ℂ (𝔇.center i)).symm z))
      (chartMap 𝔇 i x) := by
  unfold mlPart
  by_cases hk : k = j₀
  · rw [if_pos hk]
    have hxj' := hxj hk
    -- the read IS `fun z => r * (transitionMap 𝔇 i j₀ z − α)⁻¹` definitionally
    have htrans : AnalyticAt ℂ (transitionMap 𝔇 i j₀) (chartMap 𝔇 i x) :=
      transitionMap_analyticAt 𝔇 hxi hxj'
    have hden : transitionMap 𝔇 i j₀ (chartMap 𝔇 i x) - chartMap 𝔇 j₀ a ≠ 0 := by
      rw [transitionMap_chartMap 𝔇 hxi]
      exact mlDenom_ne_zero hiso hxj' hxa
    exact (analyticAt_const.mul
      ((htrans.sub analyticAt_const).inv hden)).differentiableAt
  · rw [if_neg hk]
    exact differentiableAt_const _

/-- Under isolation, the cocycle is holomorphic on overlaps. -/
theorem holomorphicOnOverlaps_mlCocycle (hiso : MLIsolated 𝔇 j₀ a) :
    HolomorphicOnOverlaps 𝔇 (mlCocycle 𝔇 j₀ a r) := by
  intro i j x hx
  by_cases hij : i = j₀ ∧ j = j₀
  · refine (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => ?_)
    simp [mlCocycle, hij.1, hij.2]
  · have hxa : x ≠ a := by
      rcases not_and_or.mp hij with hi | hj
      · exact fun h => hiso.2 i hi (h ▸ hx.1)
      · exact fun h => hiso.2 j hj (h ▸ hx.2)
    exact (differentiableAt_mlPart_read hiso hx.1 hxa fun h => h ▸ hx.1).sub
      (differentiableAt_mlPart_read hiso hx.1 hxa fun h => h ▸ hx.2)

/-- The glued family of the ML cocycle is a global `(1,1)` family (R3's
headline applied to the verified hypotheses). -/
theorem mlGlue_mem_oneOneCoeff (hiso : MLIsolated 𝔇 j₀ a)
    {g : 𝔇.toFiniteCover.ι → ℂ → ℂ} (hg : IsOneZeroCoeff 𝔇 g) :
    glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g ∈ oneOneCoeff 𝔇 :=
  glueCoeff_mem_oneOneCoeff 𝔇 (smoothOnOverlaps_mlCocycle hiso)
    isOverlapCocycle_mlCocycle (holomorphicOnOverlaps_mlCocycle hiso) hg

end Hypotheses

section Tie

variable {𝔇} {j₀ : 𝔇.toFiniteCover.ι} {a : X} {r : ℂ}
variable {g : 𝔇.toFiniteCover.ι → ℂ → ℂ}

/-- **R6 headline — the simple-pole Mittag-Leffler tie.** On an isolated
simple pole, the residue functional of the glued ML family is the residue
times the `dz`-slot value at the pole. -/
theorem resFunctional_mlGlue (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) :
    resFunctional 𝔇 ⟨glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a r) g,
        mlGlue_mem_oneOneCoeff hiso hg⟩
      = r * g j₀ (chartMap 𝔇 j₀ a) := by
  sorry

/-- **The R0-contract sign test (END-TO-END):** a residue-1 datum with the
`dz`-slot normalized to `1` at the pole evaluates to EXACTLY `1`. -/
theorem resFunctional_mlCocycle_residue_one (hiso : MLIsolated 𝔇 j₀ a)
    (hg : IsOneZeroCoeff 𝔇 g) (hnorm : g j₀ (chartMap 𝔇 j₀ a) = 1) :
    resFunctional 𝔇 ⟨glueCoeff 𝔇 (mlCocycle 𝔇 j₀ a (1 : ℂ)) g,
        mlGlue_mem_oneOneCoeff hiso hg⟩ = 1 := by
  rw [resFunctional_mlGlue hiso hg, hnorm, mul_one]

end Tie

end Jacobians.Dolbeault.FineResidue
